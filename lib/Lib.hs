{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Lib (serverMain, indexInGhcid) where

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (runExceptT, throwE)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Coerce
import Data.Functor ((<&>))
import Data.Functor.Compose
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust, listToMaybe)
import Data.Monoid (Endo (..))
import Data.String.Conversions
import Data.Text (Text, intercalate, pack, replace, unpack)
import GHC.Iface.Ext.Types
import GHC.Plugins hiding (Type, empty, getDynFlags, (<>))
import GhcideSteal (gotoDefinition, hoverInfo, intToUInt, symbolKindOfOccName)
import HieDb
  ( ModuleInfo (modInfoName),
    getAllIndexedMods,
    getHieFilesIn,
    hieModInfo,
    initConn,
    pointCommand,
    searchDef,
    withHieDb,
    withTarget,
    type (:.) ((:.)),
  )
import HieDb.Run
  ( Options (..),
    doIndex,
  )
import HieDb.Types
  ( DefRow (..),
    HieDb,
    HieDbErr (..),
    HieTarget,
    Res,
  )
import Language.LSP.Server
  ( Handlers,
    LanguageContextEnv (..),
    LspT,
    MonadLsp,
    ServerDefinition (..),
    defaultOptions,
    getRootPath,
    requestHandler,
    runLspT,
    runServer,
    type (<~>) (Iso),
  )
import Language.LSP.Types
import Language.LSP.Types.Lens (uri)
import Lens.Micro ((^.))
import SymbolInformation (mkSymbolInformation)
import System.Directory (doesFileExist, getCurrentDirectory)
import System.FilePath ((<.>), (</>))
import System.IO (stderr)
import Utils (EK, ekbind, eklift, etbind, etpure, kbind, kcodensity, kliftIO)

-- LSP utils
getWsRoot :: MonadLsp cfg m => EK (m r) (m r) ResponseError FilePath
getWsRoot = kcodensity $ do
  mRootPath <- getRootPath
  pure $ case mRootPath of
    Nothing -> Left $ ResponseError InvalidRequest "No root workspace was found" Nothing
    Just p -> Right p

-- TODO: Store the hiedb location, cradle, and GHC libdir on startup instead of reading them on every request

-- HieDb utils
coordsHieDbToLSP :: (Int, Int) -> Maybe Position
coordsHieDbToLSP (l, c) = Position <$> intToUInt (l - 1) <*> intToUInt (c - 1)

coordsLSPToHieDb :: Position -> (Int, Int)
coordsLSPToHieDb Position {..} = (fromIntegral _line + 1, fromIntegral _character + 1)

-- {{{ hacky garbage that needs to be replaced

hardcodedSourceDirs :: [Text]
hardcodedSourceDirs = ["src", "lib", "test"]

replaceMany :: [Text] -> Text -> Text -> Text
replaceMany patterns substitution = appEndo . foldMap (Endo . flip replace substitution) $ patterns

-- Less dumb alternative compose
type LDAC :: (Type -> Type) -> (Type -> Type) -> Type -> Type
newtype LDAC f g a = LDAC (f (g a))
  deriving (Functor)
  deriving (Applicative) via (Compose f g)

instance (Applicative f, Alternative g) => Alternative (LDAC f g) where
  empty = LDAC $ pure empty
  LDAC x <|> LDAC y = LDAC $ liftA2 (<|>) x y

whicheverOfManyThingsWorks ::
  (Applicative f, Applicative g, Alternative h) =>
  [f (g (h b))] ->
  f (g (h b))
whicheverOfManyThingsWorks = coerce . asum . fmap (LDAC . LDAC)

-- TODO: Make this less hacky, involves fixing up the NULL entries in the modules table in hiedb
textDocumentIdentifierToHieFilePath :: TextDocumentIdentifier -> HieTarget
textDocumentIdentifierToHieFilePath (TextDocumentIdentifier u) =
  Left $
    unpack $
      replace ".hs" ".hie" $
        replaceMany hardcodedSourceDirs ".hiefiles" $
          pack $
            fromJust $
              uriToFilePath u

fmap2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 = fmap . fmap

-- TODO: Get rid of this hack, defer to populated modules table
moduleToTextDocumentIdentifier :: FilePath -> ModuleInfo -> IO (Maybe TextDocumentIdentifier)
moduleToTextDocumentIdentifier wsroot = fmap2 (TextDocumentIdentifier . filePathToUri) . whicheverOfManyThingsWorks (fmap (moduleFileInSourceDirIfExists . cs) hardcodedSourceDirs)
  where
    moduleFileInSourceDirIfExists :: FilePath -> ModuleInfo -> IO (Maybe FilePath)
    moduleFileInSourceDirIfExists sourceDir = ensureFilePathExists . (wsroot </>) . (sourceDir </>) . (<.> "hs") . moduleNameSlashes . modInfoName

    ensureFilePathExists :: FilePath -> IO (Maybe FilePath)
    ensureFilePathExists path = doesFileExist path <&> \b -> if b then Just path else Nothing

-- }}}

astsAtPoint :: HieFile -> (Int, Int) -> Maybe (Int, Int) -> [HieAST TypeIndex]
astsAtPoint hiefile start end = pointCommand hiefile start end id

hieFileFromTextDocumentIdentifier :: HieDb -> TextDocumentIdentifier -> IO (Either ResponseError HieFile)
hieFileFromTextDocumentIdentifier hiedb tdocId =
  first hiedbErrorToResponseError <$> withTarget hiedb (textDocumentIdentifierToHieFilePath tdocId) id

hieFileAndAstsFromPointRequest :: HieDb -> TextDocumentIdentifier -> Position -> IO (Either ResponseError (HieFile, [HieAST TypeIndex]))
hieFileAndAstsFromPointRequest hiedb tdocId position =
  hieFileFromTextDocumentIdentifier hiedb tdocId `etbind` \hiefile ->
    etpure (hiefile, astsAtPoint hiefile (coordsLSPToHieDb position) Nothing)

hieFileAndAstFromPointRequest :: HieDb -> TextDocumentIdentifier -> Position -> IO (Either ResponseError (HieFile, Maybe (HieAST TypeIndex)))
hieFileAndAstFromPointRequest hiedb tdocId position =
  fmap (second listToMaybe) <$> hieFileAndAstsFromPointRequest hiedb tdocId position

-- TODO: Render these properly
renderHieDbError :: HieDbErr -> Text
renderHieDbError =
  pack . \case
    NotIndexed modname munitid ->
      "NotIndexed ModuleName: "
        <> show modname
        <> ", "
        <> "(Maybe Unit): "
        <> show (unitString <$> munitid)
    AmbiguousUnitId modinfo ->
      "AmbiguousUnitId (NonEmpty ModuleInfo): "
        <> show modinfo
    NameNotFound occname mmodname munitid ->
      "NameNotFound OccName: "
        <> occNameString occname
        <> ", (Maybe ModuleName):"
        <> show mmodname
        <> ", (Maybe Unit): "
        <> show (unitString <$> munitid)
    NoNameAtPoint tgt hiepos ->
      "NoNameAtPoint HieTarget: "
        <> show tgt
        <> ", (Int, Int): "
        <> show hiepos
    NameUnhelpfulSpan name str ->
      "NameUnhelpfulSpan Name: "
        <> nameStableString name
        <> ", String: "
        <> str

hiedbErrorToResponseError :: HieDbErr -> ResponseError
hiedbErrorToResponseError = flip (ResponseError InternalError) Nothing . renderHieDbError

moduleSourcePathMap :: HieDb -> FilePath -> IO (Map ModuleName Uri)
moduleSourcePathMap hiedb wsroot = do
  rows <- getAllIndexedMods hiedb
  m <- sequenceA $ M.fromList $ fmap ((modInfoName &&& moduleToTextDocumentIdentifier wsroot) . hieModInfo) rows
  pure $ (M.mapMaybe . fmap) (^. uri) $ m

-- The actual code

symbolInfo :: FilePath -> Res DefRow -> IO SymbolInformation
symbolInfo wsroot (DefRow {..} :. m) = do
  let mStart = coordsHieDbToLSP (defSLine, defSCol)
      mEnd = coordsHieDbToLSP (defELine, defECol)
  mtdi <- moduleToTextDocumentIdentifier wsroot m
  case (mtdi, mStart, mEnd) of
    (Nothing, _, _) -> fail "unable to find text document corresponding to module"
    (_, Nothing, _) -> fail "unable to convert hiedb coords to lsp coords"
    (_, _, Nothing) -> fail "unable to convert hiedb coords to lsp coords"
    (Just tdi, Just start, Just end) ->
      pure $
        mkSymbolInformation
          (pack $ occNameString defNameOcc)
          (symbolKindOfOccName defNameOcc)
          Nothing
          ( Location
              { _uri = tdi ^. uri,
                _range =
                  Range
                    { _start = start,
                      _end = end
                    }
              }
          )
          (Just $ pack $ moduleNameString $ modInfoName m)

handleWorkspaceSymbolRequest :: Handlers (LspT c IO)
handleWorkspaceSymbolRequest = requestHandler SWorkspaceSymbol $ \req ->
  getWsRoot `ekbind` \wsroot -> eklift . kcodensity . liftIO $ do
    results <- withHieDb (wsroot </> ".hiedb") $ flip searchDef $ unpack $ requestQuery req
    prepareSymbolResults wsroot results
  where
    prepareSymbolResults :: FilePath -> [Res DefRow] -> IO (List SymbolInformation)
    prepareSymbolResults wsroot = fmap List . traverse (symbolInfo wsroot)

    requestQuery :: Message 'WorkspaceSymbol -> Text
    requestQuery RequestMessage {_params = WorkspaceSymbolParams {_query = q}} = q

retrieveHoverData :: HieDb -> Message 'TextDocumentHover -> IO (Either ResponseError (Maybe Hover))
retrieveHoverData hiedb RequestMessage {_params = HoverParams {..}} =
  hieFileAndAstFromPointRequest hiedb _textDocument _position `etbind` \(hiefile, mast) -> case mast of
    Nothing -> etpure Nothing
    Just ast -> etpure $
      Just $ case hoverInfo (hie_types hiefile) ast of
        (mbrange, contents) ->
          Hover
            { _range = mbrange,
              _contents = HoverContents $ MarkupContent MkMarkdown $ intercalate sectionSeparator contents
            }

handleTextDocumentHoverRequest :: Handlers (LspT c IO)
handleTextDocumentHoverRequest = requestHandler STextDocumentHover $ \req ->
  getWsRoot `ekbind` \wsroot ->
    kliftIO $
      withHieDb (wsroot </> ".hiedb") `kbind` \hiedb ->
        kcodensity $
          retrieveHoverData hiedb req

handleDefinitionRequest :: Handlers (LspT c IO)
handleDefinitionRequest = requestHandler STextDocumentDefinition $ \RequestMessage {_params = DefinitionParams {..}} ->
  getWsRoot `ekbind` \wsroot ->
    kliftIO $
      withHieDb (wsroot </> ".hiedb") `kbind` \hiedb ->
        kcodensity $
          hieFileFromTextDocumentIdentifier hiedb _textDocument `etbind` \hiefile -> do
            modmap <- moduleSourcePathMap hiedb wsroot
            result <- runMaybeT $ gotoDefinition hiedb wsroot modmap (hie_asts hiefile) _position
            pure $ case result of
              Nothing -> Left $ ResponseError InternalError "Unable to go to definition" Nothing
              Just l -> Right $ InR $ InL $ List l

doInitialize :: LanguageContextEnv a -> Message 'Initialize -> IO (Either ResponseError (LanguageContextEnv a))
doInitialize env _ = runExceptT $ do
  wsroot <- getWsRootInit
  let database = wsroot </> ".hiedb"
  lift . withHieDb database $ \hiedb -> do
    initConn hiedb
    hieFiles <- getHieFilesIn (wsroot </> ".hiefiles")
    let options =
          Options
            { trace = False,
              quiet = True,
              colour = True,
              context = Nothing,
              reindex = False,
              keepMissing = False,
              database
            }
    doIndex hiedb options stderr hieFiles
    pure env
  where
    getWsRootInit =
      case resRootPath env of
        Nothing -> throwE $ ResponseError InvalidRequest "No root workspace was found" Nothing
        Just wsroot -> pure wsroot

indexInGhcid :: IO ()
indexInGhcid = do
  currentDir <- getCurrentDirectory
  let database = currentDir </> ".hiedb"
  withHieDb database $ \hiedb -> do
    initConn hiedb
    hieFiles <- getHieFilesIn (currentDir </> ".hiefiles")
    let options =
          Options
            { trace = False,
              quiet = True,
              colour = True,
              context = Nothing,
              reindex = False,
              keepMissing = False,
              database
            }
    doIndex hiedb options stderr hieFiles

serverDef :: ServerDefinition ()
serverDef =
  ServerDefinition
    { onConfigurationChange = id,
      doInitialize = Lib.doInitialize,
      staticHandlers =
        mconcat
          [ handleWorkspaceSymbolRequest,
            handleTextDocumentHoverRequest,
            handleDefinitionRequest
          ],
      interpretHandler = \env -> Iso (runLspT env) liftIO,
      options = defaultOptions,
      defaultConfig = ()
    }

serverMain :: IO Int
serverMain = runServer serverDef
