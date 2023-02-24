{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module GhcideSteal (hoverInfo, symbolKindOfOccName, locationsAtPoint, gotoDefinition, intToUInt) where

import Control.Monad (guard)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Array
import Data.Containers.ListUtils (nubOrd)
import Data.List (isSuffixOf)
import qualified Data.Map as M
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Text as T
import GHC
import qualified GHC.Data.FastString as FS
import GHC.Iface.Ext.Types
import GHC.Iface.Ext.Utils
import GHC.Plugins hiding ((<>))
import GHC.Utils.Monad (mapMaybeM)
import HieDb hiding (pointCommand)
import Language.LSP.Types
import System.FilePath ((</>))

-- {{{ Development.IDE.Types.Location
--
-- }}}

-- {{{ Development.IDE.GHC.Error

realSrcSpanToRange :: RealSrcSpan -> Maybe Range
realSrcSpanToRange real =
  Range
    <$> (realSrcLocToPosition $ realSrcSpanStart real)
    <*> (realSrcLocToPosition $ realSrcSpanEnd real)

realSrcLocToPosition :: RealSrcLoc -> Maybe Position
realSrcLocToPosition real =
  Position
    <$> intToUInt (srcLocLine real - 1)
    <*> intToUInt (srcLocCol real - 1)

-- | Extract a file name from a GHC SrcSpan (use message for unhelpful ones)
-- FIXME This may not be an _absolute_ file name, needs fixing.
srcSpanToFilename :: SrcSpan -> Maybe FilePath
srcSpanToFilename (UnhelpfulSpan _) = Nothing
srcSpanToFilename (RealSrcSpan real _) = Just $ FS.unpackFS $ srcSpanFile real

srcSpanToLocation :: FilePath -> SrcSpan -> Maybe Location
srcSpanToLocation wsroot src = do
  fs <- srcSpanToFilename src
  rng <- srcSpanToRange src
  pure $ Location (filePathToUri $ wsroot </> fs) rng

-- | Convert a GHC SrcSpan to a DAML compiler Range
srcSpanToRange :: SrcSpan -> Maybe Range
srcSpanToRange (UnhelpfulSpan _) = Nothing
srcSpanToRange (RealSrcSpan real _) = realSrcSpanToRange real

-- }}}

showGhc :: Outputable a => a -> T.Text
showGhc = showSD . ppr

showSD :: SDoc -> T.Text
showSD = T.pack . unsafePrintSDoc

pprStyleToSDocContext :: PprStyle -> SDocContext
pprStyleToSDocContext pprStyle = defaultSDocContext {sdocStyle = pprStyle}

unsafePrintSDoc :: SDoc -> String
unsafePrintSDoc sdoc = renderWithContext sdocContext sdoc
  where
    sdocContext = pprStyleToSDocContext $ mkUserStyle neverQualify AllTheWay

showNameWithoutUniques :: Outputable a => a -> T.Text
showNameWithoutUniques outputable = T.pack $ renderWithContext sdocContext (ppr outputable)
  where
    sdocContext = pprStyleToSDocContext $ mkUserStyle neverQualify AllTheWay

hoverInfo :: Array TypeIndex HieTypeFlat -> HieAST TypeIndex -> (Maybe Range, [T.Text])
hoverInfo typeLookup ast = (range, prettyNames ++ pTypes)
  where
    pTypes
      | Prelude.length names == 1 = dropEnd1 $ map wrapHaskell prettyTypes
      | otherwise = map wrapHaskell prettyTypes

    range = realSrcSpanToRange $ nodeSpan ast

    wrapHaskell x = "\n```haskell\n" <> x <> "\n```\n"
    info = sourcedNodeInfo ast
    names = M.assocs $ sourcedNodeIdents info
    types = concat $ nodeType <$> (M.elems $ getSourcedNodeInfo info)

    prettyNames :: [T.Text]
    prettyNames = map prettyName names

    prettyName :: (Identifier, IdentifierDetails TypeIndex) -> T.Text
    prettyName (Right n, dets) =
      T.unlines $
        wrapHaskell (showNameWithoutUniques n <> maybe "" (" :: " <>) (prettyType <$> identType dets)) :
        definedAt n
    prettyName (Left m, _) = showGhc m

    prettyTypes = map (("_ :: " <>) . prettyType) types

    prettyType t = showGhc $ hieTypeToIface $ recoverFullType t typeLookup

    definedAt name =
      -- do not show "at <no location info>" and similar messages
      -- see the code of 'pprNameDefnLoc' for more information
      case nameSrcLoc name of
        UnhelpfulLoc {} | isInternalName name || isSystemName name -> []
        _ -> ["*Defined " <> showSD (pprNameDefnLoc name) <> "*"]

symbolKindOfOccName :: OccName -> SymbolKind
symbolKindOfOccName ocn
  | isVarOcc ocn = SkVariable
  | isDataOcc ocn = SkConstructor
  | isTcOcc ocn = SkStruct
  | otherwise = SkUnknown 1

gotoDefinition ::
  MonadIO m =>
  HieDb ->
  FilePath ->
  M.Map ModuleName Uri ->
  HieASTs TypeIndex ->
  Position ->
  MaybeT m [Location]
gotoDefinition hiedb wsroot imports srcSpans pos =
  lift $ locationsAtPoint hiedb wsroot imports pos srcSpans

locationsAtPoint ::
  forall m.
  MonadIO m =>
  HieDb ->
  FilePath ->
  M.Map ModuleName Uri ->
  Position ->
  HieASTs TypeIndex ->
  m [Location]
locationsAtPoint hiedb wsroot imports pos ast =
  let ns = concat $ pointCommand ast pos (M.keys . sourcedNodeIdents . sourcedNodeInfo)
      zeroPos = Position 0 0
      zeroRange = Range zeroPos zeroPos
      modToLocation m = (\fs -> pure $ Location fs zeroRange) <$> M.lookup m imports
   in nubOrd . concat <$> mapMaybeM (either (pure . modToLocation) (nameToLocation hiedb wsroot imports)) ns

pointCommand :: HieASTs TypeIndex -> Position -> (HieAST TypeIndex -> a) -> [a]
pointCommand hf pos k =
  catMaybes $
    M.elems $
      flip M.mapWithKey (getAsts hf) $ \(LexicalFastString fs) ast ->
        case selectSmallestContaining (sp fs) ast of
          Nothing -> Nothing
          Just ast' -> Just $ k ast'
  where
    sloc fs = mkRealSrcLoc fs (fromIntegral line + 1) (fromIntegral cha + 1)
    sp fs = mkRealSrcSpan (sloc fs) (sloc fs)
    line = _line pos
    cha = _character pos

-- | Given a 'Name' attempt to find the location where it is defined.
nameToLocation :: MonadIO m => HieDb -> FilePath ->  M.Map ModuleName Uri -> Name -> m (Maybe [Location])
nameToLocation hiedb wsroot imports name = runMaybeT $
  case nameSrcSpan name of
    sp@(RealSrcSpan rsp _)
      -- Lookup in the db if we got a location in a boot file
      | not $ "boot" `isSuffixOf` unpackFS (srcSpanFile rsp) -> MaybeT $ pure $ pure <$> srcSpanToLocation wsroot sp
    sp -> do
      guard (sp /= wiredInSrcSpan)
      -- This case usually arises when the definition is in an external package.
      -- In this case the interface files contain garbage source spans
      -- so we instead read the .hie files to get useful source spans.
      mod <- MaybeT $ return $ nameModule_maybe name
      erow <- liftIO $ findDef hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnit mod)
      case erow of
        [] -> do
          -- If the lookup failed, try again without specifying a unit-id.
          -- This is a hack to make find definition work better with ghcide's nascent multi-component support,
          -- where names from a component that has been indexed in a previous session but not loaded in this
          -- session may end up with different unit ids
          erow <- liftIO $ findDef hiedb (nameOccName name) (Just $ moduleName mod) Nothing
          case erow of
            [] -> MaybeT $ pure Nothing
            xs -> pure $ mapMaybe (defRowToLocation wsroot imports) xs
        xs -> pure $ mapMaybe (defRowToLocation wsroot imports) xs

defRowToLocation :: FilePath -> M.Map ModuleName Uri -> Res DefRow -> Maybe Location
defRowToLocation wsroot imports (row :. info) = do
  let start = Position <$> (intToUInt $ defSLine row - 1) <*> (intToUInt $ defSCol row - 1)
      end = Position <$> (intToUInt $ defELine row - 1) <*> (intToUInt $ defECol row - 1)
      range = Range <$> start <*> end
      file = case modInfoSrcFile info of
                Just src -> Just $ filePathToUri $ wsroot </> src
                Nothing -> M.lookup (modInfoName info) imports
  Location <$> file <*> range

dropEnd1 :: [a] -> [a]
dropEnd1 [] = []
dropEnd1 (x : xs) = foldr (\z f y -> y : f z) (const []) xs x

-- | Use 'fromIntegral' when it is safe to do so
intToUInt :: Int -> Maybe UInt
intToUInt x =
  if minBoundAsInt <= x && x <= maxBoundAsInt
    then Just $ fromIntegral x
    else Nothing
  where
    minBoundAsInt = fromIntegral $ minBound @UInt
    maxBoundAsInt = fromIntegral $ maxBound @UInt
