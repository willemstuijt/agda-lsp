module SemanticTokens (tokenizeFull, tokenizeFull') where

import Colog.Core ( (<&), logStringStderr )
import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO (liftIO))
import State
import Language.LSP.Server
import Language.LSP.Protocol.Lens (HasUri (uri))

import Data.IORef (IORef, readIORef)
import Language.LSP.Protocol.Types (SemanticTokenTypes (..), SemanticTokens (..), SemanticTokenAbsolute (..), UInt, encodeTokens, defaultSemanticTokensLegend, relativizeTokens)
import Agda.Syntax.Concrete
import Data.Map qualified as M
import Scope (Symbol (Symbol), Sym (..), getSym, allSymbols)
import Language.LSP.Protocol.Types qualified as LSP
import AgdaToLSP (unpackName)
import ScopeAnalysis (ScanState (ScanState), SymUse (SymUse))
import Data.Maybe (mapMaybe)
import Traversal (traverseIdents, foldModule, Node (D, E))

tokenizeFull :: LSP.TextDocumentIdentifier -> IORef State -> LspT () IO SemanticTokens
tokenizeFull doc stateRef = do
  logStringStderr <& "tokenizeFull ..."

  let fileUri = doc ^. uri
  state <- liftIO $ readIORef stateRef

  let empty = SemanticTokens Nothing []

  case getFileStateByUri state fileUri of
    Nothing -> return empty
    Just (FileState _ m _ ss) -> do
      case m of
        Right modl -> return $ tokenizeFull' ss modl
        _ -> return empty

tokenizeFull' :: ScanState -> Module -> SemanticTokens
tokenizeFull' state modl = SemanticTokens Nothing (encode toks)
  where
    (ScanState _ _ scope uses) = state
    syms = allSymbols scope
    usesR = mapMaybe (sequenceA . (\(SymUse a b) -> (a, M.lookup b syms))) uses
    defsR = fmap (\s@(Symbol r _ _ _) -> (r, s)) (M.elems syms)
    fn = tokenizeQName (M.fromList $ defsR <> usesR)

    -- toks = mergeAbsToks (tokenizeModuleNames fn modl) (tokenizeModuleKeywords modl)
    toks = tokenizeModuleNames fn modl

encode :: [SemanticTokenAbsolute] -> [UInt]
encode toks = case encodeTokens defaultSemanticTokensLegend (relativizeTokens toks) of
  Left x -> error (show x)
  Right x -> x

tokenizeModuleNames :: (QName -> [SemanticTokenAbsolute]) -> Module -> [SemanticTokenAbsolute]
tokenizeModuleNames = traverseIdents

tokenizeModuleKeywords :: Module -> [SemanticTokenAbsolute]
tokenizeModuleKeywords = foldModule fn
  where
    fn (E _) = []
    fn _ = []

tokenizeQName :: M.Map LSP.Range Symbol -> QName -> [SemanticTokenAbsolute]
tokenizeQName mp (QName a) = maybeToList $ tokenizeName mp a
tokenizeQName mp (Qual a b) = case tokenizeName mp a of
  Nothing -> tokenizeQName mp b
  Just a' -> a' : tokenizeQName mp b

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just x) = [x]

tokenizeName :: M.Map LSP.Range Symbol -> Name -> Maybe SemanticTokenAbsolute
tokenizeName mp n = case M.lookup rng mp of
    Nothing -> Nothing
    Just x -> Just $ symbolToToken rng x
  where
    (rng, _) = unpackName n

symbolToToken :: LSP.Range -> Symbol -> SemanticTokenAbsolute
symbolToToken range s = SemanticTokenAbsolute
  {
  _line = line,
  _startChar = startChar,
  _length = len,
  _tokenType = symToTokenType $ getSym s,
  _tokenModifiers = []
  }
  where
    (line, startChar, len) = rangeToPos range

rangeToPos :: LSP.Range -> (UInt, UInt, UInt)
rangeToPos (LSP.Range (LSP.Position l1 c1) (LSP.Position _ c2)) = (l1, c1, c2-c1)

symToTokenType :: Sym -> SemanticTokenTypes
symToTokenType (SModl {}) = SemanticTokenTypes_Namespace
symToTokenType (SData {}) = SemanticTokenTypes_Type
symToTokenType (SConstr {}) = SemanticTokenTypes_Type
symToTokenType (SFunc {}) = SemanticTokenTypes_Function
symToTokenType (SImpl {}) = SemanticTokenTypes_Variable
symToTokenType (SExpl {}) = SemanticTokenTypes_Variable

mergeAbsToks :: [SemanticTokenAbsolute] -> [SemanticTokenAbsolute] -> [SemanticTokenAbsolute]
mergeAbsToks = mergeSorted
-- mergeAbsToks (x@(SemanticTokenAbsolute {_line = xl, _startChar = xc}):xs) (y@(SemanticTokenAbsolute {_line = yl, _startChar = yc}):ys)
--   | LSP.Position xl xc < LSP.Position yl yc = x : mergeSorted xs (y:ys)
--   | otherwise = y : mergeSorted (x:xs) ys
-- mergeAbsToks xs [] = xs
-- mergeAbsToks [] ys = ys

mergeSorted :: Ord a => [a] -> [a] -> [a]
mergeSorted (x:xs) (y:ys)
  | x < y = x : mergeSorted xs (y:ys)
  | otherwise = y : mergeSorted (x:xs) ys
mergeSorted xs [] = xs
mergeSorted [] ys = ys