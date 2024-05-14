{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Completions (makeCompletions, completionsAtPos) where

import Colog.Core ( (<&), logStringStderr )
import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Language.LSP.Protocol.Lens (HasUri (uri))
import Language.LSP.Protocol.Types
    ( CompletionItem (_labelDetails),
    CompletionParams(CompletionParams),
    CompletionItemKind (..),
    CompletionItem (..) )
import Language.LSP.Server
import Language.LSP.Protocol.Types qualified as LSP
import Data.IORef (IORef, readIORef)
import State
import Scope (allSymbols, innerMostScope, inScopeSymbols, SymId, Symbol (Symbol), Sym(..), Scope, lookupParent, getSym, rmParent, symScope)
import ScopeAnalysis (ScanState(ScanState))
import Data.Text (pack)
import Agda.Syntax.Concrete
import Traversal (Done (..), traverseIdents, doneAsMaybe)
import AgdaToLSP (unpackName, rangeContainsPos, decLSPRangeEnd)

makeCompletions :: CompletionParams -> IORef State -> LspT () IO [CompletionItem]
makeCompletions (CompletionParams doc pos _ _ _) stateRef = do
  logStringStderr <& "sendCompletions ..."

  let fileUri = doc ^. uri
  state <- liftIO $ readIORef stateRef

  case getFileStateByUri state fileUri of
    Just (FileState _ (Right modl) _ (ScanState _ _ scope _)) -> do
      logStringStderr <& show pos
      logStringStderr <& show (findUseIdent modl pos)
      return $ completionsAtPos modl scope pos
    _ -> return []

completionsAtPos :: Module -> Scope -> LSP.Position -> [CompletionItem]
completionsAtPos modl s pos = fmap symbolToCompletion allSyms
  where
    scope = innerMostScope pos s
    qname = findUseIdent modl pos
    scope' = case qname of
      Nothing -> Just scope
      Just x -> scopeAtPos scope pos x
    allSyms = case scope' of
      Nothing -> []
      Just scp -> inScopeSymbols symsIdx pos scp
        where
          symsIdx = allSymbols scp

scopeAtPos :: Scope -> LSP.Position -> QName -> Maybe Scope
scopeAtPos scope pos (Qual n x) = if rangeContainsPos r pos then Just scope else scope'
  where
    (r', modName) = unpackName n
    r = decLSPRangeEnd r'
    sym = lookupParent modName scope
    scope' = case sym of
      Nothing -> Nothing
      Just s -> case symScope $ getSym s of
          Just s' -> scopeAtPos (rmParent s') pos x
          _ -> Nothing
scopeAtPos scope _ (QName _) = Just scope

-- Returns the QName at position if any
findUseIdent :: Module -> LSP.Position -> Maybe QName
findUseIdent modl pos = doneAsMaybe $ traverseIdents (\n -> if containedName n then Done n else Continue) modl
  where
    containedName (Qual n x) = rangeContainsPos r pos || containedName x
      where
        (r, _) = unpackName n
    containedName (QName x) = rangeContainsPos r pos
      where
        (r, _) = unpackName x

symbolToCompletion :: (String, Symbol) -> CompletionItem
symbolToCompletion (name, Symbol _ sname _ sym) = CompletionItem
  { _label = pack name
  , _labelDetails = Nothing
  , _kind = case sym of
      SModl {} -> Just CompletionItemKind_Module
      SFunc {} -> Just CompletionItemKind_Function
      SConstr {} -> Just CompletionItemKind_Constructor
      SData {} -> Just CompletionItemKind_Class
      SImpl {} -> Just CompletionItemKind_Variable
      SExpl {} -> Just CompletionItemKind_Variable
  , _tags = Nothing
  , _detail = Just $ pack sname
  , _documentation = Nothing
  , _deprecated = Nothing
  , _preselect = Nothing
  , _sortText = Nothing
  , _filterText = Nothing
  , _insertText = Nothing
  , _insertTextFormat = Nothing
  , _insertTextMode = Nothing
  , _textEdit = Nothing
  , _textEditText = Nothing
  , _additionalTextEdits = Nothing
  , _commitCharacters = Nothing
  , _command = Nothing
  , _data_ = Nothing
  }
