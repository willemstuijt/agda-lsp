module Rename (makeRename, declarationLocation, referencesLocations) where

import Colog.Core ( (<&), logStringStderr )
import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.IORef (IORef, readIORef)
import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Protocol.Lens (HasUri (uri))
import State
import Language.LSP.Server
import Data.Map qualified as Map
import Language.LSP.Protocol.Types
    ( CompletionItem (_labelDetails),
    WorkspaceEdit (WorkspaceEdit),
    TextEdit (TextEdit),
    RenameParams(RenameParams),
    Uri,
    RenameParams (..) )
import Scope (innerMostScope, inScopeSymbols, SymId, Symbol (Symbol), symId, symRange)
import ScopeAnalysis (ScanState(ScanState), symbolAtPos, SymUse(SymUse), allUsesOfSymbol)
import Data.Text (Text)

declarationLocation :: LSP.TextDocumentIdentifier -> LSP.Position -> IORef State -> LspT () IO (Maybe LSP.Location)
declarationLocation doc pos stateRef = do
  logStringStderr <& "declarationLocation ..."

  let fileUri = doc ^. uri
  state <- liftIO $ readIORef stateRef

  case getFileStateByUri state fileUri of
    Nothing -> return Nothing
    Just (FileState _ _ _ ss) -> do
      case symbolAtPos ss pos of
        Nothing -> return Nothing
        Just sym -> return $ Just $ LSP.Location fileUri (symRange sym)

referencesLocations :: LSP.TextDocumentIdentifier -> LSP.Position -> IORef State -> LspT () IO [LSP.Location]
referencesLocations doc pos stateRef = do
  logStringStderr <& "referencesLocations ..."

  let fileUri = doc ^. uri
  state <- liftIO $ readIORef stateRef

  case getFileStateByUri state fileUri of
    Nothing -> return []
    Just (FileState _ _ _ ss) -> do
      case symbolAtPos ss pos of
        Nothing -> return []
        Just sym -> do
          let uses = allUsesOfSymbol ss (symId sym)
          let locs = fmap (\(SymUse r _) -> LSP.Location fileUri r) uses
          return locs

makeRename :: RenameParams -> IORef State -> LspT () IO (Maybe WorkspaceEdit)
makeRename (RenameParams _ doc pos name) stateRef = do
  logStringStderr <& "makeRename ..."

  let fileUri = doc ^. uri
  state <- liftIO $ readIORef stateRef

  case getFileStateByUri state fileUri of
    Nothing -> return Nothing
    Just (FileState _ _ _ ss) -> do
      case symbolAtPos ss pos of
        Nothing -> return Nothing
        Just sym -> return $ Just $ makeRenameEdit fileUri name sym (allUsesOfSymbol ss (symId sym))

makeRenameEdit :: Uri -> Text -> Symbol -> [SymUse] -> WorkspaceEdit
makeRenameEdit file_uri name (Symbol sr _ _ _) uses = WorkspaceEdit (Just $ Map.singleton file_uri edits) Nothing Nothing
    where
        useEdits = fmap (\(SymUse r _) -> TextEdit r name) uses
        edits = TextEdit sr name : useEdits