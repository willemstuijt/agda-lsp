module Diagnostics
  ( sendDiagnostics,
    diagnosticKindFromJSON,
    diagnosticKindFromJSON',
    badImportDiagnostics,
    DiagnosticKind (DiagnosticUnused),
  )
where

import Agda.Utils.FileName (mkAbsolute)
import Colog.Core
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Aeson (Value (Number))
import Data.IORef (IORef, readIORef, writeIORef)
import ScopeAnalysis
import Scope
import Data.Text (pack, unpack)
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS (virtualFileText)
import State
import Agda.Syntax.Concrete (QName)
import Agda.Syntax.Position (HasRange(getRange))
import AgdaToLSP (toLSPRange')
import Agda.Syntax.Common.Pretty (Pretty(pretty))

newtype DiagnosticKind = DiagnosticUnused SymId

diagnosticKindToJSON :: DiagnosticKind -> Value
diagnosticKindToJSON (DiagnosticUnused (SymId sid)) = Number $ fromIntegral sid

diagnosticKindFromJSON :: Value -> Maybe DiagnosticKind
diagnosticKindFromJSON (Number n) = Just $ DiagnosticUnused $ SymId $ truncate n
diagnosticKindFromJSON _ = Nothing

diagnosticKindFromJSON' :: Maybe Value -> Maybe DiagnosticKind
diagnosticKindFromJSON' (Just (Number n)) = Just $ DiagnosticUnused $ SymId $ truncate n
diagnosticKindFromJSON' _ = Nothing

makeDiagnostics :: State -> Uri -> [Diagnostic]
makeDiagnostics state fileUri = case getFileStateByUri state fileUri of
  Nothing -> []
  Just (FileState _ (Left (r, s)) _ _) -> [Diagnostic r (Just DiagnosticSeverity_Error) Nothing Nothing (pack <$> uriToFilePath fileUri) (pack s) Nothing Nothing Nothing]
  Just (FileState _ _ _ scope) -> do
    let implicits = unusedSymbols scope
    fmap (unusedSymToDiagnostic fileUri) implicits

badImportDiagnostics :: Uri -> [QName] -> [Diagnostic]
badImportDiagnostics _ [] = []
badImportDiagnostics file_uri (x:xs) = badImportToDiagnostic file_uri r n : badImportDiagnostics file_uri xs
  where
    r = toLSPRange' $ getRange x
    n = show $ pretty x

sendDiagnostics :: [Diagnostic] -> IORef State -> Uri -> Maybe Int32 -> LspT () IO ()
sendDiagnostics ds stateRef fileUri version = do
  logStringStderr <& "sendDiagnostics ..."

  state <- liftIO $ readIORef stateRef
  let diagnostics = ds <> makeDiagnostics state fileUri
  publishDiagnostics 100 (toNormalizedUri fileUri) version (partitionBySource diagnostics)

unusedSymToDiagnostic :: Uri -> Symbol -> Diagnostic
unusedSymToDiagnostic file_uri (Symbol range name (SymId num) _) = Diagnostic range (Just DiagnosticSeverity_Warning) (Just $ InL (fromIntegral num)) Nothing (pack <$> uriToFilePath file_uri) (pack ("Unused {" ++ name ++ "}")) (Just [DiagnosticTag_Unnecessary]) Nothing kind
  where
    kind = Just $ diagnosticKindToJSON $ DiagnosticUnused (SymId num)

badImportToDiagnostic :: Uri -> Range -> String -> Diagnostic
badImportToDiagnostic file_uri range name = Diagnostic range (Just DiagnosticSeverity_Error) (Just $ InR txt) Nothing (pack <$> uriToFilePath file_uri) (pack ("Invalid import " ++ name)) (Just []) Nothing kind
  where
    kind = Nothing
    txt = pack name
