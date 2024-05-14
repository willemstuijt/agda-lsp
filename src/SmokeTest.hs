module SmokeTest (runTests) where

import Agda.Syntax.Concrete (Module)
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Utils.FileName

import Control.Monad.IO.Class (MonadIO(liftIO))
import ScopeAnalysis (scanModule, unusedSymbols)
import SemanticTokens (tokenizeFull')
import Language.LSP.Protocol.Types (SemanticTokens(SemanticTokens))
import Data.Map qualified as Map
import ScopeImport qualified as Imp
import Agda.Syntax.Common.Pretty (Pretty(pretty))

runTests :: IO [String]
runTests = do
    let files = ["/home/willem/plfa/standard-library/src/Data/List/Relation/Unary/All.agda"]
    mapM testFile files

testFile :: String -> IO String
testFile path = do
    modl <- parseFilePath path
    (imps, faileds, _) <- Imp.resolveAllModules modl Imp.emptyState
    let state = scanModule imps modl
    let (SemanticTokens _ toks) = tokenizeFull' state modl
    let uns = unusedSymbols state
    print $ pretty <$> Map.keys imps
    print $ pretty <$> faileds
    return $ "Passed " ++ show (length toks) ++ " " ++ show (length uns) ++ " " ++ show (length faileds)

parseFilePath :: String -> IO Module
parseFilePath path = do
  code <- readFile path
  let tmp = parseFile moduleParser (mkRangeFile (mkAbsolute path) Nothing) code
  (res, _) <- liftIO $ runPMIO tmp
  case res of
    (Left err) -> error $ "could not parse: " ++ show err ++ "\n\n" ++ code
    (Right ((modl, _), _)) -> do
      return modl