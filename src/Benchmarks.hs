{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Benchmarks (runOnFile, runAndOutCSV, buildCache, generateAgdaData, runLineCounter, generateMyCheckData) where

import Agda.Interaction.FindFile (SourceFile (SourceFile))
import Agda.Interaction.Imports
import Agda.Interaction.Options (defaultPragmaOptions)
import Agda.Interaction.Options qualified as AO
import Agda.TypeChecking.Monad
import Agda.Utils.Benchmark qualified as B
import Agda.Utils.FileName
import Agda.Utils.Monad (concatMapM, ifM, whenM)
import Agda.Utils.ProfileOptions (ProfileOption (Definitions, Internal, Modules), addProfileOption, noProfileOptions)
import Agda.Utils.Time (CPUTime (CPUTime))
import Agda.Utils.Trie qualified as Trie
import Control.Monad (forM)
import Control.Monad.Except (MonadError (catchError))
import Criterion.Main
import Criterion.Types
import Data.Aeson
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key (fromString)
import Data.ByteString.Lazy.Char8 qualified as B8
import Data.Either (fromRight)
import Data.List (intercalate, isPrefixOf, nub)
import Data.Map qualified as Map
import Data.Set (Set, fromList)
import Data.Text qualified as T
import GHC.Generics
import ScopeAnalysis qualified as Scope
import System.CPUTime
import System.Directory
import System.Directory.Internal.Prelude (catch, isDoesNotExistError)
import System.Environment (withArgs)
import System.FilePath (takeDirectory, takeExtension, takeFileName, (</>))
import System.IO
import System.Random (newStdGen, randomRs)
import Text.Printf

removeAgdaExt :: String -> String
removeAgdaExt str = take (length str - 5) str

-- outputs
runLineCounter :: String -> IO ()
runLineCounter path = do
  allFiles <- allStdLib
  counts <- mapM processFileLineCount allFiles
  writeLineCountCSV path counts

processFileLineCount :: String -> IO (String, Int, Int)
processFileLineCount fullPath = do
  content <- readFile fullPath
  let lines = length $ T.lines (T.pack content)
  let chars = T.length (T.pack content)
  return (fullPath, lines, chars)

-- runs typechecking on all files so that
-- Agda caches interface files
buildCache :: IO ()
buildCache = do
  allFiles <- allStdLib
  let filtered =
        drop 1 allFiles -- filter (\x -> not $ member x disabled) allFiles
  print $ length filtered
  let inputs = fmap (\path -> (takeDirectory path, removeAgdaExt $ takeFileName path, TCheck)) filtered

  mapM_ (\(s1, s2, k) -> runFileIO s1 s2 k) inputs

runOnFile :: String -> String -> IO ()
runOnFile dir fileName = do
  let inputs = [(dir, fileName)]

  let config =
        defaultConfig
          { reportFile = Just "benchmark.html",
            verbosity = Verbose
          }

  withArgs [] $
    defaultMainWith
      config
      [ bgroup "myFunction" $
          map (\(d, fn) -> bench (d ++ "/" ++ fn ++ ".agdap") $ nfIO (runFileIO d fn Parse)) inputs
            ++ map (\(d, fn) -> bench (d ++ "/" ++ fn ++ ".agdam") $ nfIO (runFileIO d fn MyCheck)) inputs
            ++ map (\(d, fn) -> bench (d ++ "/" ++ fn ++ ".agdas") $ nfIO (runFileIO d fn SCheck)) inputs
            ++ map (\(d, fn) -> bench (d ++ "/" ++ fn ++ ".agdat") $ nfIO (runFileIO d fn TCheck)) inputs
      ]

-- runs agda benchmarking on all standard library files
-- 10 times and outputs as JSON
generateAgdaData :: String -> IO ()
generateAgdaData path = do
  inputs <- allStdLibSplit
  res <- runAgdaBenchAll 8 inputs
  B8.writeFile path (encodePretty res)

-- runs my check on all standard library files
-- 10 times and outputs to CSV
generateMyCheckData :: String -> IO ()
generateMyCheckData path = do
  inputs <- allStdLibSplit
  let trimmed = fmap (\(a, b) -> (a, take (length b - 5) b)) inputs
  runAndOutCSV path 8 trimmed

runAndOutCSV :: String -> Int -> [(String, String)] -> IO ()
runAndOutCSV path n inputs = do
  let inputsK = concatMap (\(d, f) -> [(d, f, k) | k <- [MyCheck]]) inputs
  results <- runMultipleTimes n inputsK
  writeCSV path results

data Kind = Parse | MyCheck | SCheck | TCheck deriving (Eq, Show)

runFileIO :: String -> String -> Kind -> IO Int
runFileIO dir fileName k = do
  -- print $ dir ++ "/" ++ fileName ++ ".agda"
  runTCMTop' $ do
    runFile dir fileName k

trimPrefix :: String -> String -> String
trimPrefix prefix str
  | prefix `isPrefixOf` str = drop (length prefix) str
  | otherwise = error "Prefix not found"

clearInterface :: String -> IO ()
clearInterface file = do
  let buildPrefix = "/home/willem/plfa/standard-library/_build/2.6.4/agda/src"
  let ifacePath = buildPrefix <> trimPrefix stdLibPath file <> "i"
  catch (removeFile ifacePath) handleClearErrors

handleClearErrors :: IOError -> IO ()
handleClearErrors e
  | isDoesNotExistError e = return ()
  | otherwise = error "could not delete file"

data AgdaBenchOut = AgdaBenchOut
  { dir :: String,
    file :: String,
    results :: [(String, CPUTime)] -- Using Int64 here to represent CPUTime
  }
  deriving (Generic, Show)

instance ToJSON AgdaBenchOut where
  toJSON (AgdaBenchOut dir file results) =
    object
      [ "dir" .= dir,
        "file" .= file,
        "results" .= object [fromString key .= value | (key, CPUTime value) <- results]
      ]

maybeError :: (MonadError e m) => m a -> m (Maybe a)
maybeError x = catchError (Just <$> x) (\_ -> return Nothing)

-- discards Maybe inputs
runAgdaBenchAll :: Int -> [(String, String)] -> IO [AgdaBenchOut]
runAgdaBenchAll _ [] = return []
runAgdaBenchAll n ((d, f) : xs) = do
  r <- runAgdaBenchFull n d f
  print $ "To Go: " <> show (length xs)
  rs <- runAgdaBenchAll n xs
  case r of
    Nothing -> return rs
    Just r' -> return (r' <> rs)

-- First checks so that all imports are cached, then runs results
-- n times. If an error occurs it returns Nothing
runAgdaBenchFull :: Int -> String -> String -> IO (Maybe [AgdaBenchOut])
runAgdaBenchFull n dir fileName = do
  res <- runTCMTop' (maybeError (runAgdaBench dir fileName))
  case res of
    Nothing -> return Nothing
    Just _ -> do
      x <- runAgdaBenchN n dir fileName
      return $ Just x

runAgdaBenchN :: Int -> String -> String -> IO [AgdaBenchOut]
runAgdaBenchN 0 _ _ = return []
runAgdaBenchN n dir fileName = do
  clearInterface (dir ++ "/" ++ fileName)
  x <- runTCMTop' $ runAgdaBench dir fileName
  xs <- runAgdaBenchN (n - 1) dir fileName
  return (x : xs)

runAgdaBench :: String -> String -> TCM AgdaBenchOut
runAgdaBench dir fileName = do
  let profileOpts = fromRight noProfileOptions $ addProfileOption "all" noProfileOptions
  let pragOpts = defaultPragmaOptions {AO._optProfiling = profileOpts}
  let opts = AO.defaultOptions {AO.optPragmaOptions = pragOpts}
  setCommandLineOptions' (mkAbsolute dir) opts

  B.reset

  let file = dir ++ "/" ++ fileName
  src <- parseSource (SourceFile (mkAbsolute file))
  _ <- typeCheckMain TypeCheck src
  bm <- B.getBenchmark
  let timings = B.timings bm
  let res = (\(k, v) -> (intercalate "." (fmap show k), v)) <$> Trie.toList timings
  return $ AgdaBenchOut dir fileName res

runFile :: String -> String -> Kind -> TCM Int
runFile dir fileName k = do
  let file = dir ++ "/" ++ fileName ++ ".agda"
  src <- parseSource (SourceFile (mkAbsolute file))

  case k of
    Parse -> return 0
    MyCheck -> do
      let modl = srcModule src
      let (Scope.ScanState _ _ _ uses) = Scope.scanModule Map.empty modl
      return $ length uses
    SCheck -> do
      _ <- typeCheckMain ScopeCheck src
      return 0
    TCheck -> do
      _ <- typeCheckMain TypeCheck src
      return 0

writeCSV :: FilePath -> [(String, String, Kind, Integer)] -> IO ()
writeCSV filePath results = do
  handle <- openFile filePath WriteMode
  hPutStrLn handle "dir,file,kind,runtime"
  mapM_ (hPutStrLn handle . showResult) results
  hClose handle
  where
    showResult (a, b, k, time) = printf "%s,%s,%s,%d" a b (show k) time

writeLineCountCSV :: FilePath -> [(String, Int, Int)] -> IO ()
writeLineCountCSV filePath results = do
  handle <- openFile filePath WriteMode
  hPutStrLn handle "path,linecount,charcount"
  mapM_ (hPutStrLn handle . showResult) results
  hClose handle
  where
    showResult (a, b, c) = printf "%s,%d,%d" a b c

runMultipleTimes :: Int -> [(String, String, Kind)] -> IO [(String, String, Kind, Integer)]
runMultipleTimes n = concatMapM (runNTimes n)
  where
    runNTimes 0 _ = return []
    runNTimes n' (a, b, k) = do
      time <- timeFunction a b k
      rest <- runNTimes (n' - 1) (a, b, k)
      return $ (a, b, k, time) : rest

-- timeFunction :: String -> String -> Kind -> IO (Int, Double)
-- timeFunction a b k = do
--     start <- getCPUTime
--     result <- runFileIO a b k
--     end <- getCPUTime
--     let diff = fromIntegral (end - start) / (10^9)
--     return (result, diff)

timeFunction :: String -> String -> Kind -> IO Integer
timeFunction a b k = do
  start <- getCPUTime
  _ <- runFileIO a b k
  end <- getCPUTime
  let diff = end - start
  return diff

-- Utilities to get file paths

stdLibPath :: FilePath
stdLibPath = "/home/willem/plfa/standard-library/src"

allStdLibSplit :: IO [(String, String)]
allStdLibSplit = do
  fmap (\path -> (takeDirectory path, takeFileName path)) <$> allStdLib

allStdLib :: IO [FilePath]
allStdLib = do
  allFiles <- listFilesRecursive stdLibPath
  return $ filterByExtension ".agda" allFiles

listFilesRecursive :: FilePath -> IO [FilePath]
listFilesRecursive path = do
  contents <- listDirectory path
  paths <- forM contents $ \name -> do
    let fullPath = path </> name
    isDirectory <- doesDirectoryExist fullPath
    if isDirectory
      then listFilesRecursive fullPath
      else return [fullPath]
  return (concat paths)

filterByExtension :: String -> [FilePath] -> [FilePath]
filterByExtension ext = filter ((== ext) . takeExtension)

randomSample :: Int -> [a] -> IO [a]
randomSample n xs = do
  gen <- newStdGen
  return $ map (xs !!) . take n . nub . randomRs (0, length xs - 1) $ gen

getRandomAgdaFiles :: FilePath -> Int -> IO [FilePath]
getRandomAgdaFiles path n = do
  allFiles <- listFilesRecursive path
  let agdaFiles = filterByExtension ".agda" allFiles
  randomSample n agdaFiles

splitFilePath :: FilePath -> (FilePath, FilePath)
splitFilePath path = (dir, filename)
  where
    dir = takeDirectory path
    filename = takeFileName path
