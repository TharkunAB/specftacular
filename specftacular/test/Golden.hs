{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings #-}
-- | Golden tests. Each case runs a small signature and compares the laws
-- with a file in test/golden. Each case runs twice: on untyped values, and
-- with the test of the types at each application (SPECFTACULAR_CHECKED=1).
-- Set GOLDEN_ACCEPT=1 to write the files again.
module Main (main) where

import Control.Monad (unless, when)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.Exit (exitFailure)
import Test.QuickCheck (Arbitrary (..), CoArbitrary, suchThat)

import Spectacular

newtype PosInt = P Int
  deriving (Eq, Ord, Show, Num, Enum, Real, Integral, CoArbitrary)

instance Arbitrary PosInt where
  arbitrary = P <$> arbitrary `suchThat` (>= 0)

-- | The generator and the equality of PosInt for the Gcd signature.
posIntReps :: TypeSkeleton -> Maybe GeneratedInstance
posIntReps t | t == typeSkeletonOf (Proxy :: Proxy PosInt) = Just $ genRepFromProxy (Proxy :: Proxy PosInt)
posIntReps _ = Nothing

-- | The name of each golden file and the run that gives its laws.
cases :: [(String, IO [String])]
cases =
  [ ("lists-4", discoverMonomorphic 4 (const Nothing)
      [ con "reverse" (reverse :: [A] -> [A])
      , con "++" ((++) :: [A] -> [A] -> [A])
      , con "[]" ([] :: [A])
      , con "map" (map :: (A -> B) -> [A] -> [B])
      , con "length" (length :: [A] -> Int)
      , con "concat" (concat :: [[A]] -> [A])
      , arith (Proxy :: Proxy Int) ])
  , ("list-monad-4", discoverMonomorphic 4 (const Nothing)
      [ con "return" (return :: A -> [A])
      , con ">>=" ((>>=) :: [A] -> (A -> [B]) -> [B])
      , con "++" ((++) :: [A] -> [A] -> [A]) ])
  , ("mini-list-4", discoverMonomorphic 4 (const Nothing)
      [ con "reverse" (reverse :: [A] -> [A])
      , con "[]" ([] :: [A])
      , con "null" (null :: [A] -> Bool)
      , con "True" True
      , con "False" False ])
  , ("gcd-3", discoverMonomorphic 3 posIntReps
      [ con "0" (P 0)
      , con "21" (P 21)
      , con "1029" (P 1029)
      , con "1071" (P 1071)
      , con "gcd" (gcd :: PosInt -> PosInt -> PosInt) ])
  ]

-- | Run one case on untyped values and on checked values. Return whether
-- the laws of both runs equal the golden file.
check :: Bool -> (String, IO [String]) -> IO Bool
check accept (name, run) = do
  unsetEnv "SPECFTACULAR_CHECKED"
  laws <- run
  setEnv "SPECFTACULAR_CHECKED" "1"
  checkedLaws <- run
  unsetEnv "SPECFTACULAR_CHECKED"
  let file = "test/golden/" ++ name ++ ".laws"
  when accept $ writeFile file (unlines laws)
  expected <- lines <$> readFile file
  and <$> mapM (same file expected) [(name, laws), (name ++ " (checked)", checkedLaws)]

-- | Whether the laws of a run equal the golden file. Print both when they
-- differ.
same :: FilePath -> [String] -> (String, [String]) -> IO Bool
same file expected (name, laws) = do
  let equal = expected == laws
  unless equal $ do
    putStrLn ("FAIL " ++ name ++ ": the laws differ from " ++ file)
    putStrLn "expected:"
    mapM_ putStrLn expected
    putStrLn "actual:"
    mapM_ putStrLn laws
  return equal

main :: IO ()
main = do
  accept <- (== Just "1") <$> lookupEnv "GOLDEN_ACCEPT"
  results <- mapM (check accept) cases
  unless (and results) exitFailure
