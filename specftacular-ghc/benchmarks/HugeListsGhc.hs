{-# LANGUAGE OverloadedStrings #-}
-- | The signature of HugeLists, from a GHC session: the functions by their
-- names.
import Spectacular
import Spectacular.GHC (withGhcSignature)
import qualified Data.Text as T
import System.Environment (getArgs)

main :: IO ()
main = do
  [s, p] <- map read <$> getArgs
  withGhcSignature ["import Prelude", "import Data.List", "import Control.Monad"]
    [ "usort :: [Int] -> [Int]\nusort [] = []\nusort (a:as) = usort (filter (<= a) as) ++ [a] ++ usort (filter (> a) as)" ]
    [ (name, if name `elem` operators then "(" <> T.unpack name <> ")" else T.unpack name) | name <- names ]
    []
    $ \sig instances -> do
      res <- searchPhases s p instances sig
      mapM_ print res
      print (length res)
  where
    names = [ "length", "sort", "scanr", "succ", ">>=", "snd", "reverse", "0", ",", ">=>", ":", "break"
            , "filter", "scanl", "zipWith", "concat", "zip", "usort", "sum", "++", "map", "foldl"
            , "takeWhile", "foldr", "drop", "dropWhile", "span", "unzip", "+", "[]", "partition", "fst", "take" ]
    operators = [">>=", ",", ">=>", ":", "++", "+"]
