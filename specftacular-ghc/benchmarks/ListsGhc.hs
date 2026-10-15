{-# LANGUAGE OverloadedStrings #-}
-- | The signature of Lists, from a GHC session: the functions by their
-- names, at the carrier A.
import Spectacular
import Spectacular.GHC (withGhcSignature)
import System.Environment (getArgs)

main :: IO ()
main = do
  [s, p] <- map read <$> getArgs
  withGhcSignature ["import Prelude", "import Data.List"] []
    [ ("reverse", "reverse"), ("++", "(++)"), ("[]", "[]"), ("map", "map")
    , ("length", "length"), ("concat", "concat") ]
    [ ("0", "0 :: Int"), ("1", "1 :: Int") ]
    $ \sig instances -> do
      res <- searchPhases s p instances sig
      mapM_ print res
      print (length res)
