{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
{- | A signature from a GHC session: each function by its expression, with
each type variable at the carrier A, as the first phase gives it. GHC gives
the type of a function, and 'erase' of cfta-ghc makes it a type of the
automaton. The session compiles the function once at the type
with Int in place of A: A has the values of Int, and the code of Int is
compiled, while the instances of a type that the session declares run in the
interpreter. The session also compiles the generator and the equality of
each type that the search needs, when the type has the instance of
QuickCheck or of Eq.

The session is a session of cfta-ghc. It has the unit of QuickCheck of the
program ('quickCheckUnit') and the package database of the store of cabal
that has the unit ('storeDatabase'), so that the generators of the session
give the values of the program. The values of the session are untyped (see
'Value'), so SPECFTACULAR_CHECKED=1 does not test their applications.

The search runs inside the session, so that the compiled code stays loaded.

Phase 1 gives the laws of a signature of Haskell. Phases 2 to 4 give fewer:
each type variable is at A, while a signature of Haskell can keep the
variables apart at A to Acc, so the laws with B to Acc do not come.
-}
module Spectacular.GHC (
    withGhcSignature,
) where

import Control.Monad (filterM)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe, isNothing, listToMaybe, maybeToList)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable (tyConPackage, typeRep, typeRepTyCon)
import GHC.Builtin.Types (intTy, listTyCon)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.TyCon (TyCon)
import GHC.Core.Type (getTyVar_maybe, mkTyConTy, substTyWith, tyConsOfType)
import qualified GHC.Core.Type as GHC
import GHC.Exts (Any)
import GHC.Tc.Utils.TcType (tcSplitNestedSigmaTys)
import GHC.Types.Name (getName, getOccString, nameModule_maybe)
import GHC.Types.Unique.Set (nonDetEltsUniqSet)
import GHC.Unit.Module (moduleName, moduleNameString)
import GHC.Utils.Outputable (showPprUnsafe)
import System.Directory (XdgDirectory (XdgState), doesDirectoryExist, doesFileExist, getHomeDirectory, getXdgDirectory, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((<.>), (</>))
import qualified Test.QuickCheck as QC
import Unsafe.Coerce (unsafeCoerce)

import qualified Data.CFTA.Gen.Synthesis as Hectare
import Data.CFTA.GHC.Erase (erase)
import Data.CFTA.GHC.Session (SessionOptions (..), compileExpression, declare, defaultSessionOptions, typeOfExpression, withSessionOptions)

import Spectacular.Types

{- | Start a session with the imports and the declarations, build the
signature of the functions and the extra functions, each given by its name
and its expression, and run the action with the signature and the instances
of its types.
-}
withGhcSignature ::
    [String] -> [String] -> [(Text, String)] -> [(Text, String)] ->
    (Sig -> (TypeSkeleton -> Maybe Instance) -> IO a) -> IO a
withGhcSignature imports declarations functions extras action = do
    database <- storeDatabase quickCheckUnit
    let options = defaultSessionOptions
            { sessionPackageIds = [quickCheckUnit]
            , sessionPackageDbs = maybeToList database
            , sessionFlags = ["-XGeneralizedNewtypeDeriving", "-XDerivingStrategies"]
            , sessionCompile = True }
        qualifiedImports =
            [ "import qualified Test.QuickCheck as QC"
            , "import qualified Test.QuickCheck.Gen as QCG"
            , "import qualified Test.QuickCheck.Random as QCR" ]
    withSessionOptions options (imports <> qualifiedImports) $ \session -> do
        let typeOf expression = fromMaybe (error ("Spectacular.GHC: no type for " <> expression)) <$> typeOfExpression session expression
            -- A compiled expression, or Nothing when it does not typecheck.
            compiled = compileExpression session
        declare session "newtype A = A Int deriving newtype (Eq, Ord, Show, QC.Arbitrary, QC.CoArbitrary)"
        mapM_ (declare session) declarations
        carrier <- typeOf "undefined :: A"
        let function make (name, expression) = do
                typ <- typeOf expression
                let (bound, theta, body) = tcSplitNestedSigmaTys typ
                    classes v = [ getOccString cls | p <- theta, Just (cls, args) <- [getClassPredTys_maybe p]
                                                   , Just v `elem` map getTyVar_maybe args ]
                    -- A variable of a class of containers or monads is the
                    -- list, a variable of another class is Int, and any other
                    -- variable is the carrier, as the signatures of the
                    -- benchmarks write them.
                    at c v
                      | any (`elem` ["Foldable", "Traversable", "Functor", "Applicative", "Monad"]) (classes v) = mkTyConTy listTyCon
                      | not (null (classes v)) = intTy
                      | otherwise = c
                    instantiated c = substTyWith bound (map (at c) bound) body
                    source = "(" <> expression <> ") :: " <> showPprUnsafe (instantiated intTy)
                value <- fromMaybe (error ("Spectacular.GHC: cannot compile " <> source)) <$> compiled source
                case skeletonOf (instantiated carrier) of
                    Just skeleton -> pure (name, make (Untyped (unsafeCoerce value)) skeleton)
                    Nothing -> error ("Spectacular.GHC: no type for " <> expression)
            -- The generator and the equality of a type, if the session has
            -- them, for the types that have variables in the front end of
            -- Spectacular.Types ('frontInstances'): QuickCheck generates more
            -- types, such as any function whose arguments have CoArbitrary,
            -- and a variable of each such type would add many terms.
            instanceOf t
              | isNothing (frontInstances (const Nothing) t) = pure Nothing
            instanceOf t = do
                let source = sourceType t
                gen <- compiled ("\\seed size -> QCG.unGen (QC.arbitrary :: QC.Gen (" <> source <> ")) (QCR.mkQCGen seed) size")
                eq <- compiled ("(==) :: (" <> source <> ") -> (" <> source <> ") -> Bool")
                pure $ case gen of
                    Nothing -> Nothing
                    Just g ->
                        Just ( t
                             , Instance { inst_text = typeText t
                                        , inst_prefix = prefixOf t
                                        , inst_gen = Generator (\seed size -> Untyped ((unsafeCoerce g :: Int -> Int -> Any) seed size))
                                        , inst_eq = Untyped . unsafeCoerce <$> eq } )
        sigFunctions <- traverse (function SigFunc) functions
        extraFunctions <- traverse (function GenFunc) extras
        let sig = Map.fromList (sigFunctions <> extraFunctions)
            types = Map.keys (Map.fromList [ (t, ()) | t <- instanceTypes monomorphiseType sig <> instanceTypes id sig ])
        table <- Map.fromList . catMaybes <$> traverse instanceOf types
        action sig (`Map.lookup` table)

-- | The unit of QuickCheck of the program: the package of the type of its
-- generators.
quickCheckUnit :: String
quickCheckUnit = tyConPackage (typeRepTyCon (typeRep (Proxy :: Proxy (QC.Gen ()))))

-- | The package database of the store of cabal that has a unit. cabal keeps
-- its store in $CABAL_DIR/store, in ~/.cabal/store, or in the XDG state
-- directory, with one package database for each compiler. Nothing when no
-- store has the unit, as when the unit is in the global database.
storeDatabase :: String -> IO (Maybe FilePath)
storeDatabase unit = do
    cabalDir <- lookupEnv "CABAL_DIR"
    home <- getHomeDirectory
    state <- getXdgDirectory XdgState "cabal"
    let stores = [ dir </> "store" | Just dir <- [cabalDir] ] <> [home </> ".cabal" </> "store", state </> "store"]
    databases <- concat <$> traverse compilers stores
    listToMaybe <$> filterM (\database -> doesFileExist (database </> unit <.> "conf")) databases
  where
    compilers store = do
        exists <- doesDirectoryExist store
        if exists then map (\compiler -> store </> compiler </> "package.db") <$> listDirectory store else pure []

-- | The type of the automaton of a GHC type: the type of 'erase', with the
-- names of the type constructors as 'typeRepToTypeSkeleton' gives them. The
-- carrier A of the session is the A of "Spectacular.Types".
skeletonOf :: GHC.Type -> Maybe TypeSkeleton
skeletonOf typ = convert <$> erase (const Nothing) typ
  where
    names = Map.fromList [ (getOccString tc, qualified tc) | tc <- nonDetEltsUniqSet (tyConsOfType typ) ]
    qualified :: TyCon -> Text
    qualified tc = case (getOccString tc, nameModule_maybe (getName tc)) of
        ("A", Just m) | "Ghci" `T.isPrefixOf` T.pack (moduleNameString (moduleName m)) -> "Spectacular.Types.A"
        (occ, Just m) -> T.pack (moduleNameString (moduleName m) <> "." <> occ)
        (occ, Nothing) -> T.pack occ
    convert (Hectare.TVar v) = TVar v
    convert (Hectare.TFun a b) = TFun (convert a) (convert b)
    convert (Hectare.TCons "List" [a]) = TCons "[]" [convert a]
    convert (Hectare.TCons "Unit" []) = TCons "()" []
    convert (Hectare.TCons "Pair" [a, b]) = TCons "(,)" [convert a, convert b]
    convert (Hectare.TCons name args) = TCons (Map.findWithDefault name (T.unpack name) names) (map convert args)

-- | A type as Haskell source, with each type constructor by its name
-- without its module, and Int for the carrier A.
sourceType :: TypeSkeleton -> String
sourceType (TCons "Spectacular.Types.A" []) = "Int"
sourceType (TCons "[]" [a]) = "[" <> sourceType a <> "]"
sourceType (TCons "(,)" [a, b]) = "(" <> sourceType a <> ", " <> sourceType b <> ")"
sourceType (TCons "()" []) = "()"
sourceType (TFun a b) = "(" <> sourceType a <> " -> " <> sourceType b <> ")"
sourceType (TCons name []) = unqualified name
sourceType (TCons name args) = "(" <> unwords (unqualified name : map sourceType args) <> ")"
sourceType (TVar v) = T.unpack v

-- | A type as 'show' of a 'TypeRep' gives it: @[A]@, @A -> B@, @(A,B)@.
typeText :: TypeSkeleton -> Text
typeText = T.pack . go False
  where
    go _ (TCons "[]" [a]) = "[" <> go False a <> "]"
    go _ (TCons "(,)" [a, b]) = "(" <> go False a <> "," <> go False b <> ")"
    go _ (TCons "()" []) = "()"
    go p (TFun a b) = parens p (go True a <> " -> " <> go False b)
    go _ (TCons name []) = unqualified name
    go p (TCons name args) = parens p (unwords (unqualified name : map (go True) args))
    go _ (TVar v) = T.unpack v
    parens True s = "(" <> s <> ")"
    parens False s = s

-- | The prefix of the names of the variables of a type: xs for a list, f
-- for a function, and x for any other type.
prefixOf :: TypeSkeleton -> Text
prefixOf (TCons "[]" _) = "xs"
prefixOf (TFun _ _) = "f"
prefixOf _ = "x"

-- | The name of a type constructor without its module.
unqualified :: Text -> String
unqualified name = T.unpack (last (T.splitOn "." name))
