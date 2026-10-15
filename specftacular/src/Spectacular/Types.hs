{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings,
             ScopedTypeVariables, TypeApplications, RecordWildCards, GADTs,
             StandaloneDeriving, KindSignatures, PolyKinds, RankNTypes,
             GeneralizedNewtypeDeriving, FlexibleContexts, TupleSections,
             PatternSynonyms, DeriveGeneric #-}

module Spectacular.Types where
import Data.Dynamic
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Map as Map
import GHC.Generics (Generic)

import Data.Typeable
import qualified Data.Text as T
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.CFTA.Term as CT
import Data.Proxy
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Exception (Exception, SomeException, evaluate, fromException, throw, throwIO, try)
import Debug.Trace (trace)

import Test.QuickCheck (Arbitrary(..), Gen(..))
import qualified Test.QuickCheck as QC
import Unsafe.Coerce
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import GHC.Exts (Any)
import qualified Type.Reflection as TR

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Hashable (Hashable, hash)
import Data.Containers.ListUtils (nubOrd)

-- | A type: a type variable, a function type, or a type constructor with
-- its arguments.
data TypeSkeleton
  = TVar Text
  | TFun TypeSkeleton TypeSkeleton
  | TCons Text [TypeSkeleton]
  deriving (Eq, Ord, Show, Read, Generic)

instance Hashable TypeSkeleton

-- | A term of the automata. The symbols are interned texts.
type Term = CT.Term Symbol

-- | A term as its symbol and the list of its children.
pattern Term :: Symbol -> [Term] -> Term
pattern Term s ts = CT.Node s ts
{-# COMPLETE Term #-}
-- The matcher inlines, as the matcher of 'CT.Node' does, so that a match
-- does not build the list of the children.
{-# INLINE Term #-}

-- | The types that stand for type variables in a signature. Each type has
-- many values, so that a law that holds only for a small type does not
-- pass the tests. QuickSpec tests type variables at Int too.
newtype A = A Int deriving (Typeable, Eq, Show, Ord)
newtype B = B Int deriving (Typeable, Eq, Show, Ord)
newtype C = C Int deriving (Typeable, Eq, Show, Ord)
newtype D = D Int deriving (Typeable, Eq, Show, Ord)
newtype Acc = Acc Int deriving (Typeable, Eq, Show, Ord)


deriving instance Arbitrary A
deriving instance QC.CoArbitrary A
deriving instance Arbitrary B
deriving instance QC.CoArbitrary B
deriving instance Arbitrary C
deriving instance QC.CoArbitrary C
deriving instance Arbitrary D
deriving instance QC.CoArbitrary D
deriving instance Arbitrary Acc
deriving instance QC.CoArbitrary Acc

data GeneratedInstance = Gend {
    g_tr :: TypeRep,
    g_arb :: DynGen,
    g_eq :: Maybe Dynamic,
    g_li_i :: GeneratedInstance
    }

-- | The generator and the equality of a type, for the search: the type as
-- 'TypeRep' shows it, the prefix of the names of its variables, the
-- generator, and the equality, if the type has one.
data Instance = Instance {
    inst_text :: Text,
    inst_prefix :: Text,
    inst_gen :: Generator,
    inst_eq :: Maybe Value
    }

-- | The instance of a generated instance.
toInstance :: GeneratedInstance -> Instance
toInstance rep = Instance { inst_text = T.pack (show (g_tr rep))
                          , inst_prefix = namePrefix (g_tr rep)
                          , inst_gen = generator (g_arb rep)
                          , inst_eq = dynamicValue <$> g_eq rep }

-- | The instances of the types that the signatures of the benchmarks use
-- (see 'builtinReps'), of A to Acc for the type variables, of the lists of
-- these, and of the types that the function gives.
frontInstances :: (TypeSkeleton -> Maybe GeneratedInstance) -> TypeSkeleton -> Maybe Instance
frontInstances extraReps = fmap toInstance . genRep
  where
        genRep :: TypeSkeleton -> Maybe GeneratedInstance
        genRep (TVar a) | Just t <- lookup a [ (v, t) | (t, v) <- carriers ] = genRep t
        genRep t | Just g <- lookup t builtinReps = Just g
        genRep (TCons "[]" [ts]) = g_li_i <$> genRep ts
        genRep (TFun _ _) = Nothing
        --- To allow for types not considered here
        --- Not sure if this is the best way to go about it
        genRep x = 
          case extraReps x of 
            Just t -> Just t
            Nothing -> trace ("*** Warning: Could not generate instances for '" ++ (show x) ++ "', ignoring...") Nothing

-- | The types of a signature that the search needs instances of: the
-- types of the functions, their parts, and the lists of these types, after
-- the function changes them.
instanceTypes :: (TypeSkeleton -> TypeSkeleton) -> Sig -> [TypeSkeleton]
instanceTypes typeMod sigs = nubOrd $ concatMap addLi $ Set.toList $ Set.unions $ map cons trs
  where trs = map (typeMod . sfTypeRep) $ Map.elems sigs
        -- we specialcase lists
        cons :: TypeSkeleton -> Set TypeSkeleton
        cons t@(TCons _ r) = Set.unions $ (Set.singleton t):(map cons r)
        cons t@(TFun arg ret) = Set.singleton t <> cons arg <> cons ret
        cons (TVar _) = Set.empty
        addLi :: TypeSkeleton -> [TypeSkeleton]
        addLi t = t:(addLi' 1 t) -- bump this to get more [A], [[A]],
                                 -- [[[A]]], etc.
          where addLi' :: Int -> TypeSkeleton -> [TypeSkeleton]
                addLi' 0 _ = []
                addLi' n t = t':(addLi' (n-1) t')
                 where t' = TCons "[]" [t]

sigGivens :: (TypeSkeleton -> TypeSkeleton) -> Sig -> (TypeSkeleton -> Maybe Instance)
          -> (Sig, Map TypeSkeleton (Text, Value) , Map TypeSkeleton (Text,Func))
sigGivens typeMod sigs instances = (
                   Map.fromList (mapMaybe consName allCons)
                 , eq_insts
                 , arbs)
  where user_eq = mapMaybe g_eq $ Map.assocs sigs
          where g_eq (k, GivenFun (GivenInst _ eq) tsk)  = Just (tsk, (k, eq))
                g_eq _ = Nothing
        eq_insts = Map.fromList $ user_eq ++
                    mapMaybe (\c -> (c,) . fmap sfFunc <$> toEqInst c)
                             (filter isCon allCons)
        user_arbs = mapMaybe g_arb $ Map.assocs sigs
          where g_arb (k, f@(GivenFun (GivenVar {})  tsk)) = Just (tsk, (k,f))
                g_arb _ = Nothing
        arbs = Map.fromList 
                    (user_arbs ++
                    mapMaybe (\ty -> (ty,)  <$> consName ty) allCons)
        
        isCon (TCons _ _) = True
        isCon _ = False
        allCons = instanceTypes typeMod sigs
        toEqInst e | Just inst <- instances e,
                     Just eqf <- inst_eq inst = g inst eqf
           where g inst eqf = Just ("<@Eq_" <> inst_text inst <> "@>",
                                    GivenFun (GivenInst (inst_text inst) eqf)
                                    $ TCons "Eq" [e])
        toEqInst _ = Nothing

        consName :: TypeSkeleton -> Maybe (Text, Func)
        consName t = g <$> instances t
           where g inst = toTup (GivenFun (GivenVar (inst_prefix inst) (inst_text inst) 0 (inst_gen inst)) t)
                 toTup gf@(GivenFun gv _) = (gvToName gv, gf)

addExplicitEquality :: Typeable a => (a -> a -> Bool) -> Sig
addExplicitEquality (fun :: a -> a -> Bool) = Map.singleton key val
  where g_tr = typeRep (Proxy :: Proxy a)
        key = "<@Eq_"<>(T.pack $ show g_tr)<>"@>"
        val = GivenFun (GivenInst (T.pack (show g_tr)) (toValue fun)) $
                        TCons "Eq" [typeRepToTypeSkeleton g_tr]

        

addEquality :: (Eq a, Typeable a) => Proxy a -> Sig
addEquality (Proxy :: Proxy a) = Map.singleton key val
  where g_tr = typeRep (Proxy :: Proxy a)
        key = "<@Eq_"<>(T.pack $ show g_tr)<>"@>"
        val = GivenFun (GivenInst (T.pack (show g_tr)) (toValue ((==) :: a -> a -> Bool))) $
                        TCons "Eq" [typeRepToTypeSkeleton g_tr]

addArbitrary :: (Typeable a, Arbitrary a) => Proxy a -> Sig
addArbitrary (Proxy :: Proxy a) = Map.singleton (gvToName gv) val
  where g_tr = typeRep (Proxy :: Proxy a)
        gv = givenVar g_tr 0 (generator (DynGen (arbitrary :: Gen a)))
        val = GivenFun gv $ typeRepToTypeSkeleton g_tr

genRepFromProxy :: (Show a, Eq a, Typeable a, Arbitrary a) =>
                    Proxy a -> GeneratedInstance
genRepFromProxy (Proxy :: Proxy a) = Gend {..}
    where g_tr = typeRep (Proxy :: Proxy a)
          g_arb = DynGen (arbitrary :: Gen a)
          g_eq = Just (toDyn ((==) :: a -> a -> Bool))
          g_li_i = genRepFromProxy (Proxy :: Proxy [a])

genRepFromProxyNoEq :: (Typeable a, Arbitrary a) =>
                        Proxy a -> GeneratedInstance
genRepFromProxyNoEq (Proxy :: Proxy a) = Gend {..}
    where g_tr = typeRep (Proxy :: Proxy a)
          g_arb = DynGen (arbitrary :: Gen a)
          g_eq = Nothing
          g_li_i = genRepFromProxyNoEq (Proxy :: Proxy [a])




arith :: (Typeable a, Num a, Eq a) => Proxy a -> Sig
arith p = Map.fromList $
                (map (fmap extraFunc) $
                 [ ("0", toDyn zero)
                 , ("1", toDyn $ (fromInteger 1) `asProxyTypeOf` p)
                 ]
                 )
  where zero = (fromInteger 0) `asProxyTypeOf` p

typeRepToTypeSkeleton :: TypeRep -> TypeSkeleton
typeRepToTypeSkeleton tr
     | tcn == "->",
       [arg,ret] <- args
     = TFun arg ret
     | otherwise = TCons (T.pack tcn) args
  where (tc, tra) = splitTyConApp tr
        tcn = typeConName tc
        args = map typeRepToTypeSkeleton tra

-- | The type skeleton of a type. An extraReps function can use it to
-- recognize a type: t == typeSkeletonOf (Proxy :: Proxy MyType).
typeSkeletonOf :: Typeable a => Proxy a -> TypeSkeleton
typeSkeletonOf = typeRepToTypeSkeleton . typeRep

-- | The name of a type constructor, with its module, so that two types with
-- the same name in different modules stay apart. GHC 9.6 and later give
-- some built-in type constructors new names, for example List for []. For
-- these, the function gives the name of the special syntax.
typeConName :: TyCon -> String
typeConName tc
  | tc == tyConOf (Proxy :: Proxy [()]) = "[]"
  | tc == tyConOf (Proxy :: Proxy ((), ())) = "(,)"
  | tc == tyConOf (Proxy :: Proxy ()) = "()"
  | tc == tyConOf (Proxy :: Proxy (() -> ())) = "->"
  | otherwise = tyConModule tc ++ "." ++ tyConName tc

-- | The types that stand for type variables, with the names of the type
-- variables.
carriers :: [(TypeSkeleton, Text)]
carriers =
  [ (typeSkeletonOf (Proxy :: Proxy A), "a")
  , (typeSkeletonOf (Proxy :: Proxy B), "b")
  , (typeSkeletonOf (Proxy :: Proxy C), "c")
  , (typeSkeletonOf (Proxy :: Proxy D), "d")
  , (typeSkeletonOf (Proxy :: Proxy Acc), "acc") ]

-- | The generators and the equalities of the types that the signatures of
-- the benchmarks use.
builtinReps :: [(TypeSkeleton, GeneratedInstance)]
builtinReps =
  [ withEq (Proxy :: Proxy A), withEq (Proxy :: Proxy B), withEq (Proxy :: Proxy C)
  , withEq (Proxy :: Proxy D), withEq (Proxy :: Proxy Acc), withEq (Proxy :: Proxy ())
  , withEq (Proxy :: Proxy Int), withEq (Proxy :: Proxy Bool), withEq (Proxy :: Proxy Char)
  , withEq (Proxy :: Proxy Integer), withEq (Proxy :: Proxy Double)
  , withEq (Proxy :: Proxy Float), withEq (Proxy :: Proxy Ordering)
  , withEq (Proxy :: Proxy Word)
  , withoutEq (Proxy :: Proxy (A -> B)), withoutEq (Proxy :: Proxy (A -> A))
  , withEq (Proxy :: Proxy (A, B)), withEq (Proxy :: Proxy (A, A))
  , withEq (Proxy :: Proxy ([A], [B])), withEq (Proxy :: Proxy ([A], [A])) ]
  where
    withEq :: (Show a, Eq a, Typeable a, Arbitrary a) => Proxy a -> (TypeSkeleton, GeneratedInstance)
    withEq p = (typeSkeletonOf p, genRepFromProxy p)
    withoutEq :: (Typeable a, Arbitrary a) => Proxy a -> (TypeSkeleton, GeneratedInstance)
    withoutEq p = (typeSkeletonOf p, genRepFromProxyNoEq p)

-- | The type constructor of a type.
tyConOf :: Typeable a => Proxy a -> TyCon
tyConOf = typeRepTyCon . typeRep


type Sig = Map Text Func

-- | A function of the signature, and its type.
data Func = SigFunc { sf_func :: Value
                    , sf_rep :: TypeSkeleton}
          | GenFunc { gf_func :: Value
                    , gf_rep :: TypeSkeleton}
          | GivenFun {given_info :: GivenInfo, giv_rep :: TypeSkeleton}
          deriving (Show)

moreGenerators :: Func -> [Func]
moreGenerators (GivenFun (GivenVar prefix ty _ g) grep) =
    map (\v -> GivenFun (GivenVar prefix ty v g) grep) [0..]
moreGenerators _ = []

-- | What the search gives a signature: an equality, with the type as
-- 'TypeRep' shows it, or a variable, with the prefix of its name, the type
-- as 'TypeRep' shows it, its index, and the generator of its values.
data GivenInfo
    = GivenInst Text Value
    | GivenVar Text Text Int Generator
    deriving (Show)

-- | The variable with an index of the type of a 'TypeRep'. The name of a
-- list variable starts with xs, of a function variable with f, and of any
-- other variable with x.
givenVar :: TypeRep -> Int -> Generator -> GivenInfo
givenVar tr = GivenVar (namePrefix tr) (T.pack (show tr))

-- | The prefix of the names of the variables of a type: xs for a list, f
-- for a function, and x for any other type.
namePrefix :: TypeRep -> Text
namePrefix tr = case typeConName (typeRepTyCon tr) of
                  "[]" -> "xs"
                  "->" -> "f"
                  _ -> "x"

gvToNameNoType :: GivenInfo -> Text
gvToNameNoType (GivenVar prefix _ i _) = prefix <> T.pack (show i)
gvToNameNoType _ = error "not a given var!"

gvToName :: GivenInfo -> Text
gvToName gv@(GivenVar _ ty _ _) = gvToNameNoType gv <> "_<" <> ty <> ">"
gvToName _ = error "not a given var!"

-- | A generator of QuickCheck, with the type of its values.
data DynGen where
   DynGen :: forall a. Typeable a => Gen a -> DynGen

-- | A value of the search: a 'Dynamic', with its type, or a value without
-- its type. The front end of Haskell gives typed values. By default the
-- search makes them untyped once, before its phases (see 'untypedSig'). It
-- runs a term only when each application fits its argument (see
-- 'termType'), and the values of A, B, C, D, and Acc have the representation
-- of Int. Thus an application of untyped values needs no test of the types.
--
-- With SPECFTACULAR_CHECKED=1, the values stay typed, and an application of
-- two typed values tests the types: a function takes an argument of its
-- type, or of another of A to Acc, and any other application raises
-- 'IllTyped'. The golden test runs in this mode too, so that a wrong
-- application fails a test.
data Value = Typed Dynamic | Untyped Any

instance Show Value where
  show _ = "<value>"

-- | An application of a typed function to a typed argument of another type.
newtype IllTyped = IllTyped String
  deriving (Show)

instance Exception IllTyped

-- | A value as a typed value of the search.
toValue :: Typeable a => a -> Value
toValue = Typed . toDyn

-- | A value of the search as a value of its type.
fromValue :: Typeable a => Value -> a
fromValue (Typed d) = fromMaybe (throw (IllTyped ("not a value of its type: " ++ show (dynTypeRep d)))) (fromDynamic d)
fromValue (Untyped x) = unsafeCoerce x

-- | Apply a function to an argument. When both are typed, A, B, C, D, and
-- Acc have the representation of Int, so a function can take an argument of
-- another of them, and any other difference raises 'IllTyped'. When one of
-- them is untyped, the application has no test. Two untyped values come
-- first, as in the search without SPECFTACULAR_CHECKED.
apply :: Value -> Value -> Value
apply (Untyped f) (Untyped x) = Untyped ((unsafeCoerce f :: Any -> Any) x)
apply (Typed df@(Dynamic (TR.Fun ta tr) f)) (Typed dx@(Dynamic tx x)) =
    case dynApply df dx of
      Just r -> Typed r
      Nothing
        | sameUpToCarriers (typeRepToTypeSkeleton (TR.SomeTypeRep ta)) (typeRepToTypeSkeleton (TR.SomeTypeRep tx)) ->
            Typed (Dynamic (unsafeCoerce tr) (unsafeCoerce f x))
        | otherwise -> illTyped df dx
apply (Typed df) (Typed dx) = illTyped df dx
apply f x = Untyped ((unsafeCoerce (rawValue f) :: Any -> Any) (rawValue x))

-- | The representation of a value, without its type.
rawValue :: Value -> Any
rawValue (Typed (Dynamic _ x)) = unsafeCoerce x
rawValue (Untyped x) = x

-- | The value without its type.
untyped :: Value -> Value
untyped = Untyped . rawValue

-- | The error of an application of two values whose types do not fit.
illTyped :: Dynamic -> Dynamic -> a
illTyped df dx = throw (IllTyped ("cannot apply " ++ show (dynTypeRep df) ++ " to " ++ show (dynTypeRep dx)))

-- | The value of a 'Dynamic'.
dynamicValue :: Dynamic -> Value
dynamicValue = Typed

-- | A generator of the values of a type: the value of a seed and a size.
newtype Generator = Generator (Int -> Int -> Value)

instance Show Generator where
  show _ = "<generator>"

-- | The generator of a generator of QuickCheck: unGen with the seed through
-- mkQCGen.
generator :: DynGen -> Generator
generator (DynGen g) = Generator (\seed size -> toValue (unGen g (mkQCGen seed) size))

-- ConFunc comes from the user provided signature, and we want at least
-- one of these to show up.
conFunc :: Dynamic -> Func
conFunc f = SigFunc {sf_func = dynamicValue f, sf_rep = typeRepToTypeSkeleton (dynTypeRep f)}

-- extraFuncs are from generators like arith, but we don't *require* them,
-- they're just extra.
extraFunc :: Dynamic -> Func
extraFunc f = GenFunc {gf_func = dynamicValue f, gf_rep = typeRepToTypeSkeleton (dynTypeRep f)}


sfFunc :: Func -> Value
sfFunc (SigFunc {..}) = sf_func
sfFunc (GenFunc {..}) = gf_func
-- Should not happen
sfFunc (GivenFun {given_info = GivenInst _ inst_f}) = inst_f
sfFunc (GivenFun {}) = toValue ()

sfTypeRep :: Func -> TypeSkeleton
sfTypeRep (SigFunc{..}) = sf_rep
sfTypeRep (GenFunc{..}) = gf_rep
sfTypeRep (GivenFun {..}) = giv_rep

con :: Typeable a => Text -> a -> Sig
con name fun = Map.singleton name $ (conFunc $ toDyn fun)

extra :: Typeable a => Text -> a -> Sig
extra name fun = Map.singleton name $ (extraFunc $ toDyn fun)

type VarVals = Map Text Value


generalizeType :: TypeSkeleton -> TypeSkeleton
generalizeType t | Just v <- lookup t carriers = TVar v
generalizeType (TCons s r) = TCons s $ map generalizeType r
generalizeType (TFun arg ret) = TFun (generalizeType arg) (generalizeType ret)
generalizeType tsk = tsk


monomorphiseType :: TypeSkeleton -> TypeSkeleton
monomorphiseType t | Just _ <- lookup t carriers = typeSkeletonOf (Proxy :: Proxy A)
monomorphiseType (TCons s r) = TCons s $ map monomorphiseType r
monomorphiseType (TFun arg ret) = TFun (monomorphiseType arg) (monomorphiseType ret)
monomorphiseType tsk = tsk

-- | The template of a term: each variable becomes a template variable of
-- the same type. Equal variables give equal template variables.
toTemplate :: Sig -> Term -> Term
toTemplate sig (Term (Symbol s) ty) |
    Just (GivenFun {given_info = GivenVar {}}) <- sig Map.!? s =
         Term (Symbol $ "<v>" <> s) ty
toTemplate sig (Term s args) = Term s $ map (toTemplate sig) args
 
-- | Whether two types are equal when A, B, C, D, and Acc are one type.
sameUpToCarriers :: TypeSkeleton -> TypeSkeleton -> Bool
sameUpToCarriers a b | isCarrier a && isCarrier b = True
  where isCarrier t = t `elem` map fst carriers
sameUpToCarriers (TCons ca as) (TCons cb bs) =
    ca == cb && length as == length bs && and (zipWith sameUpToCarriers as bs)
sameUpToCarriers (TFun a r) (TFun b s) = sameUpToCarriers a b && sameUpToCarriers r s
sameUpToCarriers a b = a == b


-- | The value of a term on a test case.
evalTerm :: Sig -> VarVals -> Term -> Value
evalTerm sig tc (Term "app" [_, f, v]) = apply (evalTerm sig tc f) (evalTerm sig tc v)
evalTerm sig tc (Term (Symbol sym) _) =
    case sig Map.!? sym of
      Just (GivenFun {given_info = GivenVar {}}) ->
          fromMaybe (error "evalTerm: variable not found") (tc Map.!? sym)
      Just (GivenFun {given_info = GivenInst _ inst}) -> inst
      Just f@(SigFunc {}) -> sfFunc f
      Just f@(GenFunc {}) -> sfFunc f
      _ -> error ("evalTerm: symbol not found: " ++ T.unpack sym)

-- | The type of the value of a term, from the types of its functions and of
-- its variables. An application takes an argument of the type of its
-- function, or of another of A to Acc, which have the representation of
-- Int, as 'apply' tests it for two typed values. Left: an application
-- whose argument does not fit, so the search cannot run the term on untyped
-- values. The types are the type skeletons of the functions and the
-- variables, which every front end gives, so the test needs no 'TypeRep'.
termType :: Sig -> Term -> Either String TypeSkeleton
termType sig (Term "app" [_, f, v]) = do
    tf <- termType sig f
    tv <- termType sig v
    case tf of
      TFun ta tr | sameUpToCarriers ta tv -> Right tr
      _ -> Left ("cannot apply " ++ show tf ++ " to " ++ show tv)
termType sig (Term (Symbol sym) _) =
    maybe (Left ("no symbol " ++ T.unpack sym)) (Right . sfTypeRep) (sig Map.!? sym)

-- | A signature with untyped values (see 'Value'): its functions, its
-- equalities, and the values of its generators.
untypedSig :: Sig -> Sig
untypedSig = fmap untypedFunc
  where untypedFunc f@(SigFunc {sf_func = v}) = f {sf_func = untyped v}
        untypedFunc f@(GenFunc {gf_func = v}) = f {gf_func = untyped v}
        untypedFunc (GivenFun (GivenInst t v) r) = GivenFun (GivenInst t (untyped v)) r
        untypedFunc (GivenFun (GivenVar p t i g) r) = GivenFun (GivenVar p t i (untypedGenerator g)) r

-- | An instance with untyped values.
untypedInstance :: Instance -> Instance
untypedInstance inst = inst { inst_gen = untypedGenerator (inst_gen inst), inst_eq = untyped <$> inst_eq inst }

-- | A generator of untyped values.
untypedGenerator :: Generator -> Generator
untypedGenerator (Generator g) = Generator (\seed size -> untyped (g seed size))

-- | The test cases of a signature: a value for each generated variable.
-- Test case k has the size k of 'testSizes'. Each variable takes its value
-- from a seed of its own, so a variable has the same values in each phase.
testCases :: Int -> Sig -> [VarVals]
testCases n sig =
    [ Map.fromList [ (v, value g k size v) | (v, GivenFun {given_info = GivenVar _ _ _ g}) <- Map.assocs sig ]
    | (k, size) <- zip [0 :: Int ..] (testSizes n) ]
  where value (Generator g) k size v = g (hash (k, v)) size

-- | The sizes of n test cases, as QuickSpec chooses them (run in
-- QuickSpec.Internal.Testing.QuickCheck of quickspec-2.2.2). 1% of the test
-- cases have the size 0. The others are biased towards small sizes: the
-- size is the maximum size 100 minus the cube root of a number that is
-- spread evenly over [0, 100^3).
testSizes :: Int -> [Int]
testSizes n =
    replicate zeroes 0
    ++ reverse [ maxSize - truncate (fromIntegral u ** (1 / 3) :: Double) | u <- uniform others (maxSize ^ (3 :: Int)) ]
  where
    others = ceiling (fromIntegral n * (1 - 0.01 :: Double))
    zeroes = n - others
    maxSize = 100
    -- m numbers spread evenly over [0, k), as uniform in QuickSpec.
    uniform m k = concat [ replicate (m `div` k) i | i <- [0 .. k - 1] ]
                  ++ [ i * k `div` (m `mod` k) | i <- [0 .. m `mod` k - 1] ]

-- | Whether two values are equal by an equality. Untyped values compare
-- without the tests of 'apply'.
equalBy :: Value -> Value -> Value -> Bool
equalBy (Untyped eq) (Untyped a) (Untyped b) = (unsafeCoerce eq :: Any -> Any -> Bool) a b
equalBy eq a b = fromValue (apply (apply eq a) b)

-- | Whether two values are equal, by the equality of their type. Nothing
-- means that the comparison threw an exception.
valuesEqual :: Value -> Value -> Value -> IO (Maybe Bool)
valuesEqual eq a b = do
    r <- try (evaluate (equalBy eq a b))
    case r of
        Left (e :: SomeException)
          | Just (illTyped :: IllTyped) <- fromException e -> throwIO illTyped
          | otherwise -> return Nothing
        Right x -> return (Just x)


-- TODO: can we kill a branch once a rewriteable term is detected?
--
