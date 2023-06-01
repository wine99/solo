{-# LANGUAGE
    AllowAmbiguousTypes
   ,DataKinds
   ,FlexibleContexts
   ,GADTs
   ,GeneralizedNewtypeDeriving
   ,KindSignatures
   ,PartialTypeSignatures
   ,PolyKinds
   ,RankNTypes
   ,ScopedTypeVariables
   ,TypeApplications
   ,TypeFamilies
   ,TypeOperators
   ,TypeSynonymInstances
   ,TypeFamilyDependencies
   ,UndecidableInstances
   ,EmptyCase
   #-}

module Primitives where

import Prelude hiding (return,(>>=), sum)
import qualified Prelude as P
import Data.TypeLits as TL
import Data.Proxy
import Data.Function
import qualified Data.Map.Strict as Map

import Unsafe.Coerce

import Sensitivity
import Privacy
import qualified Data.List as List

import System.IO
import Data.Maybe ( mapMaybe, fromMaybe, mapMaybe )
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Text.Read (readMaybe)

--------------------------------------------------
-- Axioms about sensitivities
--------------------------------------------------

data Id a b where
  Id :: a ~ b => Id a b

eq_sym :: Id a b -> Id b a
eq_sym p = case p of
  Id -> Id

-- a==b ⇔ t a == t b
cong :: forall a b t. Id a b -> t a -> t b
cong p x = case p of
             Id -> x

cong1 :: forall a b t c. Id a b -> t a c -> t b c
cong1 p x = case p of
              Id -> x

cong2 :: forall a b t c. Id a b -> t c a -> t c b
cong2 p x = case p of
              Id -> x

-- axioms
scale_unit     :: forall s.        Id (ScaleSens s 1) s
maxnat_idemp   :: forall n.        Id (MaxNat n n) n
truncate_n_inf :: forall n s.      Id (TruncateSens n (TruncateInf s)) (TruncateSens n s)
scale_distrib  :: forall n s1 s2.  Id (ScaleSens (s1 +++ s2) n) (ScaleSens s1 n +++ ScaleSens s2 n)
trunc_distrib  :: forall n1 n2 s.  Id (TruncateSens (n1 TL.+ n2) s) (TruncateSens n1 s +++ TruncateSens n2 s)
scale_max      :: forall n1 n2 s.  Id (ScaleSens s n1 +++ ScaleSens s n2) (ScaleSens s (MaxNat n1 n2))

scale_cong1    :: forall n s1 s2.  Id s1 s2 -> Id (ScaleSens s1 n) (ScaleSens s2 n)
scale_cong2    :: forall n1 n2 s.  Id n1 n2 -> Id (ScaleSens s n1) (ScaleSens s n2)

plus_cong      :: forall s1 s1' s2 s2'. Id s1 s1' -> Id s2 s2' -> Id (s1 +++ s2) (s1' +++ s2')

priv_idemp     :: forall n eps delta senv. Id (TruncatePriv eps delta (TruncateSens n senv))
                                              (TruncatePriv eps delta senv)

scale_unit = unsafeCoerce Id
maxnat_idemp = undefined
truncate_n_inf = undefined
scale_distrib = undefined
trunc_distrib = undefined
scale_max = undefined
scale_cong1 = undefined
scale_cong2 = undefined
plus_cong = undefined
priv_idemp = undefined

--------------------------------------------------
-- Primitives for Doubles
--------------------------------------------------

(<+>) :: SDouble m s1 -> SDouble m s2 -> SDouble m (s1 +++ s2)
x <+> y = D_UNSAFE $ unSDouble x + unSDouble y

(<->) :: SDouble m s1 -> SDouble m s2 -> SDouble m (s1 +++ s2)
x <-> y = D_UNSAFE $ unSDouble x - unSDouble y

sabs :: SDouble m s -> SDouble m s
sabs x = D_UNSAFE $ abs $ unSDouble x

-- TODO: can we do better than putting "Double" here?
sfilter_fn :: (forall s. Double -> Bool)
  -> SDouble m s1
  -> L1List (SDouble m) s2
  -> L1List (SDouble m) (ScaleSens s1 1 +++ ScaleSens s2 1)
sfilter_fn f x xs =
  (if f x' then x' : xs' else xs') & map D_UNSAFE & SList_UNSAFE
  where
    x' = unSDouble x
    xs' = unSList xs & map unSDouble

-- Run a regular Haskell function and treat its output as infinitely sensitive
infsensL :: ([Double] -> [Double])
  -> SList cm (SDouble m) senv
  -> SList cm (SDouble m) (TruncateInf senv)
infsensL f (SList_UNSAFE xs) = map unSDouble xs & f & map D_UNSAFE & SList_UNSAFE

infsensD :: (Double -> Double)
  -> SDouble m senv
  -> SDouble m (TruncateInf senv)
infsensD f (D_UNSAFE x) = D_UNSAFE $ f x

--------------------------------------------------
-- Primitives for Lists
--------------------------------------------------

-- Helpers for reading files

readDoublesFromFile :: FilePath -> IO [Double]
readDoublesFromFile filepath =
  readFile filepath P.>>= \contents ->
  let lines' = lines contents in
  P.return $ mapMaybe readMaybe lines'

-- Split a string into a list of strings at delimiter
splitOn :: Char -> String -> [String]
splitOn delimiter input = case dropWhile (== delimiter) input of
  "" -> []
  s' -> w : splitOn delimiter s'' where (w, s'') = break (== delimiter) s'

-- Parse a line of CSV data as a list of doubles
parseLine :: T.Text -> [Double]
parseLine line = Data.Maybe.fromMaybe
  [] (mapM readMaybe (splitOn ',' (T.unpack line)))

-- Parse a file contents into a list of lists of doubles
parseCSV :: T.Text -> [[Double]]
parseCSV input = map parseLine (T.lines input)


sReadFileL :: FilePath -> IO (SList m (SDouble Disc) '[ '(f, NatSens 1) ])
sReadFileL filepath =
  readDoublesFromFile filepath P.>>= \xs ->
  P.return $ SList_UNSAFE $ map D_UNSAFE xs

sReadCsvNoHeader :: FilePath -> IO (SList m1 (SList m2 (SDouble Disc)) '[ '(f, NatSens 1) ])
sReadCsvNoHeader filepath =
  TIO.readFile filepath P.>>= \contents ->
  let values = parseCSV contents in
  P.return $ SList_UNSAFE $ map (SList_UNSAFE . map D_UNSAFE) values

sReadFile :: forall f t. t '[ '(f, NatSens 1) ]
sReadFile = undefined

source :: forall o m. Double -> SDouble Diff '[ '(o, NatSens 1) ]
source = D_UNSAFE

sConstD :: forall s. Double -> SDouble Diff s
sConstD = D_UNSAFE

sConstL :: forall s m t. [t s] -> SList m t s
sConstL = SList_UNSAFE

mkL1ListDouble :: forall o m. [Double] -> SList L1 (SDouble m) '[ '(o, NatSens 1) ]
mkL1ListDouble xs = SList_UNSAFE $ map D_UNSAFE xs

emptySList :: SList m t '[]
emptySList = SList_UNSAFE []

scons :: forall t m s1 s2. t s1 -> SList m t s2 -> SList m t (s1 +++ s2)
scons x xs = (unsafeDropSens x : unSList (unsafeDropSens xs)) & SList_UNSAFE & unsafeLiftSens

sfoldr :: forall fn_sens1 fn_sens2 t1 t2 cm s3 s4 s5.
           (forall s1p s2p.
            t1 s1p -> t2 s2p -> t2 (ScaleSens s1p fn_sens1 +++ ScaleSens s2p fn_sens2))
        -> t2 s5
        -> SList cm t1 s4
        -> t2 (ScaleSens s4 (MaxNat fn_sens1 fn_sens2) +++ TruncateInf s5)
sfoldr f init xs = unsafeLiftSens $ unSFoldr f (unsafeDropSens init) (unSList xs) where
  unSFoldr f init [] = init
  unSFoldr f init (x:xs) = unSFoldr f (unsafeDropSens $ f x (unsafeLiftSens init)) xs

-- this could be defined using a truncation version of "fold"
-- stmap :: forall n s2 a b.
--   (forall s1. a s1 -> b (TruncateSens n s1))
--   -> L1List a s2
--   -> L1List b (TruncateSens n s2)
-- stmap f as = SList_UNSAFE $ map f (unSList as)

clipDouble :: forall b m senv. (KnownNat b) => SDouble Disc senv -> SDouble Diff (ScaleSens senv b)
clipDouble x =
  let
    bound = fromIntegral $ natVal (Proxy :: Proxy b)
    x' = unSDouble x
  in
    D_UNSAFE $ if x' > bound then bound else if x' < -bound then -bound else x'

clipL1 :: forall b m senv. (KnownNat b) =>
  L1List (SDouble m) senv -> L1List (SDouble Diff) (ScaleSens senv b)
clipL1 (SList_UNSAFE xs) =
    if norm > valb
    then map (\x -> D_UNSAFE $ x / norm ) xs' & SList_UNSAFE
    else map D_UNSAFE xs' & SList_UNSAFE
    where
        valb = fromIntegral $ natVal (Proxy::Proxy b)
        xs' = map (abs . unSDouble) xs
        norm = List.sum xs'

clipL2 :: forall b m senv. (KnownNat b) =>
  L2List (SDouble m) senv -> L2List (SDouble Diff) (ScaleSens senv b)
clipL2 (SList_UNSAFE xs) =
    if norm > valb
    then map (\x -> D_UNSAFE $ x / norm ) xs' & SList_UNSAFE
    else map D_UNSAFE xs' & SList_UNSAFE
    where
        valb = fromIntegral $ natVal (Proxy::Proxy b)
        xs' = map unSDouble xs
        norm = sqrt $ List.sum $ map (**2) xs'

szip :: SList m a s1 -> SList m b s2 -> SList m (L1Pair a b) (s1 +++ s2)
szip xs ys = SList_UNSAFE xys & unsafeLiftSens where
  xs' = unsafeDropSens xs & unSList
  ys' = unsafeDropSens ys & unSList
  xys = zipWith (curry P_UNSAFE) xs' ys'

p_elim :: forall fn_sens1 fn_sens2 s t1 t2 t3.
          (forall s1p s2p.
            t1 s1p -> t2 s2p -> t3 (ScaleSens s1p fn_sens1 +++ ScaleSens s2p fn_sens2))
       -> L1Pair t1 t2 s
       -> t3 (ScaleSens s (MaxNat fn_sens1 fn_sens2))
p_elim f p = cong (scale_max @fn_sens1 @fn_sens2 @s) (uncurry f (unSPair p))

sfst :: LInfPair t1 t2 s -> t1 s
sfst p = fst $ unSPair p

ssnd :: LInfPair t1 t2 s -> t2 s
ssnd p = snd $ unSPair p

--------------------------------------------------
-- Primitives for Partition
--------------------------------------------------

-- Given a partitioning function f and a dataset xs, part computes the
-- partition according to f
part :: forall k cm t s. (Ord k, (MaxSens s) TL.== 1) => (t s -> k) -> SList cm t s -> Partition k cm t s
part f xs =
  let
    insertF newValue oldValue = oldValue ++ newValue
    emptyMap = Map.empty :: Map.Map k [t s]
    mapList = foldl (\m x -> let k = f x in Map.insertWith insertF k [x] m) emptyMap (unSList xs)
  in
    Partition_UNSAFE $ Map.map SList_UNSAFE mapList

--------------------------------------------------
-- Looping combinators
--------------------------------------------------

seqloop :: forall (k :: Nat) a (p :: EDEnv). (TL.KnownNat k) => (Int -> a -> PM p a) -> a -> PM (ScalePriv p k) a
seqloop f init =
  let
    iteration = fromInteger (TL.natVal (Proxy :: Proxy k))
    loop :: Int -> IO a -> IO a
    loop i accu =
      if i == iteration then
        accu
      else
        accu P.>>= \accu' ->
        loop (i+1) (unPM $ f i accu')
  in
    PM_UNSAFE $ loop 0 (P.return init)

-- advloop :: forall k delta_prime p a.
--   (TL.KnownNat k) => (Int -> a -> PM p a) -> a -> PM (AdvComp k delta_prime p) a
-- advloop = undefined


--------------------------------------------------
-- Parallel composition
--------------------------------------------------

-- Given a function and partition, parallel computes f on each part making up
-- the partition
parallel :: (SList cm t s -> PM p a) -> Partition k cm t s -> PM p (Map.Map k a)
parallel f partition =
  let
    unsens_part = unPartition partition
    applied_part = Map.map f unsens_part
    unpm_part = Map.map (\pm -> unPM pm P.>>= P.return) applied_part
    p = sequence unpm_part
  in
    PM_UNSAFE p
