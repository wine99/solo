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
   ,RebindableSyntax
   ,EmptyCase
   #-}

module Main where

import Prelude hiding (return,(>>=), sum)
import qualified Prelude as P
import Data.TypeLits as TL
import Data.Proxy

import System.Random
import qualified System.Random.MWC as MWC
import qualified Statistics.Distribution.Laplace as Lap
import Statistics.Distribution (ContGen(genContVar))
import System.Random.MWC (createSystemRandom)

import SensitivitySafe
import PrivacySafe
import Primitives
import StdLib
import Text.Read (readMaybe)

import qualified Data.Map.Strict as Map
import qualified GHC.List as List
import Sensitivity (SList(SList_UNSAFE), SDouble (D_UNSAFE))


--------------------------------------------------
-- Simple examples
--------------------------------------------------

dbl :: SDouble Diff senv -> SDouble Diff (senv +++ senv)
dbl x = x <+> x

simplePrivacyFunction :: TL.KnownNat (MaxSens (s +++ s)) =>
  SDouble Diff s -> PM (TruncatePriv (RNat 2) Zero (s +++ s)) Double
simplePrivacyFunction x = laplace @(RNat 2) (dbl x)

addNoiseTwice :: TL.KnownNat (MaxSens s) => SDouble Diff s
  -> PM (TruncatePriv (RNat 2) Zero s ++++ TruncatePriv (RNat 3) Zero s) Double
addNoiseTwice x = do
  a <- laplace @(RNat 2) x
  b <- laplace @(RNat 3) x
  return $ a + b

egAddNoiseTwice :: Double -> PM '[ '("input_db", RNat 5, Zero) ] Double
egAddNoiseTwice x = addNoiseTwice (sConstD @'[ '( "input_db", NatSens 1 ) ] x)

-- FAIL version from the paper:
--
-- sumListFail xs = sfoldr (<+>) (sConstD @'[] 0) xs

-- Correct version
sumList :: L1List (SDouble Diff) s -> SDouble Diff s
sumList xs = cong scale_unit $ sfoldr @1 @1 scalePlus (sConstD @'[] 0) xs
  where scalePlus a b = cong (eq_sym scale_unit) a <+> cong (eq_sym scale_unit) b

-- FAIL branching on sdouble
-- (NOTE: this no longer fails if you change the import `SensitivitySafe` to
-- `Sensitivity`)
--
-- tryBranchFail :: SDouble Diff s1 -> Double
-- tryBranchFail x = case x of
--   D_UNSAFE z -> z


--------------------------------------------------
-- CDF Example
--------------------------------------------------

cdf :: forall ε iterations s. (TL.KnownNat (MaxSens s), TL.KnownNat iterations, TL.KnownRat ε) =>
  [Double] -> L1List (SDouble Disc) s -> PM (ScalePriv (TruncatePriv ε Zero s) iterations) [Double]
cdf buckets db = seqloop @iterations (\i results -> do
                                         let c = count $ sfilter ((<) $ buckets !! i) db
                                         r <- laplace @ε c
                                         return (r : results)) []

exampleDB :: IO (L1List (SDouble Disc) '[ '("random_numbers.txt", NatSens 1 ) ])
exampleDB = sReadFileL "random_numbers.txt"

-- ε = 100
examplecdf :: IO (PM '[ '("random_numbers.txt", RNat 100, Zero ) ] [Double])
examplecdf =
  exampleDB P.>>= \exampleDB ->
  P.return $ cdf @(RNat 1) @100 [0..100] exampleDB


assignBin :: SDouble m s -> Integer
assignBin sdouble = truncate $ unSDouble sdouble

parted =
  exampleDB P.>>= \exampleDB ->
  P.return $ part assignBin exampleDB

noisyCount k xs = do
  let c = count xs
  laplace @(RNat 1) c

-- Here Haskell can infer the type of `histogramPM` is
--  PM '[ '("random_numbers.txt", 'Pos 1 ':% 1, 'Pos 0 ':% 1)] (Map Integer Double)
-- So parallel cdf satisfies 1,0-differential privacy
parallelCdf =
  parted P.>>= \parted ->
  let histogramPM = parallel noisyCount parted in
  unPM histogramPM P.>>= \histogram ->
  let kvs = Map.toAscList histogram in
  P.return [List.sum (map snd (take i kvs)) | i <- [1 .. length kvs]]

--------------------------------------------------
-- Gradient descent example
--------------------------------------------------

type Weights = [Double]
type Example = [Double]
type SExample = L2List (SDouble Disc)
type SDataset senv = L1List SExample senv
gradient :: Weights -> Example -> Weights
gradient = undefined


clippedGrad :: forall senv cm m.
  Weights -> SExample senv -> L2List (SDouble Diff) (TruncateSens 1 senv)
clippedGrad weights x =
  let g = infsensL (gradient weights) x         -- apply the infinitely-sensitive function
  in cong (truncate_n_inf @1 @senv) $ clipL2 g  -- clip the results and return

gradientDescent :: forall ε δ iterations s.
  (TL.KnownNat iterations) =>
  Weights -> SDataset s -> PM (ScalePriv (TruncatePriv ε δ s) iterations) Weights
gradientDescent weights xs =
  let gradStep i weights =
        let clippedGrads = stmap @1 (clippedGrad weights) xs
            gradSum = sfoldr1s sListSum1s (sConstL @'[] []) clippedGrads
        in gaussLN @ε @δ @1 @s gradSum
  in seqloop @iterations gradStep weights

{- gradient descent does not work as it requires AdvComp

gradientDescentAdv :: forall ε δ iterations s.
  (TL.KnownNat iterations) =>
  Weights -> SDataset s -> PM (AdvComp iterations δ (TruncatePriv ε δ s)) Weights
gradientDescentAdv weights xs =
  let gradStep i weights =
        let clippedGrads = stmap @1 (clippedGrad weights) xs
            gradSum = sfoldr1s sListSum1s (sConstL @'[] []) clippedGrads
        in gaussLN @ε @δ @1 @s gradSum
  in advloop @iterations @δ gradStep weights

-}

{- This could compile, but the default reduction stack for equality checking of the natrual numbers is exceeded

-- SExample of passing in specific numbers to reduce the expression down to literals
-- Satisfies (1, 1e-5)-DP
gdMain :: PM '[ '("dataset.dat", RNat 1, RLit 1 100000) ] Weights
gdMain =
  let weights = take 10 $ repeat 0
      dataset = sReadFile @"dataset.dat"
  in gradientDescent @(RLit 1 100) @(RLit 1 10000000) @100 weights dataset

-}

--------------------------------------------------
-- MWEM
--------------------------------------------------

type RangeQuery = (Double, Double)
evaluateDB :: RangeQuery -> L1List (SDouble Disc) s -> SDouble Diff s
evaluateDB (l, u) db = count $ sfilter (\x -> l < x && u > x) db
evaluateSynth :: RangeQuery -> [Double] -> Double
evaluateSynth (l, u) syn_rep = fromIntegral $ length $ filter (\x -> l < x && u > x) syn_rep

scoreFn :: forall s. [Double] -> RangeQuery -> L1List (SDouble Disc) s -> SDouble Diff s
scoreFn syn_rep q db =
  let true_answer = evaluateDB q db
      syn_answer  = evaluateSynth q syn_rep
  in sabs $ sConstD @'[] syn_answer <-> true_answer

mwem :: forall ε iterations s.
  (TL.KnownNat (MaxSens s), TL.KnownNat iterations, TL.KnownRat ε) =>
  [Double] -> [RangeQuery] -> L1List (SDouble Disc) s
  -> PM (ScalePriv ((TruncatePriv ε Zero s) ++++ (TruncatePriv ε Zero s)) iterations) [Double]
mwem syn_rep qs db =
  let mwemStep _ syn_rep = do
        selected_q <- expMech @ε (scoreFn syn_rep) qs db
        measurement <- laplace @ε (evaluateDB selected_q db)
        return $ multiplicativeWeights syn_rep selected_q measurement
  in seqloop @iterations mwemStep syn_rep

multiplicativeWeights :: [Double] -> (Double, Double) -> Double -> [Double]
multiplicativeWeights = undefined


--------------------------------------------------
-- Exponential Mechanism on Laplace Samples
--------------------------------------------------

samples :: IO (SList m (SDouble m1) '[ '("", NatSens 1 ) ])
samples = 
      let sampleLaplace = 
            createSystemRandom P.>>= \gen ->
            genContVar (Lap.laplace 5 10) gen P.>>= \r ->
            P.return r
          laplaceSamples = sequence [sampleLaplace | _ <- [1..1000]]
      in
          laplaceSamples P.>>= \x -> P.return $ SList_UNSAFE ([D_UNSAFE d | d <- x])

options :: [Integer]
options = [-10 .. 10]

filterCount :: Integer -> L1List (SDouble m) s -> SDouble 'Diff s
filterCount option dataset = count $ sfilter (\x -> (round x) == option) dataset


mostFrequent = samples P.>>= \s -> P.return $ expMech @(RNat 1) filterCount options s


{-

main = 
  examplecdf P.>>= \cdfResult ->
  unPM cdfResult P.>>= \cdfResult ->
  print cdfResult

 -}


main = mostFrequent P.>>= \pm -> unPM pm P.>>= print
-- main = parallelCdf P.>>= \cdfResult -> print cdfResult