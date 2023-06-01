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
-- CDF Example
--------------------------------------------------

-- Our dataset is a list of random numbers between 0 and 100
exampleDB :: IO (L1List (SDouble Disc) '[ '("random_numbers.txt", NatSens 1 ) ])
exampleDB = sReadFileL "random_numbers.txt"

-------- Computing CDF using Sequential composition --------

-- The sequential CDF query
cdf :: forall ε iterations s. (TL.KnownNat (MaxSens s), TL.KnownNat iterations, TL.KnownRat ε) =>
  [Double] -> L1List (SDouble Disc) s -> PM (ScalePriv (TruncatePriv ε Zero s) iterations) [Double]
cdf buckets db = seqloop @iterations (\i results -> do
                                         let c = count $ sfilter ((<) $ buckets !! i) db
                                         r <- laplace @ε c
                                         return (r : results)) []

-- Running the query on our dataset with privacy budget ε = 1

sequentialCDF_PM :: IO
  (PM
     '[ '("random_numbers.txt", 'Pos 1 ':% 1, 'Pos 0 ':% 1)] [Double])
sequentialCDF_PM =
  exampleDB P.>>= \exampleDB ->
  P.return $ cdf @(RLit 1 100) @100 [0..100] exampleDB

-- Extracting the result from the privacy monad and rounding (post-processing)
sequentialCDF = 
  sequentialCDF_PM P.>>= \cdfResult ->
  unPM cdfResult P.>>= \cdfResult -> 
  P.return $ map round cdfResult

-------- Computing CDF using Parallel composition --------

-- Function that designates in which bin a number from our dataset falls into
-- Here, we use 100 bins, so we can simply truncate the double
assignBin :: SDouble m s -> Integer
assignBin sdouble = truncate $ unSDouble sdouble

-- Create a partition "parted" using assignBin
parted =
  exampleDB P.>>= \exampleDB ->
  P.return $ part assignBin exampleDB

-- A 1-differentially private query that counts the number of elements in xs.
noisyCount xs = do
  let c = count xs
  laplace @(RNat 1) c

-- Compute the noisy histogram by applying noisyCount on each part of parted
noisyHistogram_PM :: IO
  (PM
     '[ '("random_numbers.txt", 'Pos 1 ':% 1, 'Pos 0 ':% 1)]
     (Map.Map Integer Double))
noisyHistogram_PM = 
  parted P.>>= \parted ->
  let histogramPM = parallel noisyCount parted in
    P.return histogramPM

-- Here Haskell can infer the type of `histogramPM` is
--  PM '[ '("random_numbers.txt", 'Pos 1 ':% 1, 'Pos 0 ':% 1)] (Map Integer Double)
-- So the histogram query satisfies 1-differential privacy

-- We now do post-processing on the noisy histogram to get out a cdf
-- The counts are also rounded off
parallelCDF =
  noisyHistogram_PM P.>>= \histogramPM ->
  unPM histogramPM P.>>= \histogram ->
  let kvs = Map.toAscList histogram
      cdf = [List.sum (map snd (take i kvs)) | i <- [1 .. length kvs]]
      rounded_cdf = map round cdf
  in
    P.return rounded_cdf


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

{- This could compile, but the default reduction stack for equality checking of the natural numbers is exceeded

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
-- Most Frequently occurring rounded number from Laplace Samples
--------------------------------------------------

-- Generating the Laplace samples
samples :: IO (SList m (SDouble m1) '[ '("", NatSens 1 ) ])
samples = 
      let sampleLaplace = 
            createSystemRandom P.>>= \gen ->
            genContVar (Lap.laplace 5 10) gen P.>>= \r ->
            P.return r
          laplaceSamples = sequence [sampleLaplace | _ <- [1..1000]]
      in
          laplaceSamples P.>>= \x -> P.return $ SList_UNSAFE ([D_UNSAFE d | d <- x])


-------- Computing Most Frequent using Exponential composition --------
options :: [Integer]
options = [0 .. 10]

filterCount :: Integer -> L1List (SDouble m) s -> SDouble 'Diff s
filterCount option dataset = count $ sfilter (\x -> (round x) == option) dataset

exponentialMF_PM :: IO (PM '[ '("", 'Pos 1 ':% 1, 'Pos 0 ':% 1)] Integer)
exponentialMF_PM = samples P.>>= \s -> P.return $ expMech @(RNat 1) filterCount options s

exponentialMF = 
  exponentialMF_PM P.>>= \result_PM ->
  unPM result_PM P.>>= \result -> 
  P.return result


-------- Computing Most Frequent using Parallel composition --------
assignBinMF sdouble = round $ unSDouble sdouble

partedMF =
  samples P.>>= \samples ->
  P.return $ part assignBinMF samples

-- Compute noisy histogram
histogramMF_PM :: IO
  (PM '[ '("", 'Pos 1 ':% 1, 'Pos 0 ':% 1)] (Map.Map Integer Double))
histogramMF_PM = 
  partedMF P.>>= \mf_p ->
  let histogramPM = parallel noisyCount mf_p in
    P.return histogramPM

-- Post processing: find most frequently occurring number
parallelMF =
  histogramMF_PM P.>>= \hg_PM ->
  unPM hg_PM P.>>= \hg ->
  let
    kvs = Map.toAscList hg
    mf = foldl (\a -> \b -> 
      case (snd a) > (snd b) of 
        True -> a 
        False -> b) (head kvs) (tail kvs)
  in
    P.return $ fst mf


--------------------------------------------------
-- Main
--------------------------------------------------
main = do
  putStrLn "------- Running all demos -------"
  putStrLn "CDF - Sequential:"
  sequentialCDF P.>>= \cdfResult -> print cdfResult
  putStrLn "CDF - Parallel:"
  parallelCDF P.>>= \cdfResult -> print cdfResult
  putStrLn "Most frequent rounded number from Laplace samples - Exponential"
  exponentialMF P.>>= \mfResult -> print mfResult
  putStrLn "Most frequent rounded number from Laplace samples - Parallel"
  parallelMF P.>>= \mfResult -> print mfResult
