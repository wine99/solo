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
   #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use >=>" #-}

module GaussianL where

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

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

assignBin :: SDouble m s -> Integer
assignBin sdouble = if (unSDouble sdouble) > 50.0 then 1 else 0

parted exampleDB =
  exampleDB P.>>= \exampleDB ->
  P.return $ part @Integer @L2 assignBin exampleDB

getValue :: forall f e. Maybe (L2List f e) -> SDouble Diff e
getValue Nothing = D_UNSAFE 0.0
getValue (Just i) = count i

ggg = let res = parted (sReadFileL "random_numbers.txt") in
          res P.>>= \pa ->
              let l2list = getValue(  Map.lookup 0 (unPartition pa)) `scons` (getValue(  Map.lookup 1 (unPartition pa)) `scons` emptySList @L2) in
                 P.return $ gaussL @('Pos 1 ':% 1) @('Pos 1 ':% 10000) l2list

main = do
    ggg P.>>= \e -> (unPM e) P.>>= \e->print e

