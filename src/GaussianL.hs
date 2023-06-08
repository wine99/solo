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

-- Our dataset is a list of random numbers between 0 and 100
-- ggg = sReadFileL "random_numbers.txt" P.>>= \db ->
    -- fmap ( \e-> print (unSDouble e) ) (unSList db)
ggg = sReadFileL "gender.txt" P.>>= \db ->
    sequence_ (map (\e-> print (unSDouble e)) (unSList db))


main = ggg

