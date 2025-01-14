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

module Privacy where

import Prelude hiding (return,(>>=), sum)
import qualified Prelude as P
import Data.Proxy
import Control.Monad.Random.Class

import Sensitivity

import System.Random
import qualified System.Random.MWC as MWC
import qualified Statistics.Distribution.Laplace as Lap
import qualified Statistics.Distribution.Normal as Gaussian
import Statistics.Distribution (ContGen(genContVar))
import System.Random.MWC (createSystemRandom)

import Data.TypeLits as TL

--------------------------------------------------
-- (epsilon, delta) privacy environments and operations
--------------------------------------------------

type EDEnv = [(TL.Symbol, TL.Rat, TL.Rat)]
type Zero = (TL.Pos 0) TL.:% 1
type RNat n = (TL.Pos n) TL.:% 1
type RLit n d = (TL.Pos n) TL.:% d

type family (++++) (s1 :: EDEnv) (s2 :: EDEnv) :: EDEnv where
 '[]            ++++ s2             = s2
 s1             ++++ '[]            = s1
 ('(o,e1,d1)':s1)  ++++ ('(o,e2,d2)':s2)  = '(o, e1 TL.+ e2, d1 TL.+ d2) ': (s1 ++++ s2)
 ('(o1,e1,d1)':s1) ++++ ('(o2,e2,d2)':s2) =
   Cond (IsLT (TL.CmpSymbol o1 o2)) ('(o1,e1,d1) ': (s1 ++++ ('(o2,e2,d2)':s2)))
                                    ('(o2,e2,d2) ': (('(o1,e1,d1)':s1) ++++ s2))

type family ScalePriv (penv :: EDEnv) (n :: TL.Nat) :: EDEnv where
  ScalePriv '[] _ = '[]
  ScalePriv ('(o, e1, e2) ': s) n =
    '(o, (RNat n) TL.* e1, (RNat n) TL.* e2) ': ScalePriv s n

type family TruncateTLReal (n1 :: TL.Rat) (n2 :: TL.Nat) :: TL.Rat where
  TruncateTLReal _ 0 = Zero
  TruncateTLReal n _ = n

type family TruncatePriv (epsilon :: TL.Rat) (delta :: TL.Rat) (s :: SEnv) :: EDEnv where
  TruncatePriv _ _ '[] = '[]
  TruncatePriv epsilon delta ('(o, NatSens n2) ': s) =
    '(o, TruncateTLReal epsilon n2, TruncateTLReal delta n2) ': TruncatePriv epsilon delta s

-- type family AdvComp (k :: TL.Nat) (δ' :: TLReal) (penv :: EDEnv) :: EDEnv where
--   AdvComp _ _ '[]                            = '[]
--   AdvComp k d2 ('(o,e1,d1)':penv)  =
--     '(o,
--       Times (Times e1 (RNat 2)) (Root (Times (Times (RNat k) (RNat 2)) (Ln (Div (RNat 1) d2)))),
--       Plus d2 (Times (RNat k) d1)) ': AdvComp k d2 penv

--------------------------------------------------
-- Privacy Monad
--------------------------------------------------

newtype PM (p :: EDEnv) a = PM_UNSAFE { unPM :: IO a }

return :: a -> PM '[] a
return x = PM_UNSAFE $ P.return x

(>>=) :: PM p1 a -> (a -> PM p2 b) -> PM (p1 ++++ p2) b
xM >>= f = PM_UNSAFE $ unPM xM P.>>= (unPM . f)


--------------------------------------------------
-- Laplace noise
--------------------------------------------------

laplace :: forall eps s. (TL.KnownNat (MaxSens s), TL.KnownRat eps)
  => SDouble Diff s
  -> PM (TruncatePriv eps Zero s) Double
laplace x =
  let maxSens :: Double
      maxSens = fromInteger $ natVal (Proxy :: Proxy (MaxSens s))
      epsilon :: Double
      epsilon = fromRational $ ratVal (Proxy :: Proxy eps)
  in
    PM_UNSAFE $ do
      gen <- createSystemRandom
      r <- genContVar (Lap.laplace 0 (maxSens / epsilon)) gen
      P.return (r + unSDouble x)

laplaceL :: forall eps s. (TL.KnownNat (MaxSens s))
  => L1List (SDouble Diff) s
  -> PM (TruncatePriv eps Zero s) [Double]
laplaceL x = undefined

gaussL :: forall eps delta n s.
  (TL.KnownNat (MaxSens s), TL.KnownRat delta, TL.KnownRat eps)
  => L2List (SDouble Diff) s
  -> PM (TruncatePriv eps delta s)  [Double]
gaussL x =
    let sens = fromInteger $ natVal (Proxy :: Proxy (MaxSens s))
        dlta = fromRational $ ratVal (Proxy :: Proxy delta)
        e = fromRational $ ratVal (Proxy :: Proxy eps)
        sigma = sqrt (2 * sens * sens * log (1.25 / dlta) / (e * e))
    in
    let addNoise x = do
            gen <- createSystemRandom
            let distr = Gaussian.normalDistr 0.0 sigma
            noise <- genContVar distr gen
            P.return $ noise + (unSDouble x)
    in
        PM_UNSAFE $ mapM addNoise (unSList x)

expMech :: forall eps s1 t1 t2. (TL.KnownNat (MaxSens s1), TL.KnownRat eps) => 
  (forall s. t1 -> t2 s -> SDouble Diff s)
  -> [t1]
  -> t2 s1
  -> PM (TruncatePriv eps Zero s1) t1
expMech scoreF options d =
  let scores = [scoreF option d | option <- options]

      maxSens :: Double
      maxSens = fromInteger $ natVal (Proxy :: Proxy (MaxSens s1))

      epsilon :: Double
      epsilon = fromRational $ ratVal (Proxy :: Proxy eps)

      weights = [ exp (epsilon * (unSDouble s) / (2 * maxSens)) | s <- scores]

      weights_rationals = [toRational w | w <- weights]
      pairs = zip options weights_rationals
  in
    PM_UNSAFE $ fromList pairs
