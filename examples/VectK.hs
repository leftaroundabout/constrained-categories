
-- |
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
--   Simple implementation of Vect /k/, the category of vector spaces
--   over the field /k/, with linear maps as morphisms.


{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleInstances      #-} 
{-# LANGUAGE UndecidableInstances   #-} 
{-# LANGUAGE MultiParamTypeClasses  #-} 
{-# LANGUAGE FunctionalDependencies #-} 
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE ConstraintKinds        #-} 
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE TupleSections          #-} 
{-# LANGUAGE GADTs                  #-} 
{-# LANGUAGE ScopedTypeVariables    #-} 
{-# LANGUAGE PackageImports         #-}




import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import Control.Arrow.Constrained

import Data.Monoid

import "vector-space" Data.VectorSpace
import Data.Basis
import Data.MemoTrie
import Data.LinearMap

import Data.Void

import "hmatrix" Numeric.LinearAlgebra hiding ((<.>), (<>))

type ℝ = Double
type ℝ² = (ℝ, ℝ)
type ℝ⁴ = (ℝ², ℝ²)
type GLℝ² = Lin ℝ ℝ² ℝ²

main :: IO ()
main = do
   putStr "45° ↺  (1,0):  "
   print $ let ϑ = pi/4 
           in  ( fromMatList [ cos ϑ, sin ϑ
                             ,-sin ϑ, cos ϑ ]  :: GLℝ²) $ (1, 0) 
   putStr "\\v → v + v  :  "
   print . asMatrix $ ( alg (\v -> v ^+^ v )
                                       :: GLℝ² )
   putStr "\\v → v ⊕ v  :  "
   print . asMatrix $ ( alg (\v -> v ^++^ v )
                                       :: Lin ℝ ℝ² ℝ⁴ )
   putStr "\\v w → v + w:  "
   print . asMatrix $ ( alg2 (\v w -> v ^+^ w )
                                       :: Lin ℝ ℝ⁴ ℝ² )


type CountablySpanned v = (HasBasis v, HasTrie (Basis v))
type FinitelySpanned v = (CountablySpanned v, InnerSpace v, Enum (Basis v), Bounded (Basis v))

data Lin k u v where
  Lin :: (CountablySpanned u, VectorSpace v, Scalar u ~ k, Scalar v ~ k) 
          => u:-*v -> Lin k u v

instance (CountablySpanned u, VectorSpace v, Scalar u ~ k, Scalar v ~ k)
                                             => AdditiveGroup (Lin k u v) where
  zeroV = Lin zeroV
  Lin f ^+^ Lin g = Lin $ f ^+^ g
  negateV (Lin f) = Lin $ negateV f
instance (AdditiveGroup (Lin k u v)) => VectorSpace (Lin k u v) where
  type Scalar (Lin k u v) = k
  a *^ Lin f = Lin $ a *^ f
instance ( InnerSpace u, FinitelySpanned u, Scalar u ~ k 
         , CountablySpanned v, Scalar v ~ k
         )      => HasBasis (Lin k u v) where
  type Basis (Lin k u v) = (Basis v, Basis u)
  basisValue (i,j) = Lin . linear $ (basisValue i ^*) . (basisValue j <.>)
  decompose (Lin f) = [ ((i,j), a) 
                      | j<-[minBound .. maxBound]
                      , (i,a) <- decompose (f `atBasis` j) ]
  decompose' (Lin f) (i,j) = decompose' (f `atBasis` j) i
  

instance Category (Lin k) where
  type Object (Lin k) v = (CountablySpanned v, Scalar v ~ k)
  id = Lin idL
  Lin f . Lin g = Lin $ f *.* g

instance Function (Lin k) where
  Lin f $ v = lapply f v

instance Curry (Lin k) where
  type UnitObject (Lin k) = ZeroDim k
  type PairObject (Lin k) u v = (CountablySpanned (u,v), Scalar (u,v) ~ k)
  type MorphObject (Lin k) u v = (FinitelySpanned u)
  uncurry f = Lin . linear $ \(u,v) -> (f$u)$v
  curry f = Lin . linear $ \u -> Lin . linear $ \v -> f$(u,v)
  swap = Lin . linear $ \(a,b) -> (b,a)
  attachUnit = Lin . linear $ \a -> (a, Origin)
  detachUnit = Lin . linear $ \(a, Origin) -> a
  regroup = Lin . linear $ \(a,(b,c)) -> ((a,b),c)

instance Morphism (Lin k) where
  first (Lin l) = Lin $ firstL l
  second l = Lin . linear $ \(u,v) -> (u, l $ v)
  m *** n = Lin . linear $ (m$) *** (n$)
instance PreArrow (Lin k) where
  m &&& n = Lin . linear $ (m$) &&& (n$)
  terminal = Lin . linear $ const Origin
  

instance HasProxy (Lin k) where
  alg = genericAlg
  ($~) = genericProxyMap

instance CartesianProxy (Lin k) where
  alg2 = genericAlg2

instance ( HasProxy (Lin k), ProxyVal (Lin k) a b ~ GenericProxy (Lin k) a b
         , Object (Lin k) a, Object (Lin k) b
         ) => AdditiveGroup (GenericProxy (Lin k) a b) where
  zeroV = Lin (linear $ \Origin -> zeroV) $~ genericUnit
  negateV v = Lin (linear negateV) $~ v
  (^+^) = genericProxyCombine . Lin . linear $ uncurry (^+^)

instance ( HasProxy (Lin k), ProxyVal (Lin k) a b ~ GenericProxy (Lin k) a b
         , Object (Lin k) a, Object (Lin k) b
         ) => VectorSpace (GenericProxy (Lin k) a b) where
  type Scalar (GenericProxy (Lin k) a b) = k
  x*^v = Lin (linear $ (x*^)) $~ v




asMatrix :: (FinitelySpanned u, FinitelySpanned v, Element k)
      => Lin k u v -> Matrix k
asMatrix (Lin f) 
  = fromLists [ map snd . decompose $ atBasis f i | i<-[minBound .. maxBound] ]



fromMatList :: forall u v k 
       . ( FinitelySpanned u, FinitelySpanned v
         , Numeric.LinearAlgebra.Product k, Scalar u ~ k, Scalar v ~ k )
      => [k] -> Lin k u v
fromMatList = fromMatrix . (dv><du)
 where dv = fromEnum (maxBound :: Basis v) - fromEnum (minBound :: Basis v) + 1
       du = fromEnum (maxBound :: Basis u) - fromEnum (minBound :: Basis u) + 1
       fromMatrix m = Lin . linear $ 
             \u -> let v =  m `mXv` (fromList . map snd $ decompose u)
                   in recompose . zip [minBound .. maxBound] $ toList v


  


class (AdditiveGroup a, AdditiveGroup b, AdditiveGroup s)
   => DirectSum a b s | s -> a b where
  (^++^) :: a -> b -> s

instance (AdditiveGroup a, AdditiveGroup b) => DirectSum a b (a,b) where 
  (^++^) = (,)

instance ( CountablySpanned a, CountablySpanned b, CountablySpanned c
         , Scalar a ~ k, Scalar b ~ k, Scalar c ~ k )
   => DirectSum ( GenericProxy (Lin k) a b )
                ( GenericProxy (Lin k) a c )
                ( GenericProxy (Lin k) a (b,c) ) where
  (^++^) = genericProxyCombine . Lin . linear $ uncurry (^++^)
  




data ZeroDim k = Origin
instance AdditiveGroup (ZeroDim k) where 
  zeroV = Origin
  (^+^) = (<>)
  negateV = id
instance VectorSpace (ZeroDim k) where
  type Scalar (ZeroDim k) = k
  _ *^ Origin = Origin
instance HasBasis (ZeroDim k) where
  type Basis (ZeroDim k) = Void
  basisValue = absurd
  decompose Origin = []
  decompose' Origin = absurd
instance Monoid (ZeroDim k) where
  mempty = Origin
  mappend Origin Origin = Origin

instance Enum Void where
  fromEnum = absurd
  toEnum n = ( toEnum 1 :: () ) `seq` undefined

instance (Enum a, Bounded a, Enum b, Bounded b)
    => Enum (Either a b) where
  fromEnum (Left a) = fromEnum a
  fromEnum e@(Right b) = fromEnum b + fromEnum ma + 1
   where ma = maxBound
         _ = Left ma `asTypeOf` e
  toEnum n = result
   where result
           | n < ca     = Left $ toEnum n
           | otherwise  = Right . toEnum $ n - ca
         ma = maxBound
         _ = Left ma `asTypeOf` result
         ca = fromEnum ma + 1

instance (Bounded a, Bounded b) => Bounded (Either a b) where
  minBound = Left minBound
  maxBound = Right maxBound
   
  

  
