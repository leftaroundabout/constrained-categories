

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


-- | A rather naïve excercise on invertible functions.
--   Tried with simple numeric expressions, this does actually
--   work in a way, but not really for nontrivial stuff. 



import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import Control.Arrow.Constrained

import Data.Monoid

import Data.VectorSpace
import Data.Basis
import Data.MemoTrie
import Data.LinearMap

import Data.Void

import Numeric.LinearAlgebra hiding ((<.>), (<>))

type R = Double
type R² = (R, R)
type GL² = Lin R R² R²

main :: IO ()
main = do
   putStr " 45° ↺  (1,0):  "
   print $ let ϑ = pi/4 
           in  ( fromMatList [ cos ϑ, sin ϑ
                             ,-sin ϑ, cos ϑ ]  :: GL²) $ (1, 0) 


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
   
  

  
