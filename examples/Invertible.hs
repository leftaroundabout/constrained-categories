-- |
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) jsag $ hvl.no
-- 
--   A rather naïve excercise on invertible functions.
--   Tried with simple numeric expressions, this does actually
--   work in a way, but not really for nontrivial stuff. 

{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleInstances      #-} 
{-# LANGUAGE MultiParamTypeClasses  #-} 
{-# LANGUAGE FunctionalDependencies #-} 
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE ConstraintKinds        #-} 
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE TupleSections          #-} 
{-# LANGUAGE LambdaCase             #-} 
{-# LANGUAGE PackageImports         #-}




import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import Control.Arrow.Constrained

import Data.Monoid

import "vector-space" Data.VectorSpace

  
main :: IO ()
main = do
   mapM_ (\(capt, solve) -> putStrLn $ capt ++ ":   x = " ++ show solve) 
     [ ( "            x² =  2",  2 != \x -> x**2              )
     , ( "e^(x³ - 4) - 5 =  7",  7 != \x -> exp(x**3 - 4) - 5 )
     , ( " (x,1) · (1,0) =  3",  3 != \x -> (x ^++^ 1) <.> (1 ^++^ 0 
                                         :: BackResult Double (Double, Double)) )
     , ( " (7,π) · (3,x) = -2", -2 != \x -> (7 ^++^ pi) <.> (3 ^++^ x
                                         :: BackResult Double (Double, Double)) )
     ]

data a <-> b = Invertible { fwd :: a->b 
                          , rev :: b->a }

class Trivial t
instance Trivial t
type (-->) = ConstrainedCategory (->) Trivial


inv :: (a<->b) -> (b<->a)
inv (Invertible f fi) = Invertible fi f

instance Category (<->) where
  id = Invertible id id
  Invertible f fi . Invertible g gi = Invertible (f.g) (gi.fi)

instance EnhancedCat (->) (<->) where
  Invertible f _ `arr` x = f x

instance Cartesian (<->) where
  swap = Invertible swap swap
  attachUnit = Invertible attachUnit detachUnit
  detachUnit = Invertible detachUnit attachUnit
  regroup = Invertible regroup regroup'
  regroup' = Invertible regroup' regroup

instance Morphism (<->) where
  first (Invertible f fi) = Invertible (first f) (first fi)
  second (Invertible f fi) = Invertible (second f) (second fi)
  Invertible f fi *** Invertible g gi 
    = Invertible (\(b,b') -> (f b, g b')) (\(c,c') -> (fi c, gi c'))

ivfm :: (Functor f (->) (->)) => (a<->b) -> f a<->f b
ivfm (Invertible f fi) = Invertible (fmap f) (fmap fi)
 
instance Functor [] (<->) (<->) where fmap = ivfm


-- | Optionally-invertible functions.
data BackResult a b = BackResult (a <-> b)
                    | Noninvertible (a -> b)
                    | Constant b

instance Category BackResult where
  id = BackResult id
  BackResult f . BackResult g = BackResult $ f . g
  BackResult (Invertible f _) . Noninvertible g = Noninvertible $ f . g
  BackResult (Invertible f _) . Constant c = Constant $ f c
  Noninvertible f . Noninvertible g = Noninvertible $ f . g
  Noninvertible f . BackResult (Invertible g _) = Noninvertible $ f . g
  Noninvertible f . Constant c = Constant $ f c
  Constant c . _ = Constant c
instance EnhancedCat (->) BackResult where
  BackResult f `arr` x = f $ x
  Noninvertible f `arr` x = f $ x
  Constant c `arr` _ = c

instance Cartesian BackResult where
  swap = BackResult swap
  attachUnit = BackResult attachUnit
  detachUnit = BackResult detachUnit
  regroup = BackResult regroup
  regroup' = BackResult regroup'
  
instance Morphism BackResult where
  first (BackResult f) = BackResult $ first f
  first f = Noninvertible $ first (f$)
  second (BackResult f) = BackResult $ second f
  second f = Noninvertible $ second (f$)
  BackResult f *** BackResult g = BackResult $ f *** g
  Constant c *** Constant d = Constant (c,d)
  f *** g = Noninvertible $ (f$) *** (g$)
instance PreArrow BackResult where
  fst = Noninvertible fst
  snd = Noninvertible snd
  Constant c &&& Constant d = Constant (c,d)
  f &&& g = Noninvertible $ (f$) &&& (g$)
  terminal = Constant ()
instance EnhancedCat BackResult (<->) where
  arr = BackResult
instance EnhancedCat BackResult (->) where
  arr = Noninvertible
instance EnhancedCat BackResult (-->) where
  arr = Noninvertible . unconstrained
  

invertible :: (BackResult a a -> BackResult a b) -> Maybe (a <-> b)
invertible f = case f $ BackResult id of
    BackResult g -> Just g
    _            -> Nothing

invert :: (BackResult a a -> BackResult a b) -> b -> Maybe a
invert f y = fmap (($y) . inv) $ invertible f

infix 4 !=
(!=) :: a -> (BackResult a a -> BackResult a a) -> Maybe a
(!=) = flip invert

instance Functor (BackResult a) (<->) (-->) where
  fmap f = arr (BackResult f .)
           
-- | This is sort of reasonable, but not quite correct in fact:
--   combining with a constant and inverse-matching with a disagreeing
--   value should really fail, here it is just ignored.
--   Its very possible we're actually violating the monoidal-functor laws here.
instance Monoidal (BackResult a) (<->) (-->) where
  pureUnit = const (Constant ())
  fzipWith (Invertible f fi) = arr bq 
   where bq (Constant c, Constant d) = Constant $ f(c, d)
         bq (BackResult (Invertible g gi), Constant d)
                = BackResult $ Invertible ( \x -> f (g x, d) ) 
                                          ( \y -> let (c,_)=fi y in gi c )
         bq (Constant c, BackResult (Invertible h hi))
                = BackResult $ Invertible ( \x -> f (c, h x) ) 
                                          ( \y -> let (_,d)=fi y in hi d )
         bq (g, h) = Noninvertible $ \x -> f (g $ x, h $ x)



instance (AdditiveGroup b) => AdditiveGroup (BackResult a b) where
  zeroV = Constant zeroV
  Constant a ^+^ Constant b = Constant $ a^+^b
  Constant o ^+^ n = fmap (Invertible (o^+^) (^-^o)) $ n
  n ^+^ Constant o = fmap (Invertible (^+^o) (^-^o)) $ n
  a ^+^ b = Noninvertible $ \x -> (a$x) ^+^ (b$x)
  negateV x = arr (Invertible negateV negateV) . x

instance (InnerSpace b, Fractional (Scalar b)) => VectorSpace (BackResult a b) where
  type Scalar (BackResult a b) = BackResult a (Scalar b)
  
  Constant a *^ Constant b = Constant $ a*^b
  Constant o *^ v = fmap (Invertible (o*^) (^/o)) $ v
  -- n *^ Constant v = fmap (Invertible (*^v) (recip . (<.>v))) $ n
  a *^ b = Noninvertible $ \x -> (a$x) *^ (b$x)

instance (InnerSpace b, Fractional (Scalar b)) => InnerSpace (BackResult a b) where
  Constant v <.> Constant w = Constant $ v<.>w
  -- Constant v <.> w = fmap (Invertible (<.>v) ((*^v) . recip)) $ w
  -- v <.> Constant w = fmap (Invertible (w<.>) ((*^w) . recip)) $ v
  a <.> b = Noninvertible $ \x -> (a$x) <.> (b$x)
  
  
  
instance (Fractional b) => Num (BackResult a b) where
  fromInteger = Constant . fromInteger
  
  Constant a + Constant b = Constant $ a+b
  Constant o + n = fmap (Invertible (o+) (subtract o)) $ n
  n + Constant o = fmap (Invertible (+o) (subtract o)) $ n
  a + b = Noninvertible $ \x -> (a$x) + (b$x)
  
  Constant a * Constant b = Constant $ a*b
  Constant o * n = fmap (Invertible (o*) (/o)) $ n
  n * Constant o = fmap (Invertible (*o) (/o)) $ n
  a * b = Noninvertible $ \x -> (a$x) * (b$x)
  
  negate x = arr (Invertible negate negate) . x
  
  abs x = arr abs . x
  signum x = arr signum . x

instance (Fractional b) => Fractional (BackResult a b) where
  fromRational = Constant . fromRational
  recip x = arr (Invertible recip recip) . x
  
instance (Floating b, Ord b) => Floating (BackResult a b) where
  pi = Constant pi
  
  Constant b ** Constant x = Constant $ b**x
  Constant b ** x 
   | b==1       = Constant 1
   | b>0        = fmap (Invertible (b**) ((/log b) . log)) $ x
   | otherwise  = arr (0**) . x
  b ** Constant x = fmap (Invertible (**x) (**(1/x))) $ b
  
  exp x = fmap (Invertible exp log) $ x
  log x = fmap (Invertible log exp) $ x
  sin x = arr sin . x
  cos x = arr cos . x
  asin x = arr asin . x
  acos x = arr acos . x
  tan x = arr tan . x
  atan x = arr atan . x
  sinh x = fmap (Invertible sinh asinh) $ x
  asinh x = fmap (Invertible asinh sinh) $ x
  cosh x = arr cosh . x
  acosh x = arr acosh . x
  tanh x = arr tanh . x
  atanh x = arr atanh . x
  
  
  

class (AdditiveGroup a, AdditiveGroup b, AdditiveGroup s)
   => DirectSum a b s | s -> a b where
  (^++^) :: a -> b -> s

instance (AdditiveGroup a, AdditiveGroup b) => DirectSum a b (a,b) where 
  (^++^) = (,)

instance (InnerSpace a, InnerSpace b, Floating (Scalar a), Scalar a ~ (Scalar b)) 
     => DirectSum (BackResult x a) (BackResult x b) (BackResult x (a,b)) where
  a^++^b = fzipWith (Invertible id id) $ (a,b)
