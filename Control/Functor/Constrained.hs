-- |
-- Module      :  Control.Functor.Constrained
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) jsag $ hvl.no
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE UndecidableInstances         #-}
{-# LANGUAGE CPP                          #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses      #-}
#endif


module Control.Functor.Constrained
   ( module Control.Category.Constrained
     -- * Functors
   , Functor(..)
   , (<$>)
   , constrainedFmap
     -- * [Co]product mapping
   , SumToProduct(..)
   ) where


import Control.Category.Constrained

import Prelude hiding (id, (.), Functor(..), filter, (<$>))
import qualified Prelude

import Data.Void

import Data.Type.Coercion
import Data.Complex

import Control.Category.Discrete


class ( Category r, Category t, Object t (f (UnitObject r)) )
           => Functor f r t | f r -> t, f t -> r where
  fmap :: (Object r a, Object t (f a), Object r b, Object t (f b))
     => r a b -> t (f a) (f b)

instance (Prelude.Functor f) => Functor f (->) (->) where
  fmap = Prelude.fmap

-- | It is fairly common for functors (typically, container-like) to map 'Either'
--   to tuples in a natural way, thus \"separating the variants\".
--   This is related to 'Data.Foldable.Constrained.Foldable'
--   (with list and tuple monoids), but rather more effective.
class ( CoCartesian r, Cartesian t, Functor f r t, Object t (f (ZeroObject r)) )
           => SumToProduct f r t where
  -- | @
  --   sum2product ≡ mapEither id
  --   @
  sum2product :: ( ObjectSum r a b, ObjectPair t (f a) (f b) )
       => t (f (a+b)) (f a, f b)
  -- | @
  --   mapEither f ≡ sum2product . fmap f
  --   @
  mapEither :: ( Object r a, ObjectSum r b c
               , Object t (f a), ObjectPair t (f b) (f c) )
       => r a (b+c) -> t (f a) (f b, f c)
  filter :: ( Object r a, Object r Bool, Object t (f a) )
       => r a Bool -> t (f a) (f a)

instance SumToProduct [] (->) (->) where
  sum2product [] = ([],[])
  sum2product (Left x  : l) = (x:xs, ys) where ~(xs,ys) = sum2product l
  sum2product (Right y : l) = (xs ,y:ys) where ~(xs,ys) = sum2product l
  mapEither _ [] = ([],[])
  mapEither f (a:l) = case f a of
      Left x  -> (x:xs, ys)
      Right y -> (xs ,y:ys)
   where ~(xs,ys) = mapEither f l
  filter = Prelude.filter


infixl 4 <$>

(<$>) :: (Functor f r (->), Object r a, Object r b)
     => r a b -> f a -> f b
(<$>) = fmap

  
constrainedFmap :: (Category r, Category t, o a, o b, o (f a), o (f b)) 
      => (   r  a b ->    t  (f a) (f b)  ) 
       -> (o⊢r) a b -> (o⊢t) (f a) (f b)
constrainedFmap q = constrained . q . unconstrained

instance (Functor [] k k, o [UnitObject k]) => Functor [] (o⊢k) (o⊢k) where
  fmap (ConstrainedMorphism f) = ConstrainedMorphism $ fmap f

instance (o (), o [()], o Void, o [Void]) => SumToProduct [] (o⊢(->)) (o⊢(->)) where
  sum2product = ConstrainedMorphism sum2product
  mapEither (ConstrainedMorphism f) = ConstrainedMorphism $ mapEither f
  filter (ConstrainedMorphism f) = ConstrainedMorphism $ filter f

  
instance Functor [] Coercion Coercion where fmap Coercion = Coercion
instance Functor Maybe Coercion Coercion where fmap Coercion = Coercion
instance Functor (Either a) Coercion Coercion where fmap Coercion = Coercion
instance Functor ((->) a) Coercion Coercion where fmap Coercion = Coercion
instance Functor ((,) a) Coercion Coercion where fmap Coercion = Coercion
instance Functor IO Coercion Coercion where fmap Coercion = Coercion
instance Functor Complex Coercion Coercion where fmap Coercion = Coercion

instance Functor [] Discrete Discrete where fmap Refl = Refl
instance Functor Maybe Discrete Discrete where fmap Refl = Refl
instance Functor (Either a) Discrete Discrete where fmap Refl = Refl
instance Functor ((->) a) Discrete Discrete where fmap Refl = Refl
instance Functor ((,) a) Discrete Discrete where fmap Refl = Refl
instance Functor IO Discrete Discrete where fmap Refl = Refl
instance Functor Complex Discrete Discrete where fmap Refl = Refl

