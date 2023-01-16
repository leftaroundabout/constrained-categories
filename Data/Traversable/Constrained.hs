-- |
-- Module      :  Data.Traversable.Constrained
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) jsag $ hvl.no
-- 
{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE CPP                          #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses      #-}
#endif
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TupleSections                #-}


module Data.Traversable.Constrained
           ( Traversable(..)
           , forM
           , EndoTraversable
           , haskTraverse
           ) where


import Control.Category.Constrained
import Control.Applicative.Constrained

import Prelude hiding (
     id, const, (.), ($)
   , Functor(..)
   , uncurry, curry
   , mapM, mapM_, sequence
   , Traversable(..)
   , Applicative(..)
   )
import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A

import qualified Data.Traversable as Hask

import Control.Arrow.Constrained

import Data.Monoid

import GHC.Exts (Constraint)



class (Category k, Category l, Functor s l l, Functor t k k) 
      => Traversable s t k l | s k l -> t, t k l -> s, s t k -> l, s t l -> k where
  type TraversalObject k t b :: Constraint
  type TraversalObject k t b = ()
  
  traverse :: ( Monoidal f k l, Object l a, Object l (s a)
              , ObjectPair k b (t b), ObjectPair l (f b) (f (t b)) 
              , TraversalObject k t b
              ) => a `l` f b -> s a `l` f (t b)
  
  -- | 'traverse', restricted to endofunctors. May be more efficient to implement.
  mapM :: ( k~l, s~t, Applicative m k k
          , Object k a, Object k (t a), ObjectPair k b (t b), ObjectPair k (m b) (m (t b))
          , TraversalObject k t b
          ) => a `k` m b -> t a `k` m (t b)
  mapM = traverse


  sequence :: ( k~l, s~t, Monoidal f k k
              , ObjectPair k a (t a), ObjectPair k (f a) (f (t a))
              , Object k (t (f a))
              , TraversalObject k t a
              ) => t (f a) `k` f (t a)
  sequence = traverse id

instance (Arrow k (->), WellPointed k, Function k, Functor [] k k) 
             => Traversable [] [] k k where
  type TraversalObject k [] b = PointObject k [b]
  traverse f = arr mM
   where mM [] = constPure [] `inCategoryOf` f $ mempty
         mM (x:xs) = fzipWith (arr $ uncurry(:)) `inCategoryOf` f 
                                                $ (f $ x, mM xs)

instance (Arrow k (->), WellPointed k, Function k, Functor Maybe k k)
            => Traversable Maybe Maybe k k where
  type TraversalObject k Maybe b = PointObject k (Maybe b)
  traverse f = arr mM 
   where mM Nothing = constPure Nothing `inCategoryOf` f $ mempty
         mM (Just x) = fmap (arr Just) . f $ x

-- | Flipped version of 'traverse' / 'mapM'.
forM :: forall s t k m a b l . 
        ( Traversable s t k l, Monoidal m k l, Function l
        , Object k b, Object k (t b), ObjectPair k b (t b)
        , Object l a, Object l (s a), ObjectPair l (m b) (m (t b))
        , TraversalObject k t b
        ) => s a -> (a `l` m b) -> m (t b)
forM v f = traverse f $ v


-- | A traversable that can be used with 'mapM'.
type EndoTraversable t k = Traversable t t k k


newtype HaskWrapApplicative f x = HaskWrapApplicative { getHWAppl :: f x }

instance (Functor f (->) (->)) => Hask.Functor (HaskWrapApplicative f) where
  fmap f (HaskWrapApplicative c) = HaskWrapApplicative $ fmap f c
instance (Monoidal f (->) (->)) => Hask.Applicative (HaskWrapApplicative f) where
  pure x = HaskWrapApplicative $ (fmap (const x) . pureUnit) ()
  HaskWrapApplicative fs <*> HaskWrapApplicative xs
       = HaskWrapApplicative $ fzipWith (uncurry ($)) (fs, xs)

-- | Use this if you want to “derive” a constrained traversable instance from a
--   given 'Hask.Traversable' one. (You will not be able to simply set
--   @'traverse' = 'Hask.traverse'@, because the latter requires the Prelude version
--   of 'Hask.Applicative', which can not be inferred from the constrained `Monoidal`.
haskTraverse :: (Hask.Traversable t, Monoidal f (->) (->))
      => (a -> f b) -> t a -> f (t b)
haskTraverse f = getHWAppl . Hask.traverse (HaskWrapApplicative . f) 

