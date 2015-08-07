-- |
-- Module      :  Data.Traversable.Constrained
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemueller $ geo.uni-koeln.de
-- 
{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TupleSections                #-}


module Data.Traversable.Constrained
           ( module Control.Applicative.Constrained 
           , Traversable(..)
           , sequence, forM
           , EndoTraversable
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

import Control.Arrow.Constrained

import Data.Monoid




class (Category k, Category l, Functor s l l, Functor t k k) 
      => Traversable s t k l | s k l -> t, t k l -> s, s t k -> l, s t l -> k where
  traverse :: ( Monoidal f k l, Object l a, Object l (s a)
              , ObjectPair k b (t b), ObjectPair l (f b) (f (t b)) 
              , ObjectPoint k (t b)
              ) => a `l` f b -> s a `l` f (t b)
  
  -- | 'traverse', restricted to endofunctors. May be more efficient to implement.
  mapM :: ( k~l, s~t, Applicative m k k
          , Object k a, Object k (t a), ObjectPair k b (t b), ObjectPair k (m b) (m (t b))
          , ObjectPoint k (t b)
          ) => a `k` m b -> t a `k` m (t b)
  mapM = traverse


sequence :: ( Traversable t t k k, Monoidal f k k
            , ObjectPair k a (t a), ObjectPair k (f a) (f (t a))
            , Object k (t (f a))
            , ObjectPoint k (t a)
            ) => t (f a) `k` f (t a)
sequence = traverse id

instance (Arrow k (->), WellPointed k, Function k, Functor [] k k) 
             => Traversable [] [] k k where
  traverse f = arr mM
   where mM [] = constPure [] `inCategoryOf` f $ mempty
         mM (x:xs) = fzipWith (arr $ uncurry(:)) `inCategoryOf` f 
                                                $ (f $ x, mM xs)

instance (Arrow k (->), WellPointed k, Function k, Functor Maybe k k)
            => Traversable Maybe Maybe k k where
  traverse f = arr mM 
   where mM Nothing = constPure Nothing `inCategoryOf` f $ mempty
         mM (Just x) = fmap (arr Just) . f $ x

-- data Stupid a = Stupid a
-- instance Functor Stupid (ConstrainedCategory (->) Num) (->) where
--   fmap (Stupid (ConstrainedMorphism f)) (Stupid a) = Stupid (f a)
-- 

-- | Flipped version of 'traverse' / 'mapM'.
forM :: forall s t k m a b l . 
        ( Traversable s t k l, Monoidal m k l, Function l
        , Object k b, Object k (t b), ObjectPair k b (t b)
        , Object l a, Object l (s a), ObjectPair l (m b) (m (t b))
        , ObjectPoint k (t b)
        ) => s a -> (a `l` m b) -> m (t b)
forM v f = traverse f $ v


-- | A traversable that can be used with 'mapM'.
type EndoTraversable t k = Traversable t t k k


