-- |
-- Module      :  Data.Traversable.Constrained
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
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
           , sequence, mapM
           ) where


import Control.Category.Constrained
import Control.Applicative.Constrained

import Prelude hiding (
     id, (.), ($)
   , Functor(..)
   , uncurry, curry
   , mapM, mapM_, sequence
   )
import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A

import Control.Arrow.Constrained




-- forM_ :: (Monad m k, Function k, Object k a, Object k b, Object k (m b), Object k ())
--         => [a] -> a `k` m b -> m ()
-- forM_ [] f = pure ()
-- forM_ (x:xs) f = (f $ x) >> forM_ xs f
-- 
class (Category k, Category l, Functor s l l, Functor t k k) 
      => Traversable s t k l | s k l -> t, t k l -> s, s t k -> l, s t l -> k where
  traverse :: ( Monoidal f k l, Object l a, Object l (s a)
              , ObjectPair k b (t b), ObjectPair l (f b) (f (t b)) 
              ) => a `l` f b -> s a `l` f (t b)

sequence :: ( Traversable t t k k, Monoidal f k k
            , ObjectPair k a (t a), ObjectPair k (f a) (f (t a))
            , Object k (t (f a))
            ) => t (f a) `k` f (t a)
sequence = traverse id

instance (Arrow k (->), Function k, Functor [] k k) => Traversable [] [] k k where
  traverse f = arr mM
   where mM [] = constPure [] `inCategoryOf` f $ undefined
         mM (x:xs) = fzipWith (arr $ uncurry(:)) `inCategoryOf` f 
                                                $ (f $ x, mM xs)

instance (Arrow k (->), Function k, Functor Maybe k k)
            => Traversable Maybe Maybe k k where
  traverse f = arr mM 
   where mM Nothing = constPure Nothing `inCategoryOf` f $ undefined
         mM (Just x) = fmap (arr Just) . f $ x


-- | 'traverse', restricted to endofunctors.
mapM :: ( Traversable t t k k, Monoidal m k k
        , Object k a, Object k (t a), ObjectPair k b (t b), ObjectPair k (m b) (m (t b))
        ) => a `k` m b -> t a `k` m (t b)
mapM = traverse



