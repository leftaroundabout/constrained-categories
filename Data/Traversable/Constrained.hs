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
           ) where


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
  mapM :: (Monoidal f k l, Object l a, Object k b, Object l (f b), Object l (f (t b)))
               => a `l` f b -> s a `l` f (t b)

sequence :: ( Traversable t t k k, Monoidal f k k
            , Object k a, Object k (f a), Object k (f (t a)) )
            => t (f a) `k` f (t a)
sequence = mapM id

instance Traversable [] [] (->) (->) where
  mapM f [] = pure []
  mapM f (x:xs) = fzipWith (uncurry(:)) (f x, mapM f xs)

instance Traversable Maybe Maybe (->) (->) where
  mapM f Nothing = pure Nothing
  mapM f (Just x) = fmap Just (f x)


