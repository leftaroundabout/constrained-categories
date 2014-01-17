-- |
-- Module      :  Data.Foldable.Constrained
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE KindSignatures               #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TupleSections                #-}


module Data.Foldable.Constrained
           ( module Control.Category.Constrained 
           , Foldable(..)
           ) where


import Control.Category.Constrained
import Control.Functor.Constrained
import Control.Applicative.Constrained

import Prelude hiding (
     id, (.), ($)
   , Functor(..)
   , uncurry, curry
   , mapM_
   )
import Data.Monoid

import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A

import Control.Arrow.Constrained




-- forM_ :: (Monad m k, Function k, Object k a, Object k b, Object k (m b), Object k ())
--         => [a] -> a `k` m b -> m ()
-- forM_ [] f = pure ()
-- forM_ (x:xs) f = (f $ x) >> forM_ xs f
-- 
class (Functor t k l) => Foldable t k l where
  foldMap :: ( Object k a, Object l (t a), Monoid m, Object k m, Object l m )
               => (a `k` m) -> t a `l` m
  mapM_ :: ( Monoidal f l l, Monoidal f k k, Monoid u, UnitObject k u
           , Object k a, Object k (f u), Object l (t a), Object l (f u) )
           => a `k` f u -> t a `l` f u

fold :: (Foldable t k k, Monoid m, Object k m, Object k (t m)) => t m `k` m
fold = foldMap id

newtype Endo' k a = Endo' { runEndo' :: k a a }
instance (Category k, Object k a) => Monoid (Endo' k a) where
  mempty = Endo' id
  mappend (Endo' f) (Endo' g) = Endo' $ f . g

-- newtype Monoidal_ (r :: * -> * -> *) (s :: * -> * -> *) (f :: * -> *) (u :: *) 
--       = Monoidal { runMonoidal :: f u }
-- instance ( Monoidal f k k, Function k, Object k u, UnitObject k u 
--          , PairObject k u u, Monoid u )
--                   => Monoid (Monoidal_ k f u) where
--   mempty = memptyMdl 
--   mappend (Monoidal x) (Monoidal y) = Monoidal (fzipWith detachUnit $ (x, y))
-- 
-- memptyMdl :: forall k f u . ( Monoidal f k k, Function k, Object k u, UnitObject k u 
--                             , PairObject k u u, Monoid u )
-- memptyMdl = Monoidal (pure $ mempty)
-- 


instance Foldable [] (->) (->) where
  foldMap f [] = mempty
  foldMap f (x:xs) = f x <> foldMap f xs
  mapM_ _ [] = pure mempty
  mapM_ f (x:xs) = fzipWith (uncurry mappend) (f x, mapM_ f xs)

instance Foldable Maybe (->) (->) where
  foldMap f Nothing = mempty
  foldMap f (Just x) = f x
  mapM_ _ Nothing = pure mempty
  mapM_ f (Just x) = f x


