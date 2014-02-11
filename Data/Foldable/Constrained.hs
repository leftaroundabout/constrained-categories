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
           , fold
           , traverse_, mapM_, forM_, sequence_
           ) where


import Control.Category.Constrained
import Control.Functor.Constrained
import Control.Applicative.Constrained

import Prelude hiding (
     id, (.), ($)
   , Functor(..)
   , uncurry, curry
   , mapM_, sequence_
   )
import Data.Monoid

import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A

import Control.Arrow.Constrained




class (Functor t k l) => Foldable t k l where
  ffoldl :: ( Object k a, Object k b, PairObject k a b
            , Object l a, Object l (t b), PairObject l a (t b)
            ) => k (a,b) a -> l (a,t b) a
  foldMap :: ( Object k a, Object l (t a), Monoid m, Object k m, Object l m )
               => (a `k` m) -> t a `l` m

fold :: (Foldable t k k, Monoid m, Object k m, Object k (t m)) => t m `k` m
fold = foldMap id

newtype Endo' k a = Endo' { runEndo' :: k a a }
instance (Category k, Object k a) => Monoid (Endo' k a) where
  mempty = Endo' id
  mappend (Endo' f) (Endo' g) = Endo' $ f . g

newtype Monoidal_ (r :: * -> * -> *) (s :: * -> * -> *) (f :: * -> *) (u :: *) 
      = Monoidal { runMonoidal :: f u }
instance ( Monoidal f k k, Function k
         , u ~ UnitObject k, Monoid u 
         , PairObject k u u, PairObject k (f u) (f u), Object k (f u,f u)
         ) => Monoid (Monoidal_ k k f u) where
  mempty = memptyMdl
  mappend = mappendMdl

memptyMdl :: forall r s f u v . ( Monoidal f r s, Function s
                                , PairObject s u u, Monoid v
                                , u~UnitObject r, v~UnitObject s )
               => Monoidal_ r s f u
memptyMdl = Monoidal ((pureUnit :: s v (f u)) $ mempty)
mappendMdl :: forall r s f u v . ( Monoidal f r s, Function s
                                , PairObject r u u, PairObject s (f u) (f u)
                                , Object s (f u, f u), Monoid v
                                , u~UnitObject r, v~UnitObject s )
               => Monoidal_ r s f u -> Monoidal_ r s f u -> Monoidal_ r s f u
mappendMdl (Monoidal x) (Monoidal y) 
      = Monoidal (combine $ (x, y))
 where combine :: s (f u, f u) (f u)
       combine = fzipWith detachUnit



instance Foldable [] (->) (->) where
  foldMap _ [] = mempty
  foldMap f (x:xs) = f x <> foldMap f xs
  ffoldl f = uncurry $ foldl (curry f)

instance Foldable Maybe (->) (->) where
  foldMap f Nothing = mempty
  foldMap f (Just x) = f x
  ffoldl _ (i,Nothing) = i
  ffoldl f (i,Just a) = f(i,a)


instance ( Foldable f s t, Arrow s (->), Arrow t (->)
         , Functor f (ConstrainedCategory s o) (ConstrainedCategory t o) 
         ) => Foldable f (ConstrainedCategory s o) (ConstrainedCategory t o) where
  foldMap (ConstrainedMorphism f) = ConstrainedMorphism $ foldMap f
  ffoldl (ConstrainedMorphism f) = ConstrainedMorphism $ ffoldl f

-- | Despite the ridiculous-looking signature, this is in fact equivalent
--   to 'Data.Foldable.traverse_' within Hask.
traverse_ :: forall t k l o f a b uk ul .
           ( Foldable t k l, PreArrow k, PreArrow l
           , Monoidal f l l, Monoidal f k k
           , ObjectPair l (f ul) (t a), ObjectPair k (f ul) a
           , ObjectPair l ul (t a), ObjectPair l (t a) ul
           , ObjectPair k b ul, Object k (f b)
           , ObjectPair k (f ul) (f ul), ObjectPair k ul ul
           , uk ~ UnitObject k, ul ~ UnitObject l, uk ~ ul
           ) => a `k` f b -> t a `l` f ul
traverse_ f = ffoldl q . first pureUnit . swap . attachUnit
    where q :: k (f uk, a) (f uk)
          q = fzipWith detachUnit . second (fmap terminal . f)
  
-- | The distinction between 'mapM_' and 'traverse_' doesn't really make sense
--   on grounds of 'Monoidal' / 'Applicative' vs 'Monad', but is has in fact its
--   benefits to restrict this to endofunctors, to make the constraint list
--   at least somewhat shorter.
mapM_ :: forall t k o f a b u .
           ( Foldable t k k, Arrow k (->), Monoidal f k k
           , u ~ UnitObject k
           , ObjectPair k (f u) (t a), ObjectPair k (f u) a
           , ObjectPair k u (t a), ObjectPair k (t a) u
           , ObjectPair k (f u) (f u), ObjectPair k u u
           , ObjectPair k b u, Object k (f b)
           ) => a `k` f b -> t a `k` f u
mapM_ = traverse_
       


forM_ :: forall t k l f a b uk ul .
          ( Foldable t k l, Monoidal f l l, Monoidal f k k
          , Function l, Arrow k (->), Arrow l (->), ul ~ UnitObject l
          , uk ~ UnitObject k, uk ~ ul
          , ObjectPair l ul ul, ObjectPair l (f ul) (f ul)
          , ObjectPair l (f ul) (t a), ObjectPair l ul (t a)
          , ObjectPair l (t a) ul, ObjectPair l (f ul) a
          , ObjectPair k b (f b), ObjectPair k b ul
          , ObjectPair k uk uk, ObjectPair k (f uk) a, ObjectPair k (f uk) (f uk)
          ) => t a -> a `k` f b -> f uk
forM_ v f = traverse_ f $ v


sequence_ :: forall t k l m a b uk ul . 
             ( Foldable t k l, Arrow k (->), Arrow l (->)
             , uk ~ UnitObject k, ul ~ UnitObject l, uk ~ ul
             , Monoidal m k k, Monoidal m l l
             , ObjectPair k a uk, ObjectPair k (t (m a)) uk
             , ObjectPair k uk uk, ObjectPair k (m uk) (m uk), PairObject k (t (m a)) ul
             , ObjectPair l (m ul) (t (m a)), ObjectPair l ul (t (m a))
             , ObjectPair l (m uk) (t (m a)), ObjectPair l (t (m a)) ul
             , ObjectPair k (m uk) (m a)
             ) => t (m a) `l` m uk
sequence_ = traverse_ id 
--   
