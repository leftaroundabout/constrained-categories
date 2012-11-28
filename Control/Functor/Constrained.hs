-- |
-- Module      : Control.Functor.Constrained 
-- Copyright   : (c) Justus Sagemüller 2012
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemuej $ smail.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- 
-- Constrained functor class. For the canonical mapping @f a -> f b@ to exist, both
-- @f a@ and @f b@ need to fulfill the constraint @'CFunctorCtxt'@.

{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Functor.Constrained where

import GHC.Exts

infixl 4  <$#

class CFunctor f where
  type CFunctorCtxt f a :: Constraint
  type CFunctorCtxt f a = ()
  
  cfmap :: (CFunctorCtxt f a, CFunctorCtxt f b)
     => (a -> b) -> f a -> f b

  (<$#) :: (CFunctorCtxt f a, CFunctorCtxt f b)
     => a -> f b -> f a
  (<$#) = cfmap . const
-- instance (Functor f) => CFunctor f where
--   cfmap = fmap

infixl 4 <$>#

(<$>#) :: (CFunctor f, CFunctorCtxt f a, CFunctorCtxt f b)
     => (a -> b) -> f a -> f b
(<$>#) = cfmap