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
-- Constrained functor class. For the canonical mapping @f a -> f b@ to exists, both
-- @f a@ and @f b@ need to fulfill the constraint @'CFunctorCtxt'@.

{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Functor.Constrained where

import GHC.Exts

class CFunctor f where
  type CFunctorCtxt f a :: Constraint
--   type CFunctorCtxt f a = ()
  cfmap :: (CFunctorCtxt f a, CFunctorCtxt f b)
     => (a -> b) -> f a -> f b

-- instance (Functor f) => CFunctor f where
--   cfmap = fmap