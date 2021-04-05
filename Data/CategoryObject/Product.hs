-- |
-- Module      : Data.CategoryObject.Product
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE FlexibleInstances      #-}

module Data.CategoryObject.Product where
    
import Data.Semigroup
import Data.Monoid hiding ((<>))

data ProductCatObj a b = ProductCatObj a b

type family LFactor t where
  LFactor (ProductCatObj l r) = l
  LFactor (a,b) = (LFactor a, LFactor b)

type family RFactor t where
  RFactor (ProductCatObj l r) = r
  RFactor (a,b) = (RFactor a, RFactor b)

instance (Semigroup a, Semigroup b) => Semigroup (ProductCatObj a b) where
  ProductCatObj x y <> ProductCatObj w z = ProductCatObj (x<>w) (y<>z)

instance (Monoid a, Monoid b) => Monoid (ProductCatObj a b) where
  mempty = ProductCatObj mempty mempty
  mappend (ProductCatObj x y) (ProductCatObj w z)
       = ProductCatObj (mappend x w) (mappend y z)
