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

class IsProduct t where
  type LFactor t
  type RFactor t

data ProductCatObj a b = ProductCatObj a b

instance IsProduct (ProductCatObj l r) where
  type LFactor (ProductCatObj l r) = l
  type RFactor (ProductCatObj l r) = r

instance (IsProduct a, IsProduct b) => IsProduct (a,b) where
  type LFactor (a,b) = (LFactor a, LFactor b)
  type RFactor (a,b) = (RFactor a, RFactor b)

instance (Semigroup a, Semigroup b) => Semigroup (ProductCatObj a b) where
  ProductCatObj x y <> ProductCatObj w z = ProductCatObj (x<>w) (y<>z)

instance (Monoid a, Monoid b) => Monoid (ProductCatObj a b) where
  mempty = ProductCatObj mempty mempty
  mappend (ProductCatObj x y) (ProductCatObj w z)
       = ProductCatObj (mappend x w) (mappend y z)
