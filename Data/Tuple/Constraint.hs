-- |
-- Module      : Data.Tuple.Constraint
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE TypeFamilies           #-}

module Data.Tuple.Constraint where

class (t ~ (Fst t, Snd t)) => IsTuple t where
  type Fst t
  type Snd t

instance IsTuple (a,b) where
  type Fst (a,b) = a
  type Snd (a,b) = b
