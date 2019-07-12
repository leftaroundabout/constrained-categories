-- |
-- Module      :  Control.Category.Constrained.Prelude
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) jsag $ hvl.no
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}

module Control.Category.Constrained.Prelude ( 
          -- * The constrained-categories facilities
           module Control.Category.Constrained
         , module Control.Functor.Constrained
         , module Control.Applicative.Constrained
         , module Control.Monad.Constrained
         , module Control.Arrow.Constrained
          -- * The compatible part of the standard Prelude 
         , module Prelude
         ) where

import Prelude hiding ( id, const, fst, snd, (.), ($), curry, uncurry
                      , Functor(..), (<$>), Applicative(..), (<*>), Monad(..), (=<<), filter
                      , mapM, mapM_, sequence, sequence_
                      , Foldable, foldMap, fold, traverse_, concatMap
                      , Traversable, traverse )

import Control.Category.Constrained hiding (ConstrainedMorphism)
import Control.Functor.Constrained
import Control.Applicative.Constrained
import Control.Monad.Constrained hiding 
         (MonadPlus(..), MonadZero(..), (>=>), (<=<), guard, forever, void)
import Control.Arrow.Constrained (Function, ($), ifThenElse, fst, snd, const)
import Control.Applicative.Constrained

import Data.Foldable.Constrained (Foldable, foldMap, fold, traverse_, concatMap)
import Data.Traversable.Constrained (Traversable, traverse)

