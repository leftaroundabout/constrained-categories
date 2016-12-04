-- |
-- Module      :  Control.Category.Compound.Prelude
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemueller $ geo.uni-koeln.de
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}

module Control.Category.Compound.Prelude ( 
          -- * The constrained-categories facilities
           module Control.Category.Compound
         , module Control.Functor.Compound
         , module Control.Applicative.Compound
         , module Control.Monad.Compound
         , module Control.Arrow.Compound
          -- * The compatible part of the standard Prelude 
         , module Prelude
         ) where

import Prelude hiding ( id, const, fst, snd, (.), ($), curry, uncurry
                      , Functor(..), (<$>), Applicative(..), (<*>), Monad(..), (=<<), filter
                      , mapM, mapM_, sequence, sequence_
                      , Foldable, foldMap, fold, traverse_, concatMap
                      , Traversable, traverse )

import Control.Category.Compound hiding (CompoundMorphism)
import Control.Functor.Compound
import Control.Applicative.Compound
import Control.Monad.Compound hiding 
         (MonadPlus(..), MonadZero(..), (>=>), (<=<), guard, forever, void)
import Control.Arrow.Compound (Function, ($), ifThenElse, fst, snd, const)
import Control.Applicative.Compound

import Data.Foldable.Compound (Foldable, foldMap, fold, traverse_, concatMap)
import Data.Traversable.Compound (Traversable, traverse)

