-- |
-- Module      :  Control.Category.Constrained.Prelude
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
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
                      , Functor(..), Monad(..), (=<<), filter
                      , mapM, mapM_, sequence, sequence_ )

import Control.Category.Constrained hiding (ConstrainedMorphism)
import Control.Functor.Constrained
import Control.Applicative.Constrained
import Control.Monad.Constrained hiding 
         (MonadPlus(..), MonadZero(..), (>=>), (<=<), guard, forever, void)
import Control.Arrow.Constrained (Function, ($), ifThenElse, fst, snd, const)

