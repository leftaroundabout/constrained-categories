-- |
-- Module      :  Control.Category.Hask
-- Copyright   :  (c) 2013 Justus Sagem\"uller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
-- Re-exports of all the common category-theory inspired classes from the
-- "base" package, i.e. basically endofunctors in the Hask category (with
-- functions @(->)@ as morphisms).
-- The module is thus intended to be imported @qualified as Hask@.
-- 
-- Main use case would be defining new such functors / monads etc.
-- yourself; even if you only intend to use them through the more
-- general category-agnostic interface established in this package
-- then the /instances/ should still be defined for the plain old
-- Hask-specific classes, i.e. for some
-- 
-- > data F a = ...
-- > fmapF :: (a->b) -> F a->F b@
-- >
-- > instance Hask.Functor F where
-- >   Hask.fmap = fmapF
-- 
-- An instance of 'Control.Functor.Constrained.Functor' arises automatically
-- from this, as defined generically for all @(->)@ functors in that
-- module.

module Control.Category.Hask( module Prelude
                            , module Control.Category
                            , module Control.Applicative
                            , module Control.Monad 
                            ) where
import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
