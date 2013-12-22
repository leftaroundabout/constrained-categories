-- |
-- Module      :  Control.Arrow.Constrained
-- Copyright   :  (c) 2013 Justus Sagem\"uller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}

module Control.Arrow.Constrained where

import Prelude ()
import Control.Category.Constrained
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import qualified Control.Arrow as Arr

class (Category a, Category k, Curry a) => Arrow a k where
  arr :: (Object k b, Object k c, Object a b, Object a c)
         => k b c -> a b c
  first :: (Object a b, Object a c, PairObject a b d, PairObject a c d) 
         => a b c -> a (b, d) (c, d)

instance (Category a, Curry a, Arr.Arrow a) => Arrow a (->) where
  arr = Arr.arr
  first = Arr.first

constrainedArr :: (Category k, Category a, o b, o c )
  => ( k b c                        -> a b c                       )
     -> ConstrainedCategory k o b c -> ConstrainedCategory a o b c
constrainedArr ar = constrained . ar . unconstrained

constrainedFirst :: ( Category a, Curry a, o b, o c, o d
                    , PairObject a b d, PairObject a c d )
  => ( a b c -> a (b, d) (c, d) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (b, d) (c, d)
constrainedFirst fs = ConstrainedMorphism . fs . unconstrained
  
  

