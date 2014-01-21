-- |
-- Module      :  Control.Arrow.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TupleSections                #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE UndecidableInstances         #-}


module Control.Arrow.Constrained where

import Prelude hiding (id, (.), ($), Functor(..), Monad(..), (=<<))
import Control.Category.Constrained
import qualified Control.Category.Hask as Hask

import qualified Control.Arrow as Arr

infixr 1 >>>, <<<
infixr 3 &&&, ***

(>>>) :: (Category k, Object k a, Object k b, Object k c) 
             => k a b -> k b c -> k a c
(>>>) = flip (.)
(<<<) :: (Category k, Object k a, Object k b, Object k c) 
             => k b c -> k a b -> k a c
(<<<) = (.)

class (Category a, Curry a) => PreArrow a where
  first :: (Object a b, Object a c, PairObject a b d, PairObject a c d) 
         => a b c -> a (b, d) (c, d)
  second :: (Object a b, Object a c, PairObject a d b, PairObject a d c) 
         => a b c -> a (d, b) (d, c)
  (&&&) :: ( Object a b, Object a c, Object a c', PairObject a c c' )
         => a b c -> a b c' -> a b (c,c')
  (***) :: ( Object a b, Object a c, Object a b', Object a c'
           , PairObject a b b', PairObject a c c' )
         => a b c -> a b' c' -> a (b,b') (c,c')
class (PreArrow a, Category k) => Arrow a k where
  arr :: (Object k b, Object k c, Object a b, Object a c)
         => k b c -> a b c

instance PreArrow (->) where
  first = Arr.first
  second = Arr.second
  (&&&) = (Arr.&&&)
  (***) = (Arr.***)
instance Arrow (->) (->) where
  arr = Arr.arr

constrainedArr :: (Category k, Category a, o b, o c )
  => ( k b c                        -> a b c  )
     -> k b c -> ConstrainedCategory a o b c
constrainedArr ar = constrained . ar

constrainedFirst :: ( Category a, Curry a, o b, o c, o d
                    , PairObject a b d, PairObject a c d )
  => ( a b c -> a (b, d) (c, d) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (b, d) (c, d)
constrainedFirst fs = ConstrainedMorphism . fs . unconstrained
  
constrainedSecond :: ( Category a, Curry a, o b, o c, o d
                    , PairObject a d b, PairObject a d c )
  => ( a b c -> a (d, b) (d, c) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (d, b) (d, c)
constrainedSecond sn = ConstrainedMorphism . sn . unconstrained


instance (PreArrow a, o (UnitObject a)) => PreArrow (ConstrainedCategory a o) where
  first = constrainedFirst first
  second = constrainedSecond second
  ConstrainedMorphism a &&& ConstrainedMorphism b = ConstrainedMorphism $ a &&& b
  ConstrainedMorphism a *** ConstrainedMorphism b = ConstrainedMorphism $ a *** b
  
instance (Arrow a k, o (UnitObject a)) => Arrow (ConstrainedCategory a o) k where
  arr = constrainedArr arr 

 
  

