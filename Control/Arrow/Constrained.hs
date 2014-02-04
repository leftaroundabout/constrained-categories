-- |
-- Module      :  Control.Arrow.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
-- Haskell's 'Arr.Arrow's, going back to [Hughes 2000], combine multiple ideas from
-- category theory:
-- 
-- * They expand upon cartesian categories, by offering ways to combine arrows between
--   simple objects to composite ones working on tuples (i.e. /products/) thereof.
-- 
-- * They constitute a \"profunctor\" interface, allowing to \"@fmap@\" both covariantly
--   over the second parameter, as well as contravariantly over the first. As in case
--   of "Control.Functor.Constrained", we wish the underlying category to fmap from
--   not to be limited to /Hask/, so 'Arrow' also has an extra parameter.
-- 
-- To facilitate these somewhat divergent needs, 'Arrow' is split up in three classes.

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TupleSections                #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE UndecidableInstances         #-}
{-# LANGUAGE TypeOperators                #-}


module Control.Arrow.Constrained (
    -- * The Arrow type classes
      Arrow, Morphism(..), PreArrow(..), EnhancedCat(..)
    -- * Alternative composition notation
    , (>>>), (<<<)
    -- * Conditionals
    , choose, ifThenElse
    -- * Misc utility
    , discard
    ) where

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

class (Category a, Curry a) => Morphism a where
  first :: (Object a b, Object a c, PairObject a b d, PairObject a c d) 
         => a b c -> a (b, d) (c, d)
  second :: (Object a b, Object a c, PairObject a d b, PairObject a d c) 
         => a b c -> a (d, b) (d, c)
  (***) :: ( Object a b, Object a c, Object a b', Object a c'
           , PairObject a b b', PairObject a c c' )
         => a b c -> a b' c' -> a (b,b') (c,c')
-- | Unlike 'first', 'second', '***' and 'arr', '&&&' has an intrinsic notion
--   of \"direction\": it is basically equivalent to precomposing the result
--   of '***' with a @b -> (b,b)@, but that is in general only available
--   for arrows that generalise ordinary functions, in their native direction.
--   (@(b,b) ->b@ is specific to semigroups.) It is for this reason the only constituent
--   class of 'Arrow' that actually has \"arrow\" in its name.
class (Morphism a) => PreArrow a where
  (&&&) :: ( Object a b, Object a c, Object a c', PairObject a c c' )
         => a b c -> a b c' -> a b (c,c')
class (Category k) => EnhancedCat a k where
  arr :: (Object k b, Object k c, Object a b, Object a c)
         => k b c -> a b c

type Arrow a k = (PreArrow a, EnhancedCat a k)

instance Morphism (->) where
  first = Arr.first
  second = Arr.second
  (***) = (Arr.***)
instance PreArrow (->) where
  (&&&) = (Arr.&&&)
instance EnhancedCat (->) (->) where
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


instance (Morphism a, o (UnitObject a)) => Morphism (ConstrainedCategory a o) where
  first = constrainedFirst first
  second = constrainedSecond second
  ConstrainedMorphism a *** ConstrainedMorphism b = ConstrainedMorphism $ a *** b
  
instance (PreArrow a, o (UnitObject a)) => PreArrow (ConstrainedCategory a o) where
  ConstrainedMorphism a &&& ConstrainedMorphism b = ConstrainedMorphism $ a &&& b
  
instance (Arrow a k, o (UnitObject a)) => EnhancedCat (ConstrainedCategory a o) k where
  arr = constrainedArr arr 




-- | Basically 'ifThenElse' with inverted argument order.
choose :: (Arrow f (->), Object f Bool, Object f a)
     => a  -- ^ \"'False'\" value
     -> a  -- ^ \"'True'\" value
     -> Bool `f` a
choose fv tv = arr $ \c -> if c then tv else fv

ifThenElse :: ( EnhancedCat f (->), Function f
              , Object f Bool, Object f a, Object f (f a a), Object f (f a (f a a))
              ) => Bool `f` (a `f` (a `f` a))
ifThenElse = arr $ \c -> arr $ \tv -> arr $ \fv -> if c then tv else fv

 


discard :: ( EnhancedCat f (->), Curry f, ObjectPair f x u, u ~ UnitObject f )
     => f x u
discard = arr snd . attachUnit
     
  

