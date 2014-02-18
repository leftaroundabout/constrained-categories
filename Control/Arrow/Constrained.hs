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
-- These do not even form an ordinary hierarchy, to allow categories to implement
-- only one /or/ the other aspect.
-- 
-- That's not the only significant difference of this module, compared to "Control.Arrow":
-- 
-- * Kleisli arrows are not defined here, but in "Control.Monad.Constrained".
--   Monads are really a much more specific concept than category arrows.
-- 
-- * Some extra utilities are included that don't apparently have much to
--   do with 'Arrow' at all, but require the expanded cartesian-category tools
--   and are therefore not in "Control.Category.Constrained".

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TupleSections                #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE UndecidableInstances         #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE RankNTypes                   #-}


module Control.Arrow.Constrained (
    -- * The Arrow type classes
      Arrow, Morphism(..), PreArrow(..), EnhancedCat(..)
    -- * Alternative composition notation
    , (>>>), (<<<)
    -- * Proxies for cartesian categories
    , CartesianProxy(..)
    , genericProxyCombine, genericUnit, genericAlg2
    -- * Misc utility
    -- ** Conditionals
    , choose, ifThenElse
    ) where

import Prelude hiding (id, fst, snd, (.), ($), Functor(..), Monad(..), (=<<))
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

class (Cartesian a) => Morphism a where
  first :: (Object a b, Object a c, Object a d, PairObject a b d, PairObject a c d) 
         => a b c -> a (b, d) (c, d)
  second :: (Object a b, Object a c, Object a d, PairObject a d b, PairObject a d c) 
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
-- 
--   In terms of category theory, this \"direction\" reflects the distinction
--   between /initial-/ and /terminal objects/. The latter are more interesting,
--   basically what 'UnitObject' is useful for. It gives rise to the tuple
--   selector morphisms as well.
class (Morphism a) => PreArrow a where
  (&&&) :: ( Object a b, Object a c, Object a c', PairObject a c c' )
         => a b c -> a b c' -> a b (c,c')
  terminal :: ( Object a b ) => a b (UnitObject a)
  fst :: (ObjectPair a x y, ObjectPair a x (UnitObject a)) => a (x,y) x
  fst = detachUnit . second terminal
  snd :: (ObjectPair a x y, ObjectPair a y x, ObjectPair a y (UnitObject a)) => a (x,y) y
  snd = fst . swap

class (Category k) => EnhancedCat a k where
  arr :: (Object k b, Object k c, Object a b, Object a c)
         => k b c -> a b c
instance (Category k) => EnhancedCat k k where
  arr = id

type Arrow a k = (PreArrow a, EnhancedCat a k)

instance Morphism (->) where
  first = Arr.first
  second = Arr.second
  (***) = (Arr.***)
instance PreArrow (->) where
  (&&&) = (Arr.&&&)
  terminal = const ()

constrainedArr :: (Category k, Category a, o b, o c )
  => ( k b c                        -> a b c  )
     -> k b c -> ConstrainedCategory a o b c
constrainedArr ar = constrained . ar

constrainedFirst :: ( Category a, Cartesian a, o b, o c, o d
                    , PairObject a b d, PairObject a c d )
  => ( a b c -> a (b, d) (c, d) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (b, d) (c, d)
constrainedFirst fs = ConstrainedMorphism . fs . unconstrained
  
constrainedSecond :: ( Category a, Cartesian a, o b, o c, o d
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
  terminal = ConstrainedMorphism terminal
  
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

 


genericProxyCombine :: ( HasProxy k, PreArrow k
                       , Object k a, ObjectPair k b c, Object k d )
     => k (b,c) d -> GenericProxy k a b -> GenericProxy k a c -> GenericProxy k a d
genericProxyCombine m (GenericProxy v) (GenericProxy w)
       = GenericProxy $ m . (v &&& w)
  
genericUnit :: ( PreArrow k, HasProxy k, Object k a )
        => GenericProxy k a (UnitObject k)
genericUnit = GenericProxy terminal


class (Morphism k, HasProxy k) => CartesianProxy k where
  alg2 :: ( ObjectPair k a b, Object k c
          ) => (forall q . Object k q
                 => ProxyVal k q a -> ProxyVal k q b -> ProxyVal k q c )
               -> k (a,b) c

genericAlg2 :: ( PreArrow k, u ~ UnitObject k
               , ObjectPair k a u, ObjectPair k a b, ObjectPair k b u, ObjectPair k b a
               ) => ( forall q . Object k q
                      => GenericProxy k q a -> GenericProxy k q b -> GenericProxy k q c )
               -> k (a,b) c
genericAlg2 f = runGenericProxy $ f (GenericProxy fst) (GenericProxy snd)

