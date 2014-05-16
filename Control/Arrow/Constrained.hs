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
{-# LANGUAGE AllowAmbiguousTypes          #-}


module Control.Arrow.Constrained (
    -- * The Arrow type classes
      Arrow, Morphism(..), PreArrow(..), WellPointed(..),ObjectPoint, EnhancedCat(..)
    -- * Function-like categories
    , Function, ($)
    -- * Alternative composition notation
    , (>>>), (<<<)
    -- * Proxies for cartesian categories
    , CartesianProxy(..)
    , genericProxyCombine, genericUnit, genericAlg1to2, genericAlg2to1, genericAlg2to2
    , PointProxy(..), genericPoint
    -- * Misc utility
    -- ** Conditionals
    , choose, ifThenElse
    ) where

import Prelude hiding (id, const, fst, snd, (.), ($), Functor(..), Monad(..), (=<<))
import Control.Category.Constrained
import qualified Control.Category.Hask as Hask

import GHC.Exts (Constraint)
import Data.Tagged

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
  first :: ( ObjectPair a b d, ObjectPair a c d )
         => a b c -> a (b, d) (c, d)
  first = (***id)
  second :: ( ObjectPair a d b, ObjectPair a d c )
         => a b c -> a (d, b) (d, c)
  second = (id***)
  (***) :: ( ObjectPair a b b', ObjectPair a c c' )
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
  (&&&) :: ( Object a b, ObjectPair a c c' )
         => a b c -> a b c' -> a b (c,c')
  terminal :: ( Object a b ) => a b (UnitObject a)
  fst :: (ObjectPair a x y) => a (x,y) x
  snd :: (ObjectPair a x y) => a (x,y) y


class (PreArrow a, ObjectPoint a (UnitObject a)) => WellPointed a where
  type PointObject a x :: Constraint
  type PointObject a x = ()
  globalElement :: (ObjectPoint a x) => x -> a (UnitObject a) x
  unit :: CatTagged a (UnitObject a)
  const :: (Object a b, ObjectPoint a x) 
            => x -> a b x
  const x = globalElement x . terminal

type ObjectPoint k a = (Object k a, PointObject k a)

value :: forall f x . (WellPointed f, Function f, Object f x)
           => f (UnitObject f) x -> x
value f = f $ untag(unit :: Tagged (f (UnitObject f) (UnitObject f)) (UnitObject f))


class (Category k) => EnhancedCat a k where
  arr :: (Object k b, Object k c, Object a b, Object a c)
         => k b c -> a b c
instance (Category k) => EnhancedCat k k where
  arr = id


-- | Many categories have as morphisms essentially /functions with extra properties/:
--   group homomorphisms, linear maps, continuous functions...
-- 
--   It makes sense to generalise the notion of function application to these
--   morphisms; we can't do that for the simple juxtaposition writing @f x@,
--   but it is possible for the function-application operator @$@.
-- 
--   This is particularly useful for 'ConstrainedCategory' versions of Hask,
--   where after all the morphisms are /nothing but functions/.
type Function f = EnhancedCat (->) f

infixr 0 $
($) :: (Function f, Object f a, Object f b) => f a b -> a -> b
f $ x = arr f x

instance (Function f) => EnhancedCat (->) (ConstrainedCategory f o) where
  arr (ConstrainedMorphism q) = arr q



type Arrow a k = (WellPointed a, EnhancedCat a k)

instance Morphism (->) where
  first = Arr.first
  second = Arr.second
  (***) = (Arr.***)
instance PreArrow (->) where
  (&&&) = (Arr.&&&)
  fst (a,_) = a
  snd (_,b) = b
  terminal = const ()
instance WellPointed (->) where
  globalElement = Hask.const
  unit = Hask.pure ()
  const = Hask.const

constrainedArr :: (Category k, Category a, o b, o c )
  => ( k b c                        -> a b c  )
     -> k b c -> ConstrainedCategory a o b c
constrainedArr ar = constrained . ar

constrainedFirst :: ( Category a, Cartesian a, ObjectPair a b d, ObjectPair a c d )
  => ( a b c -> a (b, d) (c, d) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (b, d) (c, d)
constrainedFirst fs = ConstrainedMorphism . fs . unconstrained
  
constrainedSecond :: ( Category a, Cartesian a, ObjectPair a d b, ObjectPair a d c )
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
  fst = ConstrainedMorphism fst
  snd = ConstrainedMorphism snd

instance (WellPointed a, o (UnitObject a)) => WellPointed (ConstrainedCategory a o) where
  type PointObject (ConstrainedCategory a o) x = PointObject a x
  globalElement x = ConstrainedMorphism $ globalElement x
  unit = cstrCatUnit
  const x = ConstrainedMorphism $ const x

cstrCatUnit :: forall a o . (WellPointed a, o (UnitObject a))
        => CatTagged (ConstrainedCategory a o) (UnitObject a)
cstrCatUnit = retag (unit :: CatTagged a (UnitObject a))
  
instance (Arrow a k, o (UnitObject a)) => EnhancedCat (ConstrainedCategory a o) k where
  arr = constrainedArr arr 




-- | Basically 'ifThenElse' with inverted argument order, and
--   \"morphismised\" arguments.
choose :: (Arrow f (->), Function f, Object f Bool, Object f a)
     => f (UnitObject f) a  -- ^ \"'False'\" value
     -> f (UnitObject f) a  -- ^ \"'True'\" value
     -> f Bool           a
choose fv tv = arr $ \c -> if c then value tv else value fv

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
  alg1to2 :: ( Object k a, ObjectPair k b c
          ) => (forall q . Object k q
                 => ProxyVal k q a -> (ProxyVal k q b, ProxyVal k q c) )
               -> k a (b,c)
  alg2to1 :: ( ObjectPair k a b, Object k c
          ) => (forall q . Object k q
                 => ProxyVal k q a -> ProxyVal k q b -> ProxyVal k q c )
               -> k (a,b) c
  alg2to2 :: ( ObjectPair k a b, ObjectPair k c d
          ) => (forall q . Object k q
                 => ProxyVal k q a -> ProxyVal k q b -> (ProxyVal k q c, ProxyVal k q d) )
               -> k (a,b) (c,d)

genericAlg1to2 :: ( PreArrow k, u ~ UnitObject k
                  , Object k a, ObjectPair k b c
                  ) => ( forall q . Object k q
                      => GenericProxy k q a -> (GenericProxy k q b, GenericProxy k q c) )
               -> k a (b,c)
genericAlg1to2 f = runGenericProxy b &&& runGenericProxy c
 where (b,c) = f $ GenericProxy id
genericAlg2to1 :: ( PreArrow k, u ~ UnitObject k
                  , ObjectPair k a u, ObjectPair k a b, ObjectPair k b u, ObjectPair k b a
                  ) => ( forall q . Object k q
                      => GenericProxy k q a -> GenericProxy k q b -> GenericProxy k q c )
               -> k (a,b) c
genericAlg2to1 f = runGenericProxy $ f (GenericProxy fst) (GenericProxy snd)
genericAlg2to2 :: ( PreArrow k, u ~ UnitObject k
                  , ObjectPair k a u, ObjectPair k a b, ObjectPair k c d
                  , ObjectPair k b u, ObjectPair k b a
                  ) => ( forall q . Object k q
                      => GenericProxy k q a -> GenericProxy k q b 
                         -> (GenericProxy k q c, GenericProxy k q d) )
               -> k (a,b) (c,d)
genericAlg2to2 f = runGenericProxy c &&& runGenericProxy d
 where (c,d) = f (GenericProxy fst) (GenericProxy snd)


class (HasProxy k, ProxyVal k a x ~ p a x) 
           => PointProxy p k a x | p -> k where
  point :: (Object k a, Object k x) => x -> p a x

genericPoint :: ( WellPointed k, Object k a, ObjectPoint k x )
       => x -> GenericProxy k a x
genericPoint x = GenericProxy $ const x

