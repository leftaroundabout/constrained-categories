-- |
-- Module      :  Control.Arrow.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemueller $ geo.uni-koeln.de
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
    -- * Dual / "choice" arrows
    , ArrowChoice, MorphChoice(..), PreArrChoice(..)
    -- * Distributive law between sum- and product objects
    , SPDistribute(..) 
    -- * Function-like categories
    , Function, ($)
    -- * Alternative composition notation
    , (>>>), (<<<)
    -- * Proxies for cartesian categories
    , CartesianAgent(..)
    , genericAgentCombine, genericUnit, genericAlg1to2, genericAlg2to1, genericAlg2to2
    , PointAgent(..), genericPoint
    -- * Misc utility
    -- ** Conditionals
    , choose, ifThenElse
    -- ** Coercions
    , follow, flout, pretend, swallow, pretendLike, swallowLike
    ) where

import Prelude hiding (id, const, fst, snd, (.), ($), Functor(..), Monad(..), (=<<))
import Control.Category.Constrained
import qualified Control.Category.Hask as Hask

import GHC.Exts (Constraint)
import Data.Tagged
import Data.Void

import Data.Coerce
import Data.Type.Coercion

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

-- | Dual to 'Morphism', dealing with sums instead of products.
class (CoCartesian a) => MorphChoice a where
  left :: ( ObjectSum a b d, ObjectSum a c d )
         => a b c -> a (b+d) (c+d)
  left = (+++id)
  right :: ( ObjectSum a d b, ObjectSum a d c )
         => a b c -> a (d+b) (d+c)
  right = (id+++)
  (+++) :: ( ObjectSum a b b', ObjectSum a c c' )
         => a b c -> a b' c' -> a (b+b') (c+c')



-- | Unlike 'first', 'second', '***' and 'arr', the fanout operation '&&&' has an
--   intrinsic notion of \"direction\": it is basically equivalent to precomposing
--   the result of '***' with a @b -> (b,b)@, but that is only available
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

infixr 2 |||
-- | Dual to 'PreArrow', this class deals with the vacuous initial (zero) objects,
--   but also more usefully with choices / sums.
--   This represents the most part of 'Hask.ArrowChoice'.
class (MorphChoice k) => PreArrChoice k where
  (|||) :: ( ObjectSum k b b', Object k c )
         => k b c -> k b' c -> k (b+b') c
  -- | This is basically 'absurd'.
  initial :: ( Object k b ) => k (ZeroObject k) b
  -- | Perhaps @lft@ and @rgt@ would be more consequent names, but likely more confusing as well.
  coFst :: (ObjectSum k a b) => k a (a+b)
  coSnd :: (ObjectSum k a b) => k b (a+b)


-- | Like in arithmetics, the distributive law
--   @a &#x22c5; (b + c) &#x2248; (a &#x22c5; b) + (a &#x22c5; c)@
--   holds for Haskell types &#x2013; in the usual isomorphism sense. But like many such
--   isomorphisms that are trivial to inline in /Hask/, this is not necessarily the case
--   for general categories.
class (PreArrow k, PreArrChoice k) => SPDistribute k where
  distribute :: ( ObjectSum k (a,b) (a,c), ObjectPair k a (b+c)
                , ObjectSum k b c, PairObjects k a b, PairObjects k a c )
         => k (a, b+c) ((a,b)+(a,c))
  unDistribute :: ( ObjectSum k (a,b) (a,c), ObjectPair k a (b+c)
                  , ObjectSum k b c, PairObjects k a b, PairObjects k a c )
         => k ((a,b)+(a,c)) (a, b+c)
  boolAsSwitch :: ( ObjectSum k a a, ObjectPair k Bool a ) => k (Bool,a) (a+a)
  boolFromSwitch :: ( ObjectSum k a a, ObjectPair k Bool a ) => k (a+a) (Bool,a)
-- boolFromSwitch = (boolFromSum <<< terminal +++ terminal) &&& (id ||| id)

instance ( SPDistribute k 
         , ObjectSum k (a,b) (a,c), ObjectPair k a (b+c)
         , ObjectSum k b c, PairObjects k a b, PairObjects k a c
         ) => Isomorphic k (a, b+c) ((a,b)+(a,c)) where
  iso = distribute
instance ( SPDistribute k 
         , ObjectSum k (a,b) (a,c), ObjectPair k a (b+c)
         , ObjectSum k b c, PairObjects k a b, PairObjects k a c
         ) => Isomorphic k ((a,b)+(a,c)) (a, b+c) where
  iso = unDistribute
instance ( SPDistribute k 
         , ObjectSum k a a, ObjectPair k Bool a
         ) => Isomorphic k (Bool, a) (a+a) where
  iso = boolAsSwitch
instance ( SPDistribute k 
         , ObjectSum k a a, ObjectPair k Bool a
         ) => Isomorphic k (a+a) (Bool, a) where
  iso = boolFromSwitch

 

-- | 'WellPointed' expresses the relation between your category's objects
--   and the values of the Haskell data types (which is, after all, what objects are
--   in this library). Specifically, this class allows you to \"point\" on
--   specific objects, thus making out a value of that type as a point of the object.
--   
--   Perhaps easier than thinking about what that's supposed to mean is noting
--   this class contains 'const'. Thus 'WellPointed' is /almost/ the
--   traditional 'Hask.Arrow': it lets you express all the natural transformations
--   and inject constant values, only you can't just promote arbitrary functions
--   to arrows of the category.
--   
--   Unlike with 'Morphism' and 'PreArrow', a literal dual of 'WellPointed' does
--   not seem useful.
class (PreArrow a, ObjectPoint a (UnitObject a)) => WellPointed a where
  {-# MINIMAL unit, (globalElement | const) #-}
  type PointObject a x :: Constraint
  type PointObject a x = ()
  globalElement :: (ObjectPoint a x) => x -> a (UnitObject a) x
  globalElement = const
  unit :: CatTagged a (UnitObject a)
  const :: (Object a b, ObjectPoint a x) 
            => x -> a b x
  const x = globalElement x . terminal

type ObjectPoint k a = (Object k a, PointObject k a)
  
-- -- | 'WellPointed' does not have a useful literal dual.
-- class (PreArrChoice a, ObjectPoint a (ZeroObject a)) => WellChosen a where
--   type ChoiceObject a x :: Constraint
--   type ChoiceObject a x = ()
--   localElement :: (ObjectChoice a x) => a x (ZeroObject a) -> (x -> b
--   zero :: CatTagged a (ZeroObject a)
--   doomed :: (Object a b, ObjectChoice a x) 
--             => x -> a x b
--   doomed x = globalElement x . initial
-- 
-- type ObjectChoice k a = (Object k a, ChoiceObject k x)
-- 
value :: forall f x . (WellPointed f, Function f, Object f x)
           => f (UnitObject f) x -> x
value f = f $ untag(unit :: Tagged (f (UnitObject f) (UnitObject f)) (UnitObject f))



-- | @'EnhancedCat' a k@ means that the subcategory of @k@ whose objects are also
--   objects of @a@ is a subcategory of @a@. This works like
--   'Control.Category.Constrained.Reified.EnhancedCat'', but
--   does not require @'Object' k ⊆ 'Object' a@.
class (Category a, Category k) => EnhancedCat a k where
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

instance EnhancedCat (->) Coercion where
  arr = coerceWith



type Arrow a k = (WellPointed a, EnhancedCat a k)
type ArrowChoice a k = (WellPointed a, PreArrChoice a, EnhancedCat a k)

instance Morphism (->) where
  first = Arr.first
  second = Arr.second
  (***) = (Arr.***)
instance MorphChoice (->) where
  left = Arr.left
  right = Arr.right
  (+++) = (Arr.+++)
instance PreArrow (->) where
  (&&&) = (Arr.&&&)
  fst (a,_) = a
  snd (_,b) = b
  terminal = const ()
instance PreArrChoice (->) where
  (|||) = (Arr.|||)
  coFst a = Left a
  coSnd b = Right b
  initial = absurd
instance SPDistribute (->) where
  distribute (a, Left b) = Left (a,b)
  distribute (a, Right c) = Right (a,c)
  unDistribute (Left (a,b)) = (a, Left b)
  unDistribute (Right (a,c)) = (a, Right c)
  boolAsSwitch (False, a) = Left a
  boolAsSwitch (True, a) = Right a
  boolFromSwitch (Left a) = (False, a)
  boolFromSwitch (Right a) = (True, a)
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
  
instance (EnhancedCat a k, o (UnitObject a))
            => EnhancedCat (ConstrainedCategory a o) k where
  arr = constrainedArr arr


constrainedLeft :: ( CoCartesian k, ObjectSum k b d, ObjectSum k c d )
  => ( k b c -> k (b+d) (c+d) )
     -> ConstrainedCategory k o b c -> ConstrainedCategory k o (b+d) (c+d)
constrainedLeft fs = ConstrainedMorphism . fs . unconstrained
  
constrainedRight :: ( CoCartesian k, ObjectSum k b c, ObjectSum k b d )
  => ( k c d -> k (b+c) (b+d) )
     -> ConstrainedCategory k o c d -> ConstrainedCategory k o (b+c) (b+d)
constrainedRight fs = ConstrainedMorphism . fs . unconstrained

instance (MorphChoice k, o (ZeroObject k)) => MorphChoice (ConstrainedCategory k o) where
  left = constrainedLeft left
  right = constrainedRight right
  ConstrainedMorphism a +++ ConstrainedMorphism b = ConstrainedMorphism $ a +++ b
  
instance (PreArrChoice k, o (ZeroObject k)) => PreArrChoice (ConstrainedCategory k o) where
  ConstrainedMorphism a ||| ConstrainedMorphism b = ConstrainedMorphism $ a ||| b
  initial = ConstrainedMorphism initial
  coFst = ConstrainedMorphism coFst
  coSnd = ConstrainedMorphism coSnd

instance (SPDistribute k, o (ZeroObject k), o (UnitObject k))
     => SPDistribute (ConstrainedCategory k o) where
  distribute = ConstrainedMorphism distribute
  unDistribute = ConstrainedMorphism unDistribute
  boolAsSwitch = ConstrainedMorphism boolAsSwitch
  boolFromSwitch = ConstrainedMorphism boolFromSwitch
  


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

 


genericAgentCombine :: ( HasAgent k, PreArrow k
                       , Object k a, ObjectPair k b c, Object k d )
     => k (b,c) d -> GenericAgent k a b -> GenericAgent k a c -> GenericAgent k a d
genericAgentCombine m (GenericAgent v) (GenericAgent w)
       = GenericAgent $ m . (v &&& w)
  
genericUnit :: ( PreArrow k, HasAgent k, Object k a )
        => GenericAgent k a (UnitObject k)
genericUnit = GenericAgent terminal


class (Morphism k, HasAgent k) => CartesianAgent k where
  alg1to2 :: ( Object k a, ObjectPair k b c
          ) => (forall q . Object k q
                 => AgentVal k q a -> (AgentVal k q b, AgentVal k q c) )
               -> k a (b,c)
  alg2to1 :: ( ObjectPair k a b, Object k c
          ) => (forall q . Object k q
                 => AgentVal k q a -> AgentVal k q b -> AgentVal k q c )
               -> k (a,b) c
  alg2to2 :: ( ObjectPair k a b, ObjectPair k c d
          ) => (forall q . Object k q
                 => AgentVal k q a -> AgentVal k q b -> (AgentVal k q c, AgentVal k q d) )
               -> k (a,b) (c,d)

genericAlg1to2 :: ( PreArrow k, u ~ UnitObject k
                  , Object k a, ObjectPair k b c
                  ) => ( forall q . Object k q
                      => GenericAgent k q a -> (GenericAgent k q b, GenericAgent k q c) )
               -> k a (b,c)
genericAlg1to2 f = runGenericAgent b &&& runGenericAgent c
 where (b,c) = f $ GenericAgent id
genericAlg2to1 :: ( PreArrow k, u ~ UnitObject k
                  , ObjectPair k a u, ObjectPair k a b, ObjectPair k b u, ObjectPair k b a
                  ) => ( forall q . Object k q
                      => GenericAgent k q a -> GenericAgent k q b -> GenericAgent k q c )
               -> k (a,b) c
genericAlg2to1 f = runGenericAgent $ f (GenericAgent fst) (GenericAgent snd)
genericAlg2to2 :: ( PreArrow k, u ~ UnitObject k
                  , ObjectPair k a u, ObjectPair k a b, ObjectPair k c d
                  , ObjectPair k b u, ObjectPair k b a
                  ) => ( forall q . Object k q
                      => GenericAgent k q a -> GenericAgent k q b 
                         -> (GenericAgent k q c, GenericAgent k q d) )
               -> k (a,b) (c,d)
genericAlg2to2 f = runGenericAgent c &&& runGenericAgent d
 where (c,d) = f (GenericAgent fst) (GenericAgent snd)


class (HasAgent k, AgentVal k a x ~ p a x) 
           => PointAgent p k a x | p -> k where
  point :: (Object k a, Object k x) => x -> p a x

genericPoint :: ( WellPointed k, Object k a, ObjectPoint k x )
       => x -> GenericAgent k a x
genericPoint x = GenericAgent $ const x



-- | Imitate a type change in a different category. This is usually possible
--   for type changes that are no-ops at runtime, in particular for newtype wrappers.
follow :: (EnhancedCat k Coercion, Coercible a b, Object k a, Object k b)
                 => p a b -> k a b
follow _ = arr Coercion

-- | The opposite of 'follow'.
flout :: (EnhancedCat k Coercion, Coercible b a, Object k a, Object k b)
                 => p a b -> k b a
flout _ = arr Coercion

-- | Wrap an endomorphism in inverse coercions, to have it work on any type
--   that's representationally equivalent to the one in the morphism's signature.
--   This is a specialised version of 'pretendLike'.
pretend :: (EnhancedCat k Coercion, Object k a, Object k b)
                  => Coercion a b -> k a a -> k b b
pretend crc f = arr crc . f . arr (sym crc)

-- | Equivalent to @'pretend' . 'sym'@.
swallow :: (EnhancedCat k Coercion, Object k a, Object k b)
                  => Coercion b a -> k a a -> k b b
swallow crc f = arr (sym crc) . f . arr crc

-- | This works much like <http://hackage.haskell.org/package/newtype-0.2/docs/Control-Newtype.html#v:over over>:
--   wrap a morphism in any coercions required so the result types match.
--   This will often be too polymorphic for the type checker; consider using the
--   more explicit 'follow' and 'flout'.
pretendLike :: ( EnhancedCat k Coercion, Coercible b a, Coercible c d
               , Object k a, Object k b, Object k c, Object k d )
                   => p c d -> k a c -> k b d
pretendLike _ f = arr Coercion . f . arr Coercion


-- | Generalised coercion analogue of
--   <http://hackage.haskell.org/package/newtype-0.2/docs/Control-Newtype.html#v:under under>.
swallowLike :: ( EnhancedCat k Coercion, Coercible b a, Coercible c d
               , Object k a, Object k b, Object k c, Object k d )
                   => p b a -> k a c -> k b d
swallowLike _ f = arr Coercion . f . arr Coercion
