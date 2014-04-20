-- |
-- Module      :  Control.Category.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
-- 
-- The most basic category theory tools are included partly in this
-- module, partly in "Control.Arrow.Constrained".

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE MultiParamTypeClasses        #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE RankNTypes                   #-}

module Control.Category.Constrained ( 
            -- * The category class
            Category (..)
            -- * Monoidal categories
          , Cartesian (..), ObjectPair
          , Curry (..), ObjectMorphism
            -- * Isomorphisms
          , Isomorphic (..)
            -- * Constraining a category
          , ConstrainedCategory (ConstrainedMorphism)
          , constrained, unconstrained
            -- * Global-element proxies
          , HasProxy (..)
          , genericAlg, genericProxyMap
          , GenericProxy (..)
            -- * Utility
          , inCategoryOf
          ) where

import Prelude hiding (id, (.), curry, uncurry)
import qualified Prelude
import GHC.Exts (Constraint)
import Data.Monoid

-- | In mathematics, a category is defined as a class of /objects/, plus a class of
--   /morphisms/ between those objects. In Haskell, one traditionally works in
--   the category @(->)@ (called /Hask/), in which /any Haskell type/ is an object. 
--   But of course
--   there are lots of useful categories where the objects are much more specific,
--   e.g. vector spaces with linear maps as morphisms. The obvious way to express
--   this in Haskell is as type class constraints, and the @ConstraintKinds@ extension
--   allows quantifying over such object classes.
-- 
--   Like in "Control.Category", \"the category @k@\" means actually @k@ is the 
--   /morphism type constructor/. From a mathematician's point of view this may
--   seem a bit strange way to define the category, but it just turns out to
--   be quite convenient for practical purposes.
class Category k where
  type Object k o :: Constraint
  type Object k o = ()
  id :: Object k a => k a a
  (.) :: (Object k a, Object k b, Object k c) 
         => k b c -> k a b -> k a c

infixr 9 .

instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

-- | Analogue to 'asTypeOf', this does not actually do anything but can
--   give the compiler type unification hints in a convenient manner.
inCategoryOf :: (Category k) => k a b -> k c d -> k a b
m `inCategoryOf` _ = m


-- | A given category can be specialised, by using the same morphisms but adding
--   extra constraints to what is considered an object. 
-- 
--   For instance, @'ConstrainedCategory' (->) 'Ord'@ is the category of all
--   totally ordered data types (but with arbitrary functions; this does not require
--   monotonicity or anything).
newtype ConstrainedCategory (k :: * -> * -> *) (o :: * -> Constraint) (a :: *) (b :: *)
   = ConstrainedMorphism { unconstrainedMorphism :: k a b }

-- | Cast a morphism to its equivalent in a more constrained category,
--   provided it connects objects that actually satisfy the extra constraint.
constrained :: (Category k, o a, o b) => k a b -> ConstrainedCategory k o a b
constrained = ConstrainedMorphism

-- | \"Unpack\" a constrained morphism again (forgetful functor).
-- 
--   Note that you may often not need to do that; in particular
--   morphisms that are actually 'Function's can just be applied
--   to their objects with '$' right away, no need to go back to
--   Hask first.
unconstrained :: (Category k) => ConstrainedCategory k o a b -> k a b
unconstrained = unconstrainedMorphism

instance (Category k) => Category (ConstrainedCategory k isObj) where
  type Object (ConstrainedCategory k isObj) o = (Object k o, isObj o)
  id = ConstrainedMorphism id
  ConstrainedMorphism f . ConstrainedMorphism g = ConstrainedMorphism $ f . g


-- | Apart from /the/ identity morphism, 'id', there are other morphisms that
--   can basically be considered identies. For instance, in any cartesian
--   category (where it makes sense to have tuples and unit @()@ at all), it should be
--   possible to switch between @a@ and the isomorphic @(a, ())@. 'iso' is
--   the method for such \"pseudo-identities\", the most basic of which
--   are required as methods of the 'Cartesian' class.
--   
--   Why it is necessary to make these morphisms explicit: they are needed
--   for a couple of general-purpose category-theory methods, but even though
--   they're normally trivial to define there is no uniform way to do so.
--   For instance, for vector spaces, the baseis of @(a, (b,c))@ and @((a,b), c)@
--   are sure enough structurally equivalent, but not in the same way the spaces
--   themselves are (sum vs. product types).
class (Category k) => Isomorphic k a b where
  iso :: k a b

instance (Cartesian k, Object k a, u ~ UnitObject k, ObjectPair k a u) => Isomorphic k a (a,u) where
  iso = attachUnit
instance (Cartesian k, Object k a, u ~ UnitObject k, ObjectPair k a u) => Isomorphic k (a,u) a where
  iso = detachUnit
instance (Cartesian k, Object k a, u ~ UnitObject k, ObjectPair k a u, ObjectPair k u a, Object k (u, a), Object k (a, u) ) 
              => Isomorphic k a (u,a) where
  iso = swap . attachUnit
instance (Cartesian k, Object k a, u ~ UnitObject k, ObjectPair k a u, ObjectPair k u a, Object k (u, a), Object k (a, u) ) 
              => Isomorphic k (u,a) a where
  iso = detachUnit . swap
instance ( Cartesian k, Object k a, ObjectPair k a b, ObjectPair k b c
         , ObjectPair k a (b,c), ObjectPair k (a,b) c, Object k c )
                                       => Isomorphic k (a,(b,c)) ((a,b),c) where
  iso = regroup
instance ( Cartesian k, Object k a, Object k b, Object k c, ObjectPair k a b, ObjectPair k b c, ObjectPair k c a
         , ObjectPair k a (b,c), ObjectPair k (a,b) c, ObjectPair k (b, c) a, ObjectPair k b (c, a), ObjectPair k (c,a) b, ObjectPair k c (a,b)
         , Object k (a, (b, c)), Object k ((b,c),a), Object k (b,(c,a)), Object k ((a,b), c), Object k ((c,a),b), Object k (c,(a,b)) )
                                       => Isomorphic k ((a,b),c) (a,(b,c)) where
  iso = swap . regroup . swap . regroup . swap


        


-- | Quite a few categories (/monoidal categories/) will permit pairs of 
--   objects as objects again, allowing for \"dyadic morphisms\" @(x,y) ~> r@.
-- 
--   Together with a unique 'UnitObject', this makes for a monoidal
--   structure, with a few natural isomorphisms. Ordinary tuples may not
--   always be powerful enough to express the product objects; we avoid
--   making a dedicated associated type for the sake of simplicity,
--   but allow for an extra constraint to be imposed on objects prior
--   to consideration of pair-building.
--   
--   The name 'Cartesian' is disputable: in category theory that would rather
--   Imply /cartesian closed category/ (which we represent with 'Curry').
--   'Monoidal' would make sense, but we reserve that to 'Functors'.
class ( Category k
      , Monoid (UnitObject k), Object k (UnitObject k)
      -- , PairObject k (UnitObject k) (UnitObject k), Object k (UnitObject k,UnitObject k) 
      ) => Cartesian k where
  -- | Extra properties two types @a, b@ need to fulfill so @(a,b)@ can be an
  --   object of the category. This need /not/ take care for @a@ and @b@ themselves 
  --   being objects, we do that seperately: every function that actually deals
  --   with @(a,b)@ objects should require the stronger @'ObjectPair' k a b@.
  --   
  --   If /any/ two object types of your category make up a pair object, then
  --   just leave 'PairObjects' at the default (empty constraint).
  type PairObjects k a b :: Constraint
  type PairObjects k a b = ()
  type UnitObject k :: *
  type UnitObject k = ()
  
  swap :: ( ObjectPair k a b, ObjectPair k b a ) => k (a,b) (b,a)
  
  attachUnit  :: ( Object k a, u ~ UnitObject k, ObjectPair k a u ) => k a (a,u)
  detachUnit :: ( Object k a, u ~ UnitObject k, ObjectPair k a u ) => k (a,u) a
  regroup     :: ( Object k a, Object k c, ObjectPair k a b, ObjectPair k b c
                      , ObjectPair k a (b,c), ObjectPair k (a,b) c )
                      => k (a, (b, c)) ((a, b), c)

-- | Use this constraint to ensure that @a@, @b@ and @(a,b)@ are all \"fully valid\" objects
--   of your category (meaning, you can use them with the 'Cartesian' combinators).
type ObjectPair k a b = ( Category k, Object k a, Object k b
                        , PairObjects k a b, Object k (a,b)   )
  
instance Cartesian (->) where
  swap = \(a,b) -> (b,a)
  attachUnit = \a -> (a, ())
  detachUnit = \(a, ()) -> a
  regroup = \(a, (b, c)) -> ((a, b), c)
                        
instance (Cartesian f, o (UnitObject f)) => Cartesian (ConstrainedCategory f o) where
  type PairObjects (ConstrainedCategory f o) a b = (PairObjects f a b)
  type UnitObject (ConstrainedCategory f o) = UnitObject f

  swap = ConstrainedMorphism swap
  attachUnit = ConstrainedMorphism attachUnit
  detachUnit = ConstrainedMorphism detachUnit
  regroup = ConstrainedMorphism regroup


  
  
class (Cartesian k) => Curry k where
  type MorphObjects k b c :: Constraint
  type MorphObjects k b c = ()
  uncurry :: (ObjectPair k a b, ObjectMorphism k b c)
         => k a (k b c) -> k (a, b) c
  curry :: (ObjectPair k a b, ObjectMorphism k b c) 
         => k (a, b) c -> k a (k b c)

-- | Analogous to 'ObjectPair': express that @k b c@ be an exponential object
--   representing the morphism.
type ObjectMorphism k b c = (Object k b, Object k c, MorphObjects k b c, Object k (k b c))
  

instance Curry (->) where
  uncurry = Prelude.uncurry
  curry = Prelude.curry
      

instance (Curry f, o (UnitObject f)) => Curry (ConstrainedCategory f o) where
  type MorphObjects (ConstrainedCategory f o) a c = ( MorphObjects f a c, f ~ (->) )
  uncurry (ConstrainedMorphism f) = ConstrainedMorphism $ \(a,b) -> unconstrained (f a) b
  curry (ConstrainedMorphism f) = ConstrainedMorphism $ \a -> ConstrainedMorphism $ \b -> f (a, b)
                                                                     


infixr 0 $~

-- | A proxy value is a \"general representation\" of a category's
--   values, i.e. /global elements/. This is useful to define certain
--   morphisms (including ones that can't just \"inherit\" from '->'
--   with 'Control.Arrow.Constrained.arr') in ways other than point-free
--   composition pipelines. Instead, you can write algebraic expressions
--   much as if dealing with actual values of your category's objects,
--   but using the proxy type which is restricted so any function
--   defined as such a lambda-expression qualifies as a morphism 
--   of that category.
class (Category k) => HasProxy k where
  type ProxyVal k a v :: *
  type ProxyVal k a v = GenericProxy k a v
  alg :: ( Object k a, Object k b
         ) => (forall q . Object k q
                 => ProxyVal k q a -> ProxyVal k q b) -> k a b
  ($~) :: ( Object k a, Object k b, Object k c 
          ) => k b c -> ProxyVal k a b -> ProxyVal k a c

data GenericProxy k a v = GenericProxy { runGenericProxy :: k a v }

genericAlg :: ( HasProxy k, Object k a, Object k b )
        => ( forall q . Object k q
             => GenericProxy k q a -> GenericProxy k q b ) -> k a b
genericAlg f = runGenericProxy . f $ GenericProxy id

genericProxyMap :: ( HasProxy k, Object k a, Object k b, Object k c )
        => k b c -> GenericProxy k a b -> GenericProxy k a c
genericProxyMap m (GenericProxy v) = GenericProxy $ m . v



instance HasProxy (->) where
  type ProxyVal (->) a b = b
  alg f = f
  ($~) = ($)



