-- |
-- Module      :  Control.Category.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}

module Control.Category.Constrained ( 
            -- * The category class
            Category (..)
            -- * Constraining categories
          , ConstrainedCategory (ConstrainedMorphism)
          , constrained, unconstrained
            -- * Function-like categories
          , Function (..)
          , Curry (..)
          ) where

import Prelude hiding (id, (.), ($), curry, uncurry)
import qualified Prelude
import GHC.Exts (Constraint)

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

-- | \"Unpack\" a constrained morpism again (forgetful functor).
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



infixr 0 $

-- | Many categories have as morphisms essentially /functions with extra properties/:
--   group homomorphisms, linear maps, continuous functions...
-- 
--   It makes sense to generalise the notion of function application to these
--   morphisms; we can't do that for the simple juxtaposition writing @f x@,
--   but it is possible for the function-application operator @$@.
-- 
--   This is particularly useful for 'ConstrainedCategory' versions of Hask,
--   where after all the morphisms are /nothing but functions/.
class (Category k) => Function k where
  ($) :: (Object k a, Object k b) => k a b -> a -> b

instance Function (->) where ($) = (Prelude.$)

instance (Function f) => Function (ConstrainedCategory f o) where
  ConstrainedMorphism q $ x = q $ x



-- | Quite a few categories (/monoidal categories/) will permit pairs of 
--   objects as objects again, allowing for \"dyadic morphisms\" @(x,y) ~> r@.
--   The notion of a morphism between morphisms on the other hand, seen
--   so often in Haskell type signatures @a->b->c@ but – perhaps for this reason –
--   rather more seldom elsewhere in maths\/science\/programming, generally just
--   does not make much sense within a given category.
-- 
--   Still, you should make your monoidal categories instances of 'Curry'.
--   The reason being, currying is crucial for \"applicative style\",
--   the standard way of using 'Control.Applicative.Constrained.Monoidal'
--   functors. So for keeping to the well-established class hierarchy 
--   @Functor => Applicative => Monad@ (which is desirable for a number 
--   of reasons), your monads first need some kind of notion about what
--   a curried morphism might be.
-- 
--   To keep this in bounds, both \"pair-object–pairs\" and \"morphism-objects\"
--   can have constraints on their constituent objects.
--   We deviate quite strongly from the mathematical nomenclature at this point, though,
--   in favor of standard Haskell notions. The 'PairObject' constraint should more
--   accurately be an associated type family /monoidal product/, and \"morphism objects\"
--   are better called /exponential types/. Use the @categories@ package if you
--   prefer a more rigorous approach to the one taken here.
class (Category k) => Curry k where
  type PairObject k a b :: Constraint
  type PairObject k a b = ()
  type MorphObject k b c :: Constraint
  type MorphObject k b c = ()
  uncurry :: (Object k a, Object k b, Object k c, PairObject k a b, MorphObject k b c)
         => k a (k b c) -> k (a, b) c
  curry :: (Object k a, Object k b, Object k c, PairObject k a b, MorphObject k b c) 
         => k (a, b) c -> k a (k b c)

instance Curry (->) where
  uncurry = Prelude.uncurry
  curry = Prelude.curry

instance (Curry f) => Curry (ConstrainedCategory f o) where
  type PairObject (ConstrainedCategory f o) a b = (PairObject f a b, o a, o b, o (a, b))
  type MorphObject (ConstrainedCategory f o) a c = ( MorphObject f a c, f ~ (->) )
  uncurry (ConstrainedMorphism f) = ConstrainedMorphism $ \(a,b) -> unconstrained (f a) b
  curry (ConstrainedMorphism f) = ConstrainedMorphism $ \a -> ConstrainedMorphism $ \b -> f (a, b)
                                                                     

