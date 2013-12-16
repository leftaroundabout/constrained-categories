{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE PolyKinds                    #-}
{-# LANGUAGE TypeFamilies                 #-}

module Control.Category.Constrained ( Category (..)
                                    , ConstrainedCategory ()
                                    , constrained, unconstrained
                                    , Function (..)
                                    , Curry (..)
                                    ) where

import Prelude hiding (id, (.), ($), curry, uncurry)
import qualified Prelude
import GHC.Exts (Constraint)

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


-- | A category can be specialised, by using the same morphisms but adding
--   extra constraints to what is considered an object.
newtype ConstrainedCategory (k :: * -> * -> *) (o :: * -> Constraint) (a :: *) (b :: *)
   = ConstrainedMorphism { unconstrainedMorphism :: k a b }

constrained :: (Category k, o a, o b) => k a b -> ConstrainedCategory k o a b
constrained = ConstrainedMorphism

unconstrained :: (Category k) => ConstrainedCategory k o a b -> k a b
unconstrained = unconstrainedMorphism

instance (Category k) => Category (ConstrainedCategory k isObj) where
  type Object (ConstrainedCategory k isObj) o = (Object k o, isObj o)
  id = ConstrainedMorphism id
  ConstrainedMorphism f . ConstrainedMorphism g = ConstrainedMorphism $ f . g



infixr 0 $

class (Category k) => Function k where
  ($) :: (Object k a, Object k b) => k a b -> a -> b

instance Function (->) where ($) = (Prelude.$)

instance (Function f) => Function (ConstrainedCategory f o) where
  ConstrainedMorphism q $ x = q $ x



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

-- instance (Curry f) => Curry (ConstrainedCategory f o) where
--   type PairObject (ConstrainedCategory f o) a b = (PairObject f a b, o :w
                                                                     

