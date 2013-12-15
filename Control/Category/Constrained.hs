{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE PolyKinds                    #-}
{-# LANGUAGE TypeFamilies                 #-}

module Control.Category.Constrained ( Category (..)
                                    , ConstrainedCategory ()
                                    , constrained, unconstrained
                                    ) where

import Prelude hiding (id, (.))
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


