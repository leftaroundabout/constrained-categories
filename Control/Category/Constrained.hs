{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE PolyKinds                    #-}
{-# LANGUAGE TypeFamilies                 #-}

module Control.Category.Constrained where

import Prelude hiding (id, (.))
import qualified Prelude
import GHC.Exts (Constraint)

class Category k where
  type Object k o :: Constraint
  type Object k o = ()
  id :: Object k a => k a a
  (.) :: (Object k a, Object k b, Object k c) 
         => k b c -> k a b -> k a c

instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

newtype ConstrainedCategory (k :: * -> * -> *) (o :: * -> Constraint) (a :: *) (b :: *)
   = ConstrainedMorphism { unconstrainedMorphism :: k a b }

instance (Category k) => Category (ConstrainedCategory k isObj) where
  type Object (ConstrainedCategory k isObj) o = (Object k o, isObj o)
  id = ConstrainedMorphism id
  ConstrainedMorphism f . ConstrainedMorphism g = ConstrainedMorphism $ f . g

