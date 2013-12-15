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

infixr 9 .

instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)


-- | A category can be specialised, by using the same morphisms but adding
--   extra constraints to what is considered an object.
newtype ConstrainedCategory (k :: * -> * -> *) (o :: * -> Constraint) (a :: *) (b :: *)
   = ConstrainedMorphism { unconstrainedMorphism :: k a b }


