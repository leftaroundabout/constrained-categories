{-# LANGUAGE ConstraintKinds              #-}
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

