{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}

module Control.Functor.Constrained where


import Control.Category.Constrained

import Prelude hiding (id, (.), Functor(..))
import qualified Prelude
import GHC.Exts (Constraint)


class (Category r, Category t) => Functor f r t | f r -> t, f t -> r where
  fmap :: (Object r a, Object r (f a), Object t b, Object t (f b))
     => r a b -> t (f a) (f b)

instance Functor ((->)a) (->) (->) where
  fmap = (.)

instance Functor [] (->) (->) where
  fmap = map

