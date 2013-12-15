{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE UndecidableInstances         #-}


module Control.Applicative.Constrained where


import Control.Category.Constrained
import Control.Functor.Constrained

import Prelude hiding (id, (.), Functor(..))
import qualified Prelude
import GHC.Exts (Constraint)


class (Functor f r t) => Applicative f r t where
  pure :: (Object t a, Object t (f a)) => t a (f a)
  (<*>) :: (Object r a, Object r b, Object t (f a), Object t (f b))
       => f (r a b) -> t (f a) (f b)

instance Applicative ((->)a) (->) (->) where
  pure = const
  f <*> g = \x -> f x $ g x

instance Applicative [] (->) (->) where
  pure x = [x]
  fs <*> xs = fs >>= (`map`xs)

  

