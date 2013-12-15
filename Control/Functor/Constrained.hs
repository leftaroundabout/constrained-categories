{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE UndecidableInstances         #-}


module Control.Functor.Constrained ( module Control.Category.Constrained
                                   , Functor(..)
                                   , constrainedFmap
                                   , Forgetful(..)
                                   ) where


import Control.Category.Constrained

import Prelude hiding (id, (.), ($), Functor(..))
import qualified Prelude


class (Category r, Category t) => Functor f r t | f r -> t, f t -> r where
  fmap :: (Object r a, Object r (f a), Object t b, Object t (f b))
     => r a b -> t (f a) (f b)

instance Functor ((->)a) (->) (->) where
  fmap = (.)

instance Functor [] (->) (->) where
  fmap = map

  
constrainedFmap :: (Category r, Category t, o a, o b, o (f a), o (f b)) 
      => (        r a b               -> t (f a) (f b)                      ) 
       -> ConstrainedCategory r o a b -> ConstrainedCategory t o (f a) (f b)
constrainedFmap q = constrained . q . unconstrained


newtype Forgetful a = Forgetful { runForgetful :: a }
   deriving (Eq, Ord, Show, Read)

instance Functor Forgetful (ConstrainedCategory (->) o) (->) where
  fmap q = Forgetful . unconstrained q . runForgetful

  

