{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances            #-}


module Control.Applicative.Constrained ( module Control.Functor.Constrained
                                       , Monoidal(..)
                                       , Applicative(..)
                                       , constrainedFZipWith
                                       ) where


import Control.Category.Constrained
import Control.Functor.Constrained

import Prelude hiding (id, (.), ($), Functor(..), curry, uncurry)
import qualified Control.Category.Hask as Hask


class (Functor f r t, Curry r, Curry t) => Monoidal f r t where
  pure :: (Object r a, Object t (f a)) => a -> f a
  fzipWith :: (PairObject r a b, Object r c, PairObject t (f a) (f b), Object t (f c))
              => r (a, b) c -> t (f a, f b) (f c)

class (Monoidal f r t) => Applicative f r t where
  fpure :: (MorphObject r a b, Object t (f a)) => r a b -> f (r a b)
  (<*>) :: ( MorphObject r a b, Object r (r a b)
           , MorphObject t (f a) (f b), Object t (t (f a) (f b)), Object t (f (r a b))
           , PairObject r (r a b) a, PairObject t (f (r a b)) (f a)
           , Object r a, Object r b, Object t (f a), Object t (f b))
       => f (r a b) `t` t (f a) (f b)
  (<*>) = curry (fzipWith $ uncurry id)

infixl 4 <*>


constrainedFZipWith :: ( Category r, Category t, o a, o b, o (a,b), o c
                                               , o (f a, f b), o (f c) )
        =>  ( r (a, b) c -> t (f a, f b) (f c) )
         -> ConstrainedCategory r o (a, b) c -> ConstrainedCategory t o (f a, f b) (f c)
constrainedFZipWith zf = constrained . zf . unconstrained
         

instance (Hask.Applicative f) => Monoidal f (->) (->) where
  pure = Hask.pure
  fzipWith f (p, q) = curry f Hask.<$> p Hask.<*> q

instance (Hask.Applicative f) => Applicative f (->) (->) where
  fpure = Hask.pure
  (<*>) = (Hask.<*>)

  

  

