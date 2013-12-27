-- |
-- Module      :  Control.Monad.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances            #-}


module Control.Monad.Constrained( module Control.Applicative.Constrained 
                                , Monad(..), (>>=), (=<<), (>>)
                                ) where


import Control.Applicative.Constrained

import Prelude hiding (id, (.), ($), Functor(..), Monad(..), (=<<))
import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A


class (Applicative m k k) => Monad m k where
  return :: (Object k a, Object k (m a)) => k a (m a)
  join :: (Object k a, Object k (m a), Object k (m (m a)))
       => m (m a) `k` m a

         

infixr 1 =<<
(=<<) :: ( Monad m k, Object k a, Object k b
         , Object k (m a), Object k (m b), Object k (m (m b)) )
      => k a (m b) -> k (m a) (m b)
(=<<) q = join . fmap q

infixl 1 >>=
(>>=) :: ( Function f, Monad m f, Object f a, Object f b
         , Object f (m a), Object f (m b), Object f (m (m b)) ) 
             => m a -> f a (m b) -> m b
g >>= h = (=<<) h $ g

infixl 1 >>
(>>) :: ( Function f, A.Arrow f, Monad m f, Object f a, Object f b
         , Object f (m a), Object f (m b), Object f (m (m b)) ) 
            => m a -> f (m b) (m b)
(>>) a = result
  where result = A.arr $ \b -> (join . fmap (A.arr $ const b)) `asTypeOf` catDummy $ a
        catDummy = undefined . result . undefined -- Just to get in the right category


instance (Hask.Applicative m, Hask.Monad m) => Monad m (->) where
  return = Hask.return
  join = Hask.join
  

-- | Deliberately break attempts to use this function.
fail :: ()
fail = undefined

  

