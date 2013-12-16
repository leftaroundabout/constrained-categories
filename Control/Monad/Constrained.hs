{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FlexibleContexts             #-}


module Control.Monad.Constrained( module Control.Applicative.Constrained 
                                , Monad(..), (>>=), (=<<) 
                                ) where


import Control.Category.Constrained
import Control.Functor.Constrained
import Control.Applicative.Constrained

import Prelude hiding (id, (.), ($), Functor(..), Monad(..), (=<<))
import qualified Prelude


class (Applicative m k k) => Monad m k where
  return :: (Object k a, Object k (m a)) => k a (m a)
  join :: (Object k (m a), Object k (m (m a)))
       => m (m a) `k` m a

         

infixl 1 >>=
(=<<) :: (Monad m k, Object k a, Object k (m a), Object k (m b), Object k (m (m b)))
      => k a (m b) -> k (m a) (m b)
(=<<) q = join . fmap q

infixr 1 =<<
(>>=) :: (Monad m (->)) => m a -> (a -> m b) -> m b
(>>=) = flip (=<<)

instance Monad ((->)a) (->) where
  return = const
  join f x = f x x

instance Monad [] (->) where
  return = (:[])
  join = concat
  

-- | Deliberately break attempts to use this function.
fail :: ()
fail = undefined

  

