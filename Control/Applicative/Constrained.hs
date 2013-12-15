{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleContexts             #-}


module Control.Applicative.Constrained ( module Control.Functor.Constrained
                                       , Applicative(..)
                                       ) where


import Control.Category.Constrained
import Control.Functor.Constrained

import Prelude hiding (id, (.), ($), Functor(..))
import qualified Prelude


class (Functor f r t, Curry r, Curry t) => Monoidal f r t where
  pure :: (Object r a, Object t (f a)) => a -> f a
  fpure :: (PairObject r a b, Object t (f a)) => r a c -> f (r a c)
  fzipWith :: (Object r c, PairObject t (f a) (f b), Object t (f c))
              => r (a, b) c -> t (f a, f b) (f c)

class (Monoidal f r t) => Applicative f r t where
  -- pure :: (Object r a, Object r b) => r a b -> f (r a b)
  (<*>) :: (Function r, Object r a, Object r b, Object t (f a), Object t (f b))
       => f (r a b) -> t (f a) (f b)
  (<*>) m = fzipWith 

infixl 4 <*>

-- constrainedPure :: ( Functor f, Category r, Object r a, Object r b )
--       => ( r a b -> f (r a b) ) 
--        -> ConstrainedCategory r o a b -> f (ConstrainedCategory r o a b)
-- constrainedPure f m = 
-- 
-- constrainedAp :: ( Applicative f (ConstrainedCategory r o) (ConstrainedCategory t o)
--                  , Category r, Object r a, Object r b, o a, o b
--                  , Category t, Object t (f a), Object t (f b), o (f a), o (f b) )
--        => (f (r a b)                       ->                     t (f a) (f b)   ) 
--         -> f (ConstrainedCategory r o a b) -> ConstrainedCategory t o (f a) (f b)
-- constrainedAp q m =  fmap unconstrained m
-- 

instance Monoidal ((->)a) (->) (->) where
  pure = const
  fzipWith f (a, b) x = f (a x, b x)
instance Applicative ((->)a) (->) (->) where
  f <*> g = \x -> f x $ g x
  
instance Monoidal [] (->) (->) where
  pure x = [x]
  fzipWith f (as, bs) = [ f (a,b) | a<-as, b<-bs ]
instance Applicative [] (->) (->) where
  fs <*> xs = fs >>= (`map`xs)

  

