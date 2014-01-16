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
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TupleSections                #-}


module Control.Monad.Constrained( module Control.Applicative.Constrained 
                                , Monad(..), (>>=), (=<<), (>>), Kleisli(..)
                                , mapM
                                ) where


import Control.Applicative.Constrained
import Data.Traversable.Constrained

import Prelude hiding (
     id, (.), ($)
   , Functor(..), Monad(..), (=<<)
   , uncurry, curry
   , mapM, mapM_, sequence
   )
import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A

import Control.Arrow.Constrained


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




newtype Kleisli m k a b = Kleisli { runKleisli :: k a (m b) }

instance (Monad m k) => Category (Kleisli m k) where
  type Object (Kleisli m k) o = (Object k o, Object k (m o), Object k (m (m o)))
  id = Kleisli return
  Kleisli a . Kleisli b = Kleisli $ join . fmap a . b

instance (Monad m a, Arrow a (->), Function a) => Curry (Kleisli m a) where
  type PairObject (Kleisli m a) b c 
          = ( Object a (b, c), Object a (m (b, c)), Object a (m b, c), Object a (b, m c)
            , PairObject a b c, PairObject a (m b) c, PairObject a b (m c)               )
  type MorphObject (Kleisli m a) c d
          = ( Object a c, Object a d, Object a (m d), Object a (m (m d))
            , Object a (Kleisli m a c d), Object a (m (Kleisli m a c d))
            , Object a (a c (m d))
            , MorphObject a c d, MorphObject a c (m d), MorphObject a c (m (m d)) )
  curry (Kleisli fUnc) = Kleisli $ return . arr Kleisli . curry fUnc
  uncurry (Kleisli fCur) = Kleisli . arr $ 
               \(b,c) -> join . fmap (arr $ ($c) . runKleisli) . fCur $ b
  
  unitBranchIsoIn = Kleisli $ return . unitBranchIsoIn
  unitBranchIsoOut = Kleisli $ return . unitBranchIsoOut
  regroupIsoIn = Kleisli $ return . regroupIsoIn
  regroupIsoOut = Kleisli $ return . regroupIsoOut

  

instance (Monad m a, Arrow a (->), Function a, Curry a) => Arrow (Kleisli m a) (->) where
  arr f = Kleisli $ return . arr f
instance (Monad m a, Arrow a (->), Function a, Curry a) => PreArrow (Kleisli m a) where
  first = kleisliFirst
  second = kleisliSecond

kleisliFirst :: forall m a k b c d .
                ( Monad m a, Arrow a (->), Function a, k ~ Kleisli m a, Curry k
                , Object k b, Object k c, PairObject k b d, PairObject k c d ) 
             => k b c -> k (b, d) (c, d)
kleisliFirst (Kleisli f) = Kleisli $ arr monadOut . first f 
 where monadOut :: (m c, d) -> m (c, d)
       monadOut (mc, d) = fmap dPost $ mc
        where dPost :: a c (c, d)
              dPost = arr (, d)
kleisliSecond :: forall m a k b c d .
                ( Arrow a (->), Monad m a, Function a, k ~ Kleisli m a, Curry k
                , Object k b, Object k c, PairObject k d b, PairObject k d c ) 
             => k b c -> k (d, b) (d, c)
kleisliSecond (Kleisli f) = Kleisli $ arr monadOut . second f 
 where monadOut :: (d, m c) -> m (d, c)
       monadOut (d, mc) = fmap dPre $ mc
        where dPre :: a c (d, c)
              dPre = arr (d,)

 

