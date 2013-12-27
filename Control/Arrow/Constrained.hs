-- |
-- Module      :  Control.Arrow.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE TupleSections                #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE UndecidableInstances         #-}


module Control.Arrow.Constrained where

import Prelude ()
import Control.Category.Constrained
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import qualified Control.Arrow as Arr

(>>>) :: (Category k, Object k a, Object k b, Object k c) 
             => k a b -> k b c -> k a c
(>>>) = flip (.)
(<<<) :: (Category k, Object k a, Object k b, Object k c) 
             => k b c -> k a b -> k a c
(<<<) = (.)

class (Category a, Curry a) => PreArrow a where
  first :: (Object a b, Object a c, PairObject a b d, PairObject a c d) 
         => a b c -> a (b, d) (c, d)
  second :: (Object a b, Object a c, PairObject a d b, PairObject a d c) 
         => a b c -> a (d, b) (d, c)
class (PreArrow a, Category k) => Arrow a k where
  arr :: (Object k b, Object k c, Object a b, Object a c)
         => k b c -> a b c

instance PreArrow (->) where
  first = Arr.first
  second = Arr.second
instance Arrow (->) (->) where
  arr = Arr.arr

constrainedArr :: (Category k, Category a, o b, o c )
  => ( k b c                        -> a b c  )
     -> k b c -> ConstrainedCategory a o b c
constrainedArr ar = constrained . ar

constrainedFirst :: ( Category a, Curry a, o b, o c, o d
                    , PairObject a b d, PairObject a c d )
  => ( a b c -> a (b, d) (c, d) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (b, d) (c, d)
constrainedFirst fs = ConstrainedMorphism . fs . unconstrained
  
constrainedSecond :: ( Category a, Curry a, o b, o c, o d
                    , PairObject a d b, PairObject a d c )
  => ( a b c -> a (d, b) (d, c) )
     -> ConstrainedCategory a o b c -> ConstrainedCategory a o (d, b) (d, c)
constrainedSecond sn = ConstrainedMorphism . sn . unconstrained

instance (PreArrow a) => PreArrow (ConstrainedCategory a o) where
  first = constrainedFirst first
  second = constrainedSecond second
  
instance (Arrow a k) => Arrow (ConstrainedCategory a o) k where
  arr = constrainedArr arr 

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

  
  

