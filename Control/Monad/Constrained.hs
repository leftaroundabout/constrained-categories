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
                                -- * Monads                                
                                , Monad(..), (>>=), (=<<), (>>)
                                -- * Kleisli arrows
                                , Kleisli(..)
                                -- * Monoid-Monads
                                , MonadZero(..), MonadPlus(..), mplus
                                , MonadFail(..)
                                -- * Utility
                                , mapM, mapM_, forM, forM_, sequence, sequence_
                                , when
                                ) where


import Control.Applicative.Constrained
import Data.Foldable.Constrained
import Data.Traversable.Constrained

import Prelude hiding (
     id, (.), ($)
   , Functor(..), Monad(..), (=<<)
   , uncurry, curry
   , mapM, mapM_, sequence, sequence_
   )
import qualified Control.Category.Hask as Hask
import qualified Control.Arrow as A

import Control.Arrow.Constrained


class ( Applicative m k k
      , Object k (m (UnitObject k)), Object k (m (m (UnitObject k)))
      ) => Monad m k where
  return :: (Object k a, Object k (m a)) => k a (m a)
  return = pure
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
  

-- | 'Hask.MonadPlus' cannot be adapted quite analogously to 'Monad',
--   since 'mzero' is just a value with no way to indicate its morphism
--   category. The current implementation is probably not ideal, mainly
--   written to give 'MonadFail' ('fail' being needed for @RebindableSyntax@-@do@
--   notation) a mathematically reasonable superclass.
--   
--   Consider these classes provisorial, avoid relying on them explicitly.
class MonadZero m a where
  mzero :: m a

class (Monad m k, MonadZero m (UnitObject k)) => MonadPlus m k where
  fmplus :: (MonadZero m a) => k (m a, m a) (m a)

mplus :: (MonadPlus m (->), MonadZero m a) => m a -> m a -> m a
mplus = curry fmplus
  
instance (Hask.MonadPlus m) => MonadZero m () where
  mzero = Hask.mzero
instance (Hask.MonadPlus m, Hask.Applicative m) => MonadPlus m (->) where
  fmplus = uncurry Hask.mplus


class (MonadPlus m k) => MonadFail m k where
  fail :: (Object k (m a)) => k String (m a) 

instance (Hask.MonadPlus m, Hask.Applicative m) => MonadFail m (->) where
  fail = Hask.fail
  



newtype Kleisli m k a b = Kleisli { runKleisli :: k a (m b) }

instance (Monad m k) => Category (Kleisli m k) where
  type Object (Kleisli m k) o = (Object k o, Object k (m o), Object k (m (m o)))
  id = Kleisli return
  Kleisli a . Kleisli b = Kleisli $ join . fmap a . b

instance ( Monad m a, Arrow a (->), Function a ) => Curry (Kleisli m a) where
  type PairObject (Kleisli m a) b c 
          = ( Object a (b, c), Object a (m (b, c)), Object a (m b, c), Object a (b, m c)
            , Object a (m b, m c), Object a (m (m b, m c)), Object a (m (m (m b, m c)))
            , PairObject a b c
            , PairObject a (m b) c, PairObject a b (m c), PairObject a (m b) (m c) )
  type MorphObject (Kleisli m a) c d
          = ( Object a c, Object a d, Object a (m d), Object a (m (m d))
            , Object a (Kleisli m a c d), Object a (m (Kleisli m a c d))
            , Object a (a c (m d))
            , MorphObject a c d, MorphObject a c (m d), MorphObject a c (m (m d)) )
  type UnitObject (Kleisli m a) = UnitObject a
  
  curry (Kleisli fUnc) = Kleisli $ return . arr Kleisli . curry fUnc
  uncurry (Kleisli fCur) = Kleisli . arr $ 
               \(b,c) -> join . fmap (arr $ ($c) . runKleisli) . fCur $ b
  
  swap = Kleisli $ return . swap
  attachUnit = Kleisli $ return . attachUnit
  detachUnit = Kleisli $ return . detachUnit
  regroup = Kleisli $ return . regroup

  

instance (Monad m a, Arrow a (->), Function a, Curry a) => Arrow (Kleisli m a) (->) where
  arr f = Kleisli $ return . arr f
instance (Monad m a, Arrow a (->), Function a, Curry a) => PreArrow (Kleisli m a) where
  first = kleisliFirst
  second = kleisliSecond
  (***) = kleisliSplit
  (&&&) = kleisliFanout

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
kleisliSplit :: forall m a k b b' c c' .
                ( Arrow a (->), Monad m a, Function a, k ~ Kleisli m a, Curry k
                , Object k b, Object k c, Object k b', Object k c'
                , PairObject k b b', PairObject k c c', Object k (m c, m c') )
             => k b c -> k b' c' -> k (b, b') (c, c')
kleisliSplit  (Kleisli f) (Kleisli g) 
    = Kleisli $ monadOut . (f *** g)
  where monadOut :: a (m c, m c') (m (c, c'))
        monadOut = fzipWith (arr $ uncurry(,)) 
kleisliFanout :: forall m a k b b' c c' .
                ( Arrow a (->), Monad m a, Function a, k ~ Kleisli m a, Curry k
                , Object k b, Object k c, Object k c'
                , PairObject k c c', Object k (m c, m c') )
             => k b c -> k b c' -> k b (c, c')
kleisliFanout  (Kleisli f) (Kleisli g) 
    = Kleisli $ monadOut . (f &&& g)
  where monadOut :: a (m c, m c') (m (c, c'))
        monadOut = fzipWith (arr $ uncurry(,)) 



when :: ( Monad m k, Arrow k (->), u ~ UnitObject k
        , ObjectPair k (m u) u
        ) => Bool -> m u `k` m u
when True = id
when False = return . discard
    
 

