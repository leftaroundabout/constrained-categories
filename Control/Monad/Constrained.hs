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
                                , Monad(..), (>>=), (=<<), (>>), (<<)
                                -- * Kleisli arrows
                                , (>=>), (<=<)
                                , Kleisli(..)
                                -- * Monoid-Monads
                                , MonadZero(..), MonadPlus(..), mplus
                                , MonadFail(..)
                                -- * Utility
                                , mapM, mapM_, forM, forM_, sequence, sequence_
                                , guard, when, unless
                                , forever, void
                                ) where


import Control.Applicative.Constrained
import Data.Foldable.Constrained
import Data.Traversable.Constrained

import Prelude hiding (
     id, const, fst, snd, (.), ($)
   , Functor(..), Monad(..), (=<<)
   , uncurry, curry
   , mapM, mapM_, sequence, sequence_
   )
import qualified Control.Category.Hask as Hask

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

infixr 1 <<
(<<) :: ( Monad m k, WellPointed k
        , Object k a, Object k b, Object k (m a), Object k (m b), Object k (m (m b))
        ) => m b -> k (m a) (m b)
(<<) b = join . fmap (const b)

infixl 1 >>
(>>) :: ( WellPointed k, Monad m k, Object k a, Object k b
        , Object k (m a), Object k (m b), Object k (m (m b)), Object k (a,b) 
        , ObjectPair k b (UnitObject k), ObjectPair k (m b) (UnitObject k)
        , ObjectPair k (UnitObject k) (m b), ObjectPair k b a
        , PairObject k a b, Object k (m (a,b)), ObjectPair k (m a) (m b)
        ) => m a -> k (m b) (m b)
(>>) a = fmap snd . fzip . first (globalElement a) . swap . attachUnit
  -- where result = arr $ \b -> (join . fmap (const b)) `inCategoryOf` result $ a


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
  


(>=>) :: ( Monad m k, Object k a, Object k b, Object k c
         , Object k (m b), Object k (m c), Object k (m (m c)))
       => a `k` m b -> b `k` m c -> a `k` m c
f >=> g = join . fmap g . f
(<=<) :: ( Monad m k, Object k a, Object k b, Object k c
         , Object k (m b), Object k (m c), Object k (m (m c)))
       => b `k` m c -> a `k` m b -> a `k` m c
f <=< g = join . fmap f . g

newtype Kleisli m k a b = Kleisli { runKleisli :: k a (m b) }

instance (Monad m k) => Category (Kleisli m k) where
  type Object (Kleisli m k) o = (Object k o, Object k (m o), Object k (m (m o)))
  id = Kleisli return
  Kleisli a . Kleisli b = Kleisli $ join . fmap a . b

instance ( Monad m a, Cartesian a ) => Cartesian (Kleisli m a) where
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
  swap = Kleisli $ return . swap
  attachUnit = Kleisli $ return . attachUnit
  detachUnit = Kleisli $ return . detachUnit
  regroup = Kleisli $ return . regroup
  
instance ( Monad m a, Arrow a (->), Function a ) => Curry (Kleisli m a) where
  curry (Kleisli fUnc) = Kleisli $ return . arr Kleisli . curry fUnc
  uncurry (Kleisli fCur) = Kleisli . arr $ 
               \(b,c) -> join . fmap (arr $ ($c) . runKleisli) . fCur $ b
  

  

instance (Monad m a, Arrow a q, Cartesian a) => EnhancedCat (Kleisli m a) q where
  arr f = Kleisli $ return . arr f
instance (Monad m a, Morphism a, Curry a) => Morphism (Kleisli m a) where
  first (Kleisli f) = Kleisli $ fzip . (f *** return)
  second (Kleisli f) = Kleisli $ fzip . (return *** f)
  Kleisli f *** Kleisli g = Kleisli $ fzip . (f *** g)
instance (Monad m a, PreArrow a, Curry a) => PreArrow (Kleisli m a) where
  Kleisli f &&& Kleisli g = Kleisli $ fzip . (f &&& g)
  terminal = Kleisli $ return . terminal
instance (Monad m a, WellPointed a) => WellPointed (Kleisli m a) where
  globalElement x = Kleisli $ fmap (globalElement x) . pureUnit



guard ::( MonadPlus m k, Arrow k (->), Function k
        , UnitObject k ~ (), Object k Bool
        ) => Bool `k` m ()
guard = i . choose mzero (return `inCategoryOf` i $ ())
 where i = id


when :: ( Monad m k, PreArrow k, u ~ UnitObject k
        , ObjectPair k (m u) u
        ) => Bool -> m u `k` m u
when True = id
when False = return . terminal
unless :: ( Monad m k, PreArrow k, u ~ UnitObject k
        , ObjectPair k (m u) u
        ) => Bool -> m u `k` m u
unless False = id
unless True = return . terminal
    


forever :: ( Monad m k, Function k, Arrow k (->), Object k a, Object k b 
           , Object k (m a), Object k (m (m a)), Object k (m b), Object k (m (m b))
           ) => m a `k` m b
forever = i . arr loop 
    where loop a = (join . fmap (const $ loop a)) `inCategoryOf` i $ a
          i = id

void :: ( Monad m k, PreArrow k
        , Object k a, Object k (m a), ObjectPair k a u, u ~ UnitObject k 
        ) => m a `k` m (UnitObject k)
void = fmap terminal
 

