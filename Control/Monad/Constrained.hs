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
                                , Monad(..), return, (>>=), (=<<), (>>), (<<)
                                -- * Kleisli arrows
                                , (>=>), (<=<)
                                , Kleisli(..)
                                -- * Monoid-Monads
                                , MonadZero(..), mzero, MonadPlus(..), mplus
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
  join :: (Object k a, Object k (m a), Object k (m (m a)))
       => m (m a) `k` m a

-- | This is monomorphic in the category /Hask/, thus exactly the same as 'Hask.return'
--   from the standard prelude. This allows writing expressions like
--   @'return' '$' case x of ...@, which would always be ambiguous with the more general 
--   signature @Monad m k => k a (m a)@.
-- 
--   Use 'pure' when you want to \"return\" in categories other than @(->)@; this always
--   works since 'Applicative' is a superclass of 'Monad'.
return :: Monad m (->) => a -> m a
return = pure

         

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
(>>) :: ( WellPointed k, Monad m k
        , ObjectPair k b (UnitObject k), ObjectPair k (m b) (UnitObject k)
        , ObjectPair k (UnitObject k) (m b), ObjectPair k b a
        , ObjectPair k a b, Object k (m (a,b)), ObjectPair k (m a) (m b)
        ) => m a -> k (m b) (m b)
(>>) a = fmap snd . fzip . first (globalElement a) . swap . attachUnit
  -- where result = arr $ \b -> (join . fmap (const b)) `inCategoryOf` result $ a


instance (Hask.Applicative m, Hask.Monad m) => Monad m (->) where
  join = Hask.join
  

-- | 'Hask.MonadPlus' cannot be adapted quite analogously to 'Monad',
--   since 'mzero' is just a value with no way to indicate its morphism
--   category. The current implementation is probably not ideal, mainly
--   written to give 'MonadFail' ('fail' being needed for @RebindableSyntax@-@do@
--   notation) a mathematically reasonable superclass.
--   
--   Consider these classes provisorial, avoid relying on them explicitly.
class (Monad m k) => MonadZero m k where
  fmzero :: (Object k a, Object k (m a)) => UnitObject k `k` m a

mzero :: (MonadZero m (->)) => m a
mzero = fmzero ()

class (MonadZero m k) => MonadPlus m k where
  fmplus :: (ObjectPair k (m a) (m a)) => k (m a, m a) (m a)

mplus :: (MonadPlus m (->)) => m a -> m a -> m a
mplus = curry fmplus
  
instance (Hask.MonadPlus m, Hask.Applicative m) => MonadZero m (->) where
  fmzero = const Hask.mzero
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
  id = Kleisli pure
  Kleisli a . Kleisli b = Kleisli $ join . fmap a . b

instance ( Monad m a, Cartesian a ) => Cartesian (Kleisli m a) where
  type PairObjects (Kleisli m a) b c 
          = ( ObjectPair a b c
            , ObjectPair a (m b) c, ObjectPair a b (m c), ObjectPair a (m b) (m c) )
  type UnitObject (Kleisli m a) = UnitObject a
  swap = Kleisli $ pure . swap
  attachUnit = Kleisli $ pure . attachUnit
  detachUnit = Kleisli $ pure . detachUnit
  regroup = Kleisli $ pure . regroup
  
instance ( Monad m a, Arrow a (->), Function a ) => Curry (Kleisli m a) where
  type MorphObject (Kleisli m a) c d
          = ( Object a c, Object a d, Object a (m d), Object a (m (m d))
            , Object a (Kleisli m a c d), Object a (m (Kleisli m a c d))
            , Object a (a c (m d))
            , MorphObject a c d, MorphObject a c (m d), MorphObject a c (m (m d)) )
  curry (Kleisli fUnc) = Kleisli $ pure . arr Kleisli . curry fUnc
  uncurry (Kleisli fCur) = Kleisli . arr $ 
               \(b,c) -> join . fmap (arr $ ($c) . runKleisli) . fCur $ b
  

  

instance (Monad m a, Arrow a q, Cartesian a) => EnhancedCat (Kleisli m a) q where
  arr f = Kleisli $ pure . arr f
instance (Monad m a, Morphism a, Curry a) => Morphism (Kleisli m a) where
  first (Kleisli f) = Kleisli $ fzip . (f *** pure)
  second (Kleisli f) = Kleisli $ fzip . (pure *** f)
  Kleisli f *** Kleisli g = Kleisli $ fzip . (f *** g)
instance (Monad m a, PreArrow a, Curry a) => PreArrow (Kleisli m a) where
  Kleisli f &&& Kleisli g = Kleisli $ fzip . (f &&& g)
  terminal = Kleisli $ pure . terminal
  fst = Kleisli $ pure . fst
  snd = Kleisli $ pure . snd
instance (Monad m a, WellPointed a) => WellPointed (Kleisli m a) where
  globalElement x = Kleisli $ fmap (globalElement x) . pureUnit
  unit (Kleisli f) = unit f



guard ::( MonadPlus m k, Arrow k (->), Function k
        , UnitObject k ~ (), Object k Bool
        ) => Bool `k` m ()
guard = i . choose fmzero pure
 where i = id


when :: ( Monad m k, PreArrow k, u ~ UnitObject k
        , ObjectPair k (m u) u
        ) => Bool -> m u `k` m u
when True = id
when False = pure . terminal
unless :: ( Monad m k, PreArrow k, u ~ UnitObject k
        , ObjectPair k (m u) u
        ) => Bool -> m u `k` m u
unless False = id
unless True = pure . terminal
    


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
 

