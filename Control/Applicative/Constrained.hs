-- |
-- Module      :  Control.Applicative.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE ScopedTypeVariables          #-}


module Control.Applicative.Constrained ( 
            module Control.Functor.Constrained
            -- * Monoidal / applicative functors
          , Monoidal(..)
          , Applicative(..)
            -- * Helper for constrained categories
          , constrainedFZipWith
            -- * Utility functions
          , constPure, (<**>), liftA, liftA2, liftA3
          ) where


import Control.Functor.Constrained
import Control.Arrow.Constrained

import Prelude hiding (id, (.), ($), Functor(..), curry, uncurry)
import qualified Control.Category.Hask as Hask


class (Functor f r t, Curry r, Curry t) => Monoidal f r t where
  pureUnit :: UnitObject t `t` f (UnitObject r)
  fzipWith :: (PairObject r a b, Object r c, PairObject t (f a) (f b), Object t (f c))
              => r (a, b) c -> t (f a, f b) (f c)

constPure :: (Arrow r (->), Monoidal f r t, Object r a, Object t (f a) )
       => a -> t (UnitObject t) (f a)
constPure a = fmap (arr $ const a) . pureUnit


class (Monoidal f r t) => Applicative f r t where
  -- ^ Note that this tends to make little sense for non-endofunctors. 
  --   Consider using 'constPure' instead.
  pure :: (Object r a, Object t (f a)) => a `t` f a 
  fpure :: (MorphObject r a b, Object t (f a)) => r a b -> f (r a b)
  
  (<*>) :: ( MorphObject r a b, Object r (r a b)
           , MorphObject t (f a) (f b), Object t (t (f a) (f b)), Object t (f (r a b))
           , PairObject r (r a b) a, PairObject t (f (r a b)) (f a)
           , Object r a, Object r b, Object t (f a), Object t (f b))
       => f (r a b) `t` t (f a) (f b)
  (<*>) = curry (fzipWith $ uncurry id)

infixl 4 <*>
  
(<**>) :: ( Applicative f r (->), Object r a, Object r b
          , MorphObject r a b, Object r (r a b), PairObject r (r a b) a )
             => f a -> f (r a b) -> f b
(<**>) = flip $ curry (fzipWith $ uncurry id)

liftA :: (Applicative f r t, Object r a, Object r b, Object t (f a), Object t (f b)) 
             => a `r` b -> f a `t` f b
liftA = fmap

liftA2 :: ( Applicative f r t, Object r a, Object r b, Object r c, MorphObject r b c
          , Object t (f a), Object t (f b), Object t (f c), MorphObject t (f b) (f c) 
          , PairObject r a b, PairObject t (f a) (f b) ) 
             => a `r` (b `r` c) -> f a `t` (f b `t` f c)
liftA2 = curry . fzipWith . uncurry

liftA3 :: ( Applicative f r t
          , Object r a, Object r b, Object r c, Object r d
          , MorphObject r c d, MorphObject r b (c`r`d), Object r (r c d)
          , PairObject r a b, PairObject r (r c d) c 
          , Object t (f a), Object t (f b), Object t (f c), Object t (f d), Object t(f a,f b)
          , MorphObject t (f c)(f d),MorphObject t (f b)(t(f c)(f d)),Object t(t(f c)(f d))
          , PairObject t (f a) (f b), PairObject t (t (f c) (f d)) (f c)
          , PairObject t (f (r c d)) (f c), Object t (f (r c d))
          ) => a `r` (b `r` (c `r` d)) -> f a `t` (f b `t` (f c `t` f d))
liftA3 f = curry $ (<*>) . (fzipWith $ uncurry f)


constrainedFZipWith :: ( Category r, Category t, o a, o b, o (a,b), o c
                                               , o (f a, f b), o (f c) )
        =>  ( r (a, b) c -> t (f a, f b) (f c) )
         -> ConstrainedCategory r o (a, b) c -> ConstrainedCategory t o (f a, f b) (f c)
constrainedFZipWith zf = constrained . zf . unconstrained
         

instance (Hask.Applicative f) => Monoidal f (->) (->) where
  pureUnit = Hask.pure
  fzipWith f (p, q) = curry f Hask.<$> p Hask.<*> q

instance (Hask.Applicative f) => Applicative f (->) (->) where
  pure = Hask.pure
  fpure = Hask.pure
  (<*>) = (Hask.<*>)

  

  

