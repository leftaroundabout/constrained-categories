-- |
-- Module      :  Control.Functor.Constrained
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 

{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE TypeFamilies                 #-}
{-# LANGUAGE FunctionalDependencies       #-}
{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE FlexibleContexts             #-}
{-# LANGUAGE UndecidableInstances         #-}


module Control.Functor.Constrained ( module Control.Category.Constrained
                                   , Functor(..)
                                   , (<$>)
                                   , constrainedFmap
                                   ) where


import Control.Category.Constrained

import Prelude hiding (id, (.), Functor(..))
import qualified Prelude


class ( Category r, Category t, Object t (f (UnitObject r)) )
           => Functor f r t | f r -> t, f t -> r where
  fmap :: (Object r a, Object t (f a), Object r b, Object t (f b))
     => r a b -> t (f a) (f b)

instance (Prelude.Functor f) => Functor f (->) (->) where
  fmap = Prelude.fmap

(<$>) :: (Functor f r (->), Object r a, Object r b)
     => r a b -> f a -> f b
(<$>) = fmap

  
constrainedFmap :: (Category r, Category t, o a, o b, o (f a), o (f b)) 
      => (        r a b               -> t (f a) (f b)                      ) 
       -> ConstrainedCategory r o a b -> ConstrainedCategory t o (f a) (f b)
constrainedFmap q = constrained . q . unconstrained

instance (Functor [] k k, o [UnitObject k]) 
       => Functor [] (ConstrainedCategory k o) (ConstrainedCategory k o) where
  fmap (ConstrainedMorphism f) = ConstrainedMorphism $ fmap f


  

