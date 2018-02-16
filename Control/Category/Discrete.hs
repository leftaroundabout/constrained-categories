-- |
-- Module      :  Control.Category.Discrete
-- Copyright   :  (c) 2018 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemueller $ geo.uni-koeln.de
-- 
-- 
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}


module Control.Category.Discrete where

import Control.Category

data Discrete a b where
   Refl :: Discrete a a

instance Category Discrete where
   id = Refl
   Refl . Refl = Refl
