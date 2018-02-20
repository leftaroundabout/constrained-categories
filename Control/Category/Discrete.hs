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

-- | The discrete category is the category with the minimum possible amount
--   of arrows: for any given type, there is 'id', and that's all.
--   You can use this to provide a proof that some endomorphism (of not closer
--   specified category) is the identity.
data Discrete a b where
   Refl :: Discrete a a

instance Category Discrete where
   id = Refl
   Refl . Refl = Refl
