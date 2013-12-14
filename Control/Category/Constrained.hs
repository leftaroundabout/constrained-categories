-- |
-- Module      : Control.Applicative.Constrained 
-- Copyright   : (c) Justus Sagemüller 2012
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemuej $ smail.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
-- 
-- Constraint-enabled version of the "Control.Category" module.


{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Category.Constrained where



class CCategory c where
  type CCategoryCtxt c a :: Constraint
  