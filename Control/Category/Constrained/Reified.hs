-- |
-- Module      :  Control.Category.Constrained.Reified
-- Copyright   :  (c) 2016 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemueller $ geo.uni-koeln.de
-- 
-- 
-- GADTs that mirror the class hierarchy from 'Category' to (at the moment) 'Cartesian',
-- reifying all the available “free” composition operations.
-- 
-- These can be used as a “trivial base case“ for all kinds of categories:
-- it turns out these basic operations are often not so trivial to implement,
-- or only possible with stronger constraints than you'd like. For instance,
-- the category of affine mappings can only be implemented directly as a
-- category on /vector spaces/, because the identity mapping has /zero/ constant
-- offset.
-- 
-- By leaving the free compositions reified to runtime syntax trees, this problem
-- can be avoided. In other applications, you may not /need/ these cases,
-- but can still benefit from them for optimisation (composition with 'id' is
-- always trivial, and so on).

{-# LANGUAGE GADTs           #-}
{-# LANGUAGE ConstraintKinds #-}

module Control.Category.Constrained.Reified where


import Prelude ()
import GHC.Exts (Constraint)

import Control.Category.Constrained.Prelude



data ReCategory (obj_c :: * -> Constraint) α β where
    ReCategory_Id :: c α => ReCategory c α α

instance Category (ReCategory c) where
  type Object (ReCategory c) a = c a
  id = ReCategory_Id
  ReCategory_Id . ReCategory_Id = ReCategory_Id
  
instance HasAgent (ReCategory c) where
  type AgentVal (ReCategory c) α ω = GenericAgent (ReCategory c) α ω
  alg = genericAlg
  ($~) = genericAgentMap
  

data ReCartesian (obj_c :: * -> Constraint)
                 (pair_c :: * -> * -> Constraint)
                 (unitObj :: *)
                 α β where
    ReCartesian_Id :: c α => ReCartesian c p u α α
    ReCartesian_Comp :: (c α, c β, c γ)
                => ReCartesian c p u β γ -> ReCartesian c p u α β
                  -> ReCartesian c p u α γ
    ReCartesian_Swap :: (c α, c β, c (α,β), c (β,α), p α β, p β α)
                => ReCartesian c p u (α,β) (β,α)
    ReCartesian_AttachUnit :: (c α, c u, c (α,u), p α u)
                => ReCartesian c p u α (α,u)
    ReCartesian_DetachUnit :: (c α, c u, c (α,u), p α u)
                => ReCartesian c p u (α,u) α
    ReCartesian_Regroup :: ( c α, c β, c γ, c (α,β), c (β,γ)
                           , p α β, p β γ, p α (β,γ), p (α,β) γ )
                => ReCartesian c p u (α,(β,γ)) ((α,β),γ)
    ReCartesian_Regroup' :: ( c α, c β, c γ, c (α,β), c (β,γ)
                           , p α β, p β γ, p α (β,γ), p (α,β) γ )
                => ReCartesian c p u ((α,β),γ) (α,(β,γ))

instance Category (ReCartesian c p u) where
  type Object (ReCartesian c p u) a = c a
  
  id = ReCartesian_Id
  
  ReCartesian_Id . f = f
  f . ReCartesian_Id = f
  ReCartesian_Swap . ReCartesian_Swap = ReCartesian_Id
  ReCartesian_Regroup . ReCartesian_Regroup' = ReCartesian_Id
  ReCartesian_Regroup' . ReCartesian_Regroup = ReCartesian_Id
  f . g = ReCartesian_Comp f g

instance (c u, Monoid u) => Cartesian (ReCartesian c p u) where
  type PairObjects (ReCartesian c p u) α β = p α β
  type UnitObject (ReCartesian c p u) = u
  swap = ReCartesian_Swap
  attachUnit = ReCartesian_AttachUnit
  detachUnit = ReCartesian_DetachUnit
  regroup = ReCartesian_Regroup
  regroup' = ReCartesian_Regroup'
  
instance HasAgent (ReCartesian c p u) where
  type AgentVal (ReCartesian c p u) α ω = GenericAgent (ReCartesian c p u) α ω
  alg = genericAlg
  ($~) = genericAgentMap

