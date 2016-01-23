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



data ReCategory (k :: * -> * -> *) (α :: *) (β :: *) where
    ReCategory :: k α β -> ReCategory k α β
    Id :: Object k α => ReCategory k α α
    (:>>>) :: ReCategory k α β -> ReCategory k β γ -> ReCategory k α γ

instance Category k => Category (ReCategory k) where
  type Object (ReCategory k) α = Object k α
  id = Id
  Id . g = g
  f . Id = f
  f . g = g :>>> f
  
instance HasAgent k => HasAgent (ReCategory k) where
  type AgentVal (ReCategory k) α ω = GenericAgent (ReCategory k) α ω
  alg = genericAlg
  ($~) = genericAgentMap
  

data ReCartesian (k :: * -> * -> *) (α :: *) (β :: *) where
    ReCartesian :: k α β -> ReCartesian k α β
    ReCartesianCat :: ReCategory (ReCartesian k) α β -> ReCartesian k α β
    Swap :: (ObjectPair k α β, ObjectPair k β α)
                => ReCartesian k (α,β) (β,α)
    AttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u)
                => ReCartesian k α (α,u)
    DetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u)
                => ReCartesian k (α,u) α
    Regroup :: ( ObjectPair k α β, ObjectPair k β γ
                           , ObjectPair k α (β,γ), ObjectPair k (α,β) γ )
                => ReCartesian k (α,(β,γ)) ((α,β),γ)
    Regroup' :: ( ObjectPair k α β, ObjectPair k β γ
                            , ObjectPair k α (β,γ), ObjectPair k (α,β) γ )
                => ReCartesian k ((α,β),γ) (α,(β,γ))

instance Category k => Category (ReCartesian k) where
  type Object (ReCartesian k) a = Object k a
  
  id = ReCartesianCat id
  
  ReCartesianCat f . ReCartesianCat g = ReCartesianCat $ f . g
  ReCartesianCat Id . g = g
  f . ReCartesianCat Id = f
  Swap . Swap = id
  Regroup . Regroup' = id
  Regroup' . Regroup = id
  f . g = ReCartesianCat $ ReCategory f . ReCategory g

instance Cartesian k => Cartesian (ReCartesian k) where
  type PairObjects (ReCartesian k) α β = PairObjects k α β
  type UnitObject (ReCartesian k) = UnitObject k
  swap = Swap
  attachUnit = AttachUnit
  detachUnit = DetachUnit
  regroup = Regroup
  regroup' = Regroup'
  
instance HasAgent k => HasAgent (ReCartesian k) where
  type AgentVal (ReCartesian k) α ω = GenericAgent (ReCartesian k) α ω
  alg = genericAlg
  ($~) = genericAgentMap

