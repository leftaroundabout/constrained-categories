-- |
-- Module      :  Control.Category.Compound.Reified
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

{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE CPP                   #-}

module Control.Category.Compound.Reified (
      -- * Reified versions of the category classes
         ReCategory(..)
       , ReCartesian(..)
       , ReMorphism(..)
       , RePreArrow(..)
       , ReWellPointed(..)
       ) where


import Prelude ()
import GHC.Exts (Constraint)

import Control.Category.Compound.Prelude
import Control.Arrow.Compound

import Data.Tagged


data ObjectWitness k α where
  IsObject :: Object k α => ObjectWitness k α

domObjWitness :: (Category k, Object k α) => k α β -> ObjectWitness k α
domObjWitness _ = IsObject
codomObjWitness :: (Category k, Object k β) => k α β -> ObjectWitness k β
codomObjWitness _ = IsObject

withObjWitness :: ObjectWitness k γ -> (ObjectWitness k γ -> k α β) -> k α β
withObjWitness w f = f w

data ObjPairWitness k α β where
  AreObjects :: ObjectPair k α β => ObjPairWitness k α β
data UnitObjWitness k u where
  IsUnitObj :: UnitObjWitness k (UnitObject k)






-- GHC-invoked CPP can't seem able to do token pasting, so invoke the
-- preprocessor manually to generate the GADTs.
-- @
--  $ cpp Control/Category/Constrained/Reified.hs 2> /dev/null | less
-- @
-- You can there copy-and paste the definitions of 'ReCategory' etc..
#ifndef __GLASGOW_HASKELL__
#  define GADTCPP
#endif

#ifdef GADTCPP
#  define RECATEGORY(C)                           \
    Re##C :: k α β -> Re##C k α β;                 \
    C##Id :: Object k α => Re##C k α α;             \
    C##Compo :: Object k β                           \
         => Re##C k α β -> Re##C k β γ -> Re##C k α γ
#else
#  define RECATEGORY(C)   \
    ReCategory :: k α β -> ReCategory k α β; CategoryId :: Object k α => ReCategory k α α; CategoryCompo :: Object k β => ReCategory k α β -> ReCategory k β γ -> ReCategory k α γ
#endif
data ReCategory (k :: * -> * -> *) (α :: *) (β :: *) where
    RECATEGORY(Category)

#define CATEGORYCOMPO \
  Id . f = f;          \
  g . Id = g

instance Category k => Category (ReCategory k) where
  type Object (ReCategory k) α = Object k α
  id = CategoryId
  CategoryId . f = f
  g . CategoryId = g
  g . f = CategoryCompo f g

  
instance HasAgent k => HasAgent (ReCategory k) where
  type AgentVal (ReCategory k) α ω = GenericAgent (ReCategory k) α ω
  alg = genericAlg
  ($~) = genericAgentMap
  

instance Category k => EnhancedCat (ReCategory k) k where arr = ReCategory



#ifdef GADTCPP
#  define RECARTESIAN(C)                                          \
    RECATEGORY(C);                                                 \
    C##Swap :: (ObjectPair k α β, ObjectPair k β α)                 \
                => Re##C k (α,β) (β,α);                              \
    C##AttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) \
                => Re##C k α (α,u);                                    \
    C##DetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u)   \
                => Re##C k (α,u) α;                                      \
    C##Regroup :: ( ObjectPair k α β, ObjectPair k β γ                    \
                  , ObjectPair k α (β,γ), ObjectPair k (α,β) γ )           \
                => Re##C k (α,(β,γ)) ((α,β),γ);                             \
    C##Regroup_ :: ( ObjectPair k α β, ObjectPair k β γ                      \
                   , ObjectPair k α (β,γ), ObjectPair k (α,β) γ )             \
                => Re##C k ((α,β),γ) (α,(β,γ))
#else
#  define RECARTESIAN(C) \
    ReCartesian :: k α β -> ReCartesian k α β; CartesianId :: Object k α => ReCartesian k α α; CartesianCompo :: Object k β => ReCartesian k α β -> ReCartesian k β γ -> ReCartesian k α γ; CartesianSwap :: (ObjectPair k α β, ObjectPair k β α) => ReCartesian k (α,β) (β,α); CartesianAttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => ReCartesian k α (α,u); CartesianDetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => ReCartesian k (α,u) α; CartesianRegroup :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => ReCartesian k (α,(β,γ)) ((α,β),γ); CartesianRegroup_ :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => ReCartesian k ((α,β),γ) (α,(β,γ))
#endif
data ReCartesian (k :: * -> * -> *) (α :: *) (β :: *) where
    RECARTESIAN(Cartesian)

#define CARTESIANCOMPO   \
  Swap . Swap = id;       \
  Regroup . Regroup' = id; \
  Regroup' . Regroup = id;  \
  CATEGORYCOMPO

instance Cartesian k => Category (ReCartesian k) where
  type Object (ReCartesian k) a = Object k a
  id = CartesianId
  CartesianSwap . CartesianSwap = id
  CartesianRegroup . CartesianRegroup_ = id
  CartesianRegroup_ . CartesianRegroup = id
  CartesianId . f = f
  g . CartesianId = g
  g . f = CartesianCompo f g

instance Cartesian k => Cartesian (ReCartesian k) where
  type PairObjects (ReCartesian k) α β = PairObjects k α β
  type UnitObject (ReCartesian k) = UnitObject k
  swap = CartesianSwap
  attachUnit = CartesianAttachUnit
  detachUnit = CartesianDetachUnit
  regroup = CartesianRegroup
  regroup' = CartesianRegroup_
  
  
instance (HasAgent k, Cartesian k) => HasAgent (ReCartesian k) where
  type AgentVal (ReCartesian k) α ω = GenericAgent (ReCartesian k) α ω
  alg = genericAlg
  ($~) = genericAgentMap
  
  
instance Cartesian k => EnhancedCat (ReCartesian k) k where arr = ReCartesian


#ifdef GADTCPP
#  define REMORPHISM(C)                                \
    RECARTESIAN(C);                                     \
    C##Par :: (ObjectPair k α γ, ObjectPair k β δ)       \
              => Re##C k α β -> Re##C k γ δ -> Re##C k (α,γ) (β,δ)
#else
#  define REMORPHISM(C)  \
    ReMorphism :: k α β -> ReMorphism k α β; MorphismId :: Object k α => ReMorphism k α α; MorphismCompo :: Object k β => ReMorphism k α β -> ReMorphism k β γ -> ReMorphism k α γ; MorphismSwap :: (ObjectPair k α β, ObjectPair k β α) => ReMorphism k (α,β) (β,α); MorphismAttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => ReMorphism k α (α,u); MorphismDetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => ReMorphism k (α,u) α; MorphismRegroup :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => ReMorphism k (α,(β,γ)) ((α,β),γ); MorphismRegroup_ :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => ReMorphism k ((α,β),γ) (α,(β,γ)); MorphismPar :: (ObjectPair k α γ, ObjectPair k β δ) => ReMorphism k α β -> ReMorphism k γ δ -> ReMorphism k (α,γ) (β,δ)
#endif
data ReMorphism (k :: * -> * -> *) (α :: *) (β :: *) where
    REMORPHISM(Morphism)

#define MORPHISMCOMPO               \
  (f:***g) . (h:***i) = f.h *** g.i; \
  CARTESIANCOMPO

instance Morphism k => Category (ReMorphism k) where
  type Object (ReMorphism k) a = Object k a
  id = MorphismId
  (f`MorphismPar`g) . (h`MorphismPar`i) = f.h *** g.i
  MorphismSwap . MorphismSwap = id
  MorphismRegroup . MorphismRegroup_ = id
  MorphismRegroup_ . MorphismRegroup = id
  MorphismId . f = f
  g . MorphismId = g
  g . f = MorphismCompo f g

instance Morphism k => Cartesian (ReMorphism k) where
  type PairObjects (ReMorphism k) α β = PairObjects k α β
  type UnitObject (ReMorphism k) = UnitObject k
  swap = MorphismSwap
  attachUnit = MorphismAttachUnit
  detachUnit = MorphismDetachUnit
  regroup = MorphismRegroup
  regroup' = MorphismRegroup_
  
instance Morphism k => Morphism (ReMorphism k) where
  (***) = MorphismPar

instance (HasAgent k, Morphism k) => HasAgent (ReMorphism k) where
  type AgentVal (ReMorphism k) α ω = GenericAgent (ReMorphism k) α ω
  alg = genericAlg
  ($~) = genericAgentMap

  
instance Morphism k => EnhancedCat (ReMorphism k) k where arr = ReMorphism




#ifdef GADTCPP
#  define REPREARROW(C)                                    \
    REMORPHISM(C);                                          \
    C##Fanout :: (Object k α, ObjectPair k β γ)              \
            => Re##C k α β -> Re##C k α γ -> Re##C k α (β,γ); \
    C##Terminal :: Object k α => Re##C k α (UnitObject k);     \
    C##Fst :: ObjectPair k α β => Re##C k (α,β) α;              \
    C##Snd :: ObjectPair k α β => Re##C k (α,β) β
#else
#  define REPREARROW(C) \
    RePreArrow :: k α β -> RePreArrow k α β; PreArrowId :: Object k α => RePreArrow k α α; PreArrowCompo :: Object k β => RePreArrow k α β -> RePreArrow k β γ -> RePreArrow k α γ; PreArrowSwap :: (ObjectPair k α β, ObjectPair k β α) => RePreArrow k (α,β) (β,α); PreArrowAttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => RePreArrow k α (α,u); PreArrowDetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => RePreArrow k (α,u) α; PreArrowRegroup :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => RePreArrow k (α,(β,γ)) ((α,β),γ); PreArrowRegroup_ :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => RePreArrow k ((α,β),γ) (α,(β,γ)); PreArrowPar :: (ObjectPair k α γ, ObjectPair k β δ) => RePreArrow k α β -> RePreArrow k γ δ -> RePreArrow k (α,γ) (β,δ); PreArrowFanout :: (Object k α, ObjectPair k β γ) => RePreArrow k α β -> RePreArrow k α γ -> RePreArrow k α (β,γ); PreArrowTerminal :: Object k α => RePreArrow k α (UnitObject k); PreArrowFst :: ObjectPair k α β => RePreArrow k (α,β) α; PreArrowSnd :: ObjectPair k α β => RePreArrow k (α,β) β
#endif
data RePreArrow (k :: * -> * -> *) (α :: *) (β :: *) where
    REPREARROW(PreArrow)

#define PREARROWCOMPO      \
  Terminal . _ = terminal;  \
  Fst . (f:&&&_) = f;        \
  Snd . (_:&&&g) = g;         \
  Fst . (f:***_) = f . fst;    \
  Snd . (_:***g) = g . snd;     \
  MORPHISMCOMPO

instance PreArrow k => Category (RePreArrow k) where
  type Object (RePreArrow k) a = Object k a
  id = PreArrowId
  PreArrowTerminal . _ = terminal
  PreArrowFst . (f`PreArrowFanout`_) = f
  PreArrowSnd . (_`PreArrowFanout`g) = g
  PreArrowFst . (f`PreArrowPar`_) = f . fst
  PreArrowSnd . (_`PreArrowPar`g) = g . snd
  (f`PreArrowPar`g) . (h`PreArrowPar`i) = f.h *** g.i
  PreArrowSwap . PreArrowSwap = id
  PreArrowRegroup . PreArrowRegroup_ = id
  PreArrowRegroup_ . PreArrowRegroup = id
  PreArrowId . f = f
  g . PreArrowId = g
  g . f = PreArrowCompo f g

instance PreArrow k => Cartesian (RePreArrow k) where
  type PairObjects (RePreArrow k) α β = PairObjects k α β
  type UnitObject (RePreArrow k) = UnitObject k
  swap = PreArrowSwap
  attachUnit = PreArrowAttachUnit
  detachUnit = PreArrowDetachUnit
  regroup = PreArrowRegroup
  regroup' = PreArrowRegroup_
  
instance PreArrow k => Morphism (RePreArrow k) where
  (***) = PreArrowPar

instance PreArrow k => PreArrow (RePreArrow k) where
  (&&&) = PreArrowFanout
  terminal = PreArrowTerminal
  fst = PreArrowFst
  snd = PreArrowSnd

instance (HasAgent k, PreArrow k) => HasAgent (RePreArrow k) where
  type AgentVal (RePreArrow k) α ω = GenericAgent (RePreArrow k) α ω
  alg = genericAlg
  ($~) = genericAgentMap


instance PreArrow k => EnhancedCat (RePreArrow k) k where arr = RePreArrow




#ifdef GADTCPP
#  define REWELLPOINTED(C)                                       \
    REPREARROW(C);                                                \
    C##Const :: (Object k ν, ObjectPoint k α) => α -> Re##C k ν α
#else
#  define REWELLPOINTED(C) \
    ReWellPointed :: k α β -> ReWellPointed k α β; WellPointedId :: Object k α => ReWellPointed k α α; WellPointedCompo :: Object k β => ReWellPointed k α β -> ReWellPointed k β γ -> ReWellPointed k α γ; WellPointedSwap :: (ObjectPair k α β, ObjectPair k β α) => ReWellPointed k (α,β) (β,α); WellPointedAttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => ReWellPointed k α (α,u); WellPointedDetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u) => ReWellPointed k (α,u) α; WellPointedRegroup :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => ReWellPointed k (α,(β,γ)) ((α,β),γ); WellPointedRegroup_ :: ( ObjectPair k α β, ObjectPair k β γ , ObjectPair k α (β,γ), ObjectPair k (α,β) γ ) => ReWellPointed k ((α,β),γ) (α,(β,γ)); WellPointedPar :: (ObjectPair k α γ, ObjectPair k β δ) => ReWellPointed k α β -> ReWellPointed k γ δ -> ReWellPointed k (α,γ) (β,δ); WellPointedFanout :: (Object k α, ObjectPair k β γ) => ReWellPointed k α β -> ReWellPointed k α γ -> ReWellPointed k α (β,γ); WellPointedTerminal :: Object k α => ReWellPointed k α (UnitObject k); WellPointedFst :: ObjectPair k α β => ReWellPointed k (α,β) α; WellPointedSnd :: ObjectPair k α β => ReWellPointed k (α,β) β; WellPointedConst :: (Object k ν, ObjectPoint k α) => α -> ReWellPointed k ν α
#endif
data ReWellPointed (k :: * -> * -> *) (α :: *) (β :: *) where
    REWELLPOINTED(WellPointed)


#define WELLPOINTEDCOMPO  \
  Const c . _ = const c;   \
  PREARROWCOMPO

instance WellPointed k => Category (ReWellPointed k) where
  type Object (ReWellPointed k) a = Object k a
  id = WellPointedId
  WellPointedConst c . _ = const c
  WellPointedTerminal . _ = terminal
  WellPointedFst . (f`WellPointedFanout`_) = f
  WellPointedSnd . (_`WellPointedFanout`g) = g
  WellPointedFst . (f`WellPointedPar`_) = f . fst
  WellPointedSnd . (_`WellPointedPar`g) = g . snd
  (f`WellPointedPar`g) . (h`WellPointedPar`i) = f.h *** g.i
  WellPointedSwap . WellPointedSwap = id
  WellPointedRegroup . WellPointedRegroup_ = id
  WellPointedRegroup_ . WellPointedRegroup = id
  WellPointedId . f = f
  g . WellPointedId = g
  g . f = WellPointedCompo f g

instance WellPointed k => Cartesian (ReWellPointed k) where
  type PairObjects (ReWellPointed k) α β = PairObjects k α β
  type UnitObject (ReWellPointed k) = UnitObject k
  swap = WellPointedSwap
  attachUnit = WellPointedAttachUnit
  detachUnit = WellPointedDetachUnit
  regroup = WellPointedRegroup
  regroup' = WellPointedRegroup_
  
instance WellPointed k => Morphism (ReWellPointed k) where
  -- Const c *** Const d = const (c,d)
  -- f@Terminal *** g@Terminal = tpar f g
  --  where tpar :: ∀ k α β . (WellPointed k, ObjectPair k α β)
  --           => ReWellPointed k α (UnitObject k) -> ReWellPointed k β (UnitObject k)
  --               -> ReWellPointed k (α,β) (UnitObject k, UnitObject k)
  --        tpar Terminal Terminal = const (u, u)
  --         where Tagged u = unit :: CatTagged k (UnitObject k)
  f *** g = WellPointedPar f g

instance WellPointed k => PreArrow (ReWellPointed k) where
  -- Const c &&& Const d = const (c,d)
  f &&& g = WellPointedFanout f g
  terminal = WellPointedTerminal
  fst = WellPointedFst
  snd = WellPointedSnd

instance WellPointed k => WellPointed (ReWellPointed k) where
  type PointObject (ReWellPointed k) α = PointObject k α
  const = WellPointedConst
  unit = u
   where u :: ∀ k . WellPointed k => CatTagged (ReWellPointed k) (UnitObject k)
         u = Tagged u' where Tagged u' = unit :: CatTagged k (UnitObject k)
  
  
instance (HasAgent k, WellPointed k) => HasAgent (ReWellPointed k) where
  type AgentVal (ReWellPointed k) α ω = GenericAgent (ReWellPointed k) α ω
  alg = genericAlg
  ($~) = genericAgentMap


instance WellPointed k => EnhancedCat (ReWellPointed k) k where arr = ReWellPointed


