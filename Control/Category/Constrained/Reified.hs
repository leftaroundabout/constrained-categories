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

{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ViewPatterns          #-}

module Control.Category.Constrained.Reified (
      -- * Reified versions of the category classes
         ReCategory
       , ReCartesian
       , ReMorphism
       , RePreArrow
       -- , ReWellPointed (..)
      -- * Pattern synonyms
      -- ** Category
       , pattern Specific, pattern Id, pattern (:<<<), pattern (:>>>)
      -- ** Cartesian
       , pattern Swap
       , pattern AttachUnit, pattern DetachUnit
       , pattern Regroup, pattern Regroup'
      -- ** Morphism
       , pattern (:***)
      -- ** Pre-arrow
       , pattern (:&&&), pattern Fst, pattern Snd, pattern Terminal
       ) where


import Prelude ()
import GHC.Exts (Constraint)

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

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





infixr 1 :>>>, :<<<

-- GHC-invoked CPP can't seem able to do token pasting, so invoke this manually.
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
#  define RECATEGORY(catl)   \
    ReCategory :: k α β -> ReCategory k α β; CategoryId :: Object k α => ReCategory k α α; CategoryCompo :: Object k β => ReCategory k α β -> ReCategory k β γ -> ReCategory k α γ
#endif
data ReCategory (k :: * -> * -> *) (α :: *) (β :: *) where
    RECATEGORY(Category)

#define CATEGORYCOMPO \
  Id . f = f;          \
  g . Id = g

instance Category k => Category (ReCategory k) where
  type Object (ReCategory k) α = Object k α
  id = Id
  CATEGORYCOMPO
  g . f = CategoryCompo f g

data IdPattern k α β where
    IsId :: Object k α => IdPattern k α α
    NotId :: IdPattern k α β
data CompoPattern k α β where
    IsCompo :: Object k β
         => k α β -> k β γ -> CompoPattern k α γ
    NotCompo :: CompoPattern k α β
class Category k => CRCategory k where
  type SpecificCat k :: * -> * -> *
  fromSpecific :: SpecificCat k α β -> k α β
  match_concrete :: k α β -> Maybe (SpecificCat k α β)
  match_id :: k α β -> IdPattern k α β
  match_compose :: k α β -> CompoPattern k α β

instance Category k => CRCategory (ReCategory k) where
  type SpecificCat (ReCategory k) = k
  fromSpecific = ReCategory
  match_concrete (ReCategory f) = Just f
  match_concrete _ = Nothing
  match_id CategoryId = IsId
  match_id _ = NotId
  match_compose (CategoryCompo f g) = IsCompo f g
  match_compose _ = NotCompo

pattern Specific f <- (match_concrete -> Just f) where
  Specific f = fromSpecific f
pattern Id <- (match_id -> IsId) where
  Id = id
pattern g:<<<f <- (match_compose -> IsCompo f g)
pattern f:>>>g <- (match_compose -> IsCompo f g)
  
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
#  define RECARTESIAN(catl) \
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
  CARTESIANCOMPO
  g . f = CartesianCompo f g

instance Cartesian k => Cartesian (ReCartesian k) where
  type PairObjects (ReCartesian k) α β = PairObjects k α β
  type UnitObject (ReCartesian k) = UnitObject k
  swap = CartesianSwap
  attachUnit = CartesianAttachUnit
  detachUnit = CartesianDetachUnit
  regroup = CartesianRegroup
  regroup' = CartesianRegroup_
  
instance Cartesian k => CRCategory (ReCartesian k) where
  type SpecificCat (ReCartesian k) = k
  fromSpecific = ReCartesian
  match_concrete (ReCartesian f) = Just f
  match_concrete _ = Nothing
  match_id (CartesianId) = IsId
  match_id _ = NotId
  match_compose (CartesianCompo f g) = IsCompo f g
  match_compose _ = NotCompo

data SwapPattern k α β where
    IsSwap :: (ObjectPair k α β, ObjectPair k β α)
                 => SwapPattern k (α,β) (β,α)
    NotSwap :: SwapPattern k α β
data AttachUnitPattern k α β where
    IsAttachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u)
                 => AttachUnitPattern k α (α,u)
    NotAttachUnit :: AttachUnitPattern k α β
data DetachUnitPattern k α β where
    IsDetachUnit :: (Object k α, UnitObject k ~ u, ObjectPair k α u)
                 => DetachUnitPattern k (α,u) α
    NotDetachUnit :: DetachUnitPattern k α β
data RegroupPattern k α β where
    IsRegroup :: ( ObjectPair k α β, ObjectPair k β γ
                 , ObjectPair k α (β,γ), ObjectPair k (α,β) γ )
                 => RegroupPattern k (α,(β,γ)) ((α,β),γ)
    NotRegroup :: RegroupPattern k α β
data Regroup'Pattern k α β where
    IsRegroup' :: ( ObjectPair k α β, ObjectPair k β γ
                 , ObjectPair k α (β,γ), ObjectPair k (α,β) γ )
                 => Regroup'Pattern k ((α,β),γ) (α,(β,γ))
    NotRegroup' :: Regroup'Pattern k α β
class CRCategory k => CRCartesian k where
  match_swap :: k α β -> SwapPattern k α β
  match_attachUnit :: k α β -> AttachUnitPattern k α β
  match_detachUnit :: k α β -> DetachUnitPattern k α β
  match_regroup :: k α β -> RegroupPattern k α β
  match_regroup' :: k α β -> Regroup'Pattern k α β

instance Cartesian k => CRCartesian (ReCartesian k) where
  match_swap (CartesianSwap) = IsSwap
  match_swap _ = NotSwap
  match_attachUnit (CartesianAttachUnit) = IsAttachUnit
  match_attachUnit _ = NotAttachUnit
  match_detachUnit (CartesianDetachUnit) = IsDetachUnit
  match_detachUnit _ = NotDetachUnit
  match_regroup (CartesianRegroup) = IsRegroup
  match_regroup _ = NotRegroup
  match_regroup' (CartesianRegroup_) = IsRegroup'
  match_regroup' _ = NotRegroup'

pattern Swap <- (match_swap -> IsSwap)
pattern AttachUnit <- (match_attachUnit -> IsAttachUnit)
pattern DetachUnit <- (match_detachUnit -> IsDetachUnit)
pattern Regroup <- (match_regroup -> IsRegroup) 
pattern Regroup' <- (match_regroup' -> IsRegroup')
  
instance (HasAgent k, Cartesian k) => HasAgent (ReCartesian k) where
  type AgentVal (ReCartesian k) α ω = GenericAgent (ReCartesian k) α ω
  alg = genericAlg
  ($~) = genericAgentMap
  
  
instance Cartesian k => EnhancedCat (ReCartesian k) k where arr = ReCartesian


infixr 3 :***

#ifdef GADTCPP
#  define REMORPHISM(catl)                                \
    RECARTESIAN(catl);                                     \
    catl##Par :: (ObjectPair k α γ, ObjectPair k β δ)       \
              => Re##catl k α β -> Re##catl k γ δ -> Re##catl k (α,γ) (β,δ)
#else
#  define REMORPHISM(catl)  \
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
  MORPHISMCOMPO
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

instance Morphism k => CRCategory (ReMorphism k) where
  type SpecificCat (ReMorphism k) = k
  fromSpecific = ReMorphism
  match_concrete (ReMorphism f) = Just f
  match_concrete _ = Nothing
  match_id (MorphismId) = IsId
  match_id _ = NotId
  match_compose (MorphismCompo f g) = IsCompo f g
  match_compose _ = NotCompo

instance Morphism k => CRCartesian (ReMorphism k) where
  match_swap (MorphismSwap) = IsSwap
  match_swap _ = NotSwap
  match_attachUnit (MorphismAttachUnit) = IsAttachUnit
  match_attachUnit _ = NotAttachUnit
  match_detachUnit (MorphismDetachUnit) = IsDetachUnit
  match_detachUnit _ = NotDetachUnit
  match_regroup (MorphismRegroup) = IsRegroup
  match_regroup _ = NotRegroup
  match_regroup' (MorphismRegroup_) = IsRegroup'
  match_regroup' _ = NotRegroup'

data ParPattern k α β where
    IsPar :: (ObjectPair k α γ, ObjectPair k β δ)
         => k α β -> k γ δ -> ParPattern k (α,γ) (β,δ)
    NotPar :: ParPattern k α β
class CRCartesian k => CRMorphism k where
  match_par :: k α β -> ParPattern k α β

instance Morphism k => CRMorphism (ReMorphism k) where
  match_par (MorphismPar f g) = IsPar f g
  match_par _ = NotPar

pattern f:***g <- (match_par -> IsPar f g)
  
instance Morphism k => EnhancedCat (ReMorphism k) k where arr = ReMorphism




#ifdef GADTCPP
#  define REPREARROW(catl)                                          \
    REMORPHISM(catl);                                                \
    catl##Fanout :: (Object k α, ObjectPair k β γ)                    \
            => Re##catl k α β -> Re##catl k α γ -> Re##catl k α (β,γ); \
    catl##Terminal :: Object k α => Re##catl k α (UnitObject k);        \
    catl##Fst :: ObjectPair k α β => Re##catl k (α,β) α;                 \
    catl##Snd :: ObjectPair k α β => Re##catl k (α,β) β
#else
#  define REPREARROW(catl) \
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
  PREARROWCOMPO
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

instance PreArrow k => CRCategory (RePreArrow k) where
  type SpecificCat (RePreArrow k) = k
  fromSpecific = RePreArrow
  match_concrete (RePreArrow f) = Just f
  match_concrete _ = Nothing
  match_id (PreArrowId) = IsId
  match_id _ = NotId
  match_compose (PreArrowCompo f g) = IsCompo f g
  match_compose _ = NotCompo

instance PreArrow k => CRCartesian (RePreArrow k) where
  match_swap (PreArrowSwap) = IsSwap
  match_swap _ = NotSwap
  match_attachUnit (PreArrowAttachUnit) = IsAttachUnit
  match_attachUnit _ = NotAttachUnit
  match_detachUnit (PreArrowDetachUnit) = IsDetachUnit
  match_detachUnit _ = NotDetachUnit
  match_regroup (PreArrowRegroup) = IsRegroup
  match_regroup _ = NotRegroup
  match_regroup' (PreArrowRegroup_) = IsRegroup'
  match_regroup' _ = NotRegroup'

instance PreArrow k => CRMorphism (RePreArrow k) where
  match_par (PreArrowPar f g) = IsPar f g
  match_par _ = NotPar

data FanPattern k α β where
    IsFan :: (Object k α, ObjectPair k β γ)
         => k α β -> k α γ -> FanPattern k α (β,γ)
    NotFan :: FanPattern k α β
data FstPattern k α β where
    IsFst :: (ObjectPair k α β)
                 => FstPattern k (α,β) α
    NotFst :: FstPattern k α β
data SndPattern k α β where
    IsSnd :: (ObjectPair k α β)
                 => SndPattern k (α,β) β
    NotSnd :: SndPattern k α β
data TerminalPattern k α β where
    IsTerminal :: (Object k α, UnitObject k ~ u)
                 => TerminalPattern k α u
    NotTerminal :: TerminalPattern k α β
class CRCartesian k => CRPreArrow k where
  match_fan :: k α β -> FanPattern k α β
  match_fst :: k α β -> FstPattern k α β
  match_snd :: k α β -> SndPattern k α β
  match_terminal :: k α β -> TerminalPattern k α β

pattern f:&&&g <- (match_fan -> IsFan f g)
pattern Fst <- (match_fst -> IsFst)
pattern Snd <- (match_snd -> IsSnd)
pattern Terminal <- (match_terminal -> IsTerminal)
  
instance PreArrow k => CRPreArrow (RePreArrow k) where
  match_fan (PreArrowFanout f g) = IsFan f g
  match_fan _ = NotFan
  match_fst PreArrowFst = IsFst
  match_fst _ = NotFst
  match_snd PreArrowSnd = IsSnd
  match_snd _ = NotSnd
  match_terminal PreArrowTerminal = IsTerminal
  match_terminal _ = NotTerminal

instance PreArrow k => EnhancedCat (RePreArrow k) k where arr = RePreArrow

-- 
-- 
-- 
-- data ReWellPointed (k :: * -> * -> *) (α :: *) (β :: *) where
--     ReWellPointed :: k α β -> ReWellPointed k α β
--     ReWellPointedArr' :: RePreArrow (ReWellPointed k) α β -> ReWellPointed k α β
--     Const :: (Object k ν, ObjectPoint k α) => α -> ReWellPointed k ν α
-- 
-- instance Category k => Category (ReWellPointed k) where
--   type Object (ReWellPointed k) a = Object k a
--   
--   id = ReWellPointedArr' id
--   
--   Const α . _ = Const α
--   ReWellPointedArr' f . ReWellPointedArr' g = ReWellPointedArr' $ f . g
--   ReWellPointedArr' (RePreArrowMorph (ReMorphismCart (ReCartesianCat Id))) . g = g
--   f . ReWellPointedArr' (RePreArrowMorph (ReMorphismCart (ReCartesianCat Id))) = f
--   f . g = ReWellPointedArr' $ RePreArrow f . RePreArrow g
-- 
-- instance Cartesian k => Cartesian (ReWellPointed k) where
--   type PairObjects (ReWellPointed k) α β = PairObjects k α β
--   type UnitObject (ReWellPointed k) = UnitObject k
--   swap = ReWellPointedArr' swap
--   attachUnit = ReWellPointedArr' attachUnit
--   detachUnit = ReWellPointedArr' detachUnit
--   regroup = ReWellPointedArr' regroup
--   regroup' = ReWellPointedArr' regroup'
-- 
-- instance Morphism k => Morphism (ReWellPointed k) where
--   ReWellPointedArr' f *** ReWellPointedArr' g = ReWellPointedArr' $ f *** g
--   ReWellPointedArr' f *** g = ReWellPointedArr' $ f *** RePreArrow g
--   f *** ReWellPointedArr' g = ReWellPointedArr' $ RePreArrow f *** g
--   f *** g = ReWellPointedArr' $ RePreArrow f *** RePreArrow g
-- 
-- instance PreArrow k => PreArrow (ReWellPointed k) where
--   ReWellPointedArr' f &&& ReWellPointedArr' g = ReWellPointedArr' $ f &&& g
--   ReWellPointedArr' f &&& g = ReWellPointedArr' $ f &&& RePreArrow g
--   f &&& ReWellPointedArr' g = ReWellPointedArr' $ RePreArrow f &&& g
--   f &&& g = ReWellPointedArr' $ RePreArrow f &&& RePreArrow g
--   terminal = ReWellPointedArr' terminal
--   fst = ReWellPointedArr' fst
--   snd = ReWellPointedArr' snd
-- 
-- instance WellPointed k => WellPointed (ReWellPointed k) where
--   type PointObject (ReWellPointed k) α = PointObject k α
--   const = Const
--   unit = u
--    where u :: ∀ k . WellPointed k => CatTagged (ReWellPointed k) (UnitObject k)
--          u = Tagged u' where Tagged u' = unit :: CatTagged k (UnitObject k)
--   
-- instance CRCategory (ReWellPointed k) where
--   match_id (ReWellPointedArr' (RePreArrowMorph (ReMorphismCart (ReCartesianCat Id))))
--               = Just Id
--   match_id _ = Nothing
-- --  match_compose (ReMorphismCart (ReCartesianCat (f:>>>g)))
-- --                       = Just . _ $ f :>>> g
--   match_compose _ = Nothing
-- 
-- REENHANCE(ReWellPointed)
-- 
-- 
-- 
-- 
-- -- | @'EnhancedCat'' a k@ means that @k@ is a subcategory of @a@, so @k@-arrows also
-- --   work as @a@-arrows. This requires of course that all objects of @k@ are also
-- --   objects of @a@.
-- class (EnhancedCat a k) => EnhancedCat' a k where
--   arr' :: (Object k b, Object k c)
--          => k b c -> a b c
--   arr'Object :: ObjectWitness k α -> ObjectWitness a α
-- class (EnhancedCat' a k, Cartesian a, Cartesian k) => EnhancedCat'P a k where
--   arr'ObjPair :: ObjPairWitness k α β -> ObjPairWitness a α β
--   arr'UnitObj :: UnitObjWitness k u -> UnitObjWitness a u
-- instance (Category k) => EnhancedCat' k k where
--   arr' = id
--   arr'Object IsObject = IsObject

