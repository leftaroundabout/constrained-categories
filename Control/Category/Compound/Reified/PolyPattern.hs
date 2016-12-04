-- |
-- Module      :  Control.Category.Compound.Reified.PolyPattern
-- Copyright   :  (c) 2016 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemueller $ geo.uni-koeln.de
-- 
-- 
-- Pattern synonyms which allow you to deconstruct the various types
-- in "Control.Category.Constrained.Reified" in a uniform way.
-- 
-- This kind of polymorphic pattern (with @ViewPatterns@) doesn't
-- seem to work prior to GHC-7.10, so if you have base<4.8 these
-- synonyms aren't available.

{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ViewPatterns          #-}

module Control.Category.Compound.Reified.PolyPattern (
#if __GLASGOW_HASKELL__ > 708
      -- * Pattern synonyms (GHC>=7.10)
      -- ** Category
         pattern Specific, pattern Id, pattern (:<<<), pattern (:>>>)
      -- ** Cartesian
       , pattern Swap
       , pattern AttachUnit, pattern DetachUnit
       , pattern Regroup, pattern Regroup'
      -- ** Morphism
       , pattern (:***)
      -- ** Pre-arrow
       , pattern (:&&&), pattern Fst, pattern Snd, pattern Terminal
      -- ** Well-pointed
       , pattern Const,
#endif
      -- * Deconstruction-classes
         CRCategory(..), CRCartesian(..), CRMorphism(..), CRPreArrow(..), CRWellPointed(..)
       ) where


import Prelude ()
import GHC.Exts (Constraint)

import Control.Category.Compound.Prelude
import Control.Arrow.Compound
import Control.Category.Compound.Reified

import Data.Tagged

#if __GLASGOW_HASKELL__ > 708
infixr 1 :<<<, :>>>
#endif

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

#if __GLASGOW_HASKELL__ > 708
pattern Specific f <- (match_concrete -> Just f) where
  Specific f = fromSpecific f
pattern Id <- (match_id -> IsId) where
  Id = id
pattern g:<<<f <- (match_compose -> IsCompo f g)
pattern f:>>>g <- (match_compose -> IsCompo f g)
#endif
  
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

#if __GLASGOW_HASKELL__ > 708
pattern Swap <- (match_swap -> IsSwap)
pattern AttachUnit <- (match_attachUnit -> IsAttachUnit)
pattern DetachUnit <- (match_detachUnit -> IsDetachUnit)
pattern Regroup <- (match_regroup -> IsRegroup) 
pattern Regroup' <- (match_regroup' -> IsRegroup')
#endif
  
#if __GLASGOW_HASKELL__ > 708
infixr 3 :***
#endif

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

#if __GLASGOW_HASKELL__ > 708
pattern f:***g <- (match_par -> IsPar f g)
#endif
  

#if __GLASGOW_HASKELL__ > 708
infixr 3 :&&&
#endif


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

#if __GLASGOW_HASKELL__ > 708
pattern f:&&&g <- (match_fan -> IsFan f g)
pattern Fst <- (match_fst -> IsFst)
pattern Snd <- (match_snd -> IsSnd)
pattern Terminal <- (match_terminal -> IsTerminal)
#endif
  
instance PreArrow k => CRPreArrow (RePreArrow k) where
  match_fan (PreArrowFanout f g) = IsFan f g
  match_fan _ = NotFan
  match_fst PreArrowFst = IsFst
  match_fst _ = NotFst
  match_snd PreArrowSnd = IsSnd
  match_snd _ = NotSnd
  match_terminal PreArrowTerminal = IsTerminal
  match_terminal _ = NotTerminal


instance WellPointed k => CRCategory (ReWellPointed k) where
  type SpecificCat (ReWellPointed k) = k
  fromSpecific = ReWellPointed
  match_concrete (ReWellPointed f) = Just f
  match_concrete _ = Nothing
  match_id (WellPointedId) = IsId
  match_id _ = NotId
  match_compose (WellPointedCompo f g) = IsCompo f g
  match_compose _ = NotCompo

instance WellPointed k => CRCartesian (ReWellPointed k) where
  match_swap (WellPointedSwap) = IsSwap
  match_swap _ = NotSwap
  match_attachUnit (WellPointedAttachUnit) = IsAttachUnit
  match_attachUnit _ = NotAttachUnit
  match_detachUnit (WellPointedDetachUnit) = IsDetachUnit
  match_detachUnit _ = NotDetachUnit
  match_regroup (WellPointedRegroup) = IsRegroup
  match_regroup _ = NotRegroup
  match_regroup' (WellPointedRegroup_) = IsRegroup'
  match_regroup' _ = NotRegroup'

instance WellPointed k => CRMorphism (ReWellPointed k) where
  match_par (WellPointedPar f g) = IsPar f g
  match_par _ = NotPar
  
instance WellPointed k => CRPreArrow (ReWellPointed k) where
  match_fan (WellPointedFanout f g) = IsFan f g
  match_fan _ = NotFan
  match_fst WellPointedFst = IsFst
  match_fst _ = NotFst
  match_snd WellPointedSnd = IsSnd
  match_snd _ = NotSnd
  match_terminal WellPointedTerminal = IsTerminal
  match_terminal _ = NotTerminal

data ConstPattern k α β where
    IsConst :: (Object k α, Object k β)
                 => β -> ConstPattern k α β
    NotConst :: ConstPattern k α β
class CRPreArrow k => CRWellPointed k where
  match_const :: k α β -> ConstPattern k α β

#if __GLASGOW_HASKELL__ > 708
pattern Const c <- (match_const -> IsConst c)
#endif
  
instance WellPointed k => CRWellPointed (ReWellPointed k) where
  match_const (WellPointedConst c) = IsConst c
  match_const _ = NotConst



