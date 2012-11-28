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
-- Constraint-enabled version of the "Control.Applicative" module.


{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Applicative.Constrained where


import Control.Functor.Constrained

import GHC.Exts


-- | Constrained applicative functor class, analog to 'CFunctor'. The definition
-- is a little different from 'Applicative', emphasising 'liftA2' over
-- '<*>'. The rationale: even when both @a@ and @b@ fulfill the 'CFunctor'
-- constraint, @a->b@ may not, yet 'cliftA2' works, making it a
-- useful 'CApplicative' instance. This, in a way, splits off a more general
-- type class, \"@'CFunctor' f => CLiftA2 f@\", with @CLiftA2 f => 'CApplicative' f@.

type CAppFunctorCtxt f a = (CFunctorCtxt f a, CApplicativeCtxt f a)

class CFunctor f => CApplicative f where
  type CApplicativeCtxt f a :: Constraint
  type CApplicativeCtxt f a = ()

  cpure :: CAppFunctorCtxt f a
     => a -> f a
  
  -- | Note the absence of @CFunctorCtxt (a->b)@
  cliftA2 :: ( CAppFunctorCtxt f a
             , CAppFunctorCtxt f b
             , CAppFunctorCtxt f c )
     => (a->b->c) -> f a -> f b -> f c
  (*>#) :: ( CAppFunctorCtxt f a
           , CAppFunctorCtxt f b )
     => f a -> f b -> f b
  (*>#) = cliftA2 $ const id
  (<*#) :: ( CAppFunctorCtxt f a
           , CAppFunctorCtxt f b )
     => f a -> f b -> f a
  (<*#) = cliftA2 const
  
  

(<*>#) :: ( CApplicative f
          , CAppFunctorCtxt f a
          , CAppFunctorCtxt f b
          , CAppFunctorCtxt f(a->b) )
     => f (a->b) -> f a -> f b
(<*>#) = cliftA2 ($)  
(<**>#) :: ( CApplicative f
           , CAppFunctorCtxt f a
           , CAppFunctorCtxt f b
           , CAppFunctorCtxt f(a->b) )
     => f a -> f(a->b) -> f b
(<**>#) = cliftA2 (flip($)) 


-- | 'cliftA3', unlike 'cliftA2', now needs 'CFunctorCtxt' of a function type.
-- This could be avoided by making it a method of 'CApplicative', however
-- no default definition could be given, making the implementation quite a bit
-- more cumbersome.
cliftA3 :: ( CApplicative f
           , CAppFunctorCtxt f a
           , CAppFunctorCtxt f b
           , CAppFunctorCtxt f c
           , CAppFunctorCtxt f(c->d)
           , CAppFunctorCtxt f d     )
     => (a->b->c->d) -> f a->f b->f c->f d
cliftA3 g a b c = cliftA2 g a b <*># c



type CAltFunctorCtxt f a = (CAppFunctorCtxt f a, CAlternativeCtxt f a)

class CApplicative f => CAlternative f where
  type CAlternativeCtxt f a :: Constraint
  type CAlternativeCtxt f a = ()
  
  cempty :: CAltFunctorCtxt f a => f a
  
  (<|>#) :: CAltFunctorCtxt f a => f a -> f a -> f a
  
  csome :: (CAltFunctorCtxt f a, CAltFunctorCtxt f [a])
     => f a -> f[a]
  cmany :: (CAltFunctorCtxt f a, CAltFunctorCtxt f [a])
     => f a -> f[a]
  
