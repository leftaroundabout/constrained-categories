{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleInstances    #-}

module Control.Functor.Constrained where


class CFunctor f where
  type CFunctorCtxt f a :: Constraint
  type CFunctorCtxt f a = ()
  cfmap :: (CFunctorCtxt f a, CFunctorCtxt f b)
     => (a -> b) -> f a -> f b

instance (Functor f) => CFunctor f where
  cfmap = fmap