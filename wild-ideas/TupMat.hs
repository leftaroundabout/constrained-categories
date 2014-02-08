class TupMat t where
  type TupleComps t :: *
  fromTups :: TupleComps t -> t

-- instance TupMat Double where
--   type TupleComps t = Double
--   fromTups = id
-- instance TupMat (s,t) where
--   type TupleComps (s,t) = (s,t)
--   fromTups = id
-- 
newtype Row v = R v deriving (AdditiveGroup)
instance (VectorSpace v) => VectorSpace (Row v) where 
  type Scalar(Row v)=Scalar v

instance ( CountablySpanned u, CountablySpanned v
         , Scalar u~k, Scalar v~k
instance ( CountablySpanned u, CountablySpanned v, CountablySpanned w
         , Scalar u~k, Scalar v~k, Scalar w~k, TupMat (Lin k w u), TupMat (Lin k w v) 
         ) => TupMat (Lin k w (u,v)) where
  type TupleComps (Lin k w (u,v)) = (TupleComps(Lin k w u), TupleComps(Lin k w v))
  fromTups (f,g) = Lin . linear $ \w -> (f$w, g$w)
  