
-- |
-- Copyright   :  (c) 2013 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) sagemuej $ smail.uni-koeln.de
-- 
--   Simple implementation of Vect /k/, the category of vector spaces
--   over the field /k/, with linear maps as morphisms. Furthermore, the
--   category of the same vector spaces, but with more general
--   /affine/ mappings.


{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleInstances      #-} 
{-# LANGUAGE UndecidableInstances   #-} 
{-# LANGUAGE MultiParamTypeClasses  #-} 
{-# LANGUAGE FunctionalDependencies #-} 
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE ConstraintKinds        #-} 
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE TupleSections          #-} 
{-# LANGUAGE GADTs                  #-} 
{-# LANGUAGE ScopedTypeVariables    #-} 
{-# LANGUAGE PackageImports         #-}




import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import Control.Arrow.Constrained

import Data.Monoid

import "vector-space" Data.VectorSpace
import Data.Basis
import Data.MemoTrie
import Data.LinearMap

import Data.Void

import "hmatrix" Numeric.LinearAlgebra hiding ((<.>), (<>))

type ℝ = Double
type ℝ² = (ℝ, ℝ)
type ℝ⁴ = (ℝ², ℝ²)
type GLℝ² = Lin ℝ ℝ² ℝ²

rot :: ℝ -> GLℝ²
rot ϑ = fromMatList [ cos ϑ, -sin ϑ
                    , sin ϑ,  cos ϑ ]

main :: IO ()
main = do
   putStr "\n45° ↺  (1,0):  "
   print $ rot (pi/4) $ (1, 0) 
   
   putStr "\n\\v → v + v  :  "
   print . asMatrix $ ( alg (\v -> v ^+^ v )
                                       :: GLℝ² )
   
   putStr "\n\\v → v ⊕ v  :  "
   print . asMatrix $ ( alg1to2 (\v -> (v,v) )
                                       :: Lin ℝ ℝ² ℝ⁴ )
   
   putStr "\n\\(v⊕w) → v + 2w:  "
   print . asMatrix $ ( alg2to1 (\v w -> v ^+^ 2 *^ w )
                                       :: Lin ℝ ℝ⁴ ℝ² )
   
   putStr "\n\\(v⊕w) → w ⊕ (90°↺v):  "
   print . asMatrix $ ( alg2to2 (\v w -> (w, rot (pi/2) $~ v) )
                                       :: Lin ℝ ℝ⁴ ℝ⁴ )
   
   -- Note that alg expressions won't typecheck if they do not correctly
   -- define a morphism of the desired category. For instance, addition
   -- of a constant is not a linear operation (it's an affine one). Something 
   -- like the following will thus rightly fail to even compile:
-- putStr "\n\\v → (1,0) + v:  "
-- print . asMatrix $ ( alg (\v -> (1,0) ^+^ v ) :: Lin ℝ ℝ² ℝ² )
   -- (compare this to @linear $ \v -> (1,0) ^+^ v@ from the vector-space library,
   -- which happily compiles, yielding wrong results.)
   -- 
   -- On the other hand, going explicitly to affine morphisms does the trick:
   putStr "\n\\v → (1,0) + v:  "
   print $ ( alg (\v -> point(1,0) ^+^ v ) :: Affin ℝ ℝ² ℝ² )
   
   
   

type CountablySpanned v = (HasBasis v, HasTrie (Basis v))
type FinitelySpanned v = (CountablySpanned v, InnerSpace v, Enum (Basis v), Bounded (Basis v))

data Lin k u v where
  Lin :: (CountablySpanned u, VectorSpace v, Scalar u ~ k, Scalar v ~ k) 
          => u:-*v -> Lin k u v

data Affin k u v = Lin k u v :->+ v



instance (CountablySpanned u, VectorSpace v, Scalar u ~ k, Scalar v ~ k)
                                             => AdditiveGroup (Lin k u v) where
  zeroV = Lin zeroV
  Lin f ^+^ Lin g = Lin $ f ^+^ g
  negateV (Lin f) = Lin $ negateV f
instance (AdditiveGroup (Lin k u v)) => VectorSpace (Lin k u v) where
  type Scalar (Lin k u v) = k
  a *^ Lin f = Lin $ a *^ f
  
instance (CountablySpanned u, VectorSpace v, Scalar u ~ k, Scalar v ~ k)
                          => AdditiveGroup (Affin k u v) where
  zeroV = zeroV :->+ zeroV
  (f :->+ u) ^+^ (g :->+ v) = (f ^+^ g) :->+ (u ^+^ v)
  negateV (f :->+ v) = negateV f :->+ negateV v
instance (CountablySpanned u, VectorSpace v, Scalar u ~ k, Scalar v ~ k) 
                         => VectorSpace (Affin k u v) where
  type Scalar (Affin k u v) = k
  a *^ (f :->+ v) = (a *^ f) :->+ (a *^ v)


instance ( InnerSpace u, FinitelySpanned u, Scalar u ~ k 
         , CountablySpanned v, Scalar v ~ k
         )      => HasBasis (Lin k u v) where
  type Basis (Lin k u v) = (Basis v, Basis u)
  basisValue (i,j) = Lin . linear $ (basisValue i ^*) . (basisValue j <.>)
  decompose (Lin f) = [ ((i,j), a) 
                      | j<-[minBound .. maxBound]
                      , (i,a) <- decompose (f `atBasis` j) ]
  decompose' (Lin f) (i,j) = decompose' (f `atBasis` j) i

instance ( HasBasis (Lin k u v)
         , CountablySpanned u, HasBasis v, Scalar u ~ k, Scalar v ~ k
         ) => HasBasis (Affin k u v) where
  type Basis (Affin k u v) = Either (Basis (Lin k u v)) (Basis v) 
  basisValue (Left i) = basisValue i :->+ zeroV
  basisValue (Right j) = zeroV :->+ basisValue j
  decompose (f :->+ v) = decompose (f,v)
  decompose' (f :->+ v) = decompose' (f,v)
  

instance Category (Lin k) where
  type Object (Lin k) v = (CountablySpanned v, Scalar v ~ k)
  id = Lin idL
  Lin f . Lin g = Lin $ f *.* g
instance Category (Affin k) where
  type Object (Affin k) v = Object (Lin k) v
  id = id :->+ zeroV
  (f :->+ u) . (g :->+ v) = (f . g) :->+ ((f $ v) ^+^ u)

fromLin :: ( EnhancedCat q c, Object q a, Object c a, Object q b, Object c b
           , c a b ~ Lin k a b)      => c a b -> q a b
fromLin = arr
instance EnhancedCat (Affin k) (Lin k) where
  arr f = f :->+ zeroV

instance EnhancedCat (->) (Lin k) where
  Lin f `arr` v = lapply f v
instance EnhancedCat (->) (Affin k) where
  f :->+ u `arr` v = (f $ v) ^+^ u

instance Cartesian (Lin k) where
  type UnitObject (Lin k) = ZeroDim k
  type PairObjects (Lin k) u v = (CountablySpanned (u,v), Scalar (u,v) ~ k)
  swap = Lin . linear $ \(a,b) -> (b,a)
  attachUnit = Lin . linear $ \a -> (a, Origin)
  detachUnit = Lin . linear $ \(a, Origin) -> a
  regroup = Lin . linear $ \(a,(b,c)) -> ((a,b),c)

instance Cartesian (Affin k) where
  type UnitObject (Affin k) = ZeroDim k
  type PairObjects (Affin k) u v = PairObjects (Lin k) u v
  swap = fromLin swap; regroup = fromLin regroup
  attachUnit = fromLin attachUnit; detachUnit = fromLin detachUnit


instance Morphism (Lin k) where
  first (Lin l) = Lin $ firstL l
  second l = Lin . linear $ \(u,v) -> (u, l $ v)
  m *** n = Lin . linear $ (m$) *** (n$)
instance PreArrow (Lin k) where
  m &&& n = Lin . linear $ (m$) &&& (n$)
  terminal = Lin . linear $ const Origin
  fst = Lin $ linear fst; snd = Lin $ linear snd

instance Morphism (Affin k) where
  first (f :->+ v) = first f :->+ (v, zeroV)
  second (f :->+ v) = second f :->+ (zeroV, v)
  (f :->+ u) *** (g :->+ v) = (f *** g) :->+ (u,v)
instance PreArrow (Affin k) where
  (f :->+ u) &&& (g :->+ v) = (f &&& g) :->+ (u,v)
  terminal = fromLin terminal
  fst = fromLin fst; snd = fromLin snd
instance Curry (Affin k) where
  type MorphObjects (Affin k) u v = FinitelySpanned u
  curry (f :->+ v) = Lin (linear $ \u -> zeroV :->+ (f $ (u,zeroV)) ) :->+ (zeroV :->+ v)
  uncurry (f :->+ (g :->+ u)) 
     = Lin (linear $ \(v,w) -> let (h :->+ x) = f $ v in (h $ w) ^+^ x ) :->+ u
instance WellPointed (Affin k) where
  globalElement x = zeroV :->+ x
  const x = zeroV :->+ x
  unit _ = Origin
  
  

instance HasProxy (Lin k) where
  alg = genericAlg
  ($~) = genericProxyMap

instance CartesianProxy (Lin k) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2

instance ( Object (Lin k) a, Object (Lin k) b
         ) => AdditiveGroup (GenericProxy (Lin k) a b) where
  zeroV = Lin (linear $ \Origin -> zeroV) $~ genericUnit
  negateV v = Lin (linear negateV) $~ v
  (^+^) = genericProxyCombine . Lin . linear $ uncurry (^+^)

instance ( Object (Lin k) a, Object (Lin k) b
         ) => VectorSpace (GenericProxy (Lin k) a b) where
  type Scalar (GenericProxy (Lin k) a b) = k
  x*^v = Lin (linear $ (x*^)) $~ v


instance HasProxy (Affin k) where
  alg = genericAlg
  ($~) = genericProxyMap

instance CartesianProxy (Affin k) where
  alg1to2 = genericAlg1to2
  alg2to1 = genericAlg2to1
  alg2to2 = genericAlg2to2

instance PointProxy (GenericProxy (Affin k)) (Affin k) u v where
  point = genericPoint
  
instance ( Object (Affin k) a, Object (Affin k) b
         ) => AdditiveGroup (GenericProxy (Affin k) a b) where
  zeroV = point zeroV
  negateV v = Lin (linear negateV) :->+ zeroV $~ v
  (^+^) = genericProxyCombine . (:->+ zeroV) . Lin . linear $ uncurry (^+^)

instance ( Object (Affin k) a, Object (Affin k) b
         ) => VectorSpace (GenericProxy (Affin k) a b) where
  type Scalar (GenericProxy (Affin k) a b) = k
  x*^v = Lin (linear $ (x*^)) :->+ zeroV $~ v
  



asMatrix :: (FinitelySpanned u, FinitelySpanned v, Element k)
      => Lin k u v -> Matrix k
asMatrix (Lin f) 
  = fromLists [ map snd . decompose $ atBasis f i | i<-[minBound .. maxBound] ]



fromMatList :: forall m u v k 
       . ( EnhancedCat m (Lin k), Object m u, Object m v
         , FinitelySpanned u, FinitelySpanned v
         , Numeric.LinearAlgebra.Product k, Scalar u ~ k, Scalar v ~ k )
      => [k] -> m u v
fromMatList = arr . fromMatrix . (dv><du)
 where dv = fromEnum (maxBound :: Basis v) - fromEnum (minBound :: Basis v) + 1
       du = fromEnum (maxBound :: Basis u) - fromEnum (minBound :: Basis u) + 1
       fromMatrix m = Lin . linear $ 
             \u -> let v =  m `mXv` (fromList . map snd $ decompose u)
                   in recompose . zip [minBound .. maxBound] $ toList v

instance (Show k, FinitelySpanned u, FinitelySpanned v, Element k)
         => Show (Lin k u v) where
  show f = "fromMatrix " ++ show (asMatrix f)
instance (Show v, Show k, FinitelySpanned u, FinitelySpanned v, Element k)
         => Show (Affin k u v) where
  show (f :->+ v) = "(" ++ show f ++ ") :->+ " ++ show v

  


 




data ZeroDim k = Origin
instance AdditiveGroup (ZeroDim k) where 
  zeroV = Origin
  (^+^) = (<>)
  negateV = id
instance VectorSpace (ZeroDim k) where
  type Scalar (ZeroDim k) = k
  _ *^ Origin = Origin
instance HasBasis (ZeroDim k) where
  type Basis (ZeroDim k) = Void
  basisValue = absurd
  decompose Origin = []
  decompose' Origin = absurd
instance Monoid (ZeroDim k) where
  mempty = Origin
  mappend Origin Origin = Origin

instance Enum Void where
  fromEnum = absurd
  toEnum n = ( toEnum 1 :: () ) `seq` undefined

instance (Enum a, Bounded a, Enum b, Bounded b)
    => Enum (Either a b) where
  fromEnum (Left a) = fromEnum a
  fromEnum e@(Right b) = fromEnum b + fromEnum ma + 1
   where ma = maxBound
         _ = Left ma `asTypeOf` e
  toEnum n = result
   where result
           | n < ca     = Left $ toEnum n
           | otherwise  = Right . toEnum $ n - ca
         ma = maxBound
         _ = Left ma `asTypeOf` result
         ca = fromEnum ma + 1

instance (Bounded a, Bounded b) => Bounded (Either a b) where
  minBound = Left minBound
  maxBound = Right maxBound
   
  

  
