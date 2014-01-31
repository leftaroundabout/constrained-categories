
{-# LANGUAGE MultiParamTypeClasses       #-}
{-# LANGUAGE FlexibleInstances           #-}
-- {-# LANGUAGE Arrows                      #-}
{-# LANGUAGE RebindableSyntax            #-}

import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask
  
import Control.Arrow.Constrained
import Data.Traversable.Constrained

import qualified Data.Set as Set
import Data.Set (Set)
  

import Data.Monoid

main :: IO ()
main = do
   putStr "Functor:  " 
   print $ fmap (ordd (^2)) $ Set.fromList [-3 .. 4]
   
   putStr "Monoidal: "
   print $ fzipWith (ordd $ uncurry (*)) $ (Set.fromList [1..4], Set.fromList [0, 2 .. 6])
   
   putStr "Monad:    "
   print $ join . fmap (ordd $ \x -> Set.fromList [x, 2*x])
         . join . fmap (ordd $ \x -> Set.fromList [x^2, x^2+1/x .. x^2+1]) 
                . fmap (ordd (2**)) 
                    $ Set.fromList [0..2]
   
   putStr "Kleisli:  "
   let k :: Kleisli Set Preorder Double Char
       k = arr show >>> Kleisli (arr Set.fromList)
   print $ runKleisli k $ pi
   
   putStr "Traverse: "
   print $ inOrd (traverse $ ordd Set.fromList) $ (\s -> [s, s>>=show.fromEnum]) "seq"
   

type Preorder = ConstrainedCategory (->) Ord

ordd :: (Ord a, Ord b) => (a -> b) -> Preorder a b
ordd = constrained

inOrd :: Preorder a b -> Preorder a b
inOrd = id

instance Functor Set Preorder Preorder where
  fmap = constrainedFmap Set.map

instance Monoidal Set Preorder Preorder where
  pureUnit = arr Set.singleton
  fzipWith = constrainedFZipWith $
       \zp (s1,s2) -> Set.unions [ Set.map (curry zp a) s2 | a <- Set.toList s1 ]
  
instance Applicative Set Preorder Preorder where
  pure = arr Set.singleton

instance Monad Set Preorder where
  join = arr $ Set.unions . Set.toList
  

