-- |
-- Copyright   :  (c) 2014 Justus Sagemüller
-- License     :  GPL v3 (see COPYING)
-- Maintainer  :  (@) jsag $ hvl.no
-- 
--   Using the constrained category of strict weak ordered types
--   to treat 'Data.Set' as a monad.

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
   let k :: Kleisli Set Ranking Double Char
       k = arr show >>> Kleisli (arr Set.fromList)
   print $ runKleisli k $ pi
   
   putStr "Traverse: "
   print $ inOrd (traverse $ ordd Set.fromList) $ (\s -> [s, s>>=show.fromEnum]) "seq"
   

type Ranking = ConstrainedCategory (->) Ord

ordd :: (Ord a, Ord b) => (a -> b) -> Ranking a b
ordd = constrained

inOrd :: Ranking a b -> Ranking a b
inOrd = id

instance Functor Set Ranking Ranking where
  fmap = constrainedFmap Set.map

instance Monoidal Set Ranking Ranking where
  pureUnit = arr Set.singleton
  fzipWith = constrainedFZipWith $
       \zp (s1,s2) -> Set.unions [ Set.map (curry zp a) s2 | a <- Set.toList s1 ]
  
instance Applicative Set Ranking Ranking where
  pure = arr Set.singleton

instance Monad Set Ranking where
  join = arr $ Set.unions . Set.toList
  

