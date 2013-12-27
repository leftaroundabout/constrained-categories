
{-# LANGUAGE MultiParamTypeClasses       #-}
{-# LANGUAGE FlexibleInstances           #-}
-- {-# LANGUAGE Arrows                      #-}
{-# LANGUAGE RebindableSyntax            #-}

import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask
  
import Control.Arrow.Constrained

import Data.Set as Set


main :: IO ()
main = do
   putStr "Functor:  " 
   print $ fmap (ordd (^2)) $ fromList [-3 .. 4]
   putStr "Monoidal: "
   print $ fzipWith (ordd $ uncurry (*)) $ (fromList [1..4], fromList [0, 2 .. 6])
   putStr "Monad:    "
   print $ join . fmap (ordd $ \x -> fromList [x, 2*x])
         . join . fmap (ordd $ \x -> fromList [x^2, x^2+1/x .. x^2+1]) 
                . fmap (ordd (2**)) 
                    $ fromList [0..2]
   putStr "Kleisli:  "
   let k :: Kleisli Set Preorder Double Char
       k = arr show >>> Kleisli (arr fromList)
   print $ runKleisli k $ pi


type Preorder = ConstrainedCategory (->) Ord

ordd :: (Ord a, Ord b) => (a -> b) -> Preorder a b
ordd = constrained

instance Functor Set Preorder Preorder where
  fmap = constrainedFmap Set.map

instance Monoidal Set Preorder Preorder where
  pure = singleton
  fzipWith = constrainedFZipWith $
       \zp (s1,s2) -> unions [ Set.map (curry zp a) s2 | a <- toList s1 ]
  
instance Applicative Set Preorder Preorder where
  fpure = Set.singleton

instance Monad Set Preorder where
  return = constrained singleton
  join = constrained $ unions . toList
  

