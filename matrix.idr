module matrix 

import Data.Vect as V
%default total

data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> k -> Type where
  MultMat : {j : Nat} -> {j' : Nat} -> Vect m (Vect n Double) -> 
            k -> Matrix n j j' k -> Matrix m n j k
  BaseMat : {j : Nat} -> {j' : Nat} -> Matrix m n j k

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> r -> k -> Type where
  MultMatF : Vect m (Vect n Double) -> r -> k -> MatrixF m n j r k
  BaseMatF : MatrixF m n j r k

implementation Functor (MatrixF m n j r) where
  map f (MultMatF weights r k) = MultMatF weights r (f k)
  map f (BaseMatF) = BaseMatF 

getNatj' : Matrix m n j k -> Nat 
getNatj' (MultMat {j} {j'=j'} _ _ _) = j'
getNatj' (BaseMat {j} {j'=j'}) = j'

project : (x : Matrix m n j k) -> (MatrixF m n j k (Matrix n j (getNatj' x) k) )  
project (MultMat {j} {j'} w k nextMatrix)
 = MultMatF w k nextMatrix
project (BaseMat {j} {j'})
 = BaseMatF

algebra : {j : Nat} -> {j' : Nat} ->  
          MatrixF m n j k (Matrix n j j' k) ->
          Matrix n j j' k
algebra {j} {j'} (MultMatF weights k innerMatrix) 
  = innerMatrix
algebra {j} {j'} BaseMatF
  = BaseMat {j = j'} {j' = j'}

cata : ({m : Nat} -> {n : Nat} -> {j : Nat} -> {mat : Matrix m n j k} -> (MatrixF m n j k (Matrix n j (getNatj' mat) k) -> Matrix n j (getNatj' mat) k)) -> 
          (x : Matrix m n j k) -> 
          Matrix n j (getNatj' x) k
cata alg = c 
    where c x = alg . map (cata alg) . project $ x

