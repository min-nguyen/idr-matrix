module matrix 

import Data.Vect as V
-- %default total

data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> k -> Type where
  MultMat : {j : Nat} -> {j' : Nat} -> Vect m (Vect n Double) -> 
            k -> Matrix n j j' k -> Matrix m n j k
  BaseMat : {j : Nat} -> {j' : Nat} -> Matrix m n j k

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> k -> r -> Type where
  MultMatF : Vect m (Vect n Double) -> k -> r -> MatrixF m n j k r
  BaseMatF : MatrixF m n j k r

-- data MatrixP : 

implementation Functor (MatrixF m n j k) where
  map f (MultMatF weights k r) = MultMatF weights k (f r)
  map f (BaseMatF) = BaseMatF 

getNatj' : Matrix m n j k -> Nat 
getNatj' (MultMat {j} {j'=j'} _ _ _) = j'
getNatj' (BaseMat {j} {j'=j'}) = j'

project : (x : Matrix m n j k) -> (MatrixF m n j k (Matrix n j (getNatj' x) k))  
project (MultMat {j} {j'} w k nextMatrix)
 = MultMatF w k nextMatrix
project (BaseMat {j} {j'})
 = BaseMatF

cata : ({m : Nat} -> {n : Nat} -> {j : Nat} -> {mat : Matrix m n j k} -> (MatrixF m n j k (Matrix n j (getNatj' mat) k) -> k)) -> 
       (x : Matrix m n j k) -> k
cata alg x = --c
    let a = project x
        b = map (cata alg) a 
    in  ?hole --alg $ map (cata alg) a -- ?hole
    --where c x = alg . map (cata alg) . project $ x

