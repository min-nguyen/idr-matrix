module recschemes

import Data.Vect as V

Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

interface Steppable t (f : Type -> Type) | t where
    project : Coalgebra f t

interface Nattable (t : Type) where
    nat : t -> Nat

mutual 
  data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> Type where
    MultMat : {j' : Nat} ->
              Vect m (Vect n Double) -> Matrix n j j' -> Matrix m n j
    BaseMat : {j' : Nat} -> 
              Matrix m n j
              
  implementation Nattable (Matrix m n j) where
      nat (MultMat {j} {j'=j'} _ _ ) = j'
      nat (BaseMat {j} {j'=j'}) = j'

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> (a : Type) -> Type where
    MultMatF : {x : Matrix m n j} -> 
               Vect m (Vect n Double) -> Matrix n j (nat x) -> a -> MatrixF m n j a
    BaseMatF : MatrixF m n j a

implementation Functor (MatrixF m n j) where
  map f (MultMatF {j'=j'} {x=x} weights next a) = MultMatF {j'=j'} {x=x} weights next (f a)
  map f (BaseMatF {j'=j'}) = BaseMatF {j'=j'}

implementation Steppable (Matrix m n j) (MatrixF m n j) where
    project (MultMat {j} {j'=j'} w next) 
        = MultMatF {j'=j'} w next (MultMat {j} {j'=j'} w next) 
    project (BaseMat {j} {j'=j'})  
        = BaseMatF {j'=j'}

cata' : (x : Matrix m n j) 
        (alg : (MatrixF m n j (Matrix n j (nat x)) -> Matrix n j (nat x))) 
        Matrix n j (nat x)
cata' x alg = c x
    where c z = alg . map (\y => cata' y alg) . project $ z








