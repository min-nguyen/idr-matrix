module recschemes

import Data.Vect as V

Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

interface Steppable t (f : Type -> Type) | t where
    project : Coalgebra f t

data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> Type where
    MultMat : {j' : Nat} -> 
              Vect m (Vect n Double) -> Matrix n j j' -> Matrix m n j
    BaseMat : {j' : Nat} -> 
              Matrix m n j

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> a  -> Type where
    MultMatF : {j' : Nat} -> 
               Vect m (Vect n Double) -> Matrix n j j' -> a -> MatrixF m n j a
    BaseMatF : {j' : Nat} -> 
               MatrixF m n j a

implementation Functor (MatrixF m n j) where
    map f (MultMatF {j'} weights next a) = MultMatF weights next (f a)
    map f (BaseMatF {j'=j'}) = BaseMatF {j'=j'}

implementation Steppable (Matrix m n j) (MatrixF m n j) where
    project (MultMat {j'=j'} w next) 
        = MultMatF {j'=j'} w next (MultMat {j'=j'} w next) 
    project (BaseMat {j'=j'})  
        = BaseMatF {j'=j'}

cata' : (alg : (MatrixF m n j (Matrix n j j') -> Matrix n j j')) 
        -> Matrix m n j -> Matrix n j j'
cata' alg = c
    where c x = alg . map (cata' alg) . project $ x








