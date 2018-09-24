module recschemes

import Data.Vect as V

Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

interface Recursive t (f : Type -> Type) | t where
    cata : Algebra f a -> t -> a

interface Steppable t (f : Type -> Type) | t where
    project : Coalgebra f t

interface Nattable (t : Type) where
    nat : t -> Nat

interface (Nattable t, Functor f) => Steppable' t (f : Type -> Type) (h : Nat -> Type) | t where
    project' : (t' : t) -> f (h (nat t'))
      
interface Costeppable t (f : Type -> Type) | t where
    embed : Algebra f t

data Mu : (Type -> Type) -> Type where
    MuF : ({a : Type} -> Algebra f a -> a) -> Mu f

mutual
    implementation Functor f => Costeppable (Mu f) f where
          embed fm = MuF (\alg => alg (map (cata alg) fm))

    implementation Functor f => Recursive (Mu f) f where
          cata alg (MuF f) = f alg

data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> Type where
    MultMat : {j : Nat} -> {j' : Nat} -> 
              Vect m (Vect n Double) -> Matrix n j j' -> Matrix m n j
    BaseMat : {j : Nat} -> {j' : Nat} -> 
              Matrix m n j

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> a -> Type where
    MultMatF : {j' : Nat} -> 
               Vect m (Vect n Double) -> Matrix n j j' -> a -> MatrixF m n j a
    BaseMatF : {j' : Nat} -> 
               MatrixF m n j a

implementation Nattable (Matrix m n j) where
    nat (MultMat {j} {j'=j'} _ _ ) = j'
    nat (BaseMat {j} {j'=j'}) = j'


getNatj' : Matrix m n j -> Nat
getNatj' (MultMat {j} {j'=j'} _ _ ) = j'
getNatj' (BaseMat {j} {j'=j'}) = j'


implementation Functor (MatrixF m n j) where
    map f (MultMatF {j'} weights next a) = MultMatF weights next (f a)
    map f (BaseMatF {j'=j'}) = BaseMatF {j'=j'}

implementation Steppable' (Matrix m n j) (MatrixF m n j) (Matrix n j) where
    project' (MultMat {j} {j'} w next) = MultMatF {j} {j'} w next next
    project' (BaseMat {j} {j'=j'})     = BaseMatF {j} {j'=j'} 

l : (x : Matrix m n j) -> MatrixF m n j (Matrix n j (nat x))
l x = project' x

implementation Steppable (Matrix m n j) (MatrixF m n j) where
    project (MultMat {j} {j'=j'} w next) 
        = MultMatF {j'=j'} w next (MultMat {j} {j'=j'} w next) 
    project (BaseMat {j} {j'=j'})  = BaseMatF {j'=j'}

implementation Costeppable (Matrix m n j) (MatrixF m n j) where
    embed (MultMatF {j'} w a r) = r
    embed (BaseMatF {j'=j'})  = BaseMat {j'=j'}

-- data Proj : (x : Matrix m n j) -> MatrixF m n j (Matrix n j (getNatj' x)) where
    

cata' : (x : Matrix m n j) 
        -> (alg : (MatrixF m n j (Matrix n j (nat x)) -> Matrix n j (nat x))) 
        -> Matrix n j (nat x)
cata' x alg = c x
    where c z = let p = project' z
                    q = map (\y => cata' y alg) p
                in  ?h 
                --p = map (cata' alg) . project' $ x
                -- in  ?h







