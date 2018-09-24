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
      
interface Costeppable t (f : Type -> Type) | t where
    embed : Algebra f t

interface MFunctor (f : Type -> Type -> Type)

data Mu : (Type -> Type) -> Type where
    MuF : ({a : Type} -> Algebra f a -> a) -> Mu f

data Wu : (f : Nat -> Type) -> Type where
  WuF : {a : Nat} -> f a -> Wu f
    -- WuH : Wu f -> f a  

mutual
    implementation Functor f => Costeppable (Mu f) f where
          embed fm = MuF (\alg => alg (map (cata alg) fm))

    implementation Functor f => Recursive (Mu f) f where
          cata alg (MuF f) = f alg

data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> Type where
    MultMat : {j : Nat} -> {j' : Nat} -> 
              Vect m (Vect n Double) -> Matrix n j j' -> List Nat -> Matrix m n j
    BaseMat : {j : Nat} -> {j' : Nat} -> 
              Matrix m n j

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> a -> Type where
    MultMatF : {j' : Nat} -> 
               Vect m (Vect n Double) -> Matrix n j j' 
               -> List Nat -> a -> MatrixF m n j a
    BaseMatF : {j' : Nat} -> 
               MatrixF m n j a

-- implementation FunctorM 

implementation Functor (MatrixF m n j) where
    map f (MultMatF {j'} weights nextMat values a) 
        = MultMatF weights nextMat values (f a)
    map f (BaseMatF {j'=j'}) 
        = BaseMatF {j'=j'}

implementation Steppable (Matrix m n j) (MatrixF m n j) where
    project (MultMat {j} {j'=j'} weights nextMat values) 
        = MultMatF {j'=j'} weights nextMat values 
            (MultMat {j} {j'=j'} weights nextMat values) 
    project (BaseMat {j} {j'=j'})  
        = BaseMatF {j'=j'}

implementation Costeppable (Matrix m n j) (MatrixF m n j) where
    embed (MultMatF {j'} weights nextMat values a) = a 
    embed (BaseMatF {j'=j'})  = BaseMat {j'=j'}

-- alg' : MatrixF m n j (Matrix n j j') -> Matrix n j j'
-- alg' (MultMatF {j'} weights a r) 

cata' : (alg : (MatrixF m n j (Matrix n j j') -> Matrix n j j')) 
        -> Matrix m n j -> Matrix n j j'
cata' alg = c
    where c x = alg . map (cata' alg) . project $ x








