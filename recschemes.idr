module recschemes

import Data.Vect as V


interface Nattable (f : Type) where
    nat : f -> Nat



Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a
-- CoalgebraM f a b = a -> b -- -> f a (nat a)

interface Recursive t (f : Type -> Type) | t where
    cata : Algebra f a -> t -> a

interface Steppable t (f : Type -> Type) | t where
    project : Coalgebra f t
      
interface Costeppable t (f : Type -> Type) | t where
    embed : Algebra f t

-- interface 
   -- SteppableM (a : Type) (b : Nat -> Type) (f : Type -> Type -> Type) where
    -- projectm : CoalgebraM f a b 

interface FunctorM (f : Type -> Type -> Type) where
    mapm : (g : a -> b) -> f a c -> f b c 

data Mu : (Type -> Type) -> Type where
    MuF : ({a : Type} -> Algebra f a -> a) -> Mu f

mutual
    implementation Functor f => Costeppable (Mu f) f where
          embed fm = MuF (\alg => alg (map (cata alg) fm))

    implementation Functor f => Recursive (Mu f) f where
          cata alg (MuF f) = f alg

data Matrix : (m : Nat) -> (n : Nat) -> Type where
    MultMat : {j : Nat} -> 
              Vect m (Vect n Double) -> Matrix n j -> Matrix m n
    BaseMat : {j : Nat} ->
              Matrix m n

data MatrixF : (m : Nat) -> (n : Nat) -> a -> b -> Type where
    MultMatF : {j : Nat} -> 
               Vect m (Vect n Double) -> a -> b -> MatrixF m n a b
    BaseMatF : {j : Nat} -> 
               MatrixF m n a b

CoalgebraM : (g : Nat -> Matrix n j) -> (f : MatrixF m n) -> 
             (a : Matrix m n) -> (b : g (nat a)) -> f a b

-- implementation Functor (MatrixF m n a) where
    -- map f (MultMatF {j'=j'} weights next b) = MultMatF {j'=j'} weights next (f b)
    -- map f (BaseMatF {j'=j'}) = BaseMatF {j'=j'}
implementation Nattable (Matrix m n) where
    nat (MultMat {j=j} w next) = j
    nat (BaseMat {j=j}) = j

implementation FunctorM (MatrixF m n) where
    mapm f (MultMatF {j=j} weights next b) = MultMatF {j=j} weights (f next) b 
    mapm f (BaseMatF {j=j}) = BaseMatF {j=j}

-- implementation SteppableM (Matrix m n) (b : Matrix n j) (MatrixF m n ) where
    -- projectm (MultMat {j} {j'=j'} w next) next' = MultMatF {j'=j'} w next' next  


-- implementation Steppable (Matrix m n j) (MatrixF m n j a) where
    -- project (MultMat {j} {j'=j'} w next) 
        -- = MultMatF {j'=j'} w next (MultMat {j} {j'=j'} w next) 
    -- project (BaseMat {j} {j'=j'}) 
        -- = BaseMatF {j'=j'}

-- implementation Costeppable (Matrix m n j) (MatrixF m n j) where
    -- embed (MultMatF {j'} w a r) = r
    -- embed (BaseMatF {j'=j'})  = BaseMat {j'=j'}

-- alg' : MatrixF m n j (Matrix n j j') -> Matrix n j j'
-- alg' (MultMatF {j'} weights a r) 

-- cata' : (alg : (MatrixF m n j (Matrix n j j') -> Matrix n j j')) 
        -- -> Matrix m n j -> Matrix n j j'
-- cata' alg = c
    -- where c x = alg . map (cata' alg) . project $ x








