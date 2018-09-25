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

interface (Nattable (t m n j)) => 
    Steppable' (m : Nat) (n : Nat) (j : Nat) (t : Nat -> Nat -> Nat -> Type) 
               (f : Nat -> Nat -> Nat -> Type -> Type) where
    project' : Nattable (t m n j) => (t' : t m n j) -> f m n j (t n j (nat t'))
      
interface Costeppable t (f : Type -> Type) | t where
    embed : Algebra f t

data Mu : (Type -> Type) -> Type where
    MuF : ({a : Type} -> Algebra f a -> a) -> Mu f

mutual
    implementation Functor f => Costeppable (Mu f) f where
          embed fm = MuF (\alg => alg (map (cata alg) fm))

    implementation Functor f => Recursive (Mu f) f where
          cata alg (MuF f) = f alg

mutual 
  data Matrix : (m : Nat) -> (n : Nat) -> (j : Nat) -> Type where
    MultMat : {j' : Nat} -> {x : Matrix m n j} ->
              Vect m (Vect n Double) -> Matrix n j (nat x) -> Matrix m n j
    BaseMat : {j' : Nat} -> 
              Matrix m n j

  implementation Nattable (Matrix m n j) where
      nat (MultMat {j} {j'=j'} _ _ ) = j'
      nat (BaseMat {j} {j'=j'}) = j'

data MatrixF : (m : Nat) -> (n : Nat) -> (j : Nat) -> (a : Type) -> Type where
    MultMatF : {x : Matrix m n j} -> 
               Vect m (Vect n Double) -> Matrix n j (nat x) -> a -> MatrixF m n j a
    BaseMatF : MatrixF m n j a

getNatj' : Matrix m n j -> Nat
getNatj' (MultMat {j'=j'} _ _ ) = j'
getNatj' (BaseMat {j'=j'}) = j'


-- implementation Functor (MatrixF m n j) where
  -- map f (MultMatF {j'=j'} {x=x} weights next a) = MultMatF {j'=j'} {x=x} weights next (f a)
  -- map f (BaseMatF {j'=j'}) = BaseMatF {j'=j'}

-- implementation Steppable' m n j Matrix MatrixF where
  -- project' mat = case mat of
                      -- (MultMat {j'} {x} w next) => MultMatF {x=x} w next next  
                      
                      -- (MultMat {j'=j'} w next) = MultMatF {x=(MultMat w next)}
                                                    -- w next next
    -- project' (BaseMat {j} {j'=j'})        = BaseMatF {j'=j'} 

-- l : (x : Matrix m n j) -> MatrixF m n j (Matrix n j (nat x))
-- l x = project' x

-- implementation Steppable (Matrix m n j) (MatrixF m n j) where
    -- project (MultMat {j} {j'=j'} w next) 
        -- = MultMatF {j'=j'} w next (MultMat {j} {j'=j'} w next) 
    -- project (BaseMat {j} {j'=j'})  
        -- = BaseMatF {j'=j'}

-- implementation Costeppable (Matrix m n j) (MatrixF m n j) where
    -- embed (MultMatF {j'} w a r) 
        -- = r
    -- embed (BaseMatF {j'=j'})  
        -- = BaseMat {j'=j'}

-- data Proj : (x : Matrix m n j) -> MatrixF m n j (Matrix n j (getNatj' x)) where
    

-- cata' : (x : Matrix m n j) 
        -- -> (alg : (MatrixF m n j (Matrix n j (nat x)) -> Matrix n j (nat x))) 
        -- -> Matrix n j (nat x)
-- cata' x alg = c x
    -- where c z = let p = project' z
                    -- q = map (\y => cata' y alg) p
                -- in  ?h 
                --p = map (cata' alg) . project' $ x
                -- in  ?h







