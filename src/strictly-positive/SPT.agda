module SPT where

  -- code for universes for strictly positive families

  module Finite where

    data Zero : Set where
    data One : Set where
      tt : One

    record Sig (A : Set)(B : A -> Set) : Set where
       constructor _,_
       field
         fst : A
         snd : B fst

    open Sig

    infixl 4 _*_
    infixl 6 _+_

    _*_ : Set -> Set -> Set
    A * B = Sig A (\_ -> B)

    data _+_ (A : Set)(B : Set) : Set where
       inl : A -> A + B
       inr : B -> A + B

  open Finite

  module Prelude where

    data Nat : Set where
      zero : Nat
      suc  : Nat -> Nat

    {-# BUILTIN NATURAL Nat #-}

    data Fin : Nat -> Set where
      zero : forall {n} -> Fin (suc n)
      suc  : forall {n} -> Fin n -> Fin (suc n)

    fin : (n : Nat) -> Set
    fin zero = Zero
    fin (suc n) = One + fin n

    data List (A : Set) : Set where
      [] : List A
      _::_ : A -> List A -> List A

    infix 1 _==_

    data _==_ {l}{A : Set l}(x : A) : A -> Set l where
      refl : x == x

    {-# BUILTIN EQUALITY _==_ #-}
    {-# BUILTIN REFL refl #-}

    data Dec {l}(A : Set l) : Set l where
      yes : A -> Dec A
      no  : (A -> Zero) -> Dec A
