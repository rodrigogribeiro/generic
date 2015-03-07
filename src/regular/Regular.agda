module Regular where

  -- code for exploring regular tree types

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

  module Regex where
    open Prelude

    data Rex (n : Nat) : Set where
      fail nil dot : Rex n
      only : (i : Fin n) -> Rex n
      or   : Rex n -> Rex n -> Rex n
      _then_ : Rex n -> Rex n -> Rex n
      _star : Rex n -> Rex n

    Words : forall {n} -> Rex n -> Set
    Words fail = Zero
    Words nil = One
    Words {n} dot = Fin n
    Words (only i) = One
    Words (or r r') = Words r + Words r'
    Words (r then r') = Words r * Words r'
    Words (r star) = List (Words r)


  module Regular where
    open Prelude

    data Reg : Nat -> Set where
      `Z : forall {n} -> Reg n
      `wk : forall {n}(s : Reg n) -> Reg (suc n)
      `let : forall {n}(s : Reg n)(t : Reg (suc n)) -> Reg n
      `0 : forall {n} -> Reg n
      `1 : forall {n} -> Reg n
      _`+_ : forall {n} -> (s t : Reg n) -> Reg n
      _`*_ : forall {n} -> (s t : Reg n) -> Reg n
      Mu : forall {n}(f : Reg (suc n)) -> Reg n

    -- from fin to reg

    var : forall {n} -> Fin n -> Reg n
    var zero = `Z
    var (suc n) = `wk (var n)
