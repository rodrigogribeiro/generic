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

    infix 1 _==_

    data _==_ {l}{A : Set l}(x : A) : A -> Set l where
      refl : x == x

    {-# BUILTIN EQUALITY _==_ #-}
    {-# BUILTIN REFL refl #-}

    data Dec {l}(A : Set l) : Set l where
      yes : A -> Dec A
      no  : (A -> Zero) -> Dec A

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

    -- telescopes

    data Tel : Nat -> Set where
      []   : Tel zero
      _::_ : forall {n}(t : Tel n)(r : Reg n) -> Tel (suc n)

    -- interpreting types

    infix 1 [[_]]_

    data [[_]]_ : forall {n} -> Reg n -> Tel n -> Set where
      top : forall {n}{T : Reg n}{G : Tel n} (t : [[ T ]] G) -> [[ `Z ]] (G :: T)
      pop : forall {n}{T S : Reg n}{G : Tel n}(t : [[ T ]] G) -> [[ `wk T ]] (G :: S)
      def : forall {n}{T : Reg (suc n)}{S : Reg n}{G : Tel n}(t : [[ T ]] (G :: S)) -> [[ `let S T ]] G
      inl : forall {n}{T S : Reg n}{G : Tel n}(s : [[ S ]] G) -> [[ S `+ T ]] G
      inr : forall {n}{T S : Reg n}{G : Tel n}(t : [[ T ]] G) -> [[ S `+ T ]] G
      void : forall {n}{G : Tel n} -> [[ `1 ]] G
      pair : forall {n}{T S : Reg n}{G : Tel n}(s : [[ S ]] G)(t : [[ T ]] G) -> [[ S `* T ]] G
      In   : forall {n}{F : Reg (suc n)}{G : Tel n}(x : [[ F ]] (G :: (Mu F))) -> [[ Mu F ]] G

  module PlusSample where
    open Regular
    open Prelude

    `Nat : forall {n} -> Reg n
    `Nat = Mu (`1 `+ `Z)

    ze : forall {n}{G : Tel n} -> [[ `Nat ]] G
    ze = In (inl void)

    su : forall {n}{G : Tel n}(m : [[ `Nat ]] G) -> [[ `Nat ]] G
    su m = In (inr (top m))

    plus : forall {k}{G : Tel k}(n m : [[ `Nat ]] G) -> [[ `Nat ]] G
    plus (In (inl void)) m = m
    plus (In (inr (top n))) m = su (plus n m)

  module GenericEq where
    open Regular
    open Prelude

    notEqTop : forall {n}{G : Tel n}{T : Reg n}(x y : [[ T ]] G) -> ((x == y) -> Zero) -> top x == top y -> Zero
    notEqTop x .x neq refl = neq refl

    notEqPop : forall {n}{G : Tel n}{T S : Reg n}(x y : [[ T ]] G) -> ((x == y) -> Zero) -> pop {S = S} x == pop y -> Zero
    notEqPop x .x neq refl = neq refl

    notEqIn : forall {n}{G : Tel n}{F : Reg (suc n)}(x y : [[ F ]] (G :: Mu F)) -> ((x == y) -> Zero) -> In x == In y -> Zero
    notEqIn x .x neq refl = neq refl

    decideEq : forall {n}{G : Tel n}{T : Reg n}(x y : [[ T ]] G) -> Dec (x == y)
    decideEq (top x) (top y) with decideEq x y
    decideEq (top x) (top .x) | yes refl = yes refl
    decideEq (top x) (top y) | no n = no (notEqTop x y n)
    decideEq (pop x) (pop y) with decideEq x y
    decideEq (pop x) (pop .x) | yes refl = yes refl
    decideEq (pop x) (pop y) | no n = no (notEqPop x y n)
    decideEq (def x) (def y) with decideEq x y
    decideEq (def x) (def .x) | yes refl = yes refl
    decideEq (def x) (def y) | no x₁ = {!!}
    decideEq (inl x) (inl y) with decideEq x y
    decideEq (inl x) (inl .x) | yes refl = yes refl
    decideEq (inl x) (inl y) | no x₁ = {!!}
    decideEq (inl x) (inr y) = no (λ ())
    decideEq (inr x) (inl y) = no (λ ())
    decideEq (inr x) (inr y) with decideEq x y
    decideEq (inr x) (inr .x) | yes refl = yes refl
    decideEq (inr x) (inr y) | no x₁ = {!!}
    decideEq void void = yes refl
    decideEq (pair x x') (pair y y') with decideEq x y | decideEq x' y'
    decideEq (pair x x') (pair .x .x') | yes refl | yes refl = yes refl
    decideEq (pair x x') (pair y y') | yes x₁ | no x₂ = {!!}
    decideEq (pair x x') (pair y y') | no x₁ | k' = {!!}
    decideEq (In x) (In y) with decideEq x y
    decideEq (In x) (In .x) | yes refl = yes refl
    decideEq (In x) (In y) | no n = no (notEqIn x y n)
