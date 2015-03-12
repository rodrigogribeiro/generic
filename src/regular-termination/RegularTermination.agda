module RegularTermination where

  -- experiments for type based termination of regular tree types

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

    private
      suc-eq : forall {n m : Nat} -> (n == m -> Zero) -> _==_ {A = Nat} (suc n) (suc m) -> Zero
      suc-eq x refl = x refl

    Nat-eq-dec : forall (n m : Nat) -> Dec (n == m)
    Nat-eq-dec zero zero = yes refl
    Nat-eq-dec zero (suc m) = no (λ ())
    Nat-eq-dec (suc n) zero = no (λ ())
    Nat-eq-dec (suc n) (suc m) with Nat-eq-dec n m
    Nat-eq-dec (suc n) (suc .n) | yes refl = yes refl
    Nat-eq-dec (suc n) (suc m) | no x = no (suc-eq x)

  module Ordinal where

    open Prelude

    data Ord : Set where
      #_  : Nat -> Ord -- variables
      suc : Ord -> Ord -- successor
      inf : Ord        -- infinite

    --equality

    private
      var-eq : forall {p q : Nat} -> ((p == q) -> Zero) -> _==_ {A = Ord} (# p) (# q) -> Zero
      var-eq prf refl = prf refl

      suc-eq : forall {p q : Ord} -> ((p == q) -> Zero) -> _==_ {A = Ord} (suc p) (suc q) -> Zero
      suc-eq prf refl = prf refl

    _eq?_ : forall (p q : Ord) -> Dec (p == q)
    (# x) eq? (# x') with Nat-eq-dec x x'
    (# x) eq? (# .x) | yes refl = yes refl
    (# x) eq? (# x') | no k = no (var-eq k)
    (# x) eq? suc q = no (λ ())
    (# x) eq? inf = no (λ ())
    suc p eq? (# x) = no (λ ())
    suc p eq? suc q with p eq? q
    suc p eq? suc .p | yes refl = yes refl
    suc p eq? suc q | no x = no (suc-eq x)
    suc p eq? inf = no (λ ())
    inf eq? (# x) = no (λ ())
    inf eq? suc q = no (λ ())
    inf eq? inf = yes refl

    -- ordinal partial order

    data _<=_ : Ord -> Ord -> Set where
      refl  : forall {p} -> p <= p
      suc   : forall {p} -> p <= suc p
      inf   : forall {p} -> p <= inf


  module Universe where

    open Prelude
    open Ordinal

    data Reg : Nat -> Ord -> Set where
      `Z : forall {n o} -> Reg n o
      `wk : forall {n o}(s : Reg n o) -> Reg (suc n) o
      `let : forall {n o}(s : Reg n o)(t : Reg (suc n) o) -> Reg n o
      `0 : forall {n o} -> Reg n o
      `1 : forall {n o} -> Reg n o
      _`+_ : forall {n o} -> (s t : Reg n o) -> Reg n o
      _`*_ : forall {n o} -> (s t : Reg n o) -> Reg n o
      Mu : forall {n o}(f : Reg (suc n) o) -> Reg n (suc o)

    -- telescopes

    data Tel : Nat -> Ord -> Set where
      []   : forall {o} -> Tel zero o
      _::_ : forall {n o o'}(t : Tel n o')(r : Reg n o) -> Tel (suc n) o

    -- interpreting types

    infix 1 [[_]]_

    data [[_]]_ : forall {n o o'} -> Reg n o -> Tel n o' -> Set where
      top : forall {n o o'}{T : Reg n o}{G : Tel n o'} (t : [[ T ]] G) -> [[ `Z {o = o} ]] (G :: T)
      pop : forall {n o o'}{T S : Reg n o}{G : Tel n o'}(t : [[ T ]] G) -> [[ `wk T ]] (G :: S)
      def : forall {n o o'}{T : Reg (suc n) o}{S : Reg n o}{G : Tel n o'}(t : [[ T ]] (G :: S)) -> [[ `let S T ]] G
      inl : forall {n o o'}{T S : Reg n o}{G : Tel n o'}(s : [[ S ]] G) -> [[ S `+ T ]] G
      inr : forall {n o o'}{T S : Reg n o}{G : Tel n o'}(t : [[ T ]] G) -> [[ S `+ T ]] G
      void : forall {n o o'}{G : Tel n o} -> [[ `1 {o = o'} ]] G
      pair : forall {n o o'}{T S : Reg n o}{G : Tel n o'}(s : [[ S ]] G)(t : [[ T ]] G) -> [[ S `* T ]] G
      In   : forall {n o o'}{F : Reg (suc n) (suc o)}{G : Tel n o'}(x : [[ F ]] (G :: (Mu F))) -> [[ Mu F ]] G

    `Nat : forall {n o} -> Reg n (suc o)
    `Nat = Mu (`1 `+ `Z)

    ze : forall {n o o'}{G : Tel n o} -> [[ `Nat {o = suc o'} ]] G
    ze = In (inl void)

    su : forall {n o o'}{G : Tel n o}(m : [[ `Nat {o = suc o'} ]] G) -> [[ `Nat ]] G
    su m = In (inr {!pair!})

    -- minus : forall {k o}{G : Tel k o}(n m : [[ `Nat ]] G) -> [[ `Nat ]] G
    -- minus (In (inl void)) m = m
    -- minus (In (inr n)) (In (inl void)) = In (inr n)
    -- minus (In (inr (top n))) (In (inr (top m))) = minus n m

    -- div : forall {k}{G : Tel k}(n m : [[ `Nat ]] G) -> [[ `Nat ]] G
    -- div (In (inl void)) m = m
    -- div (In (inr (top n))) m = su (div (minus n m) m)
