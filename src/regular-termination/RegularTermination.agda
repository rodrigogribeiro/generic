module RegularTermination where

  -- experiments for type based termination of regular tree types

  module Finite where

    data Zero : Set where

    record One : Set where
      constructor <>

    data Two : Set where tt ff : Two

    So : Two -> Set
    So tt = One
    So ff = Zero

    record <<_>> (P : Set) : Set where
      constructor !
      field
        {{ prf }} : P

    _=>_ : Set -> Set -> Set
    P => T = {{ p : P }} -> T

    infixr 3 _=>_

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

    <|_|> : forall{l}{A : Set l} -> Dec A -> Two
    <| yes _ |> = tt
    <| no _ |>  = ff

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

    _<=_ : Ord -> Ord -> Two
    (# x) <= (# x₁) = tt
    (# x) <= suc o' = <| (# x) eq? o' |>
    (# x) <= inf = tt
    suc o <= (# x) = ff
    suc o <= suc o' = o <= o'
    suc o <= inf = ff
    inf <= (# x) = ff
    inf <= suc o' = ff
    inf <= inf = tt

  module Universe where

    open Prelude
    open Ordinal

    data Reg : Nat -> Set where
      `Z : forall {n} -> Reg n
      `wk : forall {n}(s : Reg n) -> Reg (suc n)
      `let : forall {n}(s : Reg n)(t : Reg (suc n)) -> Reg n
      `0 : forall {n} -> Reg n
      `1 : forall {n} -> Reg n
      _`+_ : forall {n} -> (s t : Reg n) -> Reg n
      _`*_ : forall {n} -> (s t : Reg n) -> Reg n
      Mu : forall {n}(f : Reg (suc n)) -> Reg n

    -- telescopes

    data Tel : Nat -> Set where
      []   : Tel zero
      _::_ : forall {n}(t : Tel n)(r : Reg n) -> Tel (suc n)

    -- interpreting types

    infix 1 [[_]]_^_

    data [[_]]_^_ : forall {n} -> Reg n -> Tel n -> Ord -> Set where
      top : forall {n o}{T : Reg n}{G : Tel n} (t : [[ T ]] G ^ o) -> [[ `Z ]] (G :: T) ^ o
      pop : forall {n o}{T S : Reg n}{G : Tel n}(t : [[ T ]] G ^ o) -> [[ `wk T ]] (G :: S) ^ o
      def : forall {n o}{T : Reg (suc n)}{S : Reg n}{G : Tel n}(t : [[ T ]] (G :: S) ^ o) -> [[ `let S T ]] G ^ o
      inl : forall {n o}{T S : Reg n}{G : Tel n}(s : [[ S ]] G ^ o) -> [[ S `+ T ]] G ^ o
      inr : forall {n o}{T S : Reg n}{G : Tel n}(t : [[ T ]] G ^ o) -> [[ S `+ T ]] G ^ o
      void : forall {n o}{G : Tel n} -> [[ `1 ]] G ^ o
      pair : forall {n o}{T S : Reg n}{G : Tel n}(s : [[ S ]] G ^ o)(t : [[ T ]] G ^ o) -> [[ S `* T ]] G ^ o
      In   : forall {n o o'}{F : Reg (suc n)}{G : Tel n}(x : [[ F ]] (G :: (Mu F)) ^ o) -> (So (o <= o')) => ([[ Mu F ]] G ^ o')

    `Nat : forall {n} -> Reg n
    `Nat = Mu (`1 `+ `Z)

    ze : forall {n o}{G : Tel n} -> [[ `Nat ]] G ^ (suc o)
    ze {o = o} = In {o = o} {o' = suc o} (inl void)

    su : forall {n o}{G : Tel n}(m : [[ `Nat ]] G ^ o) -> [[ `Nat ]] G ^ (suc o)
    su m = {!!} -- In (inr (top m))

    -- minus : forall {k o}{G : Tel k} -> [[ `Nat ]] G ^ o -> [[ `Nat ]] G ^ inf -> [[ `Nat ]] G ^ o
    -- minus (In (inl void)) m = In (inl void)
    -- minus (In (inr n)) (In (inl void)) = In (inr n)
    -- minus (In (inr (top n))) (In (inr (top m))) = minus n m

    -- div : forall {k o}{G : Tel k}(n m : [[ `Nat ]] G ^ o) -> [[ `Nat ]] G ^ o
    -- div (In (inl void)) m = m
    -- div (In (inr (top n))) m = su (div (minus n m) m)
