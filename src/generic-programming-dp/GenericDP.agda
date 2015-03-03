module GenericDP where

  module Prelude where

    data Nat : Set where
      zero : Nat
      suc  : Nat -> Nat

    {-# BUILTIN NATURAL Nat #-}

    data Fin : Nat -> Set where
      zero : forall {n} -> Fin (suc n)
      suc  : forall {n} -> Fin n -> Fin (suc n)


    emb : forall {n : Nat} -> Fin n -> Fin (suc n)
    emb zero    = zero
    emb (suc n) = suc (emb n)

    id : forall {l}{A : Set l} -> A -> A
    id x = x

  module GenericTypes where
    open Prelude

    -- simple universe

    infixr 4 _=>_

    data U : Set where
      nat  : U
      _=>_ : U -> U -> U

    El : U -> Set
    El nat = Nat
    El (l => r) = (El l) -> (El r)

    -- simple use of universe

    `zero : forall (A : U) -> El A
    `zero nat = 0
    `zero (u => u') = \ _ -> `zero u'

    -- representing lambda terms

    data Lam : Nat -> Set where
      var : forall {n : Nat} -> Fin n -> Lam n
      abs : forall {n : Nat} -> Lam (suc n) -> Lam n
      app : forall {n : Nat} -> Lam n -> Lam n -> Lam n

    -- closing open terms

    close : forall (n : Nat) -> Lam n -> Lam 0
    close zero t = t
    close (suc n) t = close n (abs t)

  module Encoding where
    open Prelude

    -- representing kinds

    infix 4 _<-_
    infixr 4 _=>_
    infixr 6 _o_
    infixl 8 _+_ _*_

    data Kind : Set where
      Star : Kind
      _=>_ : Kind -> Kind -> Kind

    Ctx : Set
    Ctx = Kind

    [_] : Kind -> Ctx
    [_] = id

    [] = Star

    infixr 4 _::_

    _::_ : Kind -> Ctx -> Ctx
    k :: k' = k => k'

    data _<-_ : Kind -> Ctx -> Set where
      here  : forall {k k'} -> k <- (k => k')
      there : forall {k k' k''} -> k <- k'' -> k <- k' => k''

    data Ty (M P : Ctx) : Kind -> Set where
      D    : forall {k} -> k <- M -> Ty M P k
      V    : forall {k} -> k <- P -> Ty M P k
      _o_  : forall {k k'} -> Ty M P (k' => k) -> Ty M P k' -> Ty M P k
      Zero : Ty M P Star
      One  : Ty M P Star
      _+_  : Ty M P Star -> Ty M P Star -> Ty M P Star
      _*_  : Ty M P Star -> Ty M P Star -> Ty M P Star


    [[_]]Ctx : forall (C : Ctx) -> Set
    [[ C ]]Ctx = forall {k : Kind} -> k <- C -> Ty C [ k ] Star

    Args : forall (C : Ctx)(k : Kind) -> Set
    Args C k = forall {k'} -> k' <- [ k ] -> Ty C [] k'


    module TyInterp {C : Ctx}(de : [[ C ]]Ctx) where

      infix 6 _#_
      infix 4 _:[_]
      infixl 4 _,_

      hd : forall (j k : Kind)(xs : Args C (j => k)) -> Ty C [] j
      hd j k args = args here

      tl : forall (j k : Kind)(xs : Args C (j => k)) -> Args C k
      tl j k args = \ x -> args (there x)

      _#_ : forall {C k} -> Ty C [] k -> Args C k -> Ty C [] Star
      _#_ {k = Star} t args = t
      _#_ {k = k => k'} t args = _#_ {k = k'}{!t o (hd args)!}  {!tl args!}

      _:[_] : forall {Del j k} -> Ty Del [ j ] k -> Args Del j -> Ty Del [] k
      D x :[ args ] = D x
      V x :[ args ] = args x
      t o t' :[ args ] = (t :[ args ]) o (t' :[ args ])
      Zero :[ args ] = Zero
      One :[ args ] = One
      t + t' :[ args ] = (t :[ args ]) + (t' :[ args ])
      t * t' :[ args ] = (t :[ args ]) * (t' :[ args ])

      data [[_]]T : Ty C [] Star -> Set where
        con : forall {k}{x : Args C k}{v} -> [[ (de v):[ x ] ]]T -> [[ D v # x ]]T
        inl  : forall {S} T -> [[ S ]]T -> [[ S + T ]]T
        inr  : forall {T} S -> [[ T ]]T -> [[ S + T ]]T
        void : [[ One ]]T
        _,_  : forall {S T} -> [[ S ]]T -> [[ T ]]T -> [[ S * T ]]T

    module ExampleCodes where

      data Bush (A : Set) : Set where
        Nil : Bush A
        Cons : (Bush (Bush A)) -> Bush A

      data WBush : Set where
         W : Bush WBush -> WBush

      -- some examples of coding

      MBush : Ctx
      MBush = Star => Star :: Star :: []

      -- little error on paper, in the second context the correct kind is Star rather than Star => Star...

      BushCode : Ty ((Star => Star) :: Star :: []) [ Star => Star ] Star
      BushCode = One + (V here) * ((D here) o (D here) o (V here))

      WBushCode : Ty ((Star => Star) :: Star :: []) [ Star ] Star
      WBushCode = (D here) o (D (there here))

      delW : [[ (Star => Star) :: Star :: [] ]]Ctx
      delW here = BushCode
      delW (there here) = WBushCode
      delW (there (there ()))


      -- constructors

      --nil : forall {C k}(A : Ty C [] Star) -> [[ (D here) o A ]]T
