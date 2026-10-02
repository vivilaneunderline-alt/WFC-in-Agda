open import Data.Nat as ℕ
open import Data.Bool

open import WFC_parametric

module Lang_rebuilt where

open ArOps

infixr 7 _×ₛ_

data Sh : Set where
  dim  : ℕ → Sh
  _×ₛ_ : Sh → Sh → Sh

⟦_⟧ₛ : Sh → S
⟦ dim n ⟧ₛ   = ι n
⟦ s ×ₛ p ⟧ₛ = ⟦ s ⟧ₛ ⊗ ⟦ p ⟧ₛ

variable
  s p q r : Sh

infixr 5 _⇒_
infixr 8 _×τ_

data Ty : Set where
  bool : Ty
  nat  : Ty
  ix   : Sh → Ty
  _⇒_  : Ty → Ty → Ty
  _×τ_ : Ty → Ty → Ty

ar : Sh → Ty → Ty
ar s τ = ix s ⇒ τ

variable
  τ σ δ : Ty
  V : Ty → Set

data RedOp : Ty → Set where
  `natAdd  : RedOp nat
  `boolAnd : RedOp bool
  `boolOr  : RedOp bool

infixl 3 _`$_

data E (V : Ty → Set) : Ty → Set where
  `      : V τ → E V τ
  `lam   : (V τ → E V σ) → E V (τ ⇒ σ)
  _`$_   : E V (τ ⇒ σ) → E V τ → E V σ

  `numVal  : ℕ → E V nat
  `boolVal : Bool → E V bool
  `bool⇒nat : E V bool → E V nat

  _`+_   : E V nat → E V nat → E V nat
  _`-ₙ_  : E V nat → E V nat → E V nat
  _`*ₙ_  : E V nat → E V nat → E V nat
  _`==ₙ_ : E V nat → E V nat → E V bool
  _`!=ₙ_ : E V nat → E V nat → E V bool
  _`<ₙ_  : E V nat → E V nat → E V bool
  _`≤ₙ_  : E V nat → E V nat → E V bool

  _`∧_ : E V bool → E V bool → E V bool
  _`∨_ : E V bool → E V bool → E V bool
  `not : E V bool → E V bool
  `if  : E V bool → E V τ → E V τ → E V τ

  `pair : E V τ → E V σ → E V (τ ×τ σ)
  `fst  : E V (τ ×τ σ) → E V τ
  `snd  : E V (τ ×τ σ) → E V σ

  _`⊗_   : E V (ix s) → E V (ix p) → E V (ix (s ×ₛ p))
  `ixFst : E V (ix (s ×ₛ p)) → E V (ix s)
  `ixSnd : E V (ix (s ×ₛ p)) → E V (ix p)

  `foldShape : E V (ix s ⇒ τ ⇒ τ) → E V τ → E V τ
  `reduce    : E V (τ ⇒ τ ⇒ τ) → E V τ → E V (ar s τ) → E V τ

  `parReduce : RedOp τ → E V (ar s τ) → E V τ

infix 1 `lam
syntax `lam (λ x → e) = `λ x ⇒ e

`mapₐ : E V ((τ ⇒ σ) ⇒ ar s τ ⇒ ar s σ)
`mapₐ = `λ f ⇒ `λ a ⇒ `λ i ⇒ ` f `$ (` a `$ ` i)

`zipWith : E V ((τ ⇒ σ ⇒ δ) ⇒ ar s τ ⇒ ar s σ ⇒ ar s δ)
`zipWith =
  `λ f ⇒
  `λ a ⇒
  `λ b ⇒
  `λ i ⇒ (` f `$ (` a `$ ` i)) `$ (` b `$ ` i)

`nest : E V (ar (s ×ₛ p) τ ⇒ ar s (ar p τ))
`nest =
  `λ a ⇒
  `λ i ⇒
  `λ j ⇒
    ` a `$ (` i `⊗ ` j)

`unnest : E V (ar s (ar p τ) ⇒ ar (s ×ₛ p) τ)
`unnest =
  `λ a ⇒
  `λ ij ⇒
    (` a `$ `ixFst (` ij)) `$ `ixSnd (` ij)

`bool⇒natF : E V (bool ⇒ nat)
`bool⇒natF = `λ b ⇒ `bool⇒nat (` b)

`andF : E V (bool ⇒ bool ⇒ bool)
`andF = `λ x ⇒ `λ y ⇒ (` x) `∧ (` y)

`orF : E V (bool ⇒ bool ⇒ bool)
`orF = `λ x ⇒ `λ y ⇒ (` x) `∨ (` y)

`addF : E V (nat ⇒ nat ⇒ nat)
`addF = `λ x ⇒ `λ y ⇒ (` x) `+ (` y)

`sum : E V (ar s nat ⇒ nat)
`sum = `λ a ⇒ `parReduce `natAdd (` a)

`any : E V (ar s bool ⇒ bool)
`any = `λ a ⇒ `parReduce `boolOr (` a)

`all : E V (ar s bool ⇒ bool)
`all = `λ a ⇒ `parReduce `boolAnd (` a)

`countTrue : E V (ar s bool ⇒ nat)
`countTrue =
  `λ a ⇒
    `sum `$ ((`mapₐ `$ `bool⇒natF) `$ (` a))

`booleanDot : E V (ar s bool ⇒ ar s bool ⇒ bool)
`booleanDot =
  `λ a ⇒
  `λ b ⇒
    `any `$ (((`zipWith `$ `andF) `$ (` a)) `$ (` b))

`allowedCount : E V (ar (s ×ₛ p) bool ⇒ ar s nat)
`allowedCount =
  `λ a ⇒
    (`mapₐ `$ `sum) `$
      (`nest `$ ((`mapₐ `$ `bool⇒natF) `$ (` a)))

`noContradiction : E V (ar (s ×ₛ p) bool ⇒ ar s bool)
`noContradiction =
  `λ a ⇒
  `λ i ⇒
    ((`allowedCount `$ (` a)) `$ (` i)) `!=ₙ (`numVal 0)

`globallyNoContradiction : E V (ar (s ×ₛ p) bool ⇒ bool)
`globallyNoContradiction =
  `λ a ⇒
    `all `$ (`noContradiction `$ (` a))

module Interp where

  open import Data.Product
  open import Relation.Nullary
  open import Data.Nat.Properties using (_<?_; _≤?_)
  open Helper
  open ArOps

  Sem : Ty → Set
  Sem bool = Bool
  Sem nat = ℕ
  Sem (ix s) = P ⟦ s ⟧ₛ
  Sem (τ ⇒ σ) = Sem τ → Sem σ
  Sem (τ ×τ σ) = Sem τ × Sem σ

  redIdentity : RedOp τ → Sem τ
  redIdentity `natAdd  = 0
  redIdentity `boolAnd = true
  redIdentity `boolOr  = false

  applyRedOp : RedOp τ → Sem τ → Sem τ → Sem τ
  applyRedOp `natAdd  x y = x + y
  applyRedOp `boolAnd x y = x ∧ y
  applyRedOp `boolOr  x y = x ∨ y

  ixFst : ∀ {s p : S} → P (s ⊗ p) → P s
  ixFst (i ⊗ j) = i

  ixSnd : ∀ {s p : S} → P (s ⊗ p) → P p
  ixSnd (i ⊗ j) = j

  {-# TERMINATING #-}
  interp : E Sem τ → Sem τ
  interp (` x) = x
  interp (`lam f) x = interp (f x)
  interp (f `$ x) = interp f (interp x)

  interp (`numVal n) = n
  interp (`boolVal b) = b
  interp (`bool⇒nat b) = bool⇒nat (interp b)

  interp (a `+ b) = interp a + interp b
  interp (a `-ₙ b) = interp a ∸ interp b
  interp (a `*ₙ b) = interp a * interp b
  interp (a `==ₙ b) = does (interp a ℕ.≟ interp b)
  interp (a `!=ₙ b) = not (does (interp a ℕ.≟ interp b))
  interp (a `<ₙ b) = does (interp a ℕ.<? interp b)
  interp (a `≤ₙ b) = does (interp a ℕ.≤? interp b)

  interp (a `∧ b) = interp a ∧ interp b
  interp (a `∨ b) = interp a ∨ interp b
  interp (`not e) = not (interp e)
  interp (`if c t e) with interp c
  ... | true  = interp t
  ... | false = interp e

  interp (`pair a b) = interp a , interp b
  interp (`fst e) = proj₁ (interp e)
  interp (`snd e) = proj₂ (interp e)

  interp (i `⊗ j) = interp i ⊗ interp j
  interp (`ixFst ij) = ixFst (interp ij)
  interp (`ixSnd ij) = ixSnd (interp ij)

  interp (`foldShape {s = s} f z) =
    foldShape
      (λ i acc → interp ((f `$ ` i) `$ ` acc))
      (interp z)

  interp (`reduce {s = s} f z a) =
    foldShape
      (λ i acc → interp ((f `$ ` (interp a i)) `$ ` acc))
      (interp z)

  interp (`parReduce {s = s} op a) =
    foldShape
      (λ i acc → applyRedOp op (interp a i) acc)
      (redIdentity op)

module Show where

  open import Data.Nat
  open import Data.Bool
  open import Data.String hiding (show)
  open import Data.Product

  open import Data.List using (List; []; _∷_)
    renaming
      (_++_    to _++L_;
       map      to mapL;
       concatMap to concatMapL)
