open import Data.Nat as ℕ
open import Data.Bool

open import WFC_parametric

module Lang where

module Syntax where

  open ArOps

  infixr 7 _×ₛ_
  infixr 8 _×τ_

  data Sh : Set where
    dim  : ℕ → Sh
    _×ₛ_ : Sh → Sh → Sh
  ⟦_⟧ₛ : Sh → S
  ⟦ dim n ⟧ₛ   = ι n
  ⟦ s ×ₛ p ⟧ₛ = ⟦ s ⟧ₛ ⊗ ⟦ p ⟧ₛ

  data Ty : Set where
    ix   : Sh → Ty
    ar   : Sh → Ty → Ty
    bool : Ty
    nat  : Ty
    _×τ_ : Ty → Ty → Ty

  variable
    s p q r : Sh
    τ σ δ : Ty

  -- infixr 6 _`∧_
  -- infixr 5 _`∨_
  -- infix  4 _`==ₙ_ _`!=ₙ_ _`<ₙ_ _`≤ₙ_
  -- infixl 6 _`+_ _`-ₙ_
  -- infixl 7 _`*ₙ_

  data RedOp : Ty → Set where
    `natAdd  : RedOp nat
    `boolAnd : RedOp bool
    `boolOr  : RedOp bool

  data E (P : Ty → Set) : Ty → Set where
    `     : P τ → E P τ
    `imap : (P (ix s) → E P τ) → E P (ar s τ)
    `sel  : E P (ar s τ) → E P (ix s) → E P τ

    `numVal : ℕ → E P nat
    `boolVal : Bool → E P bool
    `bool⇒nat : E P bool → E P nat

    _`+_ : (a b : E P nat) → E P nat
    _`-ₙ_ : (a b : E P nat) → E P nat
    _`*ₙ_ : (a b : E P nat) → E P nat
    _`==ₙ_ : (a b : E P nat) → E P bool
    _`!=ₙ_ : (a b : E P nat) → E P bool
    _`<ₙ_ : (a b : E P nat) → E P bool
    _`≤ₙ_ : (a b : E P nat) → E P bool

    _`∧_ : (a b : E P bool) → E P bool
    _`∨_ : (a b : E P bool) → E P bool
    `not : E P bool → E P bool
    `if : E P bool → E P τ → E P τ → E P τ

    `let : E P τ → (P τ → E P σ) → E P σ

    `pair : E P τ → E P σ → E P (τ ×τ σ)
    `fst : E P (τ ×τ σ) → E P τ
    `snd : E P (τ ×τ σ) → E P σ
    `ixPair : E P (ix s) → E P (ix p) → E P (ix (s ×ₛ p))
    `ixFst : E P (ix (s ×ₛ p)) → E P (ix s)
    `ixSnd : E P (ix (s ×ₛ p)) → E P (ix p)

    `nest : E P (ar (s ×ₛ p) τ) → E P (ar s (ar p τ))
    `unnest : E P (ar s (ar p τ)) → E P (ar (s ×ₛ p) τ)
    `foldShape : (P (ix s) → P τ → E P τ) → E P τ → E P τ
    `reduce : (P τ → P τ → E P τ) → E P τ → E P (ar s τ) → E P τ
    `parFoldShape : RedOp τ → (P (ix s) → E P τ) → E P τ
    `parReduce : RedOp τ → E P (ar s τ) → E P τ

  _`<$>_ : ∀ {P} → (E P τ → E P σ) → E P (ar s τ) → E P (ar s σ)
  f `<$> a = `imap λ i → f (`sel a (` i))

  zipWith : ∀ {P} →
    (E P τ → E P σ → E P δ) → E P (ar s τ) → E P (ar s σ) → E P (ar s δ)
  `zipWith f a b =
    `imap λ i → f (`sel a (` i)) (`sel b (` i))
  `sum : ∀ {P} → E P (ar s nat) → E P nat
  `sum a = `parReduce `natAdd a
  `any : ∀ {P} → E P (ar s bool) → E P bool
  `any a = `parReduce `boolOr a
  `all : ∀ {P} → E P (ar s bool) → E P bool
  `all a = `parReduce `boolAnd a

  `countTrue : ∀ {P} → E P (ar s bool) → E P nat
  `countTrue a = `sum (`bool⇒nat `<$> a)

  `sumShape : ∀ {P} → (P (ix s) → E P nat) → E P nat
  `sumShape f = `parFoldShape `natAdd f
  `anyShape : ∀ {P} → (P (ix s) → E P bool) → E P bool
  `anyShape f = `parFoldShape `boolOr f
  `allShape : ∀ {P} → (P (ix s) → E P bool) → E P bool
  `allShape f = `parFoldShape `boolAnd f

  `booleanDot : ∀ {P} → E P (ar s bool) → E P (ar s bool) → E P bool
  `booleanDot a b = `anyShape λ i → (`sel a (` i)) `∧ (`sel b (` i))

  `allowedCount : ∀ {P} → E P (ar (s ×ₛ p) bool) → E P (ar s nat)
  `allowedCount a = `sum `<$> (`nest (`bool⇒nat `<$> a))

  `noContradiction : ∀ {P} → E P (ar (s ×ₛ p) bool) → E P (ar s bool)
  `noContradiction a =
    `imap λ i →
      `sel (`allowedCount a) (` i)
        `!=ₙ
      `numVal 0

  `globallyNoContradiction : ∀ {P} → E P (ar (s ×ₛ p) bool) → E P bool
  `globallyNoContradiction a =
    `all (`noContradiction a)


module Semantics where

  open import Data.Maybe
  open import Data.Product
  open import Relation.Nullary
  open import Data.Nat.Properties using (_<?_; _≤?_)
  open Syntax
  open Helper
  open ArOps

  ⟦_⟧ₜ : Ty → Set
  ⟦ ix s ⟧ₜ = P ⟦ s ⟧ₛ
  ⟦ ar s τ ⟧ₜ = ⟦ τ ⟧ₜ [[ ⟦ s ⟧ₛ ]]
  ⟦ bool ⟧ₜ = Bool
  ⟦ nat ⟧ₜ = ℕ
  ⟦ τ ×τ σ ⟧ₜ = ⟦ τ ⟧ₜ × ⟦ σ ⟧ₜ

  redIdentity : RedOp τ → ⟦ τ ⟧ₜ
  redIdentity `natAdd  = 0
  redIdentity `boolAnd = true
  redIdentity `boolOr  = false

  applyRedOp : RedOp τ → ⟦ τ ⟧ₜ → ⟦ τ ⟧ₜ → ⟦ τ ⟧ₜ
  applyRedOp `natAdd  x y = x + y
  applyRedOp `boolAnd x y = x ∧ y
  applyRedOp `boolOr  x y = x ∨ y

  pFst : ∀ {s p : S} → P (s ⊗ p) → P s
  pFst (i ⊗ j) = i

  pSnd : ∀ {s p : S} → P (s ⊗ p) → P p
  pSnd (i ⊗ j) = j

  ⟦_⟧ : E ⟦_⟧ₜ τ → ⟦ τ ⟧ₜ
  ⟦ ` x ⟧ = x
  ⟦ `imap f ⟧ = λ i → ⟦ f i ⟧
  ⟦ `sel a i ⟧ = ⟦ a ⟧ ⟦ i ⟧
  ⟦ `nest e ⟧ = nest ⟦ e ⟧
  ⟦ `unnest e ⟧ = λ ij → ⟦ e ⟧ (pFst ij) (pSnd ij)
  ⟦ `bool⇒nat e ⟧ = bool⇒nat ⟦ e ⟧
  ⟦ a `+ b ⟧ = ⟦ a ⟧ + ⟦ b ⟧
  ⟦ a `-ₙ b ⟧ = ⟦ a ⟧ ∸ ⟦ b ⟧
  ⟦ a `*ₙ b ⟧ = ⟦ a ⟧ * ⟦ b ⟧
  ⟦ `numVal x ⟧ = x
  ⟦ `boolVal x ⟧ = x
  ⟦ a `!=ₙ b ⟧ = not (does (⟦ a ⟧ ℕ.≟ ⟦ b ⟧))
  ⟦ a `==ₙ b ⟧ = does (⟦ a ⟧ ℕ.≟ ⟦ b ⟧)
  ⟦ a `!=ₙ b ⟧ = not (does (⟦ a ⟧ ℕ.≟ ⟦ b ⟧))
  ⟦ a `<ₙ b ⟧ = does (⟦ a ⟧ <? ⟦ b ⟧)
  ⟦ a `≤ₙ b ⟧ = does (⟦ a ⟧ ≤? ⟦ b ⟧)
  ⟦ a `∧ b ⟧ = ⟦ a ⟧ ∧ ⟦ b ⟧
  ⟦ a `∨ b ⟧ = ⟦ a ⟧ ∨ ⟦ b ⟧
  ⟦ `not e ⟧ = not ⟦ e ⟧
  ⟦ `if c t e ⟧ with ⟦ c ⟧
  ... | true  = ⟦ t ⟧
  ... | false = ⟦ e ⟧
  ⟦ `let e f ⟧ = ⟦ f ⟦ e ⟧ ⟧

  ⟦ `pair a b ⟧ = ⟦ a ⟧ , ⟦ b ⟧
  ⟦ `fst e ⟧ = proj₁ ⟦ e ⟧
  ⟦ `snd e ⟧ = proj₂ ⟦ e ⟧

  ⟦ `ixPair i j ⟧ = ⟦ i ⟧ ⊗ ⟦ j ⟧
  ⟦ `ixFst ij ⟧ = pFst ⟦ ij ⟧
  ⟦ `ixSnd ij ⟧ = pSnd ⟦ ij ⟧

  ⟦ `foldShape f z ⟧ =
    foldShape
      (λ i acc →
        ⟦ f i acc ⟧)
      ⟦ z ⟧

  ⟦ `reduce f z a ⟧ =
    foldShape
      (λ i acc →
        ⟦ f (⟦ a ⟧ i) acc ⟧)
      ⟦ z ⟧

  ⟦ `parFoldShape op f ⟧ =
    foldShape
      (λ i acc →
        applyRedOp op
          ⟦ f i ⟧
          acc)
      (redIdentity op)

  ⟦ `parReduce op a ⟧ =
    foldShape
      (λ i acc →
        applyRedOp op
          (⟦ a ⟧ i)
          acc)
      (redIdentity op)
