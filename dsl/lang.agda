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

  infixr 6 _`∧_
  infixr 5 _`∨_
  infixl 6 _`+_

  data RedOp : Ty → Set where
    `natAdd  : RedOp nat
    `boolAnd : RedOp bool
    `boolOr  : RedOp bool

  data E (P : Ty → Set) : Ty → Set where
    ` : P τ → E P τ

    `imap : (P (ix s) → E P τ) → E P (ar s τ)
    `sel : E P (ar s τ) → E P (ix s) → E P τ

    `numVal    : ℕ → E P nat
    `boolVal   : Bool → E P bool
    `bool⇒nat  : E P bool → E P nat
    _`+_       : (a b : E P nat) → E P nat
    
    _`!=ₙ_     : (a b : E P nat) → E P bool
    _`∧_       : (a b : E P bool) → E P bool
    _`∨_       : (a b : E P bool) → E P bool
    `not       : E P bool → E P bool
    `if        : E P bool → E P τ → E P τ → E P τ

    `pair : E P τ → E P σ → E P (τ ×τ σ)
    `fst : E P (τ ×τ σ) → E P τ
    `snd : E P (τ ×τ σ) → E P σ
    `ixPair : E P (ix s) → E P (ix p) → E P (ix (s ×ₛ p))
    `ixFst : E P (ix (s ×ₛ p)) → E P (ix s)
    `ixSnd : E P (ix (s ×ₛ p)) → E P (ix p)

    `nest      : E P (ar (s ×ₛ p) τ) → E P (ar s (ar p τ))
    `foldShape : (P (ix s) → P τ → E P τ) → E P τ → E P τ
    `reduce : (P τ → P τ → E P τ) → E P τ → E P (ar s τ) → E P τ
    `parFoldShape : RedOp τ → (P (ix s) → E P τ) → E P τ
    `parReduce : RedOp τ → E P (ar s τ) → E P τ


  _`<$>_ : ∀ {P} → (E P τ → E P σ) → E P (ar s τ) → E P (ar s σ)
  f `<$> a = `imap λ i → f (`sel a (` i))

  `sum : ∀ {P} → E P (ar s nat) → E P nat
  `sum a = `parReduce `natAdd a
  `any : ∀ {P} → E P (ar s bool) → E P bool
  `any a = `parReduce `boolOr a
  `all : ∀ {P} → E P (ar s bool) → E P bool
  `all a = `parReduce `boolAnd a

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
