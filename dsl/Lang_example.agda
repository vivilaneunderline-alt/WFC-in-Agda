open import Data.Nat as ℕ
open import Data.Bool

open import WFC_parametric

module Lang where
module Syntax where

  open ArOps
  
  data Ty : Set where
    ix : S → Ty
    ar : S → Ty → Ty
    bool : Ty
    nat : Ty
    --maybe : Ty → Ty

  variable
    s p q r : S
    τ σ δ : Ty

  data E (P : Ty → Set) : Ty → Set where
    ` : P τ → E P τ
    `imap : (P (ix s) → E P τ) → E P (ar s τ)
    `sel : E P (ar s τ) → E P (ix s) → E P τ
    `bool⇒nat : E P bool → E P nat
    _`+_ : (a b : E P nat) → E P nat 
    `numVal : ℕ → E P nat
    `boolVal : Bool → E P bool
    _`!=ₙ_ : (a b : E P nat) → E P bool 
    `nest : E P (ar (s ⊗ p) τ) → E P (ar s (ar p τ))
    `foldShape : (P (ix s) → P τ → E P τ) → E P τ → E P τ


  _`<$>_ : ∀ {P} → (E P τ → E P σ) → E P (ar s τ) → E P (ar s σ)
  f `<$> a = `imap λ i → f (`sel a (` i))

  `sum : ∀ {P} → E P (ar s nat) → E P nat
  `sum a = `foldShape (λ i x → `sel a (` i) `+ ` x) (`numVal 0)

  -- Assumes that the input array is the real wave
  `allowedCount : ∀ {P} → E P (ar (s ⊗ p) bool) → E P (ar s nat) 
  `allowedCount a = `sum `<$> (`nest (`bool⇒nat `<$> a)) 

  `noContradiction : ∀ {P} → E P (ar (s ⊗ p) bool) → E P (ar s bool)
  `noContradiction a
    = `imap λ i → `sel (`allowedCount a) (` i) `!=ₙ `numVal 0

  -- and so on

module Pretty where

  open import Data.String
  open import Text.Printf
  open Syntax
  open ArOps
  
  var : ℕ → String
  var n = printf "x%u" n

  pretty : E (λ _ → ℕ) τ → ℕ → String 
  pretty (` x) n = var x
  pretty (`imap f) n = let b = pretty (f (suc n)) n 
                       in printf "(imap λ %s → %s)" (var n) b  
  pretty (`sel e e₁) n = printf "(%s)[%s]" (pretty e n) (pretty e₁ n)
  pretty (`bool⇒nat e) n = printf "natFromBool(%s)" (pretty e n)
  pretty (e `+ e₁) n = printf "(%s + %s)" (pretty e n) (pretty e₁ n)
  pretty (`numVal x) n = printf "%u" x
  pretty (`boolVal false) n = printf "false"
  pretty (`boolVal true) n = printf "true"
  pretty (e `!=ₙ e₁) n = printf "(%s != %s)" (pretty e n) (pretty e₁ n)
  pretty (`nest e) n = printf "nest(%s)" (pretty e n)
  pretty (`foldShape f e) n 
    = let ix = var n
          a = var (suc n)
          e = pretty e n
          b = pretty (f (n) ((1 + n))) (2 + n)
      in printf "foldShape (λ %s %s → %s) (%s)" ix a b e 

  test = pretty (`noContradiction {ι 10}{ι 10} (` 0)) 1

module Semantics where

  open import Data.Maybe
  open import Relation.Nullary
  open Syntax
  open Helper
  open ArOps
  -- Semantics
  ⟦_⟧ₜ : Ty → Set
  ⟦ ix x ⟧ₜ = P x
  ⟦ ar x τ ⟧ₜ = ⟦ τ ⟧ₜ [[ x ]]
  ⟦ bool ⟧ₜ = Bool
  ⟦ nat ⟧ₜ = ℕ
  --⟦ maybe τ ⟧ₜ = Maybe ⟦ τ ⟧ₜ

  ⟦_⟧ : E ⟦_⟧ₜ τ → ⟦ τ ⟧ₜ
  ⟦ ` x ⟧ = x
  ⟦ `imap f ⟧ = λ i → ⟦ f i ⟧ 
  ⟦ `sel e e₁ ⟧ = ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ `bool⇒nat e ⟧ = bool⇒nat ⟦ e ⟧
  ⟦ e `+ e₁ ⟧ = ⟦ e ⟧ + ⟦ e₁ ⟧
  ⟦ `numVal x ⟧ = x
  ⟦ `boolVal x ⟧ = x
  ⟦ e `!=ₙ e₁ ⟧ = not (does (⟦ e ⟧ ℕ.≟ ⟦ e₁ ⟧))
  ⟦ `nest e ⟧ = nest ⟦ e ⟧
  ⟦ `foldShape f e ⟧ = foldShape (λ i x → ⟦ f i x ⟧) ⟦ e ⟧

  test-sem : Bool [[ s ⊗ p ]] → _
  test-sem {s} {p} a = ⟦ `noContradiction {s}{p} (` a) ⟧


