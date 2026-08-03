module ShapeLayer where

open import Agda.Primitive using (Level) public
open import Data.Nat using (ℕ; zero; suc; _+_; _*_) public
open import Data.Fin using (Fin) public
open import Data.Fin.Properties using (_≟_) public
open import Data.Bool using(Bool; true; false; if_then_else_; _∧_; _∨_) public
open import Relation.Nullary using (Dec; yes; no) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public


data S : Set where
  ι   : ℕ → S
  _⊗_ : S → S → S

data P : S → Set where
  ι   : ∀ {n} → Fin n → P (ι n)
  _⊗_ : ∀ {s t} → P s → P t → P (s ⊗ t)

_[[_]] : ∀ {ℓ} → Set ℓ → S → Set ℓ
X [[ s ]] = P s → X

_[_] : ∀ {ℓ} {X : Set ℓ} {s : S} → X [[ s ]] → P s → X
a [ i ] = a i

K : ∀ {ℓ} {X : Set ℓ} {s : S} → X → X [[ s ]]
K x _ = x

map : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} {s : S} → (X → Y) → X [[ s ]] → Y [[ s ]]
map f a i = f (a i)

zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃} {s : S} → (X → Y → Z) → X [[ s ]] → Y [[ s ]] → Z [[ s ]]
zipWith f a b i = f (a i) (b i)


shapeSize : S → ℕ
shapeSize (ι n) = n
shapeSize (s ⊗ t) = shapeSize s * shapeSize t

sameP? : ∀ {s : S} → (p q : P s) → Dec (p ≡ q)
sameP? {ι n} (ι p) (ι q) with p ≟ q
... | yes refl = yes refl
... | no p≢q = no λ { refl → p≢q refl }

sameP? {s ⊗ t} (p₁ ⊗ p₂) (q₁ ⊗ q₂)
  with sameP? p₁ q₁ | sameP? p₂ q₂
... | yes refl | yes refl = yes refl
... | no p≢q  | _        = no λ { refl → p≢q refl }
... | yes refl | no p≢q  = no λ { refl → p≢q refl }

updateAt : ∀ {s : S} {X : Set} → P s → X → X [[ s ]] → X [[ s ]]
updateAt i x a j with sameP? j i
... | yes _ = x
... | no _  = a j


foldFin : ∀ {A : Set} → (n : ℕ) → (Fin n → A → A) → A → A
foldFin zero f z = z
foldFin (suc n) f z = f Fin.zero (foldFin n
    (λ i acc → f (Fin.suc i) acc) z)

foldShape : ∀ {s : S} {A : Set} → (P s → A → A) → A → A
foldShape {ι n} f z = foldFin n
    (λ i acc → f (ι i) acc) z
foldShape {s ⊗ t} f z = foldShape {s} (λ i acc₁ → foldShape {t}
    (λ j acc₂ → f (i ⊗ j) acc₂) acc₁) z

foldMap : ∀ {s : S} {X A : Set} → (X → A → A) → A → X [[ s ]] → A
foldMap f z a = foldShape
    (λ i acc → f (a i) acc) z

reduce : ∀ {s : S} {X : Set} → (X → X → X) → X → X [[ s ]] → X
reduce _∙_ e a = foldMap _∙_ e a


sumℕ : ∀ {s : S} → ℕ [[ s ]] → ℕ
sumℕ = reduce _+_ zero

count : ∀ {s : S} → Bool [[ s ]] → ℕ
count a = foldMap (λ b acc →
    if b
    then suc acc
    else acc) zero a

any : ∀ {s : S} → Bool [[ s ]] → Bool
any = reduce _∨_ false

all : ∀ {s : S} → Bool [[ s ]] → Bool
all = reduce _∧_ true

booleanDot : ∀ {s : S} → Bool [[ s ]] → Bool [[ s ]] → Bool
booleanDot xs ys = any (zipWith _∧_ xs ys)