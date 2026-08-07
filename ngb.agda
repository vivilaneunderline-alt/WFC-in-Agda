open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Nat
open import Data.Sum hiding (map)
open import Function

module _ where

module FinOps where
 
  private variable
    n : ℕ

  prev : Fin n → Fin (2 + n)
  prev zero    = zero
  prev (suc i) = suc (prev i)

  next : Fin n → Fin (2 + n)
  next i = suc (suc i)

  lift : Fin n → Fin (1 + n)
  lift zero    = zero
  lift (suc i) = suc (lift i)

  embed : Fin n → Fin (2 + n)
  embed i = suc (lift i)

  dir : ∀ {n} → Fin n → (d : Fin 2) → Fin (2 + n)
  dir i zero = prev i
  dir i _    = next i


module Arrays where

  data S : Set where
    ι : ℕ → S
    _⊗_ : S → S → S
  
  variable
    m n : ℕ
    s p : S
    X Y : Set
  
  data P : S → Set where
    ι : Fin n → P (ι n)
    _⊗_ : P s → P p → P (s ⊗ p)
  
  Ar : S → Set → Set
  Ar s X = P s → X
  
  a-map : (X → Y) → Ar s X → Ar s Y
  a-map f a i = f (a i)
  
  nest : Ar (s ⊗ p) X → Ar s (Ar p X)
  nest a i j = a (i ⊗ j)
  
  s-map : (ℕ → ℕ) → S → S
  s-map f (ι n) = ι (f n)
  s-map f (s ⊗ p) = s-map f s ⊗ s-map f p

  rank : S → ℕ
  rank (ι _) = 1
  rank (s ⊗ p) = rank s + rank p

module Neighbours where

  open FinOps
  open Arrays

  full-s : S → S
  full-s = s-map (2 +_)
  
  embed-s : P s → P (full-s s)
  embed-s (ι i) = ι (embed i)
  embed-s (i ⊗ j) = embed-s i ⊗ embed-s j
  
  ngb : P s → P (ι (rank s)) → P (ι 2) → P (full-s s)
  ngb         (ι i)   _     (ι d) = ι (dir i d)
  ngb {s ⊗ _} (i ⊗ j) (ι a) d with Fin.splitAt (rank s) a
  ... | inj₁ a = ngb i (ι a) d ⊗ embed-s j
  ... | inj₂ a = embed-s i ⊗ ngb j (ι a) d


module Tests where

  open import Data.Vec as Vec
  open import Data.Product
  open Arrays
  open Neighbours

  Tensor : S → Set → Set
  Tensor (ι n) X = Vec X n
  Tensor (s ⊗ p) X = Tensor s (Tensor p X)
  
  toTen : (P s → X) → Tensor s X
  toTen {ι n} a = tabulate (a ∘ ι)
  toTen {s ⊗ p} a = toTen (a-map toTen (nest a))
  
  fromTen : Tensor s X → P s → X
  fromTen {ι x} t (ι i) = lookup t i
  fromTen {s ⊗ p} t (i ⊗ j) = fromTen (fromTen t i) j
  
  ten-nbgs : Tensor (full-s s) X → Tensor s (Tensor (ι (rank s) ⊗ ι 2) X)
  ten-nbgs {s} a 
    = toTen {s} λ i → toTen λ j → toTen λ k → (fromTen a (ngb i j k))
  
  iota : (n : ℕ) → Tensor (ι n) ℕ
  iota 0       = []
  iota (suc n) = 0 ∷ Vec.map suc (iota n)
  
  ex-1d : Tensor (full-s (ι 3)) ℕ
  ex-1d = iota 5 
  
  nbg-1d = ten-nbgs {ι 3} ex-1d
  
  ex-2d : Tensor (full-s (ι 2 ⊗ ι 3)) ℕ
  ex-2d = iota 5 
          ∷ Vec.map (5 +_) (iota 5)
          ∷ Vec.map (10 +_) (iota 5)
          ∷ Vec.map (15 +_) (iota 5)
          ∷ []
  
  nbg-2d = ten-nbgs {ι 2 ⊗ ι 3} ex-2d

  -- (0  ∷ 1  ∷ 2  ∷ 3  ∷ 4  ∷ []) ∷
  -- (5  ∷ 6  ∷ 7  ∷ 8  ∷ 9  ∷ []) ∷
  -- (10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ []) ∷
  -- (15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ []) ∷ []
  
  -- (((1 ∷ 11 ∷ []) ∷ (5 ∷ 7 ∷ []) ∷ []) ∷
  --  ((2 ∷ 12 ∷ []) ∷ (6 ∷ 8 ∷ []) ∷ []) ∷
  --  ((3 ∷ 13 ∷ []) ∷ (7 ∷ 9 ∷ []) ∷ []) ∷ [])
  -- ∷
  -- (((6 ∷ 16 ∷ []) ∷ (10 ∷ 12 ∷ []) ∷ []) ∷
  --  ((7 ∷ 17 ∷ []) ∷ (11 ∷ 13 ∷ []) ∷ []) ∷
  --  ((8 ∷ 18 ∷ []) ∷ (12 ∷ 14 ∷ []) ∷ []) ∷ [])
  -- ∷ []
