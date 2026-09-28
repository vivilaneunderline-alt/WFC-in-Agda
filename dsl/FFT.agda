--{-# OPTIONS --backtracking-instance-search #-}
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; cast; toℕ)
open import Data.Fin.Properties
open import Function

open import Real using (Real)
open import Complex using (Cplx)

open import Matrix renaming (length to size)
open import Matrix.Reshape
open import Matrix.NonZero 

-- FIXME: these have to be actual definitions!
_ᵗ : Shape → Shape
_ᵗ = recursive-transpose

nzᵗ : NonZeroₛ s → NonZeroₛ (s ᵗ)
nzᵗ = nonZeroₛ-s⇒nonZeroₛ-sᵗ

nz-# : NonZeroₛ s → NonZero (size s)
nz-# = nonZeroₛ-s⇒nonZero-s


infixr 5 _⇒_
data Ty : Set where
  C   : Ty
  ix  : Shape → Ty
  _⇒_ : Ty → Ty → Ty

ar : Shape → Ty → Ty
ar s X = ix s ⇒ X

variable
  τ σ δ : Ty

data Num : Ty → Set where
  C   : Num C
  arr : Num τ → Num (ix s ⇒ τ)

data Fut : Ty → Set where
  num : Num τ → Fut τ
  fun : Num τ → Fut σ → Fut (τ ⇒ σ)

infixl 3 _`$_
data E (V : Ty → Set) : Ty → Set where
  `     : V τ → E V τ
  `lam  : (V τ → E V σ) → E V (τ ⇒ σ)
  _`$_  : E V (τ ⇒ σ) →  E V τ → E V σ
  _`⊗_  : E V (ix s) → E V (ix p) → E V (ix (s ⊗ p))
  `fst  : E V (ix (s ⊗ p)) → E V (ix s)
  `snd  : E V (ix (s ⊗ p)) → E V (ix p)
  `swap : E V (ar (s ⊗ p) τ) → E V (ar (p ⊗ s) τ)
  `sum  : E V (ar (ι n) C) → E V C
  -- Too specialised?
  `ω    : (n : ℕ) → .⦃ NonZero n ⦄ → E V (ix (s ⊗ p)) → E V C
  _`*_  : (a b : E V C) → E V C

infix 1 `lam
syntax `lam (λ x → e) = `λ x ⇒ e

variable
  V : Ty → Set

{-
instance
  out : ⦃ NonZeroₛ (ι n) ⦄ → NonZero n
  out ⦃ ι x ⦄ = x

  ι-ins : ⦃ NonZero n ⦄ → NonZeroₛ (ι n)
  ι-ins ⦃ p ⦄ = ι p

  ⊗-ins : ⦃ NonZeroₛ s ⦄ → ⦃ NonZeroₛ p ⦄ → NonZeroₛ (s ⊗ p)
  ⊗-ins ⦃ p ⦄ ⦃ q ⦄ = p ⊗ q

  ᵗ-ins : ⦃ NonZeroₛ s ⦄ → NonZeroₛ (s ᵗ)
  ᵗ-ins ⦃ p ⦄ = nonZeroₛ-s⇒nonZeroₛ-sᵗ p

  --{-# INCOHERENT ι-ins ᵗ-ins out ⊗-ins #-} 
-}

`mapₐ : E V ((τ ⇒ σ) ⇒ ar s τ ⇒ ar s σ)
`mapₐ = `λ f ⇒ `λ a ⇒ `λ i ⇒ ` f `$ (` a `$ ` i)

`map : E V ((τ ⇒ σ) ⇒ τ ⇒ σ)
`map = `λ f ⇒ `λ a ⇒ ` f `$ ` a

`nest : E V (ar (s ⊗ p) τ ⇒ (ar s (ar p τ)))
`nest = `λ a ⇒ `λ i ⇒ `λ j ⇒ ` a `$ (` i `⊗ ` j)

`unnest : E V (ar s (ar p τ) ⇒ ar (s ⊗ p) τ)
`unnest = `λ a ⇒ `λ i ⇒ ` a `$ `fst (` i) `$ `snd (` i)

`dft : ⦃ NonZero n ⦄ → E V (ar (ι n) C ⇒ ar (ι n) C)
`dft {n = n} = `λ a ⇒ `λ j ⇒ `sum (`λ k ⇒ (` a `$ ` k) `* `ω n (` k `⊗ ` j))


`twid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → E V (ar (s ⊗ p) C)
`twid {s = s}{p} ⦃ nz ⦄ = `λ i ⇒ `ω (size (s ⊗ p)) ⦃ nz-# nz ⦄ (` i)

`fft : ⦃ NonZeroₛ s ⦄ → E V (ar s C ⇒ ar (s ᵗ) C)
`fft ⦃ ι nz    ⦄ = `dft ⦃ nz ⦄
`fft ⦃ ns ⊗ np ⦄ = `λ a ⇒ let 
                            a'  = `swap (` a)
                            r1  = `unnest `$ (`mapₐ `$ `fft ⦃ ns ⦄ `$ (`nest `$ a'))
                            rt  = `λ i ⇒ (r1 `$ ` i) `* (`twid ⦃ np ⊗ nzᵗ ns ⦄ `$ ` i)
                            rt' = `swap rt
                            r2  = `mapₐ `$ `fft ⦃ np ⦄ `$ (`nest `$ rt')
                            r2' = `swap (`unnest `$ r2)
                          in r2'
                          
module Interp (real : Real) (cplx : Cplx) where
  open Cplx cplx renaming (_+_ to _+𝕔_; _*_ to _*𝕔_)
  open Real.Real real using (_ᵣ)
  
  open import Matrix.Equality
  open import FFT cplx
  open import Proof cplx

  Sem : Ty → Set
  Sem C = ℂ
  Sem (ix x) = Position x
  Sem (τ ⇒ σ) = Sem τ → Sem σ

  fst : Position (s ⊗ p) → Position s
  fst (i ⊗ j) = i

  snd : Position (s ⊗ p) → Position p
  snd (i ⊗ j) = j

  interp : E Sem τ → Sem τ
  interp (` x) = x
  interp (`lam f) x = interp (f x)
  interp (e `$ e₁) = interp e (interp e₁)
  interp (e `⊗ e₁) = interp e ⊗ interp e₁
  interp (`fst e) = fst (interp e)
  interp (`snd e) = snd (interp e)
  interp (`swap e) (i ⊗ j) = interp e (j ⊗ i)
  interp (`sum e) = sum (interp e)
  interp (`ω n e) = -ω n (offset-prod (interp e))
  interp (e `* e₁) = interp e *𝕔 interp e₁

  -- I hate stupid instances!
  efft-ok :  ⦃ _ : NonZeroₛ s ⦄ → ∀ a → FFT′ {s} a ≅ interp `fft a
  efft-ok ⦃ ι nz    ⦄ a i       = refl
  efft-ok ⦃ ns ⊗ np ⦄ a (i ⊗ j) =
    begin
      _ ≡⟨ FFT′-cong ⦃ np ⦄ (λ k → cong₂ _*𝕔_ (efft-ok ⦃ ns ⦄ _ j) refl) i ⟩
      _ ≡⟨ efft-ok ⦃ np ⦄ _ i ⟩
      _
    ∎ where open ≡-Reasoning


module Show where
  open import Data.Nat
  open import Data.String hiding (show)
  open import Data.Product
  open import Text.Printf
  open import Effect.Monad 
  open import Effect.Monad.State
  open RawMonadState {{...}}
  open RawMonad {{...}} hiding (_⊗_)
  instance
    _ = monad
    _ = monadState 

  data Ix : Shape → Set where 
    ι   : String → Ix (ι n)
    _⊗_ : Ix s → Ix p → Ix (s ⊗ p)

  Val : Ty → Set
  Val C = String
  Val (ix s) = Ix s
  Val (τ ⇒ σ) = Val τ → State ℕ (Val σ)
  
  fresh : ℕ → String
  fresh = printf "x_%u"

  fresh-ix : String → Ix s
  fresh-ix n = proj₂ (runState (go n) 0)
    where
      go : String → State ℕ (Ix s)
      go {ι x} n = do
        c ← get
        modify suc
        return (ι $′ printf "%s_%u" n c)
      go {s ⊗ p} n = do
        l ← go {s} n
        r ← go {p} n
        return (l ⊗ r)

  dim : Shape → ℕ
  dim (ι _) = 1
  dim (s ⊗ p) = dim s + dim p

  offset : Ix s → String
  offset (ι x) = x
  offset {s ⊗ p} (i ⊗ j) = printf "((%u * %s) + %s)" (size p) (offset i) (offset j)

  shape-args : Shape → String
  shape-args (ι n) = printf "%u" n
  shape-args (s ⊗ p) = printf "%s %s" (shape-args s) (shape-args p)


  ix-join : Ix s → (d : String) → String
  ix-join (ι x) d = x
  ix-join (i ⊗ j) d = ix-join i d ++ d ++ ix-join j d

  ix-map : (String → String) → Ix s → Ix s
  ix-map f (ι x) = ι (f x)
  ix-map f (i ⊗ j) = ix-map f i ⊗ ix-map f j

  ix-fst : Ix (s Shape.⊗ p) → Ix s
  ix-fst (i ⊗ j) = i

  ix-snd : Ix (s Shape.⊗ p) → Ix p
  ix-snd (i ⊗ j) = j

  to-sel : Ix s → String → String
  to-sel i a = a ++ ix-join (ix-map (printf "[%s]") i) ""

  omega : ℕ → Ix (s Shape.⊗ p) → Val C
  omega sz (i ⊗ j) = printf "minus_omega %u (%s * %s)" 
                             sz (offset i) (offset j)
   
  to-val : E Val τ → State ℕ (Val τ)
  to-val (` x) = return x
  to-val (`lam f) = return (to-val ∘ f)
  to-val (e `$ e₁) = do
    f ← to-val e
    x ← to-val e₁
    f x
  to-val (e `⊗ e₁) = _⊗_ <$> to-val e ⊛ to-val e₁
  to-val (`fst e) = ix-fst <$> to-val e
  to-val (`snd e) = ix-snd <$> to-val e
  to-val (`swap e)  = do
    a ← to-val e
    return λ {(i ⊗ j) → a (j ⊗ i)}
  to-val (`sum {n} a) = do
    a ← to-val a
    c ← get
    let x = fresh c
    modify suc
    b ← a (ι x)
    return $ printf "sum (imap %u (\\ %s → %s))" n x b
  to-val (`ω n e) = omega n <$> to-val e
  to-val (e `* e₁) = do
    l ← to-val e
    r ← to-val e₁
    return $ printf "(%s * %s)" l r



  to-str : Fut τ → Val τ → State ℕ String

  -- We don't need to return stateful result right now,
  -- but conceptually, we might need free variables fro higher-oreder
  -- cases if we ever want to support them.
  num-var : Num τ → (n : String) → State ℕ (Val τ)
  num-var C n = return n
  num-var (arr p) n = return λ i → num-var p (to-sel i n)

  to-str (num C) v = return v
  to-str (num (arr {s = s} f)) v = do
    n ← get
    modify suc
    let ix = fresh-ix (fresh n)
    el ← v ix
    elₛ ← to-str (num f) el
    return (printf 
              "(imap%u %s (\\ %s -> %s))"                  -- FIXME: from a brief scan of the futhark docs, map is only supported up to map5
                                                           -- Could be that I have missed something however, as thats map not imap
              (dim s) (shape-args s) (ix-join ix " ") elₛ)

  to-str (fun nv p) v = do
    n ← get
    modify suc
    let x = (fresh n)
    w ← num-var nv x
    el ← v w
    elₛ ← to-str p el
    return (printf "(\\ %s -> %s)" x elₛ) 
 
  show : Fut τ → (∀ {V} → E V τ) → String
  show p e = runState (to-val e >>= to-str p) 0 .proj₂


module Tests where
  open import Data.Empty
  open import Relation.Nullary
  open import Data.String hiding (show)

  open Show

  sh : Shape
  sh = (ι 5 ⊗ ι 6) ⊗ ι 7

  sh-big : Shape
  sh-big = ((ι 5 ⊗ ι 7) ⊗ ι 8) ⊗ (ι 9 ⊗ ι 10)

  fft : E V _
  fft = `fft {s = sh} ⦃ (ι _ ⊗ ι _) ⊗ ι _ ⦄

  fft-big : E V _
  fft-big = `fft {s = sh-big} ⦃ ((ι _ ⊗ ι _) ⊗ ι _) ⊗ (ι _ ⊗ ι _) ⦄

  -- The inner map should normalise away
  test : E V (ar sh C ⇒ ar sh C) 
  test = `λ a ⇒ `mapₐ `$ (`λ z ⇒ ` z) `$ ` a

  -- We can define this expression, but we can't show that
  -- its type is Fut
  scary : E V (ix sh ⇒ ix sh)
  scary = `λ i ⇒ ` i

  _ : Fut (ix s ⇒ ix s) → ⊥
  _ = λ { (num (arr ())) }

  -- This one is ok, because scary will be inlined
  test₁ : E V (ar sh C ⇒ ar sh C) 
  test₁ = `λ a ⇒ `λ i ⇒ ` a `$ (scary `$ ` i) 

  -- Can't have Fut of that type
  test₂ : E V ((C ⇒ C) ⇒ _) 
  test₂ = `λ f ⇒ ` f

  _ : Fut ((C ⇒ C) ⇒ C) → ⊥
  _ = foo where
      foo : _
      foo (num ())
      foo (fun () _)

  -- This is fine
  test₃ :  E V (ar sh C ⇒ ar _ C) 
  test₃ = `λ a ⇒ `swap (` a)

  test₄ : E V (ar (ι 10 ⊗ ι 10) C ⇒ C) 
  test₄ = `λ a ⇒ `sum (`λ i ⇒ `sum (`λ j ⇒ ` a `$ (` j `⊗ ` i)))

  getType : E V τ → Ty
  getType {τ = τ} _ = τ 

  isNum : (τ : Ty) → Dec (Num τ)
  isNum C = yes C
  isNum (ix x) = no λ ()
  isNum (C ⇒ σ) = no λ ()
  isNum ((_ ⇒ _) ⇒ σ) = no λ ()
  isNum (ix x ⇒ σ) with isNum σ
  ... | yes p = yes (arr p)
  ... | no ¬p = no λ { (arr p) → ¬p p }

  isFut : (τ : Ty) → Dec (Fut τ)
  isFut C = yes (num C)
  isFut (ix x) = no λ { (num ()) }
  isFut (C ⇒ σ) with isFut σ
  ... | no ¬p = no λ { (fun _ p) → ¬p p }
  ... | yes p = yes (fun C p) 
  isFut (ix x ⇒ σ) with isNum σ
  ... | no ¬p = no λ { (num (arr p)) → ¬p p }
  ... | yes p = yes (num (arr p))
  isFut (τ@(_ ⇒ _) ⇒ σ) with isNum τ
  ... | no ¬p = no λ { (fun p _) → ¬p p }
  ... | yes p with isFut σ
  ... | no ¬q = no λ { (fun _ q) → ¬q q }
  ... | yes q = yes (fun p q)

  show-test : (∀ {V} → E V τ) → True (isFut τ) → String
  show-test {τ = τ} e t with isFut τ
  ... | yes p = show p e

  res = show-test fft _
  _ : res ≡ ?
  _ = ?



{-
-- Output of the `show fft`:
(\ x_1 -> 
      (imap2 6 5 (\ x_2_0 x_2_1 -> 
          sum (imap 6 (\ x_3 → 
              ((sum (imap 5 (\ x_7 → (x_1[x_2_1][x_2_0] 
                                     * minus_omega 5 (x_2_1 * x_7))))
                * minus_omega 30 (x_2_1 * x_2_0))
               * minus_omega 6 (x_2_0 * x_3))
            )))))
-}
{-
λ real cplx a i j →
  FFT.sum′ real cplx
  (λ i₁ →
     (cplx Cplx.*
      (cplx Cplx.*
       FFT.sum′ real cplx
       (λ i₂ →
          (cplx Cplx.* a (i₂ ⊗ i₁))
          (Cplx.-ω cplx 5 (FFT.iota real cplx i₂ * FFT.iota real cplx j))))
      (Cplx.-ω cplx 30 (FFT.iota real cplx i₁ * FFT.iota real cplx j)))
     (Cplx.-ω cplx 6 (FFT.iota real cplx i₁ * FFT.iota real cplx i)))
-}
{-
(\ x_0 -> 
 (imap2 6 5 (\ x_1_0 x_1_1 -> 
  sum (imap 6 (\ x_2 → 
    ((sum (imap 5 (\ x_3 → 
       (x_0[x_3][x_2] 
        * minus_omega 5 (x_3 * x_1_1))))
      * minus_omega 30 (x_2 * x_1_1))
    * minus_omega 6 (x_2 * x_1_0)))))))
-}

{-
5,6,7 example

(\ x_0 -> 
 (imap3 7 6 5 (\ x_1_0 x_1_1 x_1_2 -> 
               sum (imap 7 (\ x_2 → 
                            ((sum (imap 6 (\ x_3 → 
                                           ((sum (imap 5 (\ x_4 →
                                                          (x_0[x_4][x_3][x_2] * minus_omega 5 (x_4 * x_1_2))))
                                             * minus_omega 210 (((7 * x_3) + x_2) * x_1_2))
                                            * minus_omega 6 (x_3 * x_1_1))))
                              * minus_omega 42 (x_2 * x_1_1))
                             * minus_omega 7 (x_2 * x_1_0)))))))



(\ x_0 -> 
 (imap3 7 6 5 (\ x_1_0 x_1_1 x_1_2 -> 
               sum (imap 7 (\ x_2 → 
                            ((sum (imap 6 (\ x_3 →
                                           ((sum (imap 5 (\ x_4 →
                                                          (x_0[x_4][x_3][x_2] * minus_omega 5 (x_4 * x_1_2))))
                                             * minus_omega 30 (x_3 * x_1_2))
                                            * minus_omega 6 (x_3 * x_1_1))))
                              * minus_omega 210 (x_2 * ((5 * x_1_1) + x_1_2)))
                             * minus_omega 7 (x_2 * x_1_0)))))))


-}
