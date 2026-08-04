open import Data.Nat as ℕ
open import Data.Bool
open import Effect.Monad using (RawMonad)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open RawMonad {{...}} hiding (_⊗_)

module _ where

module Res where

  data Result (E A : Set) : Set where
    ok  : A → Result E A 
    err : E → Result E A 

  instance
    resFunctor : ∀ {E} → RawFunctor (Result E)
    (resFunctor RawFunctor.<$> f) (ok x) = ok (f x)
    (resFunctor RawFunctor.<$> f) (err x) = err x

    resApplicative : ∀ {E} → RawApplicative (Result E)
    resApplicative .RawApplicative.rawFunctor = resFunctor
    resApplicative .RawApplicative.pure = ok
    (resApplicative RawApplicative.<*> ok f) r = RawFunctor._<$>_ resFunctor f r
    (resApplicative RawApplicative.<*> err x) r = err x

    resMonad : ∀ {E} → RawMonad (Result E)
    resMonad .RawMonad.rawApplicative = resApplicative
    (resMonad RawMonad.>>= ok x) f = f x
    (resMonad RawMonad.>>= err x) f = err x

  infixr 4 _<$>ₑ_
  _<$>ₑ_ : ∀ {E E′ X : Set} → (E → E′) → Result E X → Result E′ X
  f <$>ₑ (ok x) = ok x
  f <$>ₑ (err e) = err (f e)

module ArOps where
  open import Data.Fin as Fin using (Fin) 
  open import Relation.Nullary using (Dec; yes; no) 
  open import Relation.Binary.PropositionalEquality using (_≡_; refl) 

  data S : Set where
    ι   : ℕ → S
    _⊗_ : S → S → S
    _⊕_ : S → S → S
  
  data P : S → Set where
    ι   : ∀ {n} → Fin n → P (ι n)
    _⊗_ : ∀ {s t} → P s → P t → P (s ⊗ t)
    inj₁ : ∀ {s t} → P s → P (s ⊕ t)
    inj₂ : ∀ {s t} → P t → P (s ⊕ t)
  
  _[[_]] : ∀ {ℓ} → Set ℓ → S → Set ℓ
  X [[ s ]] = P s → X
  
  _[_] : ∀ {ℓ} {X : Set ℓ} {s : S} → X [[ s ]] → P s → X
  a [ i ] = a i

  ar-map : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} {s : S} → (X → Y) → X [[ s ]] → Y [[ s ]]
  ar-map f a i = f (a i)

  K : ∀ {ℓ} {X : Set ℓ} {s : S} → X → X [[ s ]]
  K x _ = x
  
  --zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃} {s : S} → (X → Y → Z) → X [[ s ]] → Y [[ s ]] → Z [[ s ]]
  --zipWith f a b i = f (a i) (b i)

  instance
    ArFunctor : ∀ {s ℓ} → RawFunctor {ℓ} (_[[ s ]])
    ArFunctor .RawFunctor._<$>_ = ar-map

    ArApplicative : ∀ {s ℓ} → RawApplicative {ℓ} (_[[ s ]])
    ArApplicative .RawApplicative.rawFunctor = ArFunctor
    ArApplicative .RawApplicative.pure = K
    ArApplicative .RawApplicative._<*>_ = λ fs a i → fs i (a i)

    ArMonad : ∀ {s ℓ} → RawMonad {ℓ} (_[[ s ]])
    ArMonad .RawMonad.rawApplicative = ArApplicative
    ArMonad .RawMonad._>>=_ = λ a mf i → mf (a i) i
  

  shapeSize : S → ℕ
  shapeSize (ι n) = n
  shapeSize (s ⊗ t) = shapeSize s * shapeSize t
  shapeSize (s ⊕ t) = shapeSize s + shapeSize t
  
  sameP? : ∀ {s : S} → (p q : P s) → Dec (p ≡ q)
  sameP? {ι n} (ι p) (ι q) with p Fin.≟ q
  ... | yes refl = yes refl
  ... | no p≢q = no λ { refl → p≢q refl }
  
  sameP? {s ⊗ t} (p₁ ⊗ p₂) (q₁ ⊗ q₂)
    with sameP? p₁ q₁ | sameP? p₂ q₂
  ... | yes refl | yes refl = yes refl
  ... | no p≢q  | _        = no λ { refl → p≢q refl }
  ... | yes refl | no p≢q  = no λ { refl → p≢q refl }
  
  sameP? {s ⊕ t} (inj₁ p) (inj₁ q) with sameP? p q
  ... | yes refl = yes refl
  ... | no p≢q  = no λ { refl → p≢q refl }
  sameP? {s ⊕ t} (inj₂ p) (inj₂ q) with sameP? p q
  ... | yes refl = yes refl
  ... | no p≢q  = no λ { refl → p≢q refl }
  sameP? {s ⊕ t} (inj₁ p) (inj₂ q) = no λ ()
  sameP? {s ⊕ t} (inj₂ p) (inj₁ q) = no λ ()

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
  foldShape {s ⊕ t} f z =
    foldShape {s} (λ i acc → f (inj₁ i) acc)
      (foldShape {t} (λ j acc → f (inj₂ j) acc) z)

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


  nest : ∀ {X : Set}{s p} → X [[ s ⊗ p ]] →  X [[ p ]] [[ s ]]
  nest a i j = a (i ⊗ j)

  unnest : ∀ {X : Set}{s p} → X [[ p ]] [[ s ]] → X [[ s ⊗ p ]]
  unnest a (i ⊗ j) = a i j

  -- Syntax notation
  _⟨_⟩:=_ : ∀ {X : Set}{s} → X [[ s ]] → P s → X → X [[ s ]]
  a ⟨ i ⟩:= x = updateAt i x a

  -- foldN : ∀ {s : S} {A : Set} →
  --   (P s → A → Maybe A) → Maybe A → Maybe A
  -- foldN f = foldShape (λ i ma → ma >>= f i)

  -- foldJ : ∀ {s : S} {A : Set} →
  --   (P s → Maybe A) → Maybe A 
  -- foldJ f = foldShape (λ i result → f i <∣> result) nothing

module Helper where
  open import Data.Maybe
  open Res

  bool⇒nat : Bool → ℕ
  bool⇒nat false = 0
  bool⇒nat true = 1

  bool⇒maybe : ∀ {X  : Set} → Bool → X → Maybe X
  bool⇒maybe false x = nothing
  bool⇒maybe true x = just x

  maybe⇒res : ∀ {X Y : Set} → Maybe X → Y → Result Y X
  maybe⇒res nothing  y = err y
  maybe⇒res (just x) _ = ok x

  bool⇒res : ∀ {X Y : Set} → Bool → Y → X → Result Y X
  bool⇒res b y x = maybe⇒res (bool⇒maybe b x) y

  -- If m == nothing, return (ok y).
  -- If m == just i, compute f i.
  maybe⇒inv-res : {X Y E : Set} (m : Maybe X) (y : Y) (f : X → Result E Y) → Result E Y
  maybe⇒inv-res nothing  y f = pure y
  maybe⇒inv-res (just i) y f = f i


module WFC where

  open import Data.Maybe as Maybe hiding (_>>=_)
  open import Data.Maybe.Instances
  open import Data.Product as Prod
  open import Data.Unit
  open import Data.Fin as Fin using (Fin; zero)
  open import Relation.Nullary
  open import Function
  
  open Res
  open ArOps
  open Helper
 
  record Dimensions : Set where
    field
        Cell : S
        Pattern : S
        Direction : S
    
    ExCell : S
    ExCell = Cell ⊕ Direction
    ExPattern : S
    ExPattern = Pattern ⊕ ι 1
  
    CellIndex = P Cell
    PatternIndex = P Pattern
    DirectionIndex = P Direction

    ExCellIndex = P ExCell
    ExPatternIndex = P ExPattern

    Wave = Bool [[ ExCell ⊗ ExPattern ]]
    BasePropagator = Bool [[ (Pattern ⊗ Direction) ⊗ Pattern ]]
    Propagator = Bool [[ (ExPattern ⊗ Direction) ⊗ ExPattern ]]
    Neighbour = ExCellIndex [[ Cell ⊗ Direction ]]

  module _ (d : Dimensions) where
    
    open Dimensions d
    
    State = Wave
    Problem = Neighbour × Propagator

    data Success : Set where Done Continue : Success
    data Failure : Set where Fail OffLimit : Failure

    StepResult = Result State (Success × State)
    RunResult  = Result (Failure × State) State

------------------------------------------------------
    realCell : CellIndex → ExCellIndex
    realCell = inj₁

    ghostCell : DirectionIndex → ExCellIndex
    ghostCell = inj₂

    realPattern : PatternIndex → ExPatternIndex
    realPattern = inj₁

    outsidePattern : ExPatternIndex
    outsidePattern = inj₂ (ι Fin.zero)

    exPropagator : BasePropagator → Propagator
    exPropagator base ((inj₁ p ⊗ dir) ⊗ inj₁ q) =
      base ((p ⊗ dir) ⊗ q)
    exPropagator base ((inj₁ p ⊗ dir) ⊗ inj₂ outside) = true
    exPropagator base ((inj₂ outside ⊗ dir) ⊗ target) = false

    initialWave : Wave
    initialWave (inj₁ i ⊗ inj₁ p) = true
    initialWave (inj₁ i ⊗ inj₂ o) = false
    initialWave (inj₂ g ⊗ inj₁ p) = false
    initialWave (inj₂ g ⊗ inj₂ o) = true

    realWave : Wave → Bool [[ Cell ⊗ Pattern ]]
    realWave w (i ⊗ p) = w (realCell i ⊗ realPattern p)
-------------------------------------------------------

    allowedCount : Wave → ℕ [[ Cell ]]
    allowedCount w = sumℕ <$> nest (bool⇒nat <$> realWave w)

    contradictoryAt? : Wave → Bool [[ Cell ]]
    contradictoryAt? w i = does (allowedCount w i ℕ.≟ 0)

    noContradiction? : Wave → Bool
    noContradiction? w = all (not ∘ contradictoryAt? w)

    candidateCell : Maybe (CellIndex × ℕ) → Maybe CellIndex
    candidateCell = Maybe.map proj₁

    insertMRV : (CellIndex × ℕ) → Maybe (CellIndex × ℕ) → CellIndex × ℕ
    insertMRV ic nothing = ic
    insertMRV ic (just ic′) =
      if does (ic .proj₂ ℕ.<? ic′ .proj₂) then ic else ic′

    mrvStep : Wave → CellIndex →
              Maybe (CellIndex × ℕ) → Maybe (CellIndex × ℕ)
    mrvStep w i with cnt ← allowedCount w i | cnt ℕ.>? 1
    ... | yes _ = just ∘ insertMRV (i , cnt)
    ... | no  _ = id

    nextMRVNode : Wave → Maybe CellIndex
    nextMRVNode w = candidateCell (foldShape (mrvStep w) nothing)
--------------------------------------------------------

    chooseFirstAllowed : Wave → CellIndex → Maybe PatternIndex
    chooseFirstAllowed w i =
      foldShape
        (λ p → Maybe.maybe just
          (bool⇒maybe (w (realCell i ⊗ realPattern p)) p))
        nothing

    observe : CellIndex → PatternIndex → Wave → Wave
    observe i p w =
      unnest
        (nest w ⟨ realCell i ⟩:=
          (K false ⟨ realPattern p ⟩:=
            w (realCell i ⊗ realPattern p)))

    hasSupport? : Problem → Wave → CellIndex → PatternIndex →
                  DirectionIndex → Bool
    hasSupport? (neighbour , prop) w i p dir =
      booleanDot
        (nest w (neighbour (i ⊗ dir)))
        (nest prop (realPattern p ⊗ dir))

    supported? : Problem → Wave → Bool [[ Cell ⊗ Pattern ]]
    supported? problem w (i ⊗ p) = all (hasSupport? problem w i p)

    pruneWave : Problem → Wave → Wave
    pruneWave problem w (inj₁ i ⊗ inj₁ p) =
      w (realCell i ⊗ realPattern p) ∧ supported? problem w (i ⊗ p)
    pruneWave problem w (inj₁ i ⊗ inj₂ outside) =
      w (inj₁ i ⊗ inj₂ outside)
    pruneWave problem w (inj₂ ghost ⊗ Pattern) =
      w (inj₂ ghost ⊗ Pattern)
