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
  
  data P : S → Set where
    ι   : ∀ {n} → Fin n → P (ι n)
    _⊗_ : ∀ {s t} → P s → P t → P (s ⊗ t)
  
  _[[_]] : ∀ {ℓ} → Set ℓ → S → Set ℓ
  X [[ s ]] = P s → X
  
  _[_] : ∀ {ℓ} {X : Set ℓ} {s : S} → X [[ s ]] → P s → X
  a [ i ] = a i

  ar-map : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} {s : S} → (X → Y) → X [[ s ]] → Y [[ s ]]
  ar-map f a i = f (a i)

  K : ∀ {ℓ} {X : Set ℓ} {s : S} → X → X [[ s ]]
  K x _ = x

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
  
  
  -- Get it from Applicative 
  --zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃} {s : S} → (X → Y → Z) → X [[ s ]] → Y [[ s ]] → Z [[ s ]]
  --zipWith f a b i = f (a i) (b i)
  
  
  shapeSize : S → ℕ
  shapeSize (ι n) = n
  shapeSize (s ⊗ t) = shapeSize s * shapeSize t
  
  sameP? : ∀ {s : S} → (p q : P s) → Dec (p ≡ q)
  sameP? {ι n} (ι p) (ι q) with p Fin.≟ q
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
  
  data FoldStep (A B : Set) : Set where
      continue : A → FoldStep A B
      break : B → FoldStep A B

  foldFinUntil : ∀ {A B : Set} → (n : ℕ) →
      (Fin n → A → FoldStep A B) → A → FoldStep A B
  foldFinUntil zero f acc = continue acc

  foldFinUntil (suc n) f acc with f Fin.zero acc
  ... | break r = break r
  ... | continue acc′ = foldFinUntil n
      (λ i → f (Fin.suc i)) acc′

  foldShapeUntil : ∀ {s : S} {A B : Set} →
      (P s → A → FoldStep A B) → A → FoldStep A B
  foldShapeUntil {ι n} f acc = 
      foldFinUntil n (λ i → f (ι i)) acc
  foldShapeUntil {s ⊗ t} f acc =
    foldShapeUntil {s}
      (λ i acc₁ →
        foldShapeUntil {t}
          (λ j acc₂ → f (i ⊗ j) acc₂)
          acc₁)
      acc 


  sumℕ : ∀ {s : S} → ℕ [[ s ]] → ℕ
  sumℕ = reduce _+_ zero
  
  count : ∀ {s : S} → Bool [[ s ]] → ℕ
  count a = foldMap (λ b acc →
      if b
      then suc acc
      else acc) zero a
  
  -- any : ∀ {s : S} → Bool [[ s ]] → Bool
  -- any = reduce _∨_ false

  any : ∀ {s : S} → Bool [[ s ]] → Bool
  any {s} a
    with foldShapeUntil {s = s}
          (λ i _ →
            if a i
            then break true
            else continue tt)
          tt
  ... | break b    = b
  ... | continue _ = false
  
  -- all : ∀ {s : S} → Bool [[ s ]] → Bool
  -- all = reduce _∧_ true
  all : ∀ {s : S} → Bool [[ s ]] → Bool
  all {s} a
    with foldShapeUntil {s = s}
          (λ i _ →
            if a i
            then continue tt
            else break false)
          tt
  ... | break b    = b
  ... | continue _ = true
  
  booleanDot : ∀ {s : S} → Bool [[ s ]] → Bool [[ s ]] → Bool
  booleanDot xs ys = any (zipWith _∧_ xs ys)


  nest : ∀ {X : Set}{s p} → X [[ s ⊗ p ]] →  X [[ p ]] [[ s ]]
  nest a i j = a (i ⊗ j)

  unnest : ∀ {X : Set}{s p} → X [[ p ]] [[ s ]] → X [[ s ⊗ p ]]
  unnest a (i ⊗ j) = a i j

  -- Syntax notation
  _⟨_⟩:=_ : ∀ {X : Set}{s} → X [[ s ]] → P s → X → X [[ s ]]
  a ⟨ i ⟩:= x = updateAt i x a

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
  
    CellIndex = P Cell
    PatternIndex = P Pattern
    DirectionIndex = P Direction
    Wave = Bool [[ Cell ⊗ Pattern ]]
    Propagator =  Bool [[ (Pattern ⊗ Direction) ⊗ Pattern ]]
    Neighbour = Maybe CellIndex [[ Cell ⊗ Direction ]]

  module _ (d : Dimensions) where
    
    open Dimensions d
    
    State = Wave
    Problem = Neighbour × Propagator

    data Success : Set where Done Continue : Success
    data Failure : Set where Fail OffLimit : Failure

    StepResult = Result State (Success × State)
    RunResult  = Result (Failure × State) State

    allowedCount : Wave → ℕ [[ Cell ]]
    allowedCount w = sumℕ <$> (nest $ bool⇒nat <$> w)

    contradictoryAt? : Wave → Bool [[ Cell ]]
    contradictoryAt? w i = does (allowedCount w i ℕ.≟ 0) 

    -- XXX this could be a decideable predicate
    noContradiction? : Wave → Bool
    noContradiction? w = all (not ∘ contradictoryAt? w)

    candidateCell : Maybe (CellIndex × ℕ) → Maybe CellIndex
    candidateCell = Maybe.map proj₁

    insertMRV : (CellIndex × ℕ) → Maybe (CellIndex × ℕ) → (CellIndex × ℕ)
    insertMRV ic nothing = ic
    insertMRV ic (just ic′) = if does (ic .proj₂ ℕ.<? ic′ .proj₂) then ic else ic′

    mrvStep : Wave → CellIndex → Maybe (CellIndex × ℕ) → Maybe (CellIndex × ℕ)
    mrvStep w i with cnt ← allowedCount w i | cnt ℕ.>? 1
    ... | yes _ = just ∘ insertMRV (i , cnt)
    ... | no  _ = id
    
    nextMRVNode : Wave → Maybe CellIndex
    nextMRVNode s = candidateCell (foldShape (mrvStep s) nothing)

    chooseFirstAllowed : Wave → CellIndex → Maybe PatternIndex
    -- chooseFirstAllowed w i = foldShape (λ j → maybe just (bool⇒maybe (w (i ⊗ j)) j)) nothing
    chooseFirstAllowed w i
      with foldShapeUntil {s = Pattern}
            (λ j _ →
              if w (i ⊗ j)
              then break j
              else continue tt)
            tt
    ... | break j    = just j
    ... | continue _ = nothing


    observe : CellIndex → PatternIndex → Wave → Wave
    observe i p w = unnest (nest w ⟨ i ⟩:= (K false ⟨ p ⟩:= w (i ⊗ p)))

    hasSupport? : Problem → Wave →  CellIndex → PatternIndex → DirectionIndex → Bool
    hasSupport? (neighbour , prop) w i j k with neighbour (i ⊗ k)
    ... | nothing = true
    ... | just t = booleanDot (nest w t) (nest prop (j ⊗ k))

    supported? : Problem → Wave → Bool [[ Cell ⊗ Pattern ]]
    supported? p w (i ⊗ j) = all (hasSupport? p w i j) 

    pruneWave : Problem → Wave → Wave
    pruneWave p s (i ⊗ j) = s (i ⊗ j) ∧ supported? p s (i ⊗ j)

    propagateWithLimit : ℕ → Problem → Wave → Wave
    propagateWithLimit 0 p s = s
    propagateWithLimit (suc l) p s = propagateWithLimit l p (pruneWave p s)

    propagate : Problem → Wave → Wave
    propagate = propagateWithLimit (suc (shapeSize (Cell ⊗ Pattern)))
    
    runStep : Problem → Wave → StepResult
    runStep p s = do
      bool⇒res (noContradiction? s) s tt
      maybe⇒inv-res (nextMRVNode s) (Done ,′ s) λ i → do
        j ← maybe⇒res (chooseFirstAllowed s i) s
        let s′ = propagate p (observe i j s)
        bool⇒res (noContradiction? s′) s′ (Continue ,′ s′)

    runLimit : (limit : ℕ) → Problem → Wave → RunResult
    runLimit 0 p s = err (OffLimit , s)
    runLimit (suc l) p s = do
      r , s′ ← (Fail ,′_) <$>ₑ runStep p s
      case r of λ where
        Done → ok s′
        Continue → runLimit l p s′

    run : Problem → Wave → RunResult
    run = runLimit (suc (shapeSize Cell))




