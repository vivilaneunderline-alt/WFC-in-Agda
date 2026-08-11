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
  open import Data.Sum using (inj₁; inj₂)
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
  
  
  --zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Set ℓ₃} {s : S} → (X → Y → Z) → X [[ s ]] → Y [[ s ]] → Z [[ s ]]
  --zipWith f a b i = f (a i) (b i)
  
  shapeSize : S → ℕ
  shapeSize (ι n) = n
  shapeSize (s ⊗ t) = shapeSize s * shapeSize t

  
  rank : S → ℕ
  rank (ι _) = 1
  rank (s ⊗ p) = rank s + rank p

  prev : ∀ {n} → Fin n → Fin (2 + n)
  prev Fin.zero = Fin.zero
  prev (Fin.suc i) = Fin.suc (prev i)

  next : ∀ {n} → Fin n → Fin (2 + n)
  next i = Fin.suc (Fin.suc i)

  lift : ∀ {n} → Fin n → Fin (1 + n)
  lift Fin.zero = Fin.zero
  lift (Fin.suc i) = Fin.suc (lift i)

  embed : ∀ {n} → Fin n → Fin (2 + n)
  embed i = Fin.suc (lift i)

  dir : ∀ {n} → Fin n → Fin 2 → Fin (2 + n)
  dir i Fin.zero = prev i
  dir i _ = next i

  full-s : S → S
  full-s (ι n) = ι (2 + n)
  full-s (s ⊗ p) = full-s s ⊗ full-s p

  embed-s : ∀ {s} → P s → P (full-s s)
  embed-s (ι i) = ι (embed i)
  embed-s (i ⊗ j) = embed-s i ⊗ embed-s j

  ngb : ∀ {s} → P s → P (ι (rank s)) → P (ι 2) → P (full-s s)
  ngb (ι i) _ (ι d) = ι (dir i d)
  ngb {s ⊗ p} (i ⊗ j) (ι a) d with Fin.splitAt (rank s) a
  ... | inj₁ a′ = ngb i (ι a′) d ⊗ embed-s j
  ... | inj₂ a′ = embed-s i ⊗ ngb j (ι a′) d
  
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

  maybe⇒inv-res : {X Y E : Set} (m : Maybe X) (y : Y) (f : X → Result E Y) → Result E Y
  maybe⇒inv-res nothing  y f = pure y
  maybe⇒inv-res (just i) y f = f i


module WFC where
  open import Data.Fin as Fin using (Fin) 
  open import Data.Sum using (inj₁; inj₂)
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

    Axis : S
    Axis = ι (rank Cell)
    Side : S
    Side = ι 2
    Direction : S
    Direction = Axis ⊗ Side

    FullCell : S
    FullCell = full-s Cell

    CellIndex = P Cell
    FullCellIndex = P FullCell
    PatternIndex = P Pattern
    AxisIndex = P Axis
    SideIndex = P Side
    DirectionIndex = P Direction

    Wave = Bool [[ FullCell ⊗ Pattern ]]
    Propagator = Bool [[ (Pattern ⊗ Direction) ⊗ Pattern ]]

  module _ (d : Dimensions) where
    
    open Dimensions d
    
    State = Wave
    Problem = Propagator

    data Success : Set where Done Continue : Success
    data Failure : Set where Fail OffLimit : Failure

    StepResult = Result State (Success × State)
    RunResult  = Result (Failure × State) State


    interiorCell : CellIndex → FullCellIndex
    interiorCell = embed-s

    ngbCell : CellIndex → AxisIndex → SideIndex → FullCellIndex
    ngbCell i axis side = ngb i axis side

    neighbour : CellIndex → DirectionIndex → FullCellIndex
    neighbour i (axis ⊗ side) = ngbCell i axis side

    realWave : Wave → Bool [[ Cell ⊗ Pattern ]]
    realWave w (i ⊗ p) = w (interiorCell i ⊗ p)


    initialWave : Wave
    initialWave = K true

    allowedCount : Wave → ℕ [[ Cell ]]
    allowedCount w = sumℕ <$> (nest $ bool⇒nat <$> realWave w)

    contradictoryAt? : Wave → Bool [[ Cell ]]
    contradictoryAt? w i = does (allowedCount w i ℕ.≟ 0) 

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
    chooseFirstAllowed w i = foldShape
      (λ j → maybe just (bool⇒maybe (w (interiorCell i ⊗ j)) j)) nothing

    observe : CellIndex → PatternIndex → Wave → Wave
    observe i p w = unnest
      (nest w ⟨ interiorCell i ⟩:= (K false ⟨ p ⟩:= w (interiorCell i ⊗ p)))

    hasSupport? :
      Problem → Wave → CellIndex → PatternIndex → DirectionIndex → Bool
    hasSupport? prop w i p dir =
      booleanDot
        (nest w (neighbour i dir))
        (nest prop (p ⊗ dir))

    supported? : Problem → Wave → Bool [[ Cell ⊗ Pattern ]]
    supported? prop w (i ⊗ p) = all (hasSupport? prop w i p)

    -- pruneValue : Problem → Wave → CellIndex → PatternIndex → Bool
    -- pruneValue prop old i p =
    --   old (interiorCell i ⊗ p)
    --   ∧ supported? prop old (i ⊗ p)

    -- pruneCell : Problem → Wave → CellIndex → Wave → Wave
    -- pruneCell prop old i acc = foldShape {Pattern}
    --   (λ p acc′ → updateAt
    --   (interiorCell i ⊗ p) (pruneValue prop old i p) acc′)
    --   acc

    -- pruneWave : Problem → Wave → Wave
    -- pruneWave prop old = foldShape {Cell}
    --   (λ i acc → pruneCell prop old i acc) old

    pruneWave : Problem → Wave → Wave
    pruneWave prop old =
      foldShape {Cell ⊗ Pattern}
        (λ { (i ⊗ p) acc →
          acc ⟨ interiorCell i ⊗ p ⟩:=
          (old (interiorCell i ⊗ p) ∧ supported? prop old (i ⊗ p))
        }) old

    -- propagateWithLimit : ℕ → Problem → Wave → Wave
    -- propagateWithLimit 0 p s = s
    -- propagateWithLimit (suc l) p s = propagateWithLimit l p (pruneWave p s)

    -- propagate : Problem → Wave → Wave
    -- propagate = propagateWithLimit (suc (shapeSize (Cell ⊗ Pattern)))
    
    sameBool : Bool → Bool → Bool
    sameBool true true = true
    sameBool false false = true
    sameBool _ _ = false

    sameRealWave? : Wave → Wave → Bool
    sameRealWave? before after =
      all λ cp →
        sameBool
          (realWave before cp)
          (realWave after cp)

    propagateStep : Problem → Wave → Success × Wave
    propagateStep prop w =
      let
        w′ = pruneWave prop w
      in
        if sameRealWave? w w′
        then Done ,′ w′
        else Continue ,′ w′

    propagateWithLimit : ℕ → Problem → Wave → Wave
    propagateWithLimit zero prop w = w
    propagateWithLimit (suc n) prop w with propagateStep prop w
    ... | Done , w′ = w′
    ... | Continue , w′ = propagateWithLimit n prop w′

    propagate : Problem → Wave → Wave
    propagate =
      propagateWithLimit (suc (shapeSize (Cell ⊗ Pattern)))


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



    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    
    _⊆w_ : Wave → Wave → Set
    Φ ⊆w Ψ = ∀ i p →
      Φ (interiorCell i ⊗ p) ≡ true →
      Ψ (interiorCell i ⊗ p) ≡ true
    
    ⊆w-refl : ∀ {Φ : Wave} → Φ ⊆w Φ
    ⊆w-refl i p h = h

    ⊆w-trans : ∀ {Φ Ψ Ω : Wave} → Φ ⊆w Ψ → Ψ ⊆w Ω → Φ ⊆w Ω
    ⊆w-trans Φ⊆Ψ Ψ⊆Ω i p h = Ψ⊆Ω i p (Φ⊆Ψ i p h)

    _⊆full_ : Wave → Wave → Set
    Φ ⊆full Ψ = ∀ k → 
      Φ k ≡ true → Ψ k ≡ true

    ⊆full-refl : ∀ {Φ : Wave} → Φ ⊆full Φ
    ⊆full-refl k h = h

    ⊆full-trans : ∀ {Φ Ψ Ω : Wave} → Φ ⊆full Ψ → Ψ ⊆full Ω → Φ ⊆full Ω
    ⊆full-trans Φ⊆Ψ Ψ⊆Ω k h = Ψ⊆Ω k (Φ⊆Ψ k h)

    full⊆⇒real⊆ : ∀ {Φ Ψ : Wave} → Φ ⊆full Ψ → Φ ⊆w Ψ
    full⊆⇒real⊆ Φ⊆Ψ i p h = Φ⊆Ψ (interiorCell i ⊗ p) h

    foldFin-preserves : ∀ {A : Set} {n : ℕ}
      (Inv : A → Set) (f : Fin n → A → A) →
      (∀ i acc → Inv acc → Inv (f i acc)) →
      ∀ z → Inv z → Inv (foldFin n f z)
    foldFin-preserves {n = zero} Inv f step z Inv-z = Inv-z
    foldFin-preserves {n = suc n} Inv f step z Inv-z =
      step Fin.zero (foldFin n (λ i acc → f (Fin.suc i) acc) z)
      (foldFin-preserves
        Inv
        (λ i acc → f (Fin.suc i) acc)
        (λ i acc h → step (Fin.suc i) acc h)
        z Inv-z)

    foldShape-preserves : ∀ {A : Set} {s : S}
      (Inv : A → Set) (f : P s → A → A) →
      (∀ i acc → Inv acc → Inv (f i acc)) →
      ∀ z → Inv z → Inv (foldShape {s} f z)
    foldShape-preserves {s = ι n} Inv f step z Inv-z =
      foldFin-preserves
        Inv
        (λ i acc → f (ι i) acc)
        (λ i acc h → step (ι i) acc h)
        z Inv-z
    foldShape-preserves {s = s ⊗ t} Inv f step z Inv-z =
      foldShape-preserves {s = s}
        Inv
        (λ i acc₁ → foldShape {t} (λ j acc₂ → f (i ⊗ j) acc₂) acc₁)
        (λ i acc₁ h₁ →
          foldShape-preserves {s = t}
            Inv
            (λ j acc₂ → f (i ⊗ j) acc₂)
            (λ j acc₂ h₂ → step (i ⊗ j) acc₂ h₂)
            acc₁ h₁)
        z Inv-z
    
    -- propagation only removes patterns
    updateAt-only-removes : ∀ {old acc : Wave}
      (k : P (FullCell ⊗ Pattern)) (x : Bool) →
      acc ⊆full old → (x ≡ true → old k ≡ true) →
      (acc ⟨ k ⟩:= x) ⊆full old
    updateAt-only-removes {old} {acc} k x acc⊆old x-ok j h
      with sameP? j k
    ... | yes refl = x-ok h
    ... | no _ = acc⊆old j h

    pruneValue-only-removes : ∀ (prop : Problem)
      (old : Wave) (i : CellIndex) (p : PatternIndex) →
      (old (interiorCell i ⊗ p) ∧ supported? prop old (i ⊗ p)) ≡ true →
      old (interiorCell i ⊗ p) ≡ true
    pruneValue-only-removes prop old i p h
      with old (interiorCell i ⊗ p)
    ... | true  = refl
    ... | false with h
    ...   | ()

    pruneWave-only-removes-full : ∀ (prop : Problem)
      (old : Wave) → pruneWave prop old ⊆full old
    pruneWave-only-removes-full prop old =
      foldShape-preserves {s = Cell ⊗ Pattern}
        (λ acc → acc ⊆full old)
        (λ { (i ⊗ p) acc →
          acc ⟨ interiorCell i ⊗ p ⟩:=
          (old (interiorCell i ⊗ p) ∧ supported? prop old (i ⊗ p))
        })
        (λ { (i ⊗ p) acc acc⊆old →
          updateAt-only-removes
            (interiorCell i ⊗ p)
            (old (interiorCell i ⊗ p) ∧ supported? prop old (i ⊗ p))
            acc⊆old
            (pruneValue-only-removes prop old i p)
        })
        old
        ⊆full-refl

    pruneWave-only-removes : ∀ (prop : Problem)
      (old : Wave) → pruneWave prop old ⊆w old
    pruneWave-only-removes prop old =
      full⊆⇒real⊆ (pruneWave-only-removes-full prop old)


    FullAssignment : Set
    FullAssignment = FullCellIndex → PatternIndex

    CompatibleWithWave : Wave → FullAssignment → Set
    CompatibleWithWave w A = ∀ fc → w (fc ⊗ A fc) ≡ true

    Satisfies : Problem → FullAssignment → Set
    Satisfies prop A = ∀ {w : Wave} →
      CompatibleWithWave w A →
      ∀ i → supported? prop w (i ⊗ A (interiorCell i)) ≡ true

    record LegalSolution (prop : Problem) : Set where
      field
        assignment : FullAssignment
        satisfies  : Satisfies prop assignment
    open LegalSolution public

    PreservesSolutions : Problem → Wave → Wave → Set
    PreservesSolutions prop before after =
      ∀ A →
      Satisfies prop A →
      CompatibleWithWave before A →
      CompatibleWithWave after A
