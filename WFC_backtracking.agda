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

  ngb-s : ∀ {s} → P s → P (ι (rank s)) → P (ι 2) → P (full-s s)
  ngb-s (ι i) _ (ι d) = ι (dir i d)
  ngb-s {s ⊗ p} (i ⊗ j) (ι a) d with Fin.splitAt (rank s) a
  ... | inj₁ a′ = ngb-s i (ι a′) d ⊗ embed-s j
  ... | inj₂ a′ = embed-s i ⊗ ngb-s j (ι a′) d
  
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

  open import Data.Maybe as Maybe
  foldN : ∀ {s : S} {A : Set} →
    (P s → A → Maybe A) → Maybe A → Maybe A
  foldN f = foldShape (λ i ma → Maybe._>>=_ ma (f i))
  foldJ : ∀ {s : S} {A : Set} →
    (P s → Maybe A) → Maybe A 
  foldJ f = foldShape (λ i result → Maybe._<∣>_ (f i) result) nothing

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
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans) 
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

    Propagator = Bool [[ (Pattern ⊗ Direction) ⊗ Pattern ]]

  record WaveRep (d : Dimensions) : Set₁ where
    open Dimensions d
    field
      State : Set
      lookup : 
        State → CellIndex → PatternIndex → Bool
      neighbourPatterns :
        State → CellIndex → DirectionIndex → Bool [[ Pattern ]]
      update :
        (CellIndex → PatternIndex → Bool) →
        State → State
      lookup-update :
        ∀ (next : CellIndex → PatternIndex → Bool)
        (w : State) (i : CellIndex) (p : PatternIndex) →
        lookup (update next w) i p ≡ next i p

  module HaloWaveRep (d : Dimensions) where
    open Dimensions d
    HaloState : Set
    HaloState = Bool [[ FullCell ⊗ Pattern ]]

    initialHaloWave : HaloState
    initialHaloWave = K true

    haloLookup : HaloState → CellIndex → PatternIndex → Bool
    haloLookup w i p = w (embed-s i ⊗ p)

    haloNeighbourPatterns :
      HaloState → CellIndex → DirectionIndex → Bool [[ Pattern ]]
    haloNeighbourPatterns w i (axis ⊗ side) =
      nest w (ngb-s i axis side)

    haloUpdate :
      (CellIndex → PatternIndex → Bool) → HaloState → HaloState
    haloUpdate next old = foldShape {s = Cell ⊗ Pattern}
      (λ { (i ⊗ p) acc →
        (acc ⟨ embed-s i ⊗ p ⟩:= (next i p))
      }) old

    postulate
      haloLookup-update :
        ∀ (next : CellIndex → PatternIndex → Bool)
        (w : HaloState) (i : CellIndex) (p : PatternIndex) →
        haloLookup (haloUpdate next w) i p ≡ next i p

    haloWaveRep : WaveRep d
    haloWaveRep =
      record
      {
        State = HaloState; 
        lookup = haloLookup; 
        neighbourPatterns = haloNeighbourPatterns; 
        update = haloUpdate; 
        lookup-update = haloLookup-update
      }

  module Core (d : Dimensions) (R : WaveRep d) where
    open Dimensions d
    open WaveRep R

    wave : State → Bool [[ Cell ⊗ Pattern ]]
    wave w (i ⊗ p) = lookup w i p
    Problem = Propagator

    data Success : Set where Done Continue : Success
    data Failure : Set where Fail OffLimit : Failure
    StepResult = Result State (Success × State)
    RunResult  = Result (Failure × State) State

    allowedCount : State → ℕ [[ Cell ]]
    allowedCount w = sumℕ <$> (nest $ bool⇒nat <$> wave w)

    contradictoryAt? : State → Bool [[ Cell ]]
    contradictoryAt? w i = does (allowedCount w i ℕ.≟ 0) 

    noContradiction? : State → Bool
    noContradiction? w = all (not ∘ contradictoryAt? w)

    candidateCell : Maybe (CellIndex × ℕ) → Maybe CellIndex
    candidateCell = Maybe.map proj₁

    insertMRV : (CellIndex × ℕ) → Maybe (CellIndex × ℕ) → (CellIndex × ℕ)
    insertMRV ic nothing = ic
    insertMRV ic (just ic′) = if does (ic .proj₂ ℕ.<? ic′ .proj₂) then ic else ic′

    mrvStep : State → CellIndex → Maybe (CellIndex × ℕ) → Maybe (CellIndex × ℕ)
    mrvStep w i with cnt ← allowedCount w i | cnt ℕ.>? 1
    ... | yes _ = just ∘ insertMRV (i , cnt)
    ... | no  _ = id
    
    nextMRVNode : State → Maybe CellIndex
    nextMRVNode w = candidateCell (foldShape (mrvStep w) nothing)


    chooseFirstAllowed : State → CellIndex → Maybe PatternIndex
    -- chooseFirstAllowed w i = foldShape
    --   (λ p → maybe just (bool⇒maybe (lookup w i p) p)) nothing
    chooseFirstAllowed w i = foldJ
      (λ p → bool⇒maybe (lookup w i p) p)

    observe :
      CellIndex → PatternIndex → State → State
    observe i p w = update (λ i′ p′ →
      case sameP? i′ i of λ where
        (yes _) →
          case sameP? p′ p of λ where
            (yes _) → lookup w i′ p′
            (no  _) → false
        (no _) →
          lookup w i′ p′)
      w

    hasSupport? :
      Problem → State → CellIndex → PatternIndex → DirectionIndex → Bool
    hasSupport? prop w i p dir =
      booleanDot
        (neighbourPatterns w i dir)
        (nest prop (p ⊗ dir))

    supported? : Problem → State → Bool [[ Cell ⊗ Pattern ]]
    supported? prop w (i ⊗ p) = all (hasSupport? prop w i p)

    pruneWave : Problem → State → State
    pruneWave prop old =
      update (λ i p → lookup old i p ∧ supported? prop old (i ⊗ p)) old

    
    sameBool : Bool → Bool → Bool
    sameBool true true = true
    sameBool false false = true
    sameBool _ _ = false

    sameWave? : State → State → Bool
    sameWave? before after = all {s = Cell ⊗ Pattern}
      (λ { (i ⊗ p) →
        sameBool
          (lookup before i p)
          (lookup after  i p)})

    propagateStep : Problem → State → Success × State
    propagateStep prop w =
      let
        w′ = pruneWave prop w
      in
        if sameWave? w w′
        then Done ,′ w′
        else Continue ,′ w′

    propagateWithLimit :
      ℕ → Problem → State → State
    propagateWithLimit zero prop w = w
    propagateWithLimit (suc n) prop w with propagateStep prop w
    ... | Done , w′ = w′
    ... | Continue , w′ = propagateWithLimit n prop w′

    propagate :
      Problem → State → State
    propagate = propagateWithLimit (suc (shapeSize (Cell ⊗ Pattern)))

    -- runStep : Problem → State → StepResult
    -- runStep p w = do
    --   bool⇒res (noContradiction? w) w tt
    --   maybe⇒inv-res (nextMRVNode w) (Done ,′ w) λ i → do
    --     j ← maybe⇒res (chooseFirstAllowed w i) w
    --     let w′ = propagate p (observe i j w)
    --     bool⇒res (noContradiction? w′) w′ (Continue ,′ w′)

    -- runLimit : (limit : ℕ) → Problem → State → RunResult
    -- runLimit 0 p w = err (OffLimit , w)
    -- runLimit (suc l) p w = do
    --   r , w′ ← (Fail ,′_) <$>ₑ runStep p w
    --   case r of λ where
    --     Done → ok w′
    --     Continue → runLimit l p w′

    -- run : Problem → State → RunResult
    -- run = runLimit (suc (shapeSize Cell))


    -- Backtracking run
    rememberOffLimit : State → RunResult → RunResult
    rememberOffLimit branchState (ok solved) = ok solved
    rememberOffLimit branchState (err (Fail , previousState)) =
      err (OffLimit , branchState)
    rememberOffLimit branchState (err (OffLimit , previousState)) =
      err (OffLimit , previousState)

    tryPattern :
      (State → RunResult) → Problem → State → CellIndex → PatternIndex →
      RunResult → RunResult

    tryPattern recur prop w i p previousResult with lookup w i p
    ... | false = previousResult
    ... | true with recur (propagate prop (observe i p w))
    ...   | ok solved = ok solved

    -- A contradiction in this candidate means only this branch failed.
    -- Evaluating previousResult continues with the remaining candidates,
    -- all of which start again from the unchanged state w.
    ...   | err (Fail , branchState) = previousResult

    -- OffLimit is not a contradiction, so remaining candidates must still
    -- be tried.  If none succeeds, keep OffLimit rather than reporting Fail.
    ...   | err (OffLimit , branchState) =
      rememberOffLimit branchState previousResult

    searchLimit : ℕ → Problem → State → RunResult
    searchLimit zero prop w = err (OffLimit , w)
    searchLimit (suc n) prop w with noContradiction? w
    ... | false = err (Fail , w)
    ... | true with nextMRVNode w
    ...   | nothing = ok w
    ...   | just i = foldShape
        (tryPattern (searchLimit n prop) prop w i)
        (err (Fail , w))

    run : Problem → State → RunResult
    run prop w =
      searchLimit (suc (shapeSize Cell)) prop w


    -- semantic
    Assignment : Set
    Assignment = CellIndex → PatternIndex

    CompatibleWithWave : State → Assignment → Set
    CompatibleWithWave w A = ∀ i → lookup w i (A i) ≡ true

    Satisfies : Problem → Assignment → Set
    Satisfies prop A = ∀ {w : State} →
      CompatibleWithWave w A →
      ∀ i → supported? prop w (i ⊗ A  i) ≡ true

    record LegalSolution (prop : Problem) : Set where
      field
        assignment : Assignment
        satisfies  : Satisfies prop assignment
    open LegalSolution public

    PreservesSolutions : Problem → State → State → Set
    PreservesSolutions prop before after =
      ∀ A →
      Satisfies prop A →
      CompatibleWithWave before A →
      CompatibleWithWave after A
  
    _⊆w_ : State → State → Set
    Φ ⊆w Ψ = ∀ i p →
      lookup Φ i p ≡ true →
      lookup Ψ i p ≡ true
    
    ⊆w-refl : ∀ {Φ : State} → Φ ⊆w Φ
    ⊆w-refl i p h = h

    ⊆w-trans : ∀ {Φ Ψ Ω : State} → Φ ⊆w Ψ → Ψ ⊆w Ω → Φ ⊆w Ω
    ⊆w-trans Φ⊆Ψ Ψ⊆Ω i p h = Ψ⊆Ω i p (Φ⊆Ψ i p h)


    -- propagation only removes patterns
    pruneValue-only-removes : ∀ (prop : Problem)
      (old : State) (i : CellIndex) (p : PatternIndex) →
      (lookup old i p ∧ supported? prop old (i ⊗ p)) ≡ true →
      lookup old i p ≡ true
    pruneValue-only-removes prop old i p h
      with lookup old i p
    ... | true  = refl
    ... | false with h
    ...   | ()

    pruneWave-lookup : ∀ (prop : Problem)
      (old : State) (i : CellIndex) (p : PatternIndex) →
      lookup (pruneWave prop old) i p ≡
      (lookup old i p ∧ supported? prop old (i ⊗ p))
    pruneWave-lookup prop old i p = lookup-update
      (λ i p → lookup old i p ∧ supported? prop old (i ⊗ p)) old i p

    pruneWave-only-removes : ∀ (prop : Problem)
      (old : State) → pruneWave prop old ⊆w old
    pruneWave-only-removes prop old i p h =
      pruneValue-only-removes prop old i p
        (trans
          (sym (pruneWave-lookup prop old i p))
          h)

    propagateStep-only-removes :
      ∀ (prop : Problem) (w : State) →
      proj₂ (propagateStep prop w) ⊆w w
    propagateStep-only-removes prop w
      with sameWave? w (pruneWave prop w)
    ... | true  = pruneWave-only-removes prop w
    ... | false = pruneWave-only-removes prop w

    propagateWithLimit-only-removes :
      ∀ (limit : ℕ) (prop : Problem) (w : State) →
      propagateWithLimit limit prop w ⊆w w
    propagateWithLimit-only-removes zero prop w = 
      ⊆w-refl
    propagateWithLimit-only-removes (suc limit) prop w
      with propagateStep prop w | propagateStep-only-removes prop w
    ... | Done , w′ | w′⊆w = w′⊆w
    ... | Continue , w′ | w′⊆w =
      ⊆w-trans
        (propagateWithLimit-only-removes limit prop w′)
        w′⊆w

    propagate-only-removes :
      ∀ (prop : Problem) (w : State) →
      propagate prop w ⊆w w
    propagate-only-removes prop w =
      propagateWithLimit-only-removes
        (suc (shapeSize (Cell ⊗ Pattern)))
        prop w


    -- propagation does not remove a legal solution
    pruneWave-preserves-solution :
      ∀ (prop : Problem) (before : State) →
      PreservesSolutions prop before (pruneWave prop before)

    pruneWave-preserves-solution
      prop before A sat before-compatible i
      rewrite pruneWave-lookup
            prop before i (A i)
        | before-compatible i
        | sat before-compatible i
      = refl

    propagateStep-preserves-solution :
      ∀ (prop : Problem) (before : State) →
      PreservesSolutions
        prop before
        (proj₂ (propagateStep prop before))
    propagateStep-preserves-solution prop before
      with sameWave? before (pruneWave prop before)
    ... | true  = pruneWave-preserves-solution prop before
    ... | false = pruneWave-preserves-solution prop before

    propagateWithLimit-preserves-solutions :
      ∀ (limit : ℕ) (prop : Problem) (before : State) →
      PreservesSolutions
        prop before
        (propagateWithLimit limit prop before)
    propagateWithLimit-preserves-solutions zero prop before
      A sat before-compatible =
      before-compatible
    propagateWithLimit-preserves-solutions (suc limit) prop before
      with propagateStep prop before
        | propagateStep-preserves-solution prop before
    ... | Done , after | step-preserves =
      step-preserves
    ... | Continue , after | step-preserves =
      λ A sat before-compatible →
        propagateWithLimit-preserves-solutions
          limit prop after
          A sat
          (step-preserves A sat before-compatible)

    propagate-preserves-solutions :
      ∀ (prop : Problem) (before : State) →
      PreservesSolutions prop before (propagate prop before)
    propagate-preserves-solutions prop before =
      propagateWithLimit-preserves-solutions
        (suc (shapeSize (Cell ⊗ Pattern)))
        prop before
