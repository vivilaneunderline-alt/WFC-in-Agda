module Parser where

open import WFC_parametric

open WFC_parametric.Res
open WFC_parametric.ArOps
open WFC_parametric.WFC

open import Data.Nat as ℕ
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Show using (show)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String; primStringToList; primStringAppend)
open import Relation.Nullary using (does)



infixr 5 _++s_

_++s_ : String → String → String
_++s_ = primStringAppend


record DSLSpec : Set where
  field
    gridSize  : ℕ
    threshold : ℕ
    patternCount  : ℕ

open DSLSpec public


isColon : Char → Bool
isColon ':' = true
isColon _   = false

digitValue : Char → Maybe ℕ
digitValue '0' = just 0
digitValue '1' = just 1
digitValue '2' = just 2
digitValue '3' = just 3
digitValue '4' = just 4
digitValue '5' = just 5
digitValue '6' = just 6
digitValue '7' = just 7
digitValue '8' = just 8
digitValue '9' = just 9
digitValue _   = nothing

addDigit : ℕ → ℕ → ℕ
addDigit acc d = acc * 10 + d

parseNatUntilColonAux : List Char → ℕ → Bool → Maybe (ℕ × List Char)
parseNatUntilColonAux [] acc seenDigit = nothing
parseNatUntilColonAux (c ∷ cs) acc seenDigit with isColon c
... | true =
  if seenDigit
  then just (acc , cs)
  else nothing
... | false with digitValue c
... | nothing = nothing
... | just d = parseNatUntilColonAux cs (addDigit acc d) true

parseNatUntilColon : List Char → Maybe (ℕ × List Char)
parseNatUntilColon cs = parseNatUntilColonAux cs 0 false

parseChars : List Char → Maybe DSLSpec
parseChars cs with parseNatUntilColon cs
... | nothing = nothing
... | just (n , rest₁) with parseNatUntilColon rest₁
... | nothing = nothing
... | just (th , rest₂) with parseNatUntilColon rest₂
... | nothing = nothing
... | just (k , rest₃) =
  just record
  { 
    gridSize  = n; 
    threshold = th; 
    patternCount  = k
  }

parse : String → Maybe DSLSpec
parse input = parseChars (primStringToList input)


module GridProblem (n k th : ℕ)
  where

  GridCell : S
  GridCell = ι n ⊗ ι n

  GridPattern : S
  GridPattern = ι k

  GridDimensions : Dimensions
  GridDimensions =
    record
    { 
      Cell    = GridCell; 
      Pattern = GridPattern
    }

  open Dimensions GridDimensions

  module H = HaloWaveRep GridDimensions
  module C = Core GridDimensions H.haloWaveRep

  absDiff : ℕ → ℕ → ℕ
  absDiff m n = (m ∸ n) + (n ∸ m)

  withinThreshold : ℕ → ℕ → ℕ → Bool
  withinThreshold threshold m n = ℕ._≤ᵇ_ (absDiff m n) threshold

  notSamePattern : Fin k → Fin k → Bool
  notSamePattern p q = not (does (toℕ p ℕ.≟ toℕ q))

  nearPattern : Fin k → Fin k → Bool
  nearPattern p q = withinThreshold th (toℕ p) (toℕ q) ∧ notSamePattern p q

  gridPropagator : Propagator
  gridPropagator
    ((ι p ⊗ (axis ⊗ side)) ⊗ ι q) = nearPattern p q


  initialState : H.HaloState
  initialState = H.initialHaloWave

  runResult : C.RunResult
  runResult = C.run gridPropagator initialState


  showFin : ∀ {m : ℕ} → Fin m → String
  showFin i = show (toℕ i)

  showMaybePattern : Maybe (P GridPattern) → String
  showMaybePattern nothing = "?"
  showMaybePattern (just (ι p)) = showFin p

  renderRow : H.HaloState → Fin n → String
  renderRow w x =
    foldFin n
      (λ y acc →
        showMaybePattern
          (C.chooseFirstAllowed w (ι x ⊗ ι y))
        ++s acc)
      ""

  renderState : H.HaloState → String
  renderState w =
    foldFin n
      (λ x acc →
        renderRow w x
        ++s "\n"
        ++s acc)
      ""

  showFailure : C.Failure → String
  showFailure C.Fail = "contradiction"
  showFailure C.OffLimit = "run limit reached"

  renderResult : C.RunResult → String
  renderResult (ok w) = renderState w
  renderResult (err (failure , w)) = "failure"

runSpec : DSLSpec → String
runSpec spec =
  let
    n  = gridSize spec
    k  = patternCount spec
    th = threshold spec
    module G = GridProblem n k th
  in
    G.renderResult G.runResult


runInput : String → String
runInput input with parse input
... | nothing = "Parse error."
... | just spec = runSpec spec
