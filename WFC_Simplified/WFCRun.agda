module WFCRun where

open import ShapeLayer
open import WFCCore
open import WFCObserve using (observe; chooseFirstAllowed)
open import WFCPropagate using (propagate)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)


_<ᵇ_ : ℕ → ℕ → Bool
zero <ᵇ zero = false
zero <ᵇ suc n = true
suc m <ᵇ zero = false
suc m <ᵇ suc n = m <ᵇ n

_>1 : ℕ → Bool
_>1 zero = false
_>1 (suc zero) = false
_>1 (suc (suc _)) = true


data StepResult (D : Dimensions) : Set where
    done : State D → StepResult D
    contradiction : State D → StepResult D
    continue : State D → StepResult D

data RunResult (D : Dimensions) : Set where
    success : State D → RunResult D
    failed : State D → RunResult D
    outOfLimit : State D → RunResult D


insertMRV : ∀ {D : Dimensions} →
    CellIndex D → ℕ → Maybe (CellIndex D × ℕ) → Maybe (CellIndex D × ℕ)
insertMRV i count nothing = just (i , count)
insertMRV i count (just (oldCell , oldCount)) =
    if count <ᵇ oldCount
    then just (i , count)
    else just (oldCell , oldCount)

candidateCell : ∀ {D : Dimensions} →
    Maybe (CellIndex D × ℕ) → Maybe (CellIndex D)
candidateCell nothing = nothing
candidateCell (just (i , count)) = just i


mrvStep : ∀ {D : Dimensions} →
    Wave D → CellIndex D → Maybe (CellIndex D × ℕ) → Maybe (CellIndex D × ℕ)
mrvStep {D} w i candidate =
    let count = allowedCount {D} w i
    in
        if count >1
        then insertMRV {D} i count candidate
        else candidate

nextMRVNode : ∀ {D : Dimensions} →
    State D → Maybe (CellIndex D)
nextMRVNode {D} state = candidateCell {D}
    (foldShape {Cell D} (mrvStep {D} (wave state)) nothing)

runStep : ∀ {D : Dimensions} →
    Problem D → State D → StepResult D
runStep {D} problem state with noContradiction? {D} (wave state)
... | false = contradiction state
... | true with nextMRVNode state
...     | nothing = done state
...     | just i with chooseFirstAllowed state i
...         | nothing = contradiction state
...         | just p with propagate problem (observe i p state)
...             | false , state′ = contradiction state′
...             | true  , state′ = continue state′

runWithLimit : ∀ {D : Dimensions} →
    ℕ → Problem D → State D → RunResult D
runWithLimit zero problem state = outOfLimit state
runWithLimit (suc limit) problem state with runStep problem state
... | done state′ = success state′
... | contradiction state′ = failed state′
... | continue state′ = runWithLimit limit problem state′

defaultRunLimit : ∀ {D : Dimensions} → ℕ
defaultRunLimit {D} = suc (shapeSize (Cell D))

run : ∀ {D : Dimensions} → Problem D → State D → RunResult D
run {D} problem state = runWithLimit (defaultRunLimit {D}) problem state
