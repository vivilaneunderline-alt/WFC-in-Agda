module WFCPropagate where

open import ShapeLayer
open import WFCCore

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)


defaultLimit : ∀ {D : Dimensions} → ℕ
defaultLimit {D} = suc (shapeSize (Cell D) * shapeSize (Pattern D))


-- pattern p at cell i have support in direction d
hasSupport? : ∀ {D : Dimensions} → Problem D → Wave D → 
    CellIndex D → PatternIndex D → DirectionIndex D → Bool
hasSupport? problem w i p d with neighbour problem i d
... | nothing = true --boundaries
... | just j =  booleanDot
    (λ q → w (j ⊗ q))
    (λ q → propagator problem ((p ⊗ d) ⊗ q))

-- candidate is supported with support in every direction
supported? : ∀ {D : Dimensions} → Problem D → Wave D →
    CellIndex D → PatternIndex D → Bool
supported? {D} problem w i p = all {Direction D}
    (λ d → hasSupport? problem w i p d)



pruneOnce : ∀ {D : Dimensions} → Problem D → Wave D → Wave D
pruneOnce problem before (i ⊗ p) =
    before (i ⊗ p) ∧ supported? problem before i p

pruneState : ∀ {D : Dimensions} →
    Problem D → State D → State D
pruneState problem state =
    record { wave = pruneOnce problem (wave state) }


propagateWithLimit : ∀ {D : Dimensions} →
    ℕ → Problem D → State D → State D
propagateWithLimit zero problem state = state
propagateWithLimit (suc limit) problem state =
    propagateWithLimit limit problem (pruneState problem state)

propagate : ∀ {D : Dimensions} →
    Problem D → State D → Bool × State D
propagate {D} problem state =
    let
        final = propagateWithLimit (defaultLimit {D}) problem state
    in
        noContradiction? {D} (wave final) , final
