module WFCCore where

open import ShapeLayer public

open import Data.Maybe using (Maybe)
open import Data.Bool using(not)


record Dimensions : Set where
    field
        Cell : S
        Pattern : S
        Direction : S
open Dimensions public

CellIndex : Dimensions → Set
CellIndex D = P (Cell D)

PatternIndex : Dimensions → Set
PatternIndex D = P (Pattern D)

DirectionIndex : Dimensions → Set
DirectionIndex D = P (Direction D)


Wave : Dimensions → Set
Wave D = Bool [[ Cell D ⊗ Pattern D ]]

Propagator : Dimensions → Set
Propagator D =  Bool [[ (Pattern D ⊗ Direction D) ⊗ Pattern D ]]

Neighbour : Dimensions → Set
Neighbour D =
    CellIndex D →
    DirectionIndex D →
    Maybe (CellIndex D)


record Problem (D : Dimensions) : Set where
    field
        neighbour : Neighbour D
        propagator : Propagator D
open Problem public

record State (D : Dimensions) : Set where
    field
        wave : Wave D
open State public


initialWave : ∀ {D : Dimensions} → Wave D
initialWave = K true

initialState : ∀ {D : Dimensions} → State D
initialState {D} = record { wave = initialWave {D} }

allowedCount : ∀ {D : Dimensions} → 
    Wave D → CellIndex D → ℕ
allowedCount {D} w i = foldShape {Pattern D}
    (λ t count →
    if w (i ⊗ t)
    then suc count
    else count) zero

contradictoryAt? : ∀ {D : Dimensions} → 
    Wave D → CellIndex D → Bool
contradictoryAt? {D} w i with allowedCount {D} w i
... | zero  = true
... | suc _ = false

uncollapsedAt? : ∀ {D : Dimensions} → 
    Wave D → CellIndex D → Bool
uncollapsedAt? {D} w i with allowedCount {D} w i
... | zero = false
... | suc zero = false
... | suc (suc _) = true

noContradiction? : ∀ {D : Dimensions} → 
    Wave D → Bool
noContradiction? {D} w = all {Cell D}
    (λ i → not (contradictoryAt? {D} w i))
