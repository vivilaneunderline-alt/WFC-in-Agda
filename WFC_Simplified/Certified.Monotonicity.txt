module Certified.Monotonicity where

open import ShapeLayer
open import WFCCore
open import WFCSemantic

open import WFCObserve
open import WFCPropagate
open import WFCRun

open import Properties.Monotonicity

record MonotoneResult {D : Dimensions} (before : State D) : Set where
    constructor certified
    field
        after : State D
        only-removes : _⊆w_ {D} (wave after) (wave before)
open MonotoneResult public

certifiedObserve : ∀ {D : Dimensions} →
    CellIndex D → PatternIndex D → (state : State D) → 
    MonotoneResult state
certifiedObserve {D} i' p' state =
    certified
        (observe {D} i' p' state)
        (observe-only-removes {D} i' p' state)

certifiedPruneState : ∀ {D : Dimensions} →
    Problem D → (state : State D) → 
    MonotoneResult state
certifiedPruneState {D} problem state = 
    certified
        (pruneState {D} problem state)
        (pruneState-only-removes {D} problem state)

certifiedPropagateWithLimit : ∀ {D : Dimensions} →
    (limit : ℕ) → (problem : Problem D) → (state : State D) →
    MonotoneResult state

certifiedPropagateWithLimit {D} limit problem state = 
    certified
        (propagateWithLimit {D} limit problem state)
        (propagateWithLimit-only-removes {D} limit problem state)