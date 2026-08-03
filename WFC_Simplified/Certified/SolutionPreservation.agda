module Certified.SolutionPreservation where

open import ShapeLayer
open import WFCCore
open import WFCSemantic
open import WFCPropagate

open import Properties.SolutionPreservation


record SolutionPreservingResult
  {D : Dimensions}
  (problem : Problem D)
  (before : State D) : Set where

  constructor certified

  field
    after :
      State D

    preserves-solutions :
      PreservesSolutions
        problem
        (wave before)
        (wave after)

open SolutionPreservingResult public


certifiedPruneState :
  ∀ {D : Dimensions}
    (problem : Problem D)
    (state : State D) →
  SolutionPreservingResult problem state

certifiedPruneState {D} problem state =
  certified
    (pruneState {D} problem state)
    (pruneState-preserves-solutions
      {D}
      problem
      state)


certifiedPropagateWithLimit :
  ∀ {D : Dimensions}
    (limit : ℕ)
    (problem : Problem D)
    (state : State D) →
  SolutionPreservingResult problem state

certifiedPropagateWithLimit {D} limit problem state =
  certified
    (propagateWithLimit {D} limit problem state)
    (propagateWithLimit-preserves-solutions
      {D}
      limit
      problem
      state)
