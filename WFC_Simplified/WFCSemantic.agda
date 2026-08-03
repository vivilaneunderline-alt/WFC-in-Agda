module WFCSemantic where

open import ShapeLayer
open import WFCCore

open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; Σ; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Function.Bundles using (_⇔_; mk⇔)


_⊆w_ : ∀ {D : Dimensions} → 
    Wave D → Wave D → Set
_⊆w_ Φ Ψ = ∀ i p → Φ (i ⊗ p) ≡ true → Ψ (i ⊗ p) ≡ true

_=w_ : ∀ {D : Dimensions} → 
    Wave D → Wave D → Set
_=w_ Φ Ψ = ∀ i p → Φ (i ⊗ p) ≡ true ⇔ Ψ (i ⊗ p) ≡ true


Assignment : Dimensions → Set
Assignment D = CellIndex D → PatternIndex D

-- assignment selects pattern permitted by wave
CompatibleWithWave : ∀ {D : Dimensions} →
    Wave D → Assignment D → Set
CompatibleWithWave Φ A = ∀ i → Φ (i ⊗ (A i)) ≡ true

-- assignment satisfies every adjacency edge
Satisfies : ∀ {D : Dimensions} →
    Problem D → Assignment D → Set
Satisfies problem A = ∀ i d j →
    neighbour problem i d ≡ just j →
    propagator problem ((A i ⊗ d) ⊗ A j) ≡ true

-- complete solution is an assignment satisfying WFC problem
record LegalSolution {D : Dimensions}
    (problem : Problem D) : Set where
    field
        assignment : Assignment D
        satisfies : Satisfies problem assignment
open LegalSolution public

-- contradictory when no pattern remains possible
ContradictoryAt : ∀ {D : Dimensions} →
    Wave D → CellIndex D → Set
ContradictoryAt Φ i = ∀ p → Φ (i ⊗ p) ≡ false

-- wave contains a contradiction
Contradictory :
    ∀ {D : Dimensions} → Wave D → Set
Contradictory {D} Φ = Σ[ i ∈ CellIndex D ] ContradictoryAt {D} Φ i

-- wave is complete when every cell has one possible pattern
record CompleteWave {D : Dimensions} (Φ : Wave D) : Set₁ where
    field
        selected : CellIndex D → PatternIndex D
        selected-allowed : ∀ i → Φ (i ⊗ selected i) ≡ true
        selected-unique : ∀ i p → Φ (i ⊗ p) ≡ true → p ≡ selected i
open CompleteWave public


-- neighbour must contain at least one pattern supported
HasSupport : ∀ {D : Dimensions} → Problem D → Wave D →
    CellIndex D → PatternIndex D → DirectionIndex D → Set
HasSupport {D} problem Φ i p d =
    neighbour problem i d ≡ nothing --boundaries
    ⊎ Σ[ j ∈ CellIndex D ] (neighbour problem i d ≡ just j)
    × Σ[ q ∈ PatternIndex D ] (Φ (j ⊗ q) ≡ true)
    × (propagator problem ((p ⊗ d) ⊗ q) ≡ true)

-- possible pattern is locally supported in every direction
SupportedAt : ∀ {D : Dimensions} → Problem D → Wave D →
    CellIndex D → PatternIndex D → Set
SupportedAt {D} problem Φ i p = ∀ d →
    HasSupport {D} problem Φ i p d


-- every remaining pattern has support in every direction
ArcConsistent : ∀ {D : Dimensions} →
    Problem D → Wave D → Set
ArcConsistent problem Φ = ∀ i p →
    Φ (i ⊗ p) ≡ true → SupportedAt problem Φ i p

-- propagation should not remove any complete solution
PreservesSolutions : ∀ {D : Dimensions} →
    Problem D → Wave D → Wave D → Set
PreservesSolutions {D} problem before after = ∀ assignment →
    Satisfies problem assignment →
    CompatibleWithWave {D} before assignment →
    CompatibleWithWave {D} after assignment


record ObserveCorrect {D : Dimensions}
    (chosen : CellIndex D)
    (selected : PatternIndex D)
    (before after : Wave D) : Set₁ where
    field
        selected-was-allowed : before (chosen ⊗ selected) ≡ true
        chosen-keeps-selected : after (chosen ⊗ selected) ≡ true
        chosen-removes-others : ∀ p →
            after (chosen ⊗ p) ≡ true → p ≡ selected
        other-cells-unchanged : ∀ i → ¬ (i ≡ chosen) →
            ∀ p → before (i ⊗ p) ≡ true ⇔ after (i ⊗ p) ≡ true
open ObserveCorrect public

record PropagationCorrect {D : Dimensions}
    (problem : Problem D)
    (before after : Wave D) : Set₁ where
    field
        only-removes : _⊆w_ {D} after before
        arc-consistent : ArcConsistent problem after
        preserves-solutions : PreservesSolutions problem before after
open PropagationCorrect public
