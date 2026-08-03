module Properties.Monotonicity where

open import ShapeLayer
open import WFCCore
open import WFCSemantic
open import WFCObserve
open import WFCPropagate

⊆w-trans : ∀ {D : Dimensions} {Φ Ψ Ω : Wave D} →
    _⊆w_ {D} Φ Ψ → _⊆w_ {D} Ψ Ω → _⊆w_ {D} Φ Ω
⊆w-trans Φ⊆Ψ Ψ⊆Ω i p Φip =
    Ψ⊆Ω i p (Φ⊆Ψ i p Φip)

⊆w-refl : ∀ {D : Dimensions} {Φ : Wave D} →
    _⊆w_ {D} Φ Φ
⊆w-refl i p Φip = Φip

observeWave-only-removes : ∀ {D : Dimensions}
    (chosen : CellIndex D) (selected : PatternIndex D) (before : Wave D) →
    _⊆w_ {D} (observeWave {D} chosen selected before) before
observeWave-only-removes {D} chosen selected before i p after-true
    with sameP? i chosen
... | no _ = after-true
... | yes refl with sameP? p selected
...     | yes _ = after-true
...     | no _ with after-true
...         | ()

observe-only-removes : ∀ {D : Dimensions}
    (chosen : CellIndex D) (selected : PatternIndex D) (state : State D) →
    _⊆w_ {D} (wave (observe {D} chosen selected state)) (wave state)
observe-only-removes {D} chosen selected state =
    observeWave-only-removes {D} chosen selected (wave state)

pruneOnce-only-removes : ∀ {D : Dimensions}
    (problem : Problem D) (before : Wave D) →
    _⊆w_ {D} (pruneOnce {D} problem before) before
pruneOnce-only-removes {D} problem before i p after-true
    with before (i ⊗ p)
... | true = refl
... | false with after-true
...     | ()

pruneState-only-removes : ∀ {D : Dimensions}
    (problem : Problem D) (state : State D) →
    _⊆w_ {D} (wave (pruneState {D} problem state)) (wave state)
pruneState-only-removes {D} problem state =
    pruneOnce-only-removes {D} problem (wave state)

propagateWithLimit-only-removes : ∀ {D : Dimensions}
    (limit : ℕ) (problem : Problem D) (state : State D) →
    _⊆w_ {D} (wave (propagateWithLimit {D} limit problem state)) (wave state)
propagateWithLimit-only-removes {D} zero problem state i p final-true = final-true
propagateWithLimit-only-removes {D} (suc limit) problem state i p final-true =
    pruneState-only-removes {D} problem state i p
    (propagateWithLimit-only-removes {D}
    limit problem (pruneState {D} problem state) i p final-true)