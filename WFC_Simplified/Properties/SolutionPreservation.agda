module Properties.SolutionPreservation where

open import ShapeLayer
open import WFCCore
open import WFCSemantic
open import WFCPropagate

open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; Σ; Σ-syntax)

postulate
    any-complete :
        ∀ {s : S} {a : Bool [[ s ]]} →
        (Σ[ i ∈ P s ] (a i ≡ true)) →
        any a ≡ true

    all-complete :
        ∀ {s : S} {a : Bool [[ s ]]} →
        (∀ i → a i ≡ true) →
        all a ≡ true


preserves-trans : ∀ {D : Dimensions}
    {before middle after : Wave D} (problem : Problem D) →
    PreservesSolutions problem before middle →
    PreservesSolutions problem middle after →
    PreservesSolutions problem before after
preserves-trans {D} {before = before} {middle = middle} {after = after}
    problem before→middle middle→after
    assignment satisfies compatible-before =
    let
        compatible-middle : CompatibleWithWave {D} middle assignment
        compatible-middle = 
            before→middle assignment satisfies compatible-before
    in
        middle→after assignment satisfies compatible-middle


-- A legal assignment compatible with the old wave provides a concrete
-- Boolean support witness for its selected pattern in every direction.
assignment-supported? : ∀ {D : Dimensions}
    (problem : Problem D) (before : Wave D) (assignment : Assignment D) →
    Satisfies problem assignment → CompatibleWithWave {D} before assignment →
    ∀ i → supported? {D} problem before i (assignment i) ≡ true
assignment-supported? {D} problem before assignment
    satisfies compatible i =
    all-complete λ d → support-in-direction d
    where
        support-in-direction :
            ∀ d → hasSupport? {D} problem before i (assignment i) d ≡ true
        support-in-direction d
            with neighbour problem i d in neighbour-eq
        ... | nothing = refl
        ... | just j = any-complete (assignment j , support-witness)
            where
                support-witness : before (j ⊗ assignment j) ∧
                    propagator problem ((assignment i ⊗ d) ⊗ assignment j) ≡ true
                support-witness
                    rewrite compatible j | satisfies i d j neighbour-eq = refl


-- One synchronous pruning round cannot delete any legal assignment
-- that is compatible with the input wave.
pruneOnce-preserves-solutions : ∀ {D : Dimensions}
    (problem : Problem D) (before : Wave D) →
    PreservesSolutions problem before (pruneOnce {D} problem before)

pruneOnce-preserves-solutions {D} problem before
    assignment satisfies compatible i
    rewrite compatible i
        | assignment-supported? {D} problem before
        assignment satisfies compatible i = refl


-- State-level one-round propagation preserves every compatible legal solution.
pruneState-preserves-solutions : ∀ {D : Dimensions}
    (problem : Problem D) (state : State D) →
    PreservesSolutions problem (wave state)
    (wave (pruneState {D} problem state))

pruneState-preserves-solutions {D} problem state =
    pruneOnce-preserves-solutions {D} problem (wave state)


-- Any finite number of propagation rounds preserves every legal solution
-- compatible with the initial wave.
propagateWithLimit-preserves-solutions : ∀ {D : Dimensions}
    (limit : ℕ) (problem : Problem D) (state : State D) →
    PreservesSolutions problem (wave state)
    (wave (propagateWithLimit {D} limit problem state))

propagateWithLimit-preserves-solutions
    {D} zero problem state
    assignment satisfies compatible = compatible

propagateWithLimit-preserves-solutions
    {D} (suc limit) problem state =
    preserves-trans
        {before = wave state}
        {middle = wave (pruneState {D} problem state)}
        {after =
        wave (propagateWithLimit {D} limit problem (pruneState {D} problem state))}
        problem
        (pruneState-preserves-solutions {D} problem state)
        (propagateWithLimit-preserves-solutions {D} limit problem
        (pruneState {D} problem state))
