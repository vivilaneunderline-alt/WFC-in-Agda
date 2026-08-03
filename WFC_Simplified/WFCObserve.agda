module WFCObserve where

open import ShapeLayer
open import WFCCore

open import Data.Maybe using (Maybe; just; nothing)


-- keep selected pattern at chosen cell
observeWave : ∀ {D : Dimensions} →
    CellIndex D → PatternIndex D → Wave D → Wave D
observeWave i' p' before (i ⊗ p) with sameP? i i'
... | no _ = before (i ⊗ p)
... | yes refl with sameP? p p'
...     | yes _ = before (i' ⊗ p)
...     | no _  = false

observe : ∀ {D : Dimensions} →
    CellIndex D → PatternIndex D → State D → State D
observe {D} i' p' state =
    record { wave = observeWave {D} i' p' (wave state) }


-- choose first allowed pattern.
chooseFirstAllowedFromWave : ∀ {D : Dimensions} →
    Wave D → CellIndex D → Maybe (PatternIndex D)
chooseFirstAllowedFromWave {D} w i =
    foldShape {Pattern D} step nothing
    where
        step : PatternIndex D → Maybe (PatternIndex D) → Maybe (PatternIndex D)
        step p (just p') = just p'
        step p nothing =
            if w (i ⊗ p)
            then just p
            else nothing

chooseFirstAllowed : ∀ {D : Dimensions} →
    State D → CellIndex D → Maybe (PatternIndex D)
chooseFirstAllowed {D} state i =
    chooseFirstAllowedFromWave {D} (wave state) i
