import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open ENNReal

theorem ContinuousWithinAt.ennreal_mul {X : Type*}
  [TopologicalSpace X] {f g : X → ℝ≥0∞} {s : Set X} {t : X} (hf : ContinuousWithinAt f s t)
  (hg : ContinuousWithinAt g s t) (h₁ : f t ≠ 0 ∨ g t ≠ ∞) (h₂ : g t ≠ 0 ∨ f t ≠ ∞) :
    ContinuousWithinAt (fun x ↦ f x * g x) s t := fun _ hx =>
  ENNReal.Tendsto.mul hf h₁ hg h₂ hx
