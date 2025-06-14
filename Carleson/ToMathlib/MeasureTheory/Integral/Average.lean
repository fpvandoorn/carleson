import Mathlib.MeasureTheory.Integral.Average

open Set

open scoped ENNReal

namespace MeasureTheory

lemma laverage_le {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {f : α → ℝ≥0∞} {M : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, f x ≤ M) : ⨍⁻ x, f x ∂μ ≤ M := by
  apply le_trans <| lintegral_mono_ae <| μ.ae_smul_measure h (μ Set.univ)⁻¹
  simpa using mul_le_of_le_one_right' (μ univ).inv_mul_le_one

lemma setLAverage_le {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {f : α → ℝ≥0∞} {M : ℝ≥0∞}
    {s : Set α} (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ M) : ⨍⁻ x in s, f x ∂μ ≤ M :=
  laverage_le <| (ae_restrict_mem hs).mp (ae_restrict_of_ae h)

end MeasureTheory
