import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory MeasureTheory.Measure Filter Set

open scoped ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}

lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ :=
  lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]
lemma setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ :=
  laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self

lemma setLAverage_le_essSup (f : α → ℝ≥0∞) :
    ⨍⁻ x in s, f x ∂μ ≤ essSup f μ := by
  by_cases hμ : IsFiniteMeasure (μ.restrict s); swap
  · simp [laverage, not_isFiniteMeasure_iff.mp hμ]
  by_cases hμ0 : μ s = 0
  · rw [laverage, ← setLIntegral_univ]
    exact le_of_eq_of_le (setLIntegral_measure_zero univ f <| by simp [hμ0]) (zero_le (essSup f μ))
  apply le_of_le_of_eq (laverage_mono_ae <| Eventually.filter_mono ae_restrict_le ae_le_essSup)
  have : NeZero (μ.restrict s) :=
    have : NeZero (μ s) := { out := hμ0 }
    restrict.neZero
  exact laverage_const (μ.restrict s) _

lemma laverage_le_essSup (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ ≤ essSup f μ := by
  simpa using setLAverage_le_essSup (s := univ) f
