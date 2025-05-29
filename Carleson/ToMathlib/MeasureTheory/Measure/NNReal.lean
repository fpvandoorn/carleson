import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory NNReal

noncomputable
instance NNReal.MeasureSpace : MeasureSpace ℝ≥0 := ⟨Measure.Subtype.measureSpace.volume⟩

lemma volume_val {s : Set ℝ≥0} : volume s = volume (Subtype.val '' s) := by
  apply comap_subtype_coe_apply measurableSet_Ici

open ENNReal Set
lemma integral_nnreal {f : ℝ≥0 → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ici (0 : ℝ), f x.toNNReal := by
  change ∫⁻ (x : ℝ≥0), f x = ∫⁻ (x : ℝ) in Ici 0, (f ∘ Real.toNNReal) x
  rw [← lintegral_subtype_comap measurableSet_Ici]
  simp
  rfl


--TODO
lemma integral_nnreal' {f : ℝ≥0∞ → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) := sorry
