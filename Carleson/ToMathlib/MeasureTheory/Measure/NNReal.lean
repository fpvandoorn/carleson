import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

instance : MeasureSpace ℝ≥0 where
  volume := (volume : Measure ℝ).map Real.toNNReal

lemma NNReal.volume_apply_measurableSet {s : Set ℝ≥0} (hs : MeasurableSet s) :
    volume s = volume (Real.toNNReal ⁻¹' s) :=
  MeasureTheory.Measure.map_apply_of_aemeasurable (by fun_prop) hs

-- sanity check: this measure is what you expect
example : volume (Ioo (3 : ℝ≥0) 5) = 2 := by
  have : Real.toNNReal ⁻¹' Ioo 3 5 = Ioo (3 : ℝ) 5 := by ext; simp
  rw [NNReal.volume_apply_measurableSet measurableSet_Ioo, this]
  simpa only [Real.volume_Ioo, ENNReal.ofReal_eq_ofNat] using by norm_num

-- integral over a function over NNReal equals the integral over the right set of real numbers

instance : MeasureSpace ℝ≥0∞ where
  volume := (volume : Measure ℝ≥0).map ENNReal.ofNNReal

lemma ENNReal.volume_apply_measurableSet {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.ofReal ⁻¹' s) := by
  calc volume s
    _ = volume (ENNReal.ofNNReal ⁻¹' s) :=
      MeasureTheory.Measure.map_apply_of_aemeasurable (by fun_prop) hs
    _ = volume (Real.toNNReal ⁻¹' (ENNReal.ofNNReal ⁻¹' s)) :=
      MeasureTheory.Measure.map_apply_of_aemeasurable (by fun_prop) (by measurability)

-- sanity check: this measure is what you expect
example : volume (Set.Icc (3 : ℝ≥0∞) 42) = 39 := by
  have : ENNReal.ofReal ⁻¹' Set.Icc 3 42 = Set.Icc (3 : ℝ) 42 := by ext; simp
  rw [ENNReal.volume_apply_measurableSet measurableSet_Icc, this]
  simpa using by norm_num

-- Future: prove these integral lemmas and name them properly
lemma todo (f : ℝ≥0∞ → ℝ≥0∞) : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) := sorry

lemma todo' (f : ℝ≥0 → ℝ≥0∞) : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (Real.toNNReal x) := sorry

lemma todo'' (f : ℝ → ℝ≥0∞) : ∫⁻ x : ℝ≥0, f (x.toReal) = ∫⁻ x in Ioi (0 : ℝ), f x := sorry

-- Future: lemmas about interaction with the Bochner integral

end
