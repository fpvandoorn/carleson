import Carleson.ToMathlib.Misc
import Mathlib.MeasureTheory.Integral.IntervalIntegral


/-The lemmas in this file might either already exist in mathlib or be candidates to go there
  (in a generalized form).
-/


lemma intervalIntegral.integral_conj' {μ : MeasureTheory.Measure ℝ} {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}:
    ∫ x in a..b, (starRingEnd 𝕜) (f x) ∂μ = (starRingEnd 𝕜) (∫ x in a..b, f x ∂μ) := by
  rw [intervalIntegral_eq_integral_uIoc, integral_conj, intervalIntegral_eq_integral_uIoc,
      RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, map_mul]
  simp

lemma intervalIntegrable_of_bdd {a b : ℝ} {δ : ℝ} {g : ℝ → ℂ} (measurable_g : Measurable g) (bddg : ∀ x, ‖g x‖ ≤ δ) : IntervalIntegrable g MeasureTheory.volume a b := by
  apply @IntervalIntegrable.mono_fun' _ _ _ _ _ _ (fun _ ↦ δ)
  apply intervalIntegrable_const
  exact measurable_g.aestronglyMeasurable
  rw [Filter.EventuallyLE, ae_restrict_iff_subtype measurableSet_uIoc]
  apply Filter.eventually_of_forall
  simp only [Subtype.forall]
  intro x _
  exact bddg x

lemma IntervalIntegrable.bdd_mul {F : Type} [NormedDivisionRing F] {f g : ℝ → F} {a b : ℝ} {μ : MeasureTheory.Measure ℝ}
    (hg : IntervalIntegrable g μ a b) (hm : MeasureTheory.AEStronglyMeasurable f μ) (hfbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) : IntervalIntegrable (fun x ↦ f x * g x) μ a b := by
  rw [intervalIntegrable_iff, MeasureTheory.IntegrableOn]
  apply MeasureTheory.Integrable.bdd_mul _ hm.restrict hfbdd
  rwa [← MeasureTheory.IntegrableOn, ← intervalIntegrable_iff]

lemma IntervalIntegrable.mul_bdd {F : Type} [NormedField F] {f g : ℝ → F} {a b : ℝ} {μ : MeasureTheory.Measure ℝ}
    (hf : IntervalIntegrable f μ a b) (hm : MeasureTheory.AEStronglyMeasurable g μ) (hgbdd : ∃ C, ∀ x, ‖g x‖ ≤ C) : IntervalIntegrable (fun x ↦ f x * g x) μ a b := by
  conv => pattern (fun x ↦ f x * g x); ext x; rw [mul_comm]
  apply hf.bdd_mul hm hgbdd

lemma MeasureTheory.IntegrableOn.sub {α : Type} {β : Type} {m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} [NormedAddCommGroup β] {s : Set α} {f g : α → β} (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) : IntegrableOn (f - g) s μ := by
  apply MeasureTheory.Integrable.sub <;> rwa [← IntegrableOn]
