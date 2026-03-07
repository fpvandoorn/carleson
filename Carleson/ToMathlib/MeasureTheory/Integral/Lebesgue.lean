module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

-- Upstreaming status: ready to go
-- Remaining lemmas: shift/scaling aliases, `lintegral_set_mono_fn`
-- (already `setLIntegral_mono'` in mathlib).

open NNReal ENNReal MeasureTheory Set

variable {α α' : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞} {c : ℝ≥0} {μ : Measure α}

/-! ## Some tools for measure theory computations
    A collection of small lemmas to help with integral manipulations.
-/
namespace MeasureTheory

lemma measure_preserving_shift {a : ℝ} :
    MeasurePreserving (fun x ↦ a + x) volume volume :=
  measurePreserving_add_left volume a

lemma measureable_embedding_shift {a : ℝ} : MeasurableEmbedding (fun x ↦ a + x) :=
  measurableEmbedding_addLeft a

lemma measure_preserving_scaling {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun x ↦ a * x) volume ((ENNReal.ofReal |a⁻¹|) • volume) :=
  { measurable := measurable_const_mul a, map_eq := Real.map_volume_mul_left ha }

lemma lintegral_shift (f : ℝ → ENNReal) {a : ℝ} :
    ∫⁻ x : ℝ, (f (x + a)) = ∫⁻ x : ℝ, f x :=
  lintegral_add_right_eq_self f a

lemma lintegral_shift' (f : ℝ → ENNReal) {a : ℝ} {s : Set ℝ} :
    ∫⁻ (x : ℝ) in (fun z : ℝ ↦ z + a)⁻¹' s, f (x + a) = ∫⁻ (x : ℝ) in s, f x := by
  rw [(measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight a)]

lemma lintegral_add_right_Ioi (f : ℝ → ENNReal) {a b : ℝ} :
    ∫⁻ (x : ℝ) in Ioi (b - a), f (x + a) = ∫⁻ (x : ℝ) in Ioi b, f x := by
  nth_rewrite 2 [← lintegral_shift' (a := a)]
  simp

lemma lintegral_scale_constant (f : ℝ → ENNReal) {a : ℝ} (h : a ≠ 0) :
    ∫⁻ x : ℝ, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x := by
  rw [← smul_eq_mul, ← @lintegral_smul_measure, MeasurePreserving.lintegral_comp_emb]
  · exact measure_preserving_scaling h
  · exact measurableEmbedding_mulLeft₀ h

lemma lintegral_scale_constant_preimage (f : ℝ → ENNReal) {a : ℝ} (h : a ≠ 0) {s : Set ℝ} :
    ∫⁻ x : ℝ in (fun z : ℝ ↦ a * z)⁻¹' s, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in s, f x := by
  rw [← smul_eq_mul, ← lintegral_smul_measure,
    (measure_preserving_scaling h).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft₀ h),
    Measure.restrict_smul]

lemma lintegral_scale_constant_halfspace (f : ℝ → ENNReal) {a : ℝ} (h : 0 < a) :
    ∫⁻ x : ℝ in Ioi 0, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [← lintegral_scale_constant_preimage f h.ne']
  have h₀ : (fun z ↦ a * z) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp [mul_pos_iff_of_pos_left h]
  rw [h₀]

lemma lintegral_scale_constant_halfspace' {f : ℝ → ENNReal} {a : ℝ} (h : 0 < a) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ in Ioi 0, f (a*x) = ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [lintegral_scale_constant_halfspace f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a),
    abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h.ne')]
  simp

lemma lintegral_scale_constant' {f : ℝ → ENNReal} {a : ℝ} (h : a ≠ 0) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a), abs_inv,
      mul_inv_cancel₀ (abs_ne_zero.mpr h)]
  simp


open SimpleFunc

lemma lintegral_set_mono_fn {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x ∈ s, f x ≤ g x) :
    ∫⁻ (a : α) in s, f a ∂μ ≤ ∫⁻ (a : α) in s, g a ∂μ := by
  rw [← lintegral_indicator hs, ← lintegral_indicator hs]
  apply lintegral_mono
  intro x
  unfold Set.indicator
  split
  · rename_i hxs
    exact hfg x hxs
  · rfl

end MeasureTheory
