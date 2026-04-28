import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [TopologicalSpace E] [ENormedAddCommMonoid E] [TopologicalSpace F] [ENormedAddCommMonoid F]
  [TopologicalSpace G] [ENormedAddCommMonoid G] {μ : Measure α}
  {f : α → E} {g : α → F}

open NNReal

--TODO: move?
instance : ENormSMulClass ℝ≥0 ℝ≥0∞ where
  enorm_smul r x := by
    simp only [enorm_eq_self, enorm_NNReal]
    rw [ENNReal.smul_def, smul_eq_mul]

theorem eLpNorm_le_eLpNorm_top_mul_eLpNorm' (p : ℝ≥0∞) (f : α → E) {g : α → F}
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f ∞ μ * eLpNorm g p μ := by
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm (fun x => c • ‖f x‖ₑ * ‖g x‖ₑ) p μ :=
      eLpNorm_mono_enorm_ae h
    _ ≤ c * eLpNorm f ∞ μ * eLpNorm g p μ := ?_
  simp only [smul_mul_assoc, ← Pi.smul_def]
  apply eLpNorm_const_smul_le''.trans
  simp only [enorm_NNReal]
  rw [mul_assoc]
  gcongr
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp
  · rw [← eLpNorm_enorm f, ← eLpNorm_enorm g]
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    exact ENNReal.essSup_mul_le (‖f ·‖ₑ) (‖g ·‖ₑ)
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₁.ne' hp₂.ne, eLpNorm_exponent_top,
    eLpNormEssSup, one_div, ENNReal.rpow_inv_le_iff hp]
  simp only [enorm_eq_self]
  rw [ENNReal.mul_rpow_of_nonneg (hz := hp.le), ENNReal.rpow_inv_rpow hp.ne',
    ← lintegral_const_mul'' _ (by fun_prop)]
  simp only [← ENNReal.mul_rpow_of_nonneg (hz := hp.le)]
  apply lintegral_mono_ae
  filter_upwards [h, enorm_ae_le_eLpNormEssSup f μ] with x hb hf
  gcongr
  exact hf

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top'' (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → F) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f p μ * eLpNorm g ∞ μ :=
  calc
    eLpNorm (fun x ↦ b (f x) (g x)) p μ ≤ c * eLpNorm g ∞ μ * eLpNorm f p μ :=
      eLpNorm_le_eLpNorm_top_mul_eLpNorm' p g hf (flip b) c <| by
        convert h using 3 with x
        simp only [mul_assoc, mul_comm ‖f x‖ₑ]
    _ = c * eLpNorm f p μ * eLpNorm g ∞ μ := by
      simp only [mul_assoc]; rw [mul_comm (eLpNorm _ _ _)]

theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm'' {p q r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ) (hro_lt : 0 < r) (hrp : r < p)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    eLpNorm' (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
      ≤ eLpNorm' (fun x ↦ c • ‖f x‖ₑ * ‖g x‖ₑ) r μ := by
      simp only [eLpNorm']
      gcongr ?_ ^ _
      refine lintegral_mono_ae <| h.mono fun a ha ↦ ?_
      simp only [Algebra.smul_mul_assoc, enorm_eq_self]
      gcongr
      rwa [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
    _ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
      simp only [smul_mul_assoc, ← Pi.smul_def]
      apply (eLpNorm'_const_smul_le'' hro_lt).trans
      rw [enorm_NNReal, mul_assoc]
      gcongr
      simpa only [eLpNorm', enorm_mul, enorm_norm] using
        ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hro_lt hrp hpqr μ hf.enorm hg.enorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm {p q r : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ := by
  have hpqr := hpqr.one_div_eq
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp_all
  · have : r = q := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_top_mul_eLpNorm' r f hg b c h
  obtain (rfl | rfl | hq) := ENNReal.trichotomy q
  · simp_all
  · have : r = p := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_mul_eLpNorm_top'' p hf g b c h
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  obtain ⟨hq₁, hq₂⟩ := ENNReal.toReal_pos_iff.mp hq
  have hpqr' : 1 / r.toReal = 1 / p.toReal + 1 / q.toReal := by
    have := congr(ENNReal.toReal $(hpqr))
    rw [ENNReal.toReal_add (by simpa using hp₁.ne') (by simpa using hq₁.ne')] at this
    simpa
  have hr : 0 < r.toReal := one_div_pos.mp <| by rw [hpqr']; positivity
  obtain ⟨hr₁, hr₂⟩ := ENNReal.toReal_pos_iff.mp hr
  have hrp : r.toReal < p.toReal := lt_of_one_div_lt_one_div hp <|
    hpqr' ▸ lt_add_of_pos_right _ (by positivity)
  rw [eLpNorm_eq_eLpNorm', eLpNorm_eq_eLpNorm', eLpNorm_eq_eLpNorm']
  · exact eLpNorm'_le_eLpNorm'_mul_eLpNorm'' hf hg b c h hr hrp hpqr'
  all_goals first | positivity | finiteness

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm for functions to `ℝ≥0∞`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm' {p q r : ℝ≥0∞} {f g : α → ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hpqr : HolderTriple p q r) :
    eLpNorm (fun x => f x * g x) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm hf hg _ 1 _ (hpqr := hpqr)).trans <;> simp

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_enorm {p q r : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm hf hg b c h

open NNReal in
theorem MemLp.of_bilin' {p q r : ℝ≥0∞} {f : α → E} {g : α → F} (b : E → F → G) (c : ℝ≥0)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h : AEStronglyMeasurable (fun x ↦ b (f x) (g x)) μ)
    (hb : ∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ b (f x) (g x)) r μ := by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  have := hf.2
  have := hg.2
  finiteness

end Bilinear

end MeasureTheory
