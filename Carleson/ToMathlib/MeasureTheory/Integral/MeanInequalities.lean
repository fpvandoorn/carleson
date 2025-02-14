import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.Convolution
import Carleson.ToMathlib.Data.Real.ConjExponents
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Group.LIntegral
import Carleson.ToMathlib.MeasureTheory.Measure.Haar.Unique
import Carleson.ToMathlib.MeasureTheory.Measure.Prod

open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

---------------------------------------------------------------------------------------------------
-- NOT to be added to Mathlib

-- Temporary stand-in for Mathlib's new version of `eLpNormEssSup_const` until next bump
theorem MeasureTheory.eLpNormEssSup_const' {ε : Type*} [ENorm ε] (c : ε) (hμ : μ ≠ 0) :
    eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ := by
  sorry
---------------------------------------------------------------------------------------------------

namespace ENNReal

-- Add after `lintegral_prod_norm_pow_le`
/-- A version of Hölder with multiple arguments, allowing `∞` as an exponent. -/
theorem lintegral_prod_norm_pow_le' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Finset ι} {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {p : ι → ℝ≥0∞} (hp : ∑ i ∈ s, 1 / p i = 1) :
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  classical
  revert hp hf
  refine Finset.strongInduction (fun s hs hf hp ↦ ?_) s (p := fun s ↦
    (∀ i ∈ s, AEMeasurable (f i) μ) → (∑ i ∈ s, 1 / p i = 1) →
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ)
  by_cases exists_top : ∃ i₀ ∈ s, p i₀ = ∞    -- If one of the exponents is `∞`, we reduce to the
  · obtain ⟨i₀, hi₀, pi₀_eq_top⟩ := exists_top -- case without it and use the inductive hypothesis
    calc ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ
      _ = ∫⁻ (a : α), f i₀ a * ∏ i ∈ s.erase i₀, f i a ∂μ :=
        lintegral_congr (fun a ↦ (Finset.mul_prod_erase s (f · a) hi₀).symm)
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∫⁻ (a : α), ∏ i ∈ s.erase i₀, f i a ∂μ := by
        rw [← lintegral_const_mul'', pi₀_eq_top]
        · exact lintegral_mono_ae <| (ae_le_essSup (f i₀)).mono (fun a ha ↦ mul_le_mul_right' ha _)
        · exact Finset.aemeasurable_prod _ (fun i hi ↦ hf i (Finset.mem_of_mem_erase hi))
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∏ i ∈ s.erase i₀, eLpNorm (f i) (p i) μ := by
        apply mul_left_mono
        apply hs (s.erase i₀) (s.erase_ssubset hi₀) (fun i hi ↦ hf i (s.erase_subset i₀ hi))
        simpa [← Finset.add_sum_erase s _ hi₀, pi₀_eq_top] using hp
      _ = _ := Finset.mul_prod_erase s (fun i ↦ eLpNorm (f i) (p i) μ) hi₀
  -- If all exponents are finite, we're in the case covered by `ENNReal.lintegral_prod_norm_pow_le`
  have hf' : ∀ i ∈ s, AEMeasurable (fun a ↦ ((f i a) ^ (p i).toReal)) μ :=
    fun i hi ↦ (hf i hi).pow_const (p i).toReal
  have hp₁ : ∑ i ∈ s, 1 / (p i).toReal = 1 := by
    simp_rw [← (ENNReal.toReal_eq_one_iff 1).mpr rfl, ← ENNReal.toReal_div]
    suffices (∑ x ∈ s, 1 / p x).toReal = ∑ x ∈ s, (1 / p x).toReal by rw [← this, hp]
    refine ENNReal.toReal_sum (fun i hi eq_top ↦ ?_)
    exact ENNReal.one_ne_top <| hp ▸ ENNReal.sum_eq_top.mpr ⟨i, hi, eq_top⟩
  have hp₂ : ∀ i ∈ s, 0 ≤ 1 / (p i).toReal := by intros; positivity
  have p_ne_0 : ∀ i ∈ s, p i ≠ 0 :=
    fun i hi eq0 ↦ one_ne_top <| hp.symm.trans <| ENNReal.sum_eq_top.mpr ⟨i, hi, by simp [eq0]⟩
  have p_ne_top : ∀ i ∈ s, p i ≠ ∞ := fun i hi h ↦ exists_top ⟨i, hi, h⟩
  convert ENNReal.lintegral_prod_norm_pow_le s hf' hp₁ hp₂ with a i₀ hi₀ i hi
  · rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀, rpow_one]
    exact ENNReal.toReal_ne_zero.mpr ⟨p_ne_0 i₀ hi₀, (exists_top ⟨i₀, hi₀, ·⟩)⟩
  · simp [eLpNorm, eLpNorm', p_ne_0 i hi, p_ne_top i hi]

/-- Hölder's inequality for functions `α → ℝ≥0∞`, using exponents in `ℝ≥0∞`-/
theorem lintegral_mul_le_eLpNorm_mul_eLqNorm {p q : ℝ≥0∞} (hpq : p.IsConjExponent q)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ (a : α), (f * g) a ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  by_cases pq_top : p = ∞ ∨ q = ∞
  · wlog hp : p = ∞
    · have hq := pq_top.resolve_left hp
      simpa only [mul_comm] using this hpq.symm hg hf (Or.inl hq) hq
    apply le_of_le_of_eq <| lintegral_mono_ae ((ae_le_essSup f).mono (fun a ha ↦ mul_right_mono ha))
    simp [eLpNorm, eLpNorm', eLpNormEssSup, hp, hpq.conj_eq, lintegral_const_mul'' _ hg]
  push_neg at pq_top
  convert ENNReal.lintegral_mul_le_Lp_mul_Lq μ (hpq.conjExponent_toReal pq_top.1 pq_top.2) hf hg
  all_goals simp [eLpNorm, eLpNorm', hpq.ne_zero, hpq.symm.ne_zero, pq_top]

end ENNReal


section Convolution

open scoped Convolution

-- Used in the proof of Young's convolution inequality
private lemma r_sub_p_nonneg {p q r : ℝ} (p0 : 0 < p) (hq : 1 ≤ q) (r0 : 0 < r)
    (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) : 0 ≤ r - p := by
  rw [sub_nonneg, ← inv_le_inv₀ r0 p0, ← add_le_add_iff_right, hpqr]
  exact add_le_add_left ((inv_le_one₀ (lt_of_lt_of_le one_pos hq)).mpr hq) r⁻¹

namespace ENNReal

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} [MeasurableSpace G] {μ : Measure G}
  {E : Type uE} {E' : Type uE'} {F : Type uF}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g : G → E'}

-- Used in the proof of `enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm`
open ENNReal in
private lemma eLpNorm_eq_eLpNorm_rpow (h : G → E) {r e : ℝ} (r0 : 0 < r) (e0 : 0 < e)
    (re0 : 0 ≤ r - e) (μ0 : μ ≠ 0) :
    eLpNorm (‖h ·‖ₑ ^ ((r - e) / r)) (ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e)) μ =
    eLpNorm h (ENNReal.ofReal e) μ ^ ((r - e) / r) := by
  have er_pos : 0 < e * r := _root_.mul_pos e0 r0
  by_cases exp_zero : 0 = r - e
  · simp [eLpNorm, eLpNorm', ← exp_zero, er_pos.not_le, eLpNormEssSup_const' _ μ0] -- Replace with `eLpNormEssSup_const` after Mathlib bump
  have r_sub_e_pos : 0 < r - e := lt_of_le_of_ne re0 exp_zero
  have lt_top : ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e) < ∞ :=
    div_lt_top ofReal_ne_top <| (not_iff_not.mpr ofReal_eq_zero).mpr r_sub_e_pos.not_le
  simp only [eLpNorm, eLpNorm', reduceIte, div_eq_zero_iff, ofReal_eq_zero, ofReal_ne_top,
    lt_top.ne, er_pos.not_le, e0.not_le, or_self, enorm_eq_self, ← rpow_mul]
  congr
  · ext; congr; field_simp; ring
  · field_simp

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
variable {L : E →L[𝕜] E' →L[𝕜] F}

-- Used to handle trivial case `c ≤ 0` when proving versions of Young's convolution inequality
-- assuming `∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖)`
private theorem convolution_zero_of_c_nonpos [AddGroup G] {f : G → E} {g : G → E'} {c : ℝ}
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (hc : c ≤ 0) : f ⋆[L, μ] g = 0 := by
  have : ∀ (x y : G), L (f x) (g y) = 0 :=
    fun x y ↦ norm_le_zero_iff.mp <| (hL x y).trans <| mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg (f x))) (norm_nonneg (g y))
  unfold convolution
  simp only [this, integral_zero]
  rfl

variable [AddCommGroup G] [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G]
  [μ.IsAddHaarMeasure] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']


/-- Special case of Young's convolution inequality when `r = ∞`. -/
theorem eLpNorm_top_convolution_le {p q : ℝ≥0∞}
    (hpq : p.IsConjExponent q) {f : G → E} {g : G → E'} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) {c : ℝ} (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  by_cases hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  push_neg at hc
  rw [eLpNorm_exponent_top, eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x ↦ ?_)
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  have hg' : AEMeasurable (g <| x - ·) μ :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  calc ∫⁻ y, ‖(L (f y)) (g (x - y))‖ₑ ∂μ
  _ ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
    simp_rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc.le]
    refine lintegral_mono (fun y ↦ ?_)
    rw [← ENNReal.ofReal_mul <| mul_nonneg hc.le (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    exact hL y (x - y)
  _ ≤ _ := by
    have : eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ :=
      eLpNorm_comp_measurePreserving' hg (μ.measurePreserving_sub_left x)
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ ofReal_ne_top]
    apply mul_left_mono
    simpa [this] using ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm hpq hf.enorm hg'.enorm

open ENNReal in
/-- This inequality is used in the proof of Young's convolution inequality
`eLpNorm_convolution_le_ofReal`. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {c : ℝ} (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤ ENNReal.ofReal c *
    eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (ENNReal.ofReal r) μ *
    ((eLpNorm f (ENNReal.ofReal p) μ) ^ ((r - p) / r) *
    (eLpNorm g (ENNReal.ofReal q) μ) ^ ((r - q) / r)) := by
  by_cases hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  push_neg at hc
  by_cases μ0 : μ = 0
  · simp [μ0, convolution]
  push_neg at μ0
  let F (i : Fin 3) : G → ℝ≥0∞ :=
    match i with
    | 0 => fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)
    | 1 => fun y ↦ ‖f y‖ₑ ^ ((r - p) / r)
    | 2 => fun y ↦ ‖g (x - y)‖ₑ ^ ((r - q) / r)
  let P (i : Fin 3) : ℝ≥0∞ :=
    match i with
    | 0 => ENNReal.ofReal r
    | 1 => ENNReal.ofReal (p * r) / ENNReal.ofReal (r - p)
    | 2 => ENNReal.ofReal (q * r) / ENNReal.ofReal (r - q)
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have rp0 : 0 ≤ r - p := r_sub_p_nonneg p0 hq r0 hpqr
  have rq0 : 0 ≤ r - q := r_sub_p_nonneg q0 hp r0 <| add_comm p⁻¹ q⁻¹ ▸ hpqr
  calc
    _ ≤ ∫⁻ y, ‖L (f y) (g (x - y))‖ₑ ∂μ := by
      exact enorm_integral_le_lintegral_enorm (fun y ↦ L (f y) (g (x - y)))
    _ ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
      refine lintegral_mono (fun y ↦ ?_)
      rw [← enorm_norm, ← enorm_norm (f y), ← enorm_norm (g (x - y)), mul_assoc, ← enorm_mul]
      rw [Real.enorm_of_nonneg (norm_nonneg _)]
      rw [Real.enorm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [← ENNReal.ofReal_mul hc.le]
      exact ENNReal.ofReal_le_ofReal <| le_of_le_of_eq (hL y (x - y)) (mul_assoc _ _ _)
    _ = ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ ^ (p / r + (r - p) / r) *
                           ‖g (x - y)‖ₑ ^ (q / r + (r - q) / r) ∂μ := by
      refine lintegral_congr (fun y ↦ ?_)
      suffices p / r + (r - p) / r = 1 ∧ q / r + (r - q) / r = 1 by simp [this]
      rw [← add_div, ← add_div, add_sub_cancel, add_sub_cancel, and_self, div_self r0.ne.symm]
    _ = ∫⁻ y, ENNReal.ofReal c * (F 0) y * ((F 1) y * (F 2) y) ∂μ := by
      refine lintegral_congr (fun y ↦ ?_)
      simp_rw [F, mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (one_pos.le.trans hr))]
      repeat rw [← ENNReal.rpow_mul, ENNReal.rpow_add_of_nonneg]
      · ring_nf
      all_goals positivity
    _ = ∫⁻ y, ENNReal.ofReal c * ∏ i ∈ Finset.univ, (F i) y ∂μ := by
      simp [mul_assoc, Fin.prod_univ_succ]
    _ ≤ ENNReal.ofReal c * eLpNorm (F 0) (P 0) μ *
          (eLpNorm (F 1) (P 1) μ * eLpNorm (F 2) (P 2) μ) := by
      rw [lintegral_const_mul' _ _ ofReal_ne_top, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le (ENNReal.ofReal c))
      -- Check that the assumptions of `lintegral_prod_norm_pow_le'` apply
      have ae_meas_f : AEMeasurable (‖f ·‖ₑ) μ := hf.enorm
      have ae_meas_g : AEMeasurable (‖g <| x - ·‖ₑ) μ :=
        (hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x).enorm
      have := (ae_meas_f.pow_const p).mul (ae_meas_g.pow_const q)
      have ae_meas : ∀ i ∈ Finset.univ, AEMeasurable (F i) μ :=
        fun ⟨v, _⟩ _ ↦ by interval_cases v <;> exact AEMeasurable.pow_const (by assumption) _
      suffices ∑ i ∈ Finset.univ, 1 / P i = 1 by
        simpa [Fin.prod_univ_succ] using lintegral_prod_norm_pow_le' ae_meas this
      -- It remains to check ∑ 1 / P i = 1, which is trivial, aside from technicalities in `ℝ≥0∞`
      simp_rw [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero, P, one_div]
      repeat rw [ENNReal.inv_div]
      · rw [ofReal_sub r p0.le, ofReal_sub r q0.le, ofReal_mul p0.le, ofReal_mul q0.le]
        repeat rw [ENNReal.sub_div (by simp [p0, q0, r0])]
        nth_rewrite 2 5 [← one_mul (ENNReal.ofReal r)]
        nth_rewrite 2 [← mul_one (ENNReal.ofReal p), ← mul_one (ENNReal.ofReal q)]
        repeat rw [ENNReal.mul_div_mul_right _ _ (by simp [r0]) (by simp), one_div]
        repeat rw [ENNReal.mul_div_mul_left _ _ (by simp [p0, q0]) (by simp), one_div]
        rw [← ENNReal.ofReal_one, ← congr_arg ENNReal.ofReal (sub_eq_iff_eq_add'.mpr hpqr)]
        rw [ofReal_sub _ (inv_pos.mpr r0).le, ← add_assoc]
        rw [ofReal_add (inv_pos.mpr p0).le (inv_pos.mpr q0).le]
        have : AddLECancellable (ENNReal.ofReal r)⁻¹ := ENNReal.cancel_of_ne (by simp [r0])
        rw [← this.add_tsub_assoc_of_le, ← this.add_tsub_assoc_of_le, this.add_tsub_cancel_left]
        · rw [ofReal_inv_of_pos p0, ofReal_inv_of_pos q0, ofReal_inv_of_pos r0]
        all_goals exact ENNReal.inv_le_inv.mpr <| ofReal_le_ofReal (sub_nonneg.mp (by assumption))
      all_goals simp [ENNReal.mul_pos, p0, q0, r0]
    _ = _ := by
      congr
      · exact eLpNorm_eq_eLpNorm_rpow f r0 p0 rp0 μ0
      · rw [eLpNorm_eq_eLpNorm_rpow (g <| x - ·) r0 q0 rq0 μ0]
        simp [eLpNorm, eLpNorm', lintegral_sub_left_eq_self (‖g ·‖ₑ ^ (ENNReal.ofReal q).toReal) x]

theorem eLpNorm_convolution_le_ofReal {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {c : ℝ} (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (ENNReal.ofReal r) μ ≤
    ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hf' := hf.enorm.pow_const p
  have hg' := hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const q
  have hfg := hf'.snd.mul hg'
  rw [← ENNReal.rpow_le_rpow_iff r0]
  repeat rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
  calc eLpNorm (f ⋆[L, μ] g) (ENNReal.ofReal r) μ ^ r
    _ = ∫⁻ (x : G), ‖(f ⋆[L, μ] g) x‖ₑ ^ r ∂μ := by simp [eLpNorm, eLpNorm', r0, r0.le, r0.ne.symm]
    _ ≤ _ :=
      lintegral_mono <| fun x ↦ ENNReal.rpow_le_rpow (h₂ := r0.le) <|
        enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm hp hq hr hpqr hf hg hL x
    _ = (ENNReal.ofReal c) ^ r *
        (∫⁻ x, (eLpNorm (fun y ↦ (‖f y‖ₑ^p * ‖g (x-y)‖ₑ^q) ^ (1/r)) (ENNReal.ofReal r) μ) ^ r ∂μ) *
        (eLpNorm f (ENNReal.ofReal p) μ ^ (r - p) * eLpNorm g (ENNReal.ofReal q) μ ^ (r - q)) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
      rw [lintegral_mul_const'', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, lintegral_const_mul']
      · field_simp
      · exact ENNReal.rpow_ne_top_of_nonneg r0.le ofReal_ne_top
      · apply AEMeasurable.const_mul
        simpa [eLpNorm, eLpNorm', r0.not_le, r0.ne.symm, r0.le] using hfg.lintegral_prod_right'
    _ = _ := by
      have (a b : ℝ≥0∞) : a ^ r * b ^ r = (a ^ p * b ^ q) * (a ^ (r - p) * b ^ (r - q)) := calc
        _ = (a ^ p * a ^ (r - p)) * (b ^ q * b ^ (r - q)) := by
          rw [← ENNReal.rpow_add_of_nonneg p _ p0.le, ← ENNReal.rpow_add_of_nonneg q _ q0.le,
            add_sub_cancel, add_sub_cancel]
          · exact r_sub_p_nonneg q0 hp r0 <| add_comm p⁻¹ q⁻¹ ▸ hpqr
          · exact r_sub_p_nonneg p0 hq r0 hpqr
        _ = _ := by ring
      rw [mul_assoc, mul_assoc, this]
      congr
      calc
        _ = ∫⁻ x, ((∫⁻ y, ((‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ r⁻¹) ^ r ∂μ) ^ r⁻¹) ^ r ∂μ := by
          simp [eLpNorm, eLpNorm', r0.not_le, ENNReal.toReal_ofReal r0.le]
        _ = ∫⁻ x, (∫⁻ y, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ := by
          simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ r0.ne.symm, ENNReal.rpow_one]
        _ = ∫⁻ y, (∫⁻ x, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ :=
          lintegral_lintegral_swap hfg
        _ = (∫⁻ y, ‖f y‖ₑ ^ p ∂μ) * (∫⁻ x, ‖g x‖ₑ ^ q ∂μ) := by
          have {y : G} : ‖f y‖ₑ ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg p0.le enorm_ne_top
          simp_rw [lintegral_const_mul' _ _ this, ← lintegral_mul_const'' _ hf',
            lintegral_sub_right_eq_self (‖g ·‖ₑ ^ q) _]
        _ = eLpNorm f (ENNReal.ofReal p) μ ^ p * eLpNorm g (ENNReal.ofReal q) μ ^ q := by
          simp [eLpNorm, eLpNorm', ← ENNReal.rpow_mul, inv_mul_cancel₀,
            p0.not_le, q0.not_le, p0.le, q0.le, p0.ne.symm, q0.ne.symm]

/-- A generalization of **Young's convolution inequality** that allows an arbitrary `L` as long as
a bound on the size of `L` (on the ranges of `f` and `g`) is known. See also
`eLpNorm_convolution_le_enorm_mul`, which is stated similarly in terms of `‖L‖ₑ`. -/
theorem eLpNorm_convolution_le_of_norm_le_mul {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {c : ℝ} (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  -- First use `eLpNorm_top_convolution_le` to handle the cases where any exponent is `∞`
  by_cases r_top : r = ∞
  · rw [r_top, ENNReal.inv_top, zero_add] at hpqr
    have hpq : p.IsConjExponent q := by exact ⟨hpqr⟩
    exact r_top ▸ eLpNorm_top_convolution_le hpq hf hg hL
  have hpq : 1 < p⁻¹ + q⁻¹ := by
    rw [hpqr]
    nth_rewrite 1 [← zero_add 1]
    apply ENNReal.add_lt_add_right ENNReal.one_ne_top
    exact (zero_le r⁻¹).lt_or_eq.resolve_right (ENNReal.inv_ne_zero.mpr r_top).symm
  have p_ne_top : p ≠ ∞ := by contrapose! hq; simpa [hq] using hpq
  have q_ne_top : q ≠ ∞ := by contrapose! hp; simpa [hp] using hpq
  -- When all exponents are finite, apply `eLpNorm_convolution_le_ofReal`
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr p_ne_top, ← ENNReal.ofReal_toReal_eq_iff.mpr q_ne_top,
    ← ENNReal.ofReal_toReal_eq_iff.mpr r_top]
  refine eLpNorm_convolution_le_ofReal ?_ ?_ ?_ ?_ hf hg hL; rotate_right
  · simp_rw [← ENNReal.one_toReal, ← ENNReal.toReal_inv]
    rw [← ENNReal.toReal_add _ ENNReal.one_ne_top, ← ENNReal.toReal_add, hpqr]
    all_goals exact ENNReal.inv_ne_top.mpr (fun h ↦ (h ▸ one_pos).not_le (by assumption))
  all_goals rwa [← ENNReal.one_toReal, ENNReal.toReal_le_toReal ENNReal.one_ne_top (by assumption)]

/-- **Young's convolution inequality**: the `ℒr` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by the product of the `ℒp` and `ℒq` seminorms, where `1 / p + 1 / q = 1 / r + 1` and
`‖L‖ₑ ≤ 1`. This includes the standard form of the inequality, in which `L` is multiplication. -/
theorem eLpNorm_convolution_le_of_norm_le {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  replace hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ 1 * ‖f x‖ * ‖g y‖ := by simpa using hL
  simpa using eLpNorm_convolution_le_of_norm_le_mul hp hq hr hpqr hf hg hL

/-- A generalization of **Young's convolution inequality** for the `ℒr` seminorm of a convolution
`(f ⋆[L, μ] g)`, which applies for any `L`. -/
theorem eLpNorm_convolution_le_enorm_mul {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul hp hq hr hpqr hf hg <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

end ENNReal

end Convolution
