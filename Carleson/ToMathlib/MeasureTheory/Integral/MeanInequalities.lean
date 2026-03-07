module

public import Carleson.ToMathlib.Data.Real.ConjExponents
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.MeasureTheory.Integral.Periodic
public import Carleson.ToMathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

-- Upstreaming status: results seems useful; proofs may need polish
-- Needs dependencies to be upstreamed first.

open NNReal ENNReal MeasureTheory Finset

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace ENNReal

/-- **Minkowski inequality** for finite sums of `ENNReal`-valued functions. -/
theorem Lp_add_le_sum
    {ι κ : Type*} {s : Finset ι} {t : Finset κ} {f : ι → κ → ℝ≥0∞} {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (∑ j ∈ t, f i j) ^ p) ^ (1 / p) ≤ ∑ j ∈ t, (∑ i ∈ s, f i j ^ p) ^ (1 / p) := by
  have ppos : 0 < p := by positivity
  have pinvpos : 0 < 1 / p := by positivity
  induction t using Finset.cons_induction with
  | empty =>
    simp_rw [sum_empty, ENNReal.zero_rpow_of_pos ppos, sum_const_zero, nonpos_iff_eq_zero,
      ENNReal.zero_rpow_of_pos pinvpos]
  | cons a t h ih =>
    simp_rw [sum_cons]
    calc
      _ ≤ (∑ x ∈ s, f x a ^ p) ^ (1 / p) + (∑ i ∈ s, (∑ j ∈ t, f i j) ^ p) ^ (1 / p) :=
        Lp_add_le _ _ _ hp
      _ ≤ _ := by gcongr

-- Add after `lintegral_prod_norm_pow_le`
/-- A version of Hölder with multiple arguments, allowing `∞` as an exponent. -/
theorem lintegral_prod_norm_pow_le' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Finset ι} {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {p : ι → ℝ≥0∞} (hp : ∑ i ∈ s, (p i)⁻¹ = 1) :
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  classical
  revert hp hf
  refine Finset.strongInduction (fun s hs hf hp ↦ ?_) s (p := fun s ↦
    (∀ i ∈ s, AEMeasurable (f i) μ) → (∑ i ∈ s, (p i)⁻¹ = 1) →
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ)
  by_cases exists_top : ∃ i₀ ∈ s, p i₀ = ∞    -- If one of the exponents is `∞`, we reduce to the
  · obtain ⟨i₀, hi₀, pi₀_eq_top⟩ := exists_top -- case without it and use the inductive hypothesis
    calc ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ
      _ = ∫⁻ (a : α), f i₀ a * ∏ i ∈ s.erase i₀, f i a ∂μ :=
        lintegral_congr (fun a ↦ (Finset.mul_prod_erase s (f · a) hi₀).symm)
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∫⁻ (a : α), ∏ i ∈ s.erase i₀, f i a ∂μ := by
        rw [← lintegral_const_mul'', pi₀_eq_top]
        · exact lintegral_mono_ae <| (ae_le_essSup (f i₀)).mono (fun a ha ↦ mul_le_mul_left ha _)
        · exact Finset.aemeasurable_fun_prod _ (fun i hi ↦ hf i (Finset.mem_of_mem_erase hi))
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∏ i ∈ s.erase i₀, eLpNorm (f i) (p i) μ := by
        apply mul_right_mono
        apply hs (s.erase i₀) (s.erase_ssubset hi₀) (fun i hi ↦ hf i (s.erase_subset i₀ hi))
        simpa [← Finset.add_sum_erase s _ hi₀, pi₀_eq_top] using hp
      _ = _ := Finset.mul_prod_erase s (fun i ↦ eLpNorm (f i) (p i) μ) hi₀
  -- If all exponents are finite, we're in the case covered by `ENNReal.lintegral_prod_norm_pow_le`
  have hf' : ∀ i ∈ s, AEMeasurable (fun a ↦ ((f i a) ^ (p i).toReal)) μ :=
    fun i hi ↦ (hf i hi).pow_const (p i).toReal
  have hp₁ : ∑ i ∈ s, (p i).toReal⁻¹ = 1 := by
    simp_rw [← (ENNReal.toReal_eq_one_iff 1).mpr rfl, ← ENNReal.toReal_inv]
    suffices (∑ x ∈ s, (p x)⁻¹).toReal = ∑ x ∈ s, (p x)⁻¹.toReal by rw [← this, hp]
    refine ENNReal.toReal_sum (fun i hi eq_top ↦ ?_)
    exact ENNReal.one_ne_top <| hp ▸ ENNReal.sum_eq_top.mpr ⟨i, hi, eq_top⟩
  have hp₂ : ∀ i ∈ s, 0 ≤ (p i).toReal⁻¹ := by intros; positivity
  have p_ne_0 : ∀ i ∈ s, p i ≠ 0 :=
    fun i hi eq0 ↦ one_ne_top <| hp.symm.trans <| ENNReal.sum_eq_top.mpr ⟨i, hi, by simp [eq0]⟩
  have p_ne_top : ∀ i ∈ s, p i ≠ ∞ := fun i hi h ↦ exists_top ⟨i, hi, h⟩
  convert ENNReal.lintegral_prod_norm_pow_le s hf' hp₁ hp₂ with a i₀ hi₀ i hi
  · rw [← ENNReal.rpow_mul, mul_inv_cancel₀, rpow_one]
    exact ENNReal.toReal_ne_zero.mpr ⟨p_ne_0 i₀ hi₀, (exists_top ⟨i₀, hi₀, ·⟩)⟩
  · simp [eLpNorm, eLpNorm', p_ne_0 i hi, p_ne_top i hi]

/-- **Hölder's inequality** for functions `α → ℝ≥0∞`, using exponents in `ℝ≥0∞` -/
theorem lintegral_mul_le_eLpNorm_mul_eLqNorm {p q : ℝ≥0∞} (hpq : p.HolderConjugate q)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ (a : α), (f * g) a ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  by_cases! pq_top : p = ∞ ∨ q = ∞
  · wlog hp : p = ∞
    · have hq := pq_top.resolve_left hp
      simpa only [mul_comm] using this hpq.symm hg hf (Or.inl hq) hq
    apply le_of_le_of_eq <| lintegral_mono_ae ((ae_le_essSup f).mono (fun a ha ↦ mul_left_mono ha))
    simp [eLpNorm, eLpNorm', eLpNormEssSup, hp, hpq.conj_eq, lintegral_const_mul'' _ hg]
  have hp : p ≠ 0 := HolderConjugate.ne_zero p q
  have hq : q ≠ 0 := HolderConjugate.ne_zero q p
  convert ENNReal.lintegral_mul_le_Lp_mul_Lq μ (hpq.toReal_of_ne_top pq_top.1 pq_top.2) hf hg
  all_goals simp [eLpNorm, eLpNorm', pq_top, hp, hq]

/-- **Cauchy–Schwarz inequality** for functions `α → ℝ≥0∞` (Hölder's inequality squared). -/
theorem sq_lintegral_mul_le_mul_lintegral_sq {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  convert pow_le_pow_left₀ (zero_le _)
    (lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg) 2
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * (2 : ℕ) = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_one]
  simp_rw [show (2 : ℝ) = (2 : ℕ) by rfl, ← ENNReal.rpow_natCast]

end ENNReal


section Convolution

open scoped Convolution

-- Used in the proof of Young's convolution inequality
private lemma r_sub_p_nonneg {p q r : ℝ} (p0 : 0 < p) (hq : 1 ≤ q) (r0 : 0 < r)
    (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) : 0 ≤ r - p := by
  rw [sub_nonneg, ← inv_le_inv₀ r0 p0, ← add_le_add_iff_right, hpqr]
  exact add_le_add_right ((inv_le_one₀ (lt_of_lt_of_le one_pos hq)).mpr hq) r⁻¹

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
  · simp [eLpNorm, eLpNorm', ← exp_zero, er_pos.not_ge, eLpNormEssSup_const _ μ0]
  have r_sub_e_pos : 0 < r - e := lt_of_le_of_ne re0 exp_zero
  have lt_top : ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e) < ∞ :=
    div_lt_top ofReal_ne_top <| (not_iff_not.mpr ofReal_eq_zero).mpr r_sub_e_pos.not_ge
  simp only [eLpNorm, eLpNorm', reduceIte, div_eq_zero_iff, ofReal_eq_zero, ofReal_ne_top,
    lt_top.ne, er_pos.not_ge, e0.not_ge, or_self, enorm_eq_self, ← rpow_mul]
  simp only [e0.le, ofReal_mul, toReal_div, toReal_mul, toReal_ofReal, r0.le, re0, one_div, inv_div]
  congr
  · ext; congr; field_simp
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

-- Auxiliary inequality used to prove inequalities with simpler conditions on f and g.
private theorem eLpNorm_top_convolution_le_aux [AddGroup G] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable (‖f ·‖ₑ) μ)
    (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : ∀ x : G, eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  by_cases! hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  rw [eLpNorm_exponent_top, eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x ↦ ?_)
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  calc ∫⁻ y, ‖(L (f y)) (g (x - y))‖ₑ ∂μ
    _ ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
      simp_rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc.le]
      refine lintegral_mono (fun y ↦ ?_)
      rw [← ENNReal.ofReal_mul <| mul_nonneg hc.le (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal <| hL y (x - y)
    _ ≤ _ := by
      simp_rw [mul_assoc, lintegral_const_mul' _ _ ofReal_ne_top]
      simpa [hg' x] using mul_right_mono (ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm hpq hf (hg x))

variable [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  [μ.IsAddHaarMeasure] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] [μ.IsNegInvariant] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_top_convolution_le_aux hpq hf.enorm ?_ ?_ c hL
  · intro x; exact (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  · intro x; exact eLpNorm_comp_measurePreserving' hg (μ.measurePreserving_sub_left x)

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le' [μ.IsNegInvariant] {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (c : ℝ)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_top_convolution_le_aux hpq hf.enorm ?_ ?_ c hL
  · intro x; exact (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  · intro x; apply eLpNorm_comp_measurePreserving hg (Measure.measurePreserving_sub_left μ x)

-- Auxiliary inequality used to prove versions with simpler conditions on `f` and `g`
open ENNReal in
omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux
    [μ.IsNegInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (hf : AEMeasurable (‖f ·‖ₑ) μ) (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) := by
  by_cases! hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  by_cases! μ0 : μ = 0
  · simp [μ0, convolution]
  let F (i : Fin 3) : G → ℝ≥0∞ :=
    match i with
    | 0 => fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)
    | 1 => fun y ↦ ‖f y‖ₑ ^ ((r - p) / r)
    | 2 => fun y ↦ ‖g (x - y)‖ₑ ^ ((r - q) / r)
  let P : Fin 3 → ℝ≥0∞ :=
    ![.ofReal r, .ofReal (p * r) / .ofReal (r - p), .ofReal (q * r) / .ofReal (r - q)]
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have rp0 : 0 ≤ r - p := r_sub_p_nonneg p0 hq r0 hpqr
  have rq0 : 0 ≤ r - q := r_sub_p_nonneg q0 hp r0 <| add_comm p⁻¹ q⁻¹ ▸ hpqr
  calc
    _ ≤ ∫⁻ y, ‖L (f y) (g (x - y))‖ₑ ∂μ := by
      exact enorm_integral_le_lintegral_enorm (fun y ↦ L (f y) (g (x - y)))
    _ ≤ ∫⁻ y, .ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
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
      have ae_meas_g := hg x
      have := (hf.pow_const p).mul (ae_meas_g.pow_const q)
      have ae_meas : ∀ i ∈ Finset.univ, AEMeasurable (F i) μ :=
        fun ⟨v, _⟩ _ ↦ by interval_cases v <;> exact AEMeasurable.pow_const (by assumption) _
      suffices ∑ i, (P i)⁻¹ = 1 by
        simpa [Fin.prod_univ_succ] using lintegral_prod_norm_pow_le' ae_meas this
      -- It remains to check ∑ (P i)⁻¹ = 1, which is trivial, aside from technicalities in `ℝ≥0∞`
      simp_rw [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero, P, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_zero]
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
      all_goals simp [p0, q0, r0]
    _ = _ := by
      congr
      · exact eLpNorm_eq_eLpNorm_rpow f r0 p0 rp0 μ0
      · simp_rw [P, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [eLpNorm_eq_eLpNorm_rpow (g <| x - ·) r0 q0 rq0 μ0]
        simp [eLpNorm, eLpNorm', lintegral_sub_left_eq_self (‖g ·‖ₑ ^ (ENNReal.ofReal q).toReal) x]

open ENNReal in
/-- This inequality is used in the proof of Young's convolution inequality
`eLpNorm_convolution_le_ofReal`. See `enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm'` for
a version assuming a.e. strong measurability instead. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
    [μ.IsNegInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) :=
  enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux hp hq hr hpqr hf.enorm
    (fun x ↦ (hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x).enorm) c hL x

open ENNReal in
/-- This inequality is used in the proof of Young's convolution inequality
`eLpNorm_convolution_le_ofReal'`. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm'
    [μ.IsNegInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) :=
  enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux hp hq hr hpqr hf.enorm
    (fun x ↦ (hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x).enorm) c hL x

-- Auxiliary inequality used to prove versions with simpler conditions on `f` and `g`
private theorem eLpNorm_convolution_le_ofReal_aux
    [μ.IsAddRightInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (hf : AEMeasurable (‖f ·‖ₑ) μ) (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : AEMeasurable (fun (x : G × G) ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q) (μ.prod μ))
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hf' := hf.pow_const p
  have hfg := hf'.comp_snd.mul hg'
  replace hg' := hg'.pow_const q
  rw [← ENNReal.rpow_le_rpow_iff r0]
  repeat rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
  calc eLpNorm (f ⋆[L, μ] g) (ENNReal.ofReal r) μ ^ r
    _ = ∫⁻ (x : G), ‖(f ⋆[L, μ] g) x‖ₑ ^ r ∂μ := by simp [eLpNorm, eLpNorm', r0, r0.le, r0.ne.symm]
    _ ≤ _ :=
      lintegral_mono <| fun x ↦ ENNReal.rpow_le_rpow (h₂ := r0.le) <|
        enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux hp hq hr hpqr hf hg c hL x
    _ = (ENNReal.ofReal c) ^ r *
        (∫⁻ x, (eLpNorm (fun y ↦ (‖f y‖ₑ^p * ‖g (x-y)‖ₑ^q) ^ (1/r)) (ENNReal.ofReal r) μ) ^ r ∂μ) *
        (eLpNorm f (ENNReal.ofReal p) μ ^ (r - p) * eLpNorm g (ENNReal.ofReal q) μ ^ (r - q)) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
      rw [lintegral_mul_const'', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, lintegral_const_mul']
      · field_simp
      · exact ENNReal.rpow_ne_top_of_nonneg r0.le ofReal_ne_top
      · apply AEMeasurable.const_mul
        simpa [eLpNorm, eLpNorm', r0.not_ge, r0.ne.symm, r0.le] using hfg.lintegral_prod_right'
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
          simp [eLpNorm, eLpNorm', r0.not_ge, ENNReal.toReal_ofReal r0.le]
        _ = ∫⁻ x, (∫⁻ y, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ := by
          simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ r0.ne.symm, ENNReal.rpow_one]
        _ = ∫⁻ y, (∫⁻ x, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ :=
          lintegral_lintegral_swap hfg
        _ = (∫⁻ y, ‖f y‖ₑ ^ p ∂μ) * (∫⁻ x, ‖g x‖ₑ ^ q ∂μ) := by
          have {y : G} : ‖f y‖ₑ ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg p0.le enorm_ne_top
          simp_rw [lintegral_const_mul' _ _ this, ← lintegral_mul_const'' _ hf',
            lintegral_sub_right_eq_self (‖g ·‖ₑ ^ q) _]
        _ = eLpNorm f (ENNReal.ofReal p) μ ^ p * eLpNorm g (ENNReal.ofReal q) μ ^ q := by
          simp [eLpNorm, eLpNorm', ← ENNReal.rpow_mul, p0.not_ge, q0.not_ge, p0.le, q0.le,
            p0.ne.symm, q0.ne.symm]

theorem eLpNorm_convolution_le_ofReal [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E']
    [μ.IsAddRightInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  refine eLpNorm_convolution_le_ofReal_aux hp hq hr hpqr hf.enorm ?_ ?_ c hL
  · intro x; exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x) |>.enorm
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const q

theorem eLpNorm_convolution_le_ofReal'
    [μ.IsAddRightInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  refine eLpNorm_convolution_le_ofReal_aux hp hq hr hpqr hf.enorm ?_ ?_ c hL
  · intro x; exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x) |>.enorm
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const q

-- Auxiliary result to prove the following versions with simpler assumptions on `f` and `g`
private theorem eLpNorm_convolution_le_of_norm_le_mul_aux
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable (‖f ·‖ₑ) μ)
    (hg : ∀ (x : G), AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : ∀ (x : G), eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ)
    (hg'' : AEMeasurable (fun x ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q.toReal) (μ.prod μ))
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  -- First use `eLpNorm_top_convolution_le` to handle the cases where any exponent is `∞`
  by_cases r_top : r = ∞
  · rw [r_top, ENNReal.inv_top, zero_add] at hpqr
    have hpq : p.HolderConjugate q := holderConjugate_iff.mpr hpqr
    rw [r_top]
    refine eLpNorm_top_convolution_le_aux hpq hf hg hg' c hL
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
  refine eLpNorm_convolution_le_ofReal_aux ?_ ?_ ?_ ?_ hf hg hg'' c hL; rotate_right
  · simp_rw [← ENNReal.toReal_one, ← ENNReal.toReal_inv]
    rw [← ENNReal.toReal_add _ ENNReal.one_ne_top, ← ENNReal.toReal_add, hpqr]
    all_goals exact ENNReal.inv_ne_top.mpr (fun h ↦ (h ▸ one_pos).not_ge (by assumption))
  all_goals rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top (by assumption)]

variable (L)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E']
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_convolution_le_of_norm_le_mul_aux hp hq hr hpqr hf.enorm ?_ ?_ ?_ c hL
  · intro x; exact hg.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  · intro x; exact eLpNorm_comp_measurePreserving' hg (μ.measurePreserving_sub_left x)
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const _

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul'
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_convolution_le_of_norm_le_mul_aux hp hq hr hpqr hf.enorm ?_ ?_ ?_ c hL
  · intro x; exact hg.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  · intro x; apply eLpNorm_comp_measurePreserving hg (μ.measurePreserving_sub_left x)
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const _

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E']
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul' [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul' L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

open Set AddCircle in
lemma eLpNorm_Ioc_convolution_le_of_norm_le_mul_aux (a : ℝ) {T : ℝ} [hT : Fact (0 < T)]
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : ℝ → E} {g : ℝ → E'} (hfT : f.Periodic T) (hgT : g.Periodic T)
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (c : ℝ) (hL : ∀ (x y : ℝ), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y))) r (volume.restrict (Ioc a (a + T))) ≤
    .ofReal c * eLpNorm f p (volume.restrict (Ioc a (a + T))) *
      eLpNorm g q (volume.restrict (Ioc a (a + T))) :=
  calc
    _ = eLpNorm (liftIoc T a fun x ↦ ∫ (y : ℝ) in a..a + T, (L (f y)) (g (x - y))) r := by
      rw [← eLpNorm_liftIoc' T a]
      · apply AEStronglyMeasurable.sub
        · apply AEStronglyMeasurable.integral_prod_right' (f := fun z ↦ L (f z.2) (g (z.1 - z.2)))
          apply L.aestronglyMeasurable_comp₂ hf.restrict.comp_snd
          exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub _ _)
        · have empty_interval := Set.Ioc_eq_empty_of_le ((le_add_iff_nonneg_right a).mpr hT.out.le)
          simpa [empty_interval] using aestronglyMeasurable_const
    _ = eLpNorm (liftIoc T a f ⋆[L] liftIoc T a g) r := by
      rw [← liftIoc_convolution_liftIoc L a hfT hgT]
    _ ≤ .ofReal c * eLpNorm (liftIoc T a f) p * eLpNorm (liftIoc T a g) q := by
      exact eLpNorm_convolution_le_of_norm_le_mul' L hp hq hr hpqr (hf.liftIoc T a) (hg.liftIoc T a)
        c (by intros; apply hL)
    _ = _ := by
      rw [← eLpNorm_liftIoc' T a hf, ← eLpNorm_liftIoc' T a hg]

open Set AddCircle in
/-- **Young's convolution inequality** on (a, a + T]: the `L^r` seminorm of the convolution
of `T`-periodic functions over (a, a + T] is bounded by `‖L‖ₑ` times the product of
the `L^p` and `L^q` seminorms on that interval, where `1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ`
is replaced with a bound for `L` restricted to the ranges of `f` and `g`; see
`eLpNorm_Ioc_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_Ioc_convolution_le_of_norm_le_mul (a : ℝ) {T : ℝ} [hT : Fact (0 < T)]
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : ℝ → E} {g : ℝ → E'} (hgT : g.Periodic T)
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (c : ℝ) (hL : ∀ (x y : ℝ), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y))) r (volume.restrict (Ioc a (a + T))) ≤
    .ofReal c * eLpNorm f p (volume.restrict (Ioc a (a + T))) *
      eLpNorm g q (volume.restrict (Ioc a (a + T))) := by
  let f' := AddCircle.liftIoc T a f
  let f'' := fun (x : ℝ) ↦ f' x
  have hfT : f''.Periodic T := by simp [Function.Periodic, f'']
  have : eLpNorm (fun x ↦ ∫ y in a..a+T, L (f'' y) (g (x - y))) r
        (volume.restrict (Ioc a (a + T))) ≤
      .ofReal c * eLpNorm f'' p (volume.restrict (Ioc a (a + T))) *
      eLpNorm g q (volume.restrict (Ioc a (a + T))) := by
    apply eLpNorm_Ioc_convolution_le_of_norm_le_mul_aux L a hp hq hr hpqr hfT hgT _ hg
    · intro x y
      simp only [liftIoc, Function.comp_apply, restrict_apply, f'', f']
      apply hL
    have A : AEStronglyMeasurable f'
        (Measure.map (fun (x : ℝ) ↦ (x : AddCircle T)) (volume : Measure ℝ)) :=
      AEStronglyMeasurable.mono_ac (quasiMeasurePreserving_coe_addCircle T).absolutelyContinuous
        (by fun_prop)
    exact A.comp_measurable (by fun_prop)
  convert this using 3 with x
  · rw [intervalIntegral.integral_of_le (by linarith [hT.out]),
      intervalIntegral.integral_of_le (by linarith [hT.out])]
    apply setIntegral_congr_fun measurableSet_Ioc (fun y hy ↦ ?_)
    congr
    exact (equivIoc_coe_of_mem a hy).symm
  · apply eLpNorm_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    congr
    exact (equivIoc_coe_of_mem a hy).symm

open Set in
/-- **Young's convolution inequality** on (a, a + T]: the `L^r` seminorm of the convolution
of `T`-periodic functions over (a, a + T] is bounded by `‖L‖ₑ` times the product of
the `L^p` and `L^q` seminorms on that interval, where `1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_Ioc_convolution_le_enorm_mul (a : ℝ) {T : ℝ} [hT : Fact (0 < T)]
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : ℝ → E} {g : ℝ → E'} (hgT : g.Periodic T)
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) :
    eLpNorm (fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y))) r (volume.restrict (Ioc a (a + T))) ≤
    ‖L‖ₑ * eLpNorm f p (volume.restrict (Ioc a (a + T)))
      * eLpNorm g q (volume.restrict (Ioc a (a + T))) := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_Ioc_convolution_le_of_norm_le_mul L a hp hq hr hpqr hgT hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

end ENNReal

end Convolution
