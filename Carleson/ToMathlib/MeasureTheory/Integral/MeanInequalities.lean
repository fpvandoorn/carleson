module

public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Carleson.ToMathlib.MeasureTheory.Integral.Periodic
public import Carleson.ToMathlib.MeasureTheory.Measure.Haar.Unique

public section

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
    {s : Finset ι} {f : ι → α → ℝ≥0∞} {p : ι → ℝ≥0∞} (hp : ∑ i ∈ s, (p i)⁻¹ = 1) :
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  calc ∫⁻ a, ∏ i ∈ s, f i a ∂μ
    _ ≤ eLpNorm (∏ i ∈ s, f i) 1 μ := by
      simpa [Finset.prod_apply] using lintegral_enorm_le_eLpNorm_one (f := ∏ i ∈ s, f i) (μ := μ)
    _ ≤ _ := eLpNorm_prod_le_ennreal (by rw [hp, inv_one]) one_pos

/-- **Hölder's inequality** for functions `α → ℝ≥0∞`, using exponents in `ℝ≥0∞` -/
theorem lintegral_mul_le_eLpNorm_mul_eLqNorm {p q : ℝ≥0∞} (hpq : p.HolderConjugate q)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ (a : α), (f * g) a ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  by_cases! pq_top : p = ∞ ∨ q = ∞
  · wlog hp : p = ∞
    · have hq := pq_top.resolve_left hp
      simpa only [mul_comm] using this hpq.symm hg hf (Or.inl hq) hq
    apply le_of_le_of_eq <| lintegral_mono_ae ((ae_le_essSup f).mono (fun a ha ↦ mul_left_mono ha))
    simp [eLpNorm, eLpNorm', eLpNormEssSup, hp, hpq.conj_eq, lintegral_const_mul'' _ hg,
      hf.aestronglyMeasurable, hg.aestronglyMeasurable]
  have hp : p ≠ 0 := HolderConjugate.ne_zero p q
  have hq : q ≠ 0 := HolderConjugate.ne_zero q p
  convert ENNReal.lintegral_mul_le_Lp_mul_Lq μ (hpq.toReal_of_ne_top pq_top.1 pq_top.2) hf hg
  all_goals simp [eLpNorm, eLpNorm', pq_top, hp, hq, hf.aestronglyMeasurable,
    hg.aestronglyMeasurable]

/-- **Cauchy–Schwarz inequality** for functions `α → ℝ≥0∞` (Hölder's inequality squared). -/
theorem sq_lintegral_mul_le_mul_lintegral_sq {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  convert! pow_le_pow_left₀ zero_le
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

private lemma eLpNorm_enorm_rpow_le (h : G → E) {r e : ℝ} (e0 : 0 < e) (re0 : 0 ≤ r - e) :
    eLpNorm (‖h ·‖ₑ ^ ((r - e) / r)) (.ofReal (e⁻¹ - r⁻¹))⁻¹ μ ≤
    eLpNorm h (.ofReal e) μ ^ ((r - e) / r) := by
  rcases (sub_nonneg.mp re0).eq_or_lt with rfl | er
  · simp [eLpNorm_exponent_top aestronglyMeasurable_const, eLpNormEssSup_le_of_ae_enorm_bound]
  have r0 : 0 < r := e0.trans er
  have hexp : 0 < (r - e) / r := div_pos (sub_pos.mpr er) r0
  by_cases hh : AEStronglyMeasurable h μ; swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hh, top_rpow_of_pos hexp]
  have : (r - e) / r / (e⁻¹ - r⁻¹) = e := by field_simp
  rw [eLpNorm_enorm_rpow h hh hexp, ← ENNReal.div_eq_inv_mul,
    ← ofReal_div_of_pos (sub_pos.mpr (inv_strictAnti₀ e0 er)), this]

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

variable [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  [μ.IsAddHaarMeasure] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le [μ.IsNegInvariant] {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (c : ℝ)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  by_cases! hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  have hgx (x : G) : AEStronglyMeasurable (g <| x - ·) μ :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  have hfg : AEStronglyMeasurable (f ⋆[L, μ] g) μ := (L.aestronglyMeasurable_comp₂ hf.comp_snd
    (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ))).integral_prod_right'
  rw [eLpNorm_exponent_top hfg, eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x ↦ ?_)
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  calc ∫⁻ y, ‖(L (f y)) (g (x - y))‖ₑ ∂μ
    _ ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
      simp_rw [← ofReal_norm, ← ENNReal.ofReal_mul hc.le]
      refine lintegral_mono (fun y ↦ ?_)
      rw [← ENNReal.ofReal_mul <| mul_nonneg hc.le (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal <| hL y (x - y)
    _ ≤ _ := by
      simp_rw [mul_assoc, lintegral_const_mul' _ _ ofReal_ne_top]
      have hg' : eLpNorm (g <| x - ·) q μ = eLpNorm g q μ :=
        eLpNorm_comp_measurePreserving hg (μ.measurePreserving_sub_left x)
      simpa [eLpNorm_enorm _ hf, eLpNorm_enorm _ (hgx x), hg'] using
        mul_right_mono (ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm hpq hf.enorm (hgx x).enorm)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- This inequality is used in the proof of Young's convolution inequality
`eLpNorm_convolution_le_ofReal`. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm
    [μ.IsNegInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) := by
  have p0 : 0 < p := one_pos.trans_le hp
  have q0 : 0 < q := one_pos.trans_le hq
  have r0 : 0 < r := one_pos.trans_le hr
  have rp0 : 0 ≤ r - p := r_sub_p_nonneg p0 hq r0 hpqr
  have rq0 : 0 ≤ r - q := r_sub_p_nonneg q0 hp r0 (add_comm p⁻¹ q⁻¹ ▸ hpqr)
  let F : Fin 3 → G → ℝ≥0∞ := ![fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r),
    fun y ↦ ‖f y‖ₑ ^ ((r - p) / r), fun y ↦ ‖g (x - y)‖ₑ ^ ((r - q) / r)]
  let P : Fin 3 → ℝ≥0∞ := ![.ofReal r, (.ofReal (p⁻¹ - r⁻¹))⁻¹, (.ofReal (q⁻¹ - r⁻¹))⁻¹]
  have hP : ∑ i, (P i)⁻¹ = 1 := by
    have hq' := inv_le_one_of_one_le₀ hq
    have hp' := inv_le_one_of_one_le₀ hp
    simp only [P, Fin.sum_univ_three, Matrix.cons_val, inv_inv]
    rw [← ofReal_inv_of_pos r0, ← ofReal_add (inv_pos.mpr r0).le (by linarith),
      ← ofReal_add (by linarith [inv_pos.mpr p0]) (by linarith), ← ofReal_one]
    congr 1
    linarith
  have hgx : eLpNorm (g <| x - ·) (.ofReal q) μ = eLpNorm g (.ofReal q) μ := by
    have := (measurableEmbedding_subLeft x).eLpNorm_map_measure (g := g) (p := .ofReal q) (μ := μ)
    rw [(μ.measurePreserving_sub_left x).map_eq] at this
    exact this.symm
  calc ‖(f ⋆[L, μ] g) x‖ₑ
    _ ≤ ∫⁻ y, ‖L (f y) (g (x - y))‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, .ofReal c * (‖f y‖ₑ * ‖g (x - y)‖ₑ) ∂μ := by
      refine lintegral_mono fun y ↦ ?_
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_mul (by positivity),
        ← ofReal_mul' (by positivity), ← mul_assoc]
      exact ofReal_le_ofReal (hL y (x - y))
    _ = ∫⁻ y, .ofReal c * ∏ i, F i y ∂μ := by
      refine lintegral_congr fun y ↦ ?_
      have split (a : ℝ≥0∞) {e : ℝ} (e0 : 0 < e) (re0 : 0 ≤ r - e) :
          a ^ (e * (1 / r)) * a ^ ((r - e) / r) = a := by
        rw [← rpow_add_of_nonneg _ _ (by positivity) (by positivity), mul_one_div, ← add_div,
          add_sub_cancel, div_self r0.ne', rpow_one]
      simp only [F, Fin.prod_univ_three, Matrix.cons_val]
      rw [mul_rpow_of_nonneg _ _ (by positivity), ← rpow_mul, ← rpow_mul]
      conv_lhs => rw [← split ‖f y‖ₑ p0 rp0, ← split ‖g (x - y)‖ₑ q0 rq0]
      ring
    _ ≤ .ofReal c * ∏ i, eLpNorm (F i) (P i) μ := by
      rw [lintegral_const_mul' _ _ ofReal_ne_top]
      gcongr
      exact lintegral_prod_norm_pow_le' hP
    _ ≤ _ := by
      simp only [F, P, Fin.prod_univ_three, Matrix.cons_val, ← mul_assoc]
      gcongr
      · exact eLpNorm_enorm_rpow_le f p0 rp0
      · rw [← hgx]
        exact eLpNorm_enorm_rpow_le _ q0 rq0

theorem eLpNorm_convolution_le_ofReal
    [μ.IsAddRightInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hconv : AEStronglyMeasurable (f ⋆[L, μ] g) μ := AEStronglyMeasurable.convolution L hf hg
  have hgx (x : G) : AEStronglyMeasurable (g <| x - ·) μ :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  have hF (x : G) : AEStronglyMeasurable (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ r⁻¹) μ :=
    ((hf.enorm.pow_const p).mul ((hgx x).enorm.pow_const q)).pow_const _ |>.aestronglyMeasurable
  have hg' : AEMeasurable (fun (x : G × G) ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q) (μ.prod μ) :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const q
  have hf' := hf.enorm.pow_const p
  have hfg := hf'.comp_snd.mul hg'
  replace hg' := hg'.pow_const q
  rw [← ENNReal.rpow_le_rpow_iff r0]
  repeat rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
  calc eLpNorm (f ⋆[L, μ] g) (ENNReal.ofReal r) μ ^ r
    _ = ∫⁻ (x : G), ‖(f ⋆[L, μ] g) x‖ₑ ^ r ∂μ := by
      simp [eLpNorm, eLpNorm', hconv, r0, r0.le, r0.ne.symm]
    _ ≤ _ :=
      lintegral_mono <| fun x ↦ ENNReal.rpow_le_rpow (h₂ := r0.le) <|
        enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm hp hq hr hpqr c hL x
    _ = (ENNReal.ofReal c) ^ r *
        (∫⁻ x, (eLpNorm (fun y ↦ (‖f y‖ₑ^p * ‖g (x-y)‖ₑ^q) ^ (1/r)) (ENNReal.ofReal r) μ) ^ r ∂μ) *
        (eLpNorm f (ENNReal.ofReal p) μ ^ (r - p) * eLpNorm g (ENNReal.ofReal q) μ ^ (r - q)) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
      rw [lintegral_mul_const'', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, lintegral_const_mul']
      · field_simp
      · exact ENNReal.rpow_ne_top_of_nonneg r0.le ofReal_ne_top
      · apply AEMeasurable.const_mul
        simpa [eLpNorm, eLpNorm', hF, r0.not_ge, r0.ne.symm, r0.le] using hfg.lintegral_prod_right'
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
          simp [eLpNorm, eLpNorm', hF, r0.not_ge, ENNReal.toReal_ofReal r0.le]
        _ = ∫⁻ x, (∫⁻ y, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ := by
          simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ r0.ne.symm, ENNReal.rpow_one]
        _ = ∫⁻ y, (∫⁻ x, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ :=
          lintegral_lintegral_swap hfg
        _ = (∫⁻ y, ‖f y‖ₑ ^ p ∂μ) * (∫⁻ x, ‖g x‖ₑ ^ q ∂μ) := by
          have {y : G} : ‖f y‖ₑ ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg p0.le enorm_ne_top
          simp_rw [lintegral_const_mul' _ _ this, ← lintegral_mul_const'' _ hf',
            lintegral_sub_right_eq_self (‖g ·‖ₑ ^ q) _]
        _ = eLpNorm f (ENNReal.ofReal p) μ ^ p * eLpNorm g (ENNReal.ofReal q) μ ^ q := by
          simp [eLpNorm, eLpNorm', hf, hg, ← ENNReal.rpow_mul, p0.not_ge, q0.not_ge, p0.le, q0.le,
            p0.ne.symm, q0.ne.symm]

variable (L)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  -- First use `eLpNorm_top_convolution_le` to handle the cases where any exponent is `∞`
  by_cases r_top : r = ∞
  · rw [r_top, ENNReal.inv_top, zero_add] at hpqr
    have hpq : p.HolderConjugate q := holderConjugate_iff.mpr hpqr
    rw [r_top]
    refine eLpNorm_top_convolution_le hpq hf hg c hL
  have hpq : 1 < p⁻¹ + q⁻¹ := by
    rw [hpqr]
    nth_rewrite 1 [← zero_add 1]
    apply ENNReal.add_lt_add_right ENNReal.one_ne_top
    exact zero_le.lt_or_eq.resolve_right (ENNReal.inv_ne_zero.mpr r_top).symm
  have p_ne_top : p ≠ ∞ := by contrapose! hq; simpa [hq] using hpq
  have q_ne_top : q ≠ ∞ := by contrapose! hp; simpa [hp] using hpq
  -- When all exponents are finite, apply `eLpNorm_convolution_le_ofReal`
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr p_ne_top, ← ENNReal.ofReal_toReal_eq_iff.mpr q_ne_top,
    ← ENNReal.ofReal_toReal_eq_iff.mpr r_top]
  refine eLpNorm_convolution_le_ofReal ?_ ?_ ?_ ?_ hf hg c hL; rotate_right
  · simp_rw [← ENNReal.toReal_one, ← ENNReal.toReal_inv]
    rw [← ENNReal.toReal_add _ ENNReal.one_ne_top, ← ENNReal.toReal_add, hpqr]
    all_goals exact ENNReal.inv_ne_top.mpr (fun h ↦ (h ▸ one_pos).not_ge (by assumption))
  all_goals rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top (by assumption)]

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
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
      exact eLpNorm_convolution_le_of_norm_le_mul L hp hq hr hpqr (hf.liftIoc T a) (hg.liftIoc T a)
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
      simp only [liftIoc, Function.comp_apply, domRestrict_apply, f'', f']
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
    congr 2
    exact (AddCircle.liftIoc_coe_apply hy).symm
  · apply eLpNorm_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    exact (AddCircle.liftIoc_coe_apply hy).symm

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
