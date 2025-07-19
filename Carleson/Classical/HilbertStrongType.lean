import Carleson.Classical.DirichletKernel
import Carleson.Classical.HilbertKernel
import Carleson.Classical.SpectralProjectionBound
import Carleson.Defs
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities
import Carleson.TwoSidedCarleson.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Data.Real.Pi.Bounds

/- This file contains the proof that the Hilbert kernel is a bounded operator. -/

noncomputable section

open scoped Real ENNReal
open Complex ComplexConjugate MeasureTheory Bornology Set Filter Function

section

/-- The volume measure on the real line is doubling. -/
@[reducible]
def doublingMeasure_real_two : DoublingMeasure ℝ 2 :=
  InnerProductSpace.DoublingMeasure.mono (by simp)

instance doublingMeasure_real_16 : DoublingMeasure ℝ (2 ^ 4 : ℕ) :=
  doublingMeasure_real_two.mono (by norm_num)
end

lemma czOperator_comp_add {g : ℝ → ℂ} {k : ℝ → ℂ} {r a : ℝ} :
    (czOperator (fun x y ↦ k (x - y)) r g) ∘ (fun x ↦ x + a) =
    czOperator (fun x y ↦ k (x - y)) r (g ∘ (fun x ↦ x + a)) := by
  ext x
  simp only [Nat.reducePow, comp_apply, czOperator, Nat.cast_ofNat,
    ← integral_indicator measurableSet_ball.compl, indicator_mul_right]
  conv_lhs =>  rw [← integral_add_right_eq_self _ a]
  congr with y
  simp [add_sub_add_right_eq_sub, indicator]

/-- The modulation operator `M_n g`, defined in (11.3.1) -/
def modulationOperator (n : ℤ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x * exp (I * n * x)

lemma Measurable.modulationOperator (n : ℤ) {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (modulationOperator n g) :=
  hg.mul (measurable_const.mul measurable_ofReal).cexp

lemma AEMeasurable.modulationOperator (n : ℤ) {g : ℝ → ℂ} (hg : AEMeasurable g) :
    AEMeasurable (modulationOperator n g) :=
  hg.mul (measurable_const.mul measurable_ofReal).cexp.aemeasurable

/-- The approximate Hilbert transform `L_N g`, defined in (11.3.2).
defined slightly differently. -/
def approxHilbertTransform (n : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n),
    modulationOperator (k) (partialFourierSum k (modulationOperator (-k) g)) x

/-- The kernel `k_r(x)` defined in (11.3.11).
When used, we may assume that `r ∈ Ioo 0 1`.
Todo: find better name? -/
def niceKernel (r : ℝ) (x : ℝ) : ℝ :=
  if exp (I * x) = 1 then r⁻¹ else
    min r⁻¹ (1 + r / normSq (1 - exp (.I * x)))

lemma niceKernel_pos {r x : ℝ} (hr : 0 < r) : 0 < niceKernel r x := by
  unfold niceKernel
  split
  · positivity
  · apply lt_min (by positivity)
    apply lt_add_of_lt_of_nonneg zero_lt_one
    apply div_nonneg (by positivity) (normSq_nonneg _)

lemma niceKernel_le_inv {r x : ℝ} : niceKernel r x ≤ r⁻¹ := by
  unfold niceKernel
  split
  · exact le_rfl
  · apply (min_le_left _ _).trans le_rfl

lemma one_le_niceKernel {r x : ℝ} (hr : 0 < r) (h'r : r < 1) : 1 ≤ niceKernel r x := by
  have A : 1 ≤ r⁻¹ := le_inv_of_le_inv₀ hr (by simpa using h'r.le)
  unfold niceKernel
  split
  · exact A
  · apply le_min A
    simp only [le_add_iff_nonneg_right]
    apply div_nonneg (by positivity) (normSq_nonneg _)

lemma niceKernel_neg {r x : ℝ} : niceKernel r (-x) = niceKernel r x := by
  simp only [niceKernel, ofReal_neg, mul_neg, exp_neg, inv_eq_one]
  congr 4
  rw [← normSq_conj, inv_eq_conj (norm_exp_I_mul_ofReal x), map_sub, map_one, conj_conj]

lemma niceKernel_periodic (r : ℝ) : Function.Periodic (niceKernel r) (2 * π) := by
  simp [niceKernel, mul_add, mul_comm I (2 * π), exp_add]

@[fun_prop] lemma measurable_niceKernel {r : ℝ} : Measurable (niceKernel r) := by
  classical
  refine Measurable.piecewise ?_ (by fun_prop) (by fun_prop)
  exact isClosed_eq (by fun_prop) continuous_const |>.measurableSet

lemma niceKernel_intervalIntegrable {r : ℝ} (a b : ℝ) (hr : r > 0) :
    IntervalIntegrable (niceKernel r) volume a b := by
  apply intervalIntegrable_const (c := r⁻¹) |>.mono_fun
  · fun_prop
  · refine Filter.Eventually.of_forall <| fun y ↦ ?_
    simp_rw [Real.norm_eq_abs, abs_of_pos (niceKernel_pos hr), abs_inv, abs_of_pos hr, niceKernel]
    split <;> simp

lemma niceKernel_eq_inv {r x : ℝ} (hr : 0 < r ∧ r < π) (hx : 0 ≤ x ∧ x ≤ r) :
    niceKernel r x = r⁻¹ := by
  rw [niceKernel, ite_eq_iff', normSq_eq_norm_sq]
  refine ⟨fun _ ↦ rfl, fun hexp ↦ min_eq_left ?_⟩
  have : 0 < x := by
    contrapose! hexp
    simp [ge_antisymm hx.1 hexp]
  apply le_add_of_nonneg_of_le zero_le_one
  suffices 1 - r ^ 2 / 2 ≤ Real.cos x by
    have : Real.cos x < 1 := by
      rw [← Real.cos_zero]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi <;> linarith
    rw [norm_sub_rev, norm_exp_I_mul_ofReal_sub_one, norm_mul, RCLike.norm_ofNat, Real.norm_eq_abs,
      Real.abs_sin_half, mul_pow, Real.sq_sqrt, le_div_iff₀', mul_inv_le_iff₀] <;> linarith
  grw [Real.one_sub_sq_div_two_le_cos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith

lemma niceKernel_eq_inv' {r x : ℝ} (hr : 0 < r ∧ r < π) (hx : |x| ≤ r) :
    niceKernel r x = r⁻¹ := by
  rcases le_total 0 x with h'x | h'x
  · exact niceKernel_eq_inv hr ⟨h'x, (Real.le_norm_self x).trans hx⟩
  · rw [← niceKernel_neg, niceKernel_eq_inv hr]
    simp only [abs_of_nonpos h'x] at hx
    simp [Left.nonneg_neg_iff, h'x, hx]

lemma niceKernel_upperBound_aux {r x : ℝ} (hr : 0 < r) (hx : r ≤ x ∧ x ≤ π) :
    1 + r / ‖1 - exp (I * x)‖ ^ 2 ≤ 1 + 4 * r / x ^ 2 := calc
  _ ≤ 1 + r / (x / 2) ^ 2 := by
    gcongr 1 + ?_
    have : 0 < x := by linarith
    grw [lower_secant_bound ⟨?_, ?_⟩ (le_abs_self x)] <;> linarith
  _  = 1 + 4 * r / x ^ 2 := by ring

lemma niceKernel_upperBound {r x : ℝ} (hr : 0 < r) (hx : r ≤ x ∧ x ≤ π) :
    niceKernel r x ≤ 1 + 4 * r / x ^ 2 := by
  have : exp (I * x) ≠ 1 := by
    simp only [ne_eq, exp_I_mul_eq_one_iff_of_lt_of_lt x (by linarith) (by linarith)]; linarith
  simp only [niceKernel, this, ↓reduceIte, inf_le_iff]
  right
  simp only [normSq_eq_norm_sq]
  apply niceKernel_upperBound_aux hr hx

lemma niceKernel_lowerBound {r x : ℝ} (hr : 0 < r) (h'r : r < 1) (hx : r ≤ x ∧ x ≤ π) :
    1 + r / ‖1 - exp (I * x)‖ ^ 2 ≤ 5 * niceKernel r x := by
  have : exp (I * x) ≠ 1 := by
    simp only [ne_eq, exp_I_mul_eq_one_iff_of_lt_of_lt x (by linarith) (by linarith)]; linarith
  simp only [niceKernel, this, ↓reduceIte, ge_iff_le]
  rw [mul_min_of_nonneg _ _ (by norm_num)]
  simp only [normSq_eq_norm_sq, le_inf_iff]
  refine ⟨?_, le_mul_of_one_le_left (by positivity) (by norm_num)⟩
  apply (niceKernel_upperBound_aux hr hx).trans
  calc 1 + 4 * r / x ^ 2
  _ ≤ r ⁻¹ + 4 * r / (r ^ 2) := by
    gcongr
    · apply le_inv_of_le_inv₀ hr (by simpa using h'r.le)
    · exact hx.1
  _ = 5 * r ⁻¹ := by
    field_simp
    ring

lemma niceKernel_lowerBound' {r x : ℝ} (hr : 0 < r) (h'r : r < 1) (hx : r ≤ |x| ∧ |x| ≤ π) :
    1 + r / ‖1 - exp (I * x)‖ ^ 2 ≤ 5 * niceKernel r x := by
  rcases le_total 0 x with h'x | h'x
  · simp only [abs_of_nonneg h'x] at hx
    exact niceKernel_lowerBound hr h'r hx
  · rw [← niceKernel_neg]
    simp only [abs_of_nonpos h'x] at hx
    apply le_trans (le_of_eq ?_) (niceKernel_lowerBound hr h'r hx)
    simp [norm_one_sub_exp_neg_I_mul_ofReal]

/-- Lemma 11.1.8 -/
lemma mean_zero_oscillation {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0)..2 * π, exp (I * n * x) = 0 := by
  rw [integral_exp_mul_complex (by simp [hn])]
  simp [sub_eq_zero, exp_eq_one_iff, hn, ← mul_assoc, mul_comm I,
    mul_right_comm _ I]

theorem AddCircle.haarAddCircle_eq_smul_volume {T : ℝ} [hT : Fact (0 < T)] :
    (@haarAddCircle T _) = (ENNReal.ofReal T)⁻¹ • (volume : Measure (AddCircle T)) := by
  rw [volume_eq_smul_haarAddCircle, ← smul_assoc, smul_eq_mul,
    ENNReal.inv_mul_cancel (by simp [hT.out]) ENNReal.ofReal_ne_top, one_smul]

open AddCircle in
/-- Lemma 11.1.10.
-/
-- todo: add lemma that relates `eLpNorm ((Ioc a b).indicator f)` to `∫ x in a..b, _`
lemma spectral_projection_bound {f : ℝ → ℂ} {n : ℕ} (hmf : AEMeasurable f) :
    eLpNorm ((Ioc 0 (2 * π)).indicator (partialFourierSum n f)) 2 ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 := by
  -- Proof by massaging the statement of `spectral_projection_bound_lp` into this.
  by_cases hf_L2 : eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 = ⊤
  · rw [hf_L2]
    exact OrderTop.le_top _
  push_neg at hf_L2
  rw [← lt_top_iff_ne_top] at hf_L2
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  have lift_MemLp : MemLp (liftIoc (2 * π) 0 f) 2 haarAddCircle := by
    unfold MemLp
    constructor
    · rw [haarAddCircle_eq_smul_volume]
      apply AEStronglyMeasurable.smul_measure
      exact hmf.aestronglyMeasurable.liftIoc (2 * π) 0
    · rw [haarAddCircle_eq_smul_volume, eLpNorm_smul_measure_of_ne_top (by trivial),
        eLpNorm_liftIoc _ _ hmf.aestronglyMeasurable, smul_eq_mul, zero_add]
      apply ENNReal.mul_lt_top _ hf_L2
      rw [← ENNReal.ofReal_inv_of_pos this.out]
      apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  let F : Lp ℂ 2 haarAddCircle :=
    MemLp.toLp (AddCircle.liftIoc (2 * π) 0 f) lift_MemLp

  have lp_version := spectral_projection_bound_lp (N := n) F
  rw [Lp.norm_def, Lp.norm_def,
    ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top (partialFourierSumLp 2 n F)) (Lp.eLpNorm_ne_top F)]
    at lp_version

  rw [← zero_add (2 * π), ← eLpNorm_liftIoc _ _ hmf.aestronglyMeasurable,
    ← eLpNorm_liftIoc _ _ partialFourierSum_uniformContinuous.continuous.aestronglyMeasurable,
    volume_eq_smul_haarAddCircle,
    eLpNorm_smul_measure_of_ne_top (by trivial), eLpNorm_smul_measure_of_ne_top (by trivial),
    smul_eq_mul, smul_eq_mul, ENNReal.mul_le_mul_left (by simp [Real.pi_pos]) (by simp)]
  have ae_eq_right : F =ᶠ[ae haarAddCircle] liftIoc (2 * π) 0 f := MemLp.coeFn_toLp _
  have ae_eq_left : partialFourierSumLp 2 n F =ᶠ[ae haarAddCircle]
      liftIoc (2 * π) 0 (partialFourierSum n f) :=
    Filter.EventuallyEq.symm (partialFourierSum_aeeq_partialFourierSumLp 2 n f lift_MemLp)
  rw [← eLpNorm_congr_ae ae_eq_right, ← eLpNorm_congr_ae ae_eq_left]
  exact lp_version

private lemma norm_modulationOperator (g : ℝ → ℂ) (n : ℤ) (x : ℝ) :
    ‖modulationOperator n g x‖ = ‖g x‖ := by
  rw [modulationOperator, norm_mul, mul_assoc, mul_comm I, ← ofReal_intCast, ← ofReal_mul,
    norm_exp_ofReal_mul_I, mul_one]

private lemma indicator_modulationOperator (g : ℝ → ℂ) (n : ℤ) (s : Set ℝ) :
    s.indicator (modulationOperator n g) = modulationOperator n (s.indicator g) := by
  ext x; simp [modulationOperator, indicator]

private lemma eLpNorm_modulationOperator (g : ℝ → ℂ) (n : ℤ) (p : ℝ≥0∞) :
    eLpNorm (modulationOperator n g) p = eLpNorm g p :=
  eLpNorm_congr_norm_ae (Filter.Eventually.of_forall <| (norm_modulationOperator _ n ·))

private lemma eLpNorm_indicator_modulationOperator (g : ℝ → ℂ) (n : ℤ) (p : ℝ≥0∞) (s : Set ℝ) :
    eLpNorm (s.indicator (modulationOperator n g)) p = eLpNorm (s.indicator g) p :=
  indicator_modulationOperator g n s ▸ eLpNorm_modulationOperator (s.indicator g) n p

/-- Lemma 11.3.1.
-/
lemma modulated_averaged_projection {g : ℝ → ℂ} {n : ℕ} (hmg : AEMeasurable g) :
    eLpNorm ((Ioc 0 (2 * π)).indicator (approxHilbertTransform n g)) 2 ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator g) 2 := by
  unfold approxHilbertTransform
  by_cases hn : n = 0
  · simp [hn]
  rw [funext (indicator_const_mul _ _ _)]
  change eLpNorm ((n : ℂ)⁻¹ • _) _ _ ≤ _
  rw [eLpNorm_const_smul _ _ _ _, ← Finset.sum_fn, Finset.indicator_sum,
    enorm_inv (Nat.cast_ne_zero.mpr hn), ← one_mul (eLpNorm (indicator _ _) _ _),
    ← ENNReal.inv_mul_cancel (by simp [hn]) (enorm_ne_top (x := (n : ℂ))), mul_assoc]
  refine mul_le_mul_left' (le_trans (eLpNorm_sum_le ?_ one_le_two) ?_) _
  · refine fun i _ ↦ Measurable.indicator ?_ measurableSet_Ioc |>.aestronglyMeasurable
    exact partialFourierSum_uniformContinuous.continuous.measurable.modulationOperator _
  trans ∑ i ∈ Finset.Ico n (2 * n), eLpNorm ((Ioc 0 (2 * π)).indicator g) 2 volume; swap
  · simp [← ofReal_norm_eq_enorm, Nat.sub_eq_of_eq_add (two_mul n)]
  refine Finset.sum_le_sum (fun i _ ↦ ?_)
  rw [eLpNorm_indicator_modulationOperator, ← eLpNorm_indicator_modulationOperator g (-i)]
  exact spectral_projection_bound (hmg.modulationOperator (-i))

lemma modulated_averaged_projection' {g : ℝ → ℂ} {n : ℕ} (hmg : AEMeasurable g) :
    eLpNorm (approxHilbertTransform n g) 2 (volume.restrict (Ioc 0 (2 * π))) ≤
    eLpNorm g 2 (volume.restrict (Ioc 0 (2 * π))) := by
  convert modulated_averaged_projection (n := n) hmg using 1 <;>
  exact (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc).symm

/- Lemma 11.3.2 `periodic-domain-shift` is in Mathlib. -/

/-- Lemma 11.3.3.
-/
lemma young_convolution {f g : ℝ → ℝ} (hmf : AEMeasurable f)
    (hmg : AEMeasurable g) (periodic_g : g.Periodic (2 * π)) :
    eLpNorm (fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 (volume.restrict (Ioc 0 (2 * π))) ≤
      eLpNorm f 2 (volume.restrict (Ioc 0 (2 * π)))
      * eLpNorm g 1 (volume.restrict (Ioc 0 (2 * π))) := by
  have : Fact (0 < 2 * π) := ⟨mul_pos two_pos Real.pi_pos⟩
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by exact one_le_two
  simpa [zero_add] using ENNReal.eLpNorm_Ioc_convolution_le_of_norm_le_mul
    (ContinuousLinearMap.mul ℝ ℝ) 0 h2 (le_refl 1) h2 (by rw [inv_one])
    periodic_g hmf.aestronglyMeasurable hmg.aestronglyMeasurable 1 (by simp)

/-- Lemma 11.3.4.
-/
lemma integrable_bump_convolution {f g : ℝ → ℝ}
    (hf : MemLp f ∞ volume) (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π))
    {r : ℝ} (hr : r ∈ Ioo 0 π) (hle : ∀ x, |g x| ≤ niceKernel r x) :
    eLpNorm (fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 (volume.restrict (Ioc 0 (2 * π))) ≤
    17 * eLpNorm f 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨hr0, hrπ⟩ := hr
  have h_integrable {a b} := niceKernel_intervalIntegrable a b hr0
  have hg_integrable : Integrable g (volume.restrict (Ioc 0 (2 * π))) := by
    apply IntegrableOn.integrable
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    apply h_integrable.mono_fun hg.1.restrict (Filter.Eventually.of_forall ?_)
    simpa [abs_of_pos (niceKernel_pos hr0)] using hle
  have hbound_integrable : IntervalIntegrable (fun x ↦ 4 * r / x ^ 2) volume r π := by
    apply ContinuousOn.intervalIntegrable_of_Icc hrπ.le
    have (x) (hx : x ∈ Icc r π) : x ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [mem_Icc.mp hx])
    fun_prop (disch := assumption)

  grw [young_convolution hf.1.aemeasurable hg.1.aemeasurable periodic_g, mul_comm]
  gcongr
  have: eLpNorm g 1 (volume.restrict (Ioc 0 (2 * π))) ≠ ⊤ := by
    grw [← lt_top_iff_ne_top,
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (OrderTop.le_top 1) (hg.restrict _).1]
    exact ENNReal.mul_lt_top (hg.restrict _).eLpNorm_lt_top (by norm_num)
  rw [← ENNReal.toReal_le_toReal this (by norm_num)]

  calc
    _ ≤ ∫ x in (0)..2 * π, niceKernel r x := by
      simp_rw [eLpNorm_one_eq_lintegral_enorm]
      rw [← ofReal_integral_norm_eq_lintegral_enorm hg_integrable,
        ENNReal.toReal_ofReal (by positivity), intervalIntegral.integral_of_le (by positivity)]
      apply setIntegral_mono_on hg_integrable.norm ?_ measurableSet_Ioc (fun x _ ↦ hle x)
      exact intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith) |>.mp h_integrable
    _ = 2 * ∫ x in (0)..π, niceKernel r x := by
      have := (zero_add (2 * π)) ▸ (niceKernel_periodic r).intervalIntegral_add_eq 0 (-π)
      rw [this, show -π + 2 * π = π by group, ← intervalIntegral.integral_add_adjacent_intervals
        (b := 0) h_integrable h_integrable, two_mul]
      have := intervalIntegral.integral_comp_neg (a := -π) (b := 0) (niceKernel r)
      simpa [neg_zero, neg_neg, niceKernel_neg]
    _ = 2 * (∫ x in (0)..r, niceKernel r x) + 2 * ∫ x in r..π, niceKernel r x := by
      rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals h_integrable h_integrable]
    _ ≤ 2 * (∫ _ in (0)..r, r⁻¹) + 2 * ∫ x in r..π, 1 + (4 * r) / x ^ 2 := by
      gcongr
      · refine le_of_eq <| intervalIntegral.integral_congr (g := fun _ ↦ r⁻¹) fun x hx ↦ ?_
        rw [uIcc_of_le (by positivity)] at hx
        exact niceKernel_eq_inv ⟨hr0, hrπ⟩ hx
      · apply intervalIntegral.integral_mono_on hrπ.le h_integrable
        · exact intervalIntegrable_const.add hbound_integrable
        · exact fun x hx ↦ niceKernel_upperBound hr0 hx
    _ ≤ 2 + (2 * π + 8 * r * (r⁻¹ - π⁻¹)) := by
      gcongr
      · simp [mul_inv_le_one]
      have (x : ℝ) : 4 * r / x ^ 2 = (4 * r) * (x ^ (-2 : ℤ)) := rfl
      simp_rw [intervalIntegral.integral_add intervalIntegrable_const hbound_integrable,
        intervalIntegral.integral_const, this, intervalIntegral.integral_const_mul, ge_iff_le,
        smul_eq_mul, mul_one, mul_add, ← mul_assoc, show 2 * 4 * r = 8 * r by group]
      gcongr
      · linarith
      rw [integral_zpow]
      · apply le_of_eq; group
      · exact .inr ⟨by trivial, by simp [mem_uIcc, hr0, Real.pi_pos]⟩
    _ ≤ (17 : ℝ≥0∞).toReal := by
      rw [mul_sub, mul_inv_cancel_right₀ hr0.ne.symm]
      grw [sub_le_self 8 (by positivity), Real.pi_lt_d2]
      norm_num

/-- The function `L'`, defined in the Proof of Lemma 11.3.5. -/
def dirichletApprox (n : ℕ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n), dirichletKernel k x * exp (I * k * x)

/-- Lemma 11.3.5, part 1. -/
@[fun_prop] lemma continuous_dirichletApprox {n : ℕ} : Continuous (dirichletApprox n) := by
  change Continuous (fun x ↦ dirichletApprox n x)
  simp only [dirichletApprox]
  fun_prop

lemma norm_dirichletApprox_le {n : ℕ} {x : ℝ} :
    ‖dirichletApprox n x‖ ≤ 4 * n := calc
  ‖dirichletApprox n x‖
  _ ≤ ‖(n : ℂ)⁻¹‖ * ∑ k ∈ .Ico n (2 * n),
      ‖dirichletKernel k x * exp (I * k * x)‖ := by
    simp only [dirichletApprox, norm_mul ((n : ℂ)⁻¹)]
    gcongr
    apply norm_sum_le
  _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ .Ico n (2 * n), ‖dirichletKernel k x‖ := by
    simp only [norm_inv, norm_natCast, Complex.norm_mul]
    gcongr with i hi
    rw [mul_assoc, show (i : ℂ) * x = (i * x : ℝ) by simp, norm_exp_I_mul_ofReal]
    simp
  _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ .Ico n (2 * n), (4 * n : ℝ) := by
    gcongr with i hi
    apply norm_dirichletKernel_le.trans
    have : (i : ℕ) < 2 * n := by
      simp only [Finset.mem_Ico] at hi
      exact hi.2
    have : 2 * i + 1 ≤ 4 * n := by omega
    exact_mod_cast this
  _ ≤ _ := by
    simp only [Finset.sum_const, Nat.card_Ico, show 2 * n - n = n by omega, nsmul_eq_mul,
      ← mul_assoc]
    rcases eq_zero_or_pos n with rfl | hn
    · simp
    · rw [inv_mul_cancel₀]
      · simp
      · exact_mod_cast hn.ne'

/-- Lemma 11.3.5, part 2. -/
lemma periodic_dirichletApprox (n : ℕ) : (dirichletApprox n).Periodic (2 * π) := by
  intro x
  simp only [dirichletApprox, ofReal_add, ofReal_mul, ofReal_ofNat, mul_eq_mul_left_iff,
    inv_eq_zero, Nat.cast_eq_zero]
  left
  congr with i
  congr 1
  · apply dirichletKernel_periodic
  · simp only [mul_add, exp_add, ne_eq, exp_ne_zero, not_false_eq_true, mul_eq_left₀]
    convert exp_nat_mul_two_pi_mul_I i using 2
    ring

/-- Lemma 11.3.5, part 3.
-/
lemma approxHilbertTransform_eq_dirichletApprox {f : ℝ → ℂ} (hf : MemLp f ∞ volume)
    {n : ℕ} {x : ℝ} :
    approxHilbertTransform n f x =
      (2 * π)⁻¹ * ∫ y in (0)..2 * π, f y * dirichletApprox n (x - y) := by
  simp only [approxHilbertTransform, Finset.mul_sum, mul_inv_rev, ofReal_mul, ofReal_inv,
    ofReal_ofNat, dirichletApprox, ofReal_sub]
  rw [intervalIntegral.integral_finset_sum]; swap
  · intro i hi
    apply IntervalIntegrable.mul_continuousOn ?_ (by fun_prop)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp [Real.pi_nonneg])]
    exact (hf.restrict _).integrable le_top
  simp only [Finset.mul_sum]
  congr with i
  simp only [modulationOperator, Int.cast_natCast]
  rw [partialFourierSum_eq_conv_dirichletKernel]; swap
  · apply IntervalIntegrable.mul_continuousOn ?_ (by fun_prop)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp [Real.pi_nonneg])]
    exact (hf.restrict _).integrable le_top
  simp only [one_div, mul_inv_rev, ← intervalIntegral.integral_const_mul, ←
    intervalIntegral.integral_mul_const]
  congr with y
  simp only [modulationOperator, Int.cast_neg, Int.cast_natCast, mul_neg, neg_mul, mul_sub, exp_sub,
    div_eq_inv_mul, ← exp_neg]
  ring

/-- The convolution with `dirichletApprox` is controlled on `(0, 2π]` in `L^2` norm. This
follows from the fact that it coincides (up to a constant) with `approxHilbertTransform`,
which is essentially an average of Fourier projections (which are all contractions in `L^2`). -/
lemma eLpNorm_convolution_dirichletApprox {g : ℝ → ℂ} {n : ℕ} (hg : MemLp g ∞ volume) :
    eLpNorm (fun x ↦ ∫ y in (0)..2 * π, g y * dirichletApprox n (x - y))
      2 (volume.restrict (Ioc 0 (2 * π))) ≤
    7 * eLpNorm g 2 (volume.restrict (Ioc 0 (2 * π))) := by
  have : (fun x ↦ ∫ y in (0)..2 * π, g y * dirichletApprox n (x - y)) =
      (2 * π) • fun x ↦ approxHilbertTransform n g x := by
    ext x
    simp only [Pi.smul_apply, real_smul, ofReal_mul, ofReal_ofNat, ofReal_inv,
      approxHilbertTransform_eq_dirichletApprox hg, ← mul_assoc, Pi.smul_apply]
    rw [mul_inv_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
  rw [this, eLpNorm_const_smul]
  gcongr
  · have A : ‖2 * π‖ₑ = ENNReal.ofReal (2 * π) := by
      refine Real.enorm_of_nonneg ?_
      simp [Real.pi_nonneg]
    rw [A]
    apply ENNReal.ofReal_le_of_le_toReal
    simp only [ENNReal.toReal_ofNat]
    linarith [Real.pi_lt_d2]
  · apply modulated_averaged_projection' hg.aestronglyMeasurable.aemeasurable

/- To proceed, we will rewrite `dirichletApprox` as the sum of two terms: one is the kernel
of the Hilbert transform, and the other one will be uniformly bounded in `L^1` (and therefore
its action on `L^2` will be uniformly bounded). It will follow that the Hilberr transform
is bounded on `L^2 ((0, 2π]))`, from which the boundedness on the whole real line will follow.

The second term in the decomposition of `dirichletApprox` is built in terms of an auxiliary
kernel `dirichletApproxAux`.
-/

/-- The function `L''`, defined in the Proof of Lemma 11.3.5. -/
def dirichletApproxAux (n : ℕ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * exp (I * 2 * n * x) / (1 - exp (-I * x)) * ∑ k ∈ .Ico 0 n, exp (I * 2 * k * x)

lemma dirichletApprox_eq_add_dirichletApproxAux
    {n : ℕ} {x : ℝ} (hx : exp (I * x) ≠ 1) (hn : n ≠ 0) :
    dirichletApprox n x = (1 - exp (I * x)) ⁻¹ + dirichletApproxAux n x := by
  have : Finset.Ico n (2 * n) = Finset.Ico (0 + n) (n + n) := by simp [Nat.two_mul n]
  simp only [dirichletApprox, this, ← Finset.sum_Ico_add]
  simp_rw [dirichletKernel_eq hx]
  simp only [Nat.Ico_zero_eq_range, dirichletKernel', Nat.cast_add, mul_assoc, add_mul, neg_mul,
    div_eq_inv_mul, ← exp_add, neg_add_cancel, exp_zero, mul_one, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [mul_add, ← mul_assoc]
  rw [inv_mul_cancel₀ (mod_cast hn)]
  simp only [mul_assoc, Finset.mul_sum, one_mul, dirichletApproxAux, neg_mul, div_eq_inv_mul,
    Nat.Ico_zero_eq_range, ← exp_add, add_comm (1 - exp (I * ↑x))⁻¹, add_left_inj]
  congr with i
  ring_nf

lemma norm_dirichletApproxAux_le_of_re_nonneg {n : ℕ} {x r : ℝ} (hx : exp (I * x) ≠ 1)
    (h'x : 0 ≤ re (exp (I * x))) (hn : r⁻¹ ≤ n) (hr : 0 < r) :
    ‖dirichletApproxAux n x‖ ≤ 2 * (1 + r / ‖1 - exp (I * x)‖ ^ 2) := by
  have A (k : ℕ) : exp (I * 2 * k * x) = (exp (I * (2 * x : ℝ))) ^ k := by
    rw [← exp_nat_mul]
    simp [mul_assoc]
    ring_nf
  have B : ‖1 - exp (I * x)‖ ≤ ‖exp (I * (2 * x : ℝ)) - 1‖ := by
    have : exp (I * (2 * x : ℝ)) - 1 =
          - ((1 - exp (I * x)) * (exp (I * x) + 1)) := by
      rw [show I * (2 * x : ℝ) = I * x + I * x by simp; ring, exp_add]
      ring
    rw [this, norm_neg, norm_mul]
    apply le_mul_of_one_le_right (norm_nonneg _)
    apply le_trans _ (re_le_norm _)
    simpa using h'x
  have C : exp (I * (2 * x : ℝ)) ≠ 1 := by
    intro h
    simp only [h, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at B
    exact hx B.symm
  calc
  ‖dirichletApproxAux n x‖
  _ = (n : ℝ)⁻¹ * ‖1 - exp (I * x)‖⁻¹ * ‖∑ k ∈ Finset.range n, exp (I * (2 * x : ℝ)) ^ k‖ := by
    simp only [dirichletApproxAux, neg_mul, A, Nat.Ico_zero_eq_range, Complex.norm_mul,
      Complex.norm_div, norm_inv, norm_natCast, norm_pow, norm_exp_I_mul_ofReal,
      norm_one_sub_exp_neg_I_mul_ofReal]
    simp only [one_pow, mul_one, ofReal_mul, ofReal_ofNat, div_eq_mul_inv]
  _ = (n : ℝ)⁻¹ * ‖1 - exp (I * x)‖⁻¹ *
      ‖(exp (I * (2 * x : ℝ)) ^ n - 1) / (exp (I * (2 * x : ℝ)) - 1)‖ := by
    rw [geom_sum_eq C]
  _ ≤ (n : ℝ)⁻¹ * ‖1 - exp (I * x)‖⁻¹ * (2 * ‖(exp (I * (2 * x : ℝ)) - 1)‖⁻¹) := by
    rw [div_eq_mul_inv, norm_mul, norm_inv]
    gcongr
    apply (norm_sub_le _ _).trans_eq
    rw [norm_pow, norm_exp_I_mul_ofReal]
    simpa using by norm_num
  _ ≤ r * ‖1 - exp (I * x)‖⁻¹ * (2 * ‖1 - exp (I * x)‖⁻¹) := by
    gcongr
    · exact inv_le_of_inv_le₀ hr hn
    · simpa [sub_eq_zero] using hx.symm
  _ = 2 * (0 + r / ‖1 - exp (I * x)‖ ^ 2) := by
    rw [pow_two, div_eq_inv_mul, mul_inv]
    ring
  _ ≤ 2 * (1 + r / ‖1 - exp (I * x)‖ ^ 2) := by
    gcongr
    norm_num

lemma norm_dirichletApproxAux_le_of_re_nonpos {n : ℕ} {x r : ℝ}
    (h'x : re (exp (I * x)) ≤ 0) (hr : 0 < r) :
    ‖dirichletApproxAux n x‖ ≤ 2 * (1 + r / ‖1 - exp (I * x)‖ ^ 2) := calc
  ‖dirichletApproxAux n x‖
  _ = (n : ℝ)⁻¹ * ‖1 - exp (I * x)‖⁻¹ * ‖∑ k ∈ Finset.range n, exp (I * (2 * k * x : ℝ))‖ := by
    have A (k : ℕ) : I * 2 * k * x = I * (2 * k * x : ℝ) := by
      simp; ring
    simp only [dirichletApproxAux, neg_mul, Nat.Ico_zero_eq_range, Complex.norm_mul,
      Complex.norm_div, norm_inv, norm_natCast, A, norm_exp_I_mul_ofReal,
      norm_one_sub_exp_neg_I_mul_ofReal]
    simp only [mul_one, ofReal_mul, ofReal_ofNat, div_eq_mul_inv]
  _ ≤ (n : ℝ)⁻¹ * 1⁻¹ * ∑ k ∈ Finset.range n, ‖exp (I * (2 * k * x : ℝ))‖ := by
    gcongr
    · exact le_trans (by simpa using h'x) (re_le_norm _)
    · exact norm_sum_le _ _
  _ ≤ 1 * (1 + 0) := by
    simp only [norm_exp_I_mul_ofReal]
    simpa using inv_mul_le_one
  _ ≤ 2 * (1 + r / ‖1 - exp (I * x)‖ ^ 2) := by
    gcongr
    · norm_num
    · positivity

lemma norm_dirichletApproxAux_le {n : ℕ} {x r : ℝ} (hx : exp (I * x) ≠ 1)
    (hxr : r ≤ |x|) (hxpi : |x| ≤ π)
    (hn : r⁻¹ ≤ n) (hr : 0 < r) (h'r : r < 1) :
    ‖dirichletApproxAux n x‖ ≤ 10 * niceKernel r x := by
  have A : ‖dirichletApproxAux n x‖ ≤ 2 * (1 + r / ‖1 - exp (I * x)‖ ^ 2) := by
    rcases le_total (re (exp (I * x))) 0 with h'x | h'x
    · apply norm_dirichletApproxAux_le_of_re_nonpos h'x hr
    · apply norm_dirichletApproxAux_le_of_re_nonneg hx h'x hn hr
  apply A.trans
  rw [show (10 : ℝ) = 2 * 5 by norm_num, mul_assoc]
  gcongr
  exact niceKernel_lowerBound' hr h'r ⟨hxr, hxpi⟩

lemma norm_sub_indicator_k {x r : ℝ} (hxr : r ≤ |x|) (hxpi : |x| ≤ π) (hr : 0 < r) (h'r : r < 1) :
    ‖(1 - exp (I * x))⁻¹ - {y | |y| ∈ Ico r 1}.indicator k x‖ ≤ 2 * niceKernel r x := by
  rcases lt_or_ge (|x|) 1 with h'x | h'x
  · rw [indicator_of_mem]; swap
    · exact ⟨hxr, h'x⟩
    have : (1 - exp (I * x))⁻¹ - k x = (1 - exp (I * x))⁻¹ * |x| := by
      have : max (1 - |x|) 0 = 1 - |x| := by simpa using h'x.le
      simp [k, this, div_eq_inv_mul]
      ring
    simp only [this, Complex.norm_mul, norm_inv, norm_real, Real.norm_eq_abs, abs_abs, ge_iff_le]
    calc
    ‖1 - exp (I * x)‖⁻¹ * |x|
    _ ≤ (|x| / 2) ⁻¹ * |x| := by
      gcongr
      · linarith
      · apply lower_secant_bound _ le_rfl
        have := abs_le.1 hxpi
        simp only [neg_mul, mem_Icc, neg_add_le_iff_le_add]
        exact ⟨by linarith, by linarith⟩
    _ = 2 * 1 := by
      have := hr.trans_le hxr
      field_simp
    _ ≤ 2 * niceKernel r x := by
      gcongr
      exact one_le_niceKernel hr h'r
  · rw [indicator_of_notMem]; swap
    · simp [h'x]
    simp only [sub_zero, norm_inv]
    calc
    ‖1 - exp (I * x)‖⁻¹
    _ ≤ (|x| / 2) ⁻¹ := by
      gcongr
      apply lower_secant_bound _ le_rfl
      have := abs_le.1 hxpi
      simp only [neg_mul, mem_Icc, neg_add_le_iff_le_add]
      exact ⟨by linarith, by linarith⟩
    _ ≤ (1 / 2) ⁻¹ := by
      gcongr
    _ = 2 * 1 := by norm_num
    _ ≤ 2 * niceKernel r x := by
      gcongr
      exact one_le_niceKernel hr h'r

/-- Lemma 11.3.5, part 4.

The kernel `dirichletApprox` approximates well the kernel of the Hilbert transform, on `[-π, π]`,
up to an error which is uniformly bounded in `L^1` (as it is bounded by a constant multiple
of `niceKernel`).
-/
lemma dist_dirichletApprox_le
    {r : ℝ} (hr : r ∈ Ioo 0 1) {n : ℕ} (hn : n = ⌈r⁻¹⌉₊) {x : ℝ} (hx : x ∈ Icc (-π) π) :
    dist (dirichletApprox n x) ({y : ℝ | |y| ∈ Ico r 1}.indicator k x) ≤ 12 * niceKernel r x := by
  have rpos : 0 < r := hr.1
  have hn1 : n < r⁻¹ + 1 := by
    rw [hn]
    exact Nat.ceil_lt_add_one (by simpa using rpos.le)
  have hn2 : n ≤ 2 * r⁻¹ := by
    have : 1 ≤ r⁻¹ := (one_le_inv₀ hr.1).2 hr.2.le
    apply hn1.le.trans (by linarith)
  rcases lt_or_ge (|x|) r with h'x | h'x
  · rw [indicator_of_notMem]; swap
    · simp [h'x]
    simp only [dist_zero_right]
    apply norm_dirichletApprox_le.trans
    rw [niceKernel_eq_inv' _ h'x.le]; swap
    · simp only [hr.1, true_and]
      linarith [Real.pi_gt_d2, hr.2]
    linarith
  have hexpx : exp (I * x) ≠ 1 := by
    simp only [ne_eq, exp_I_mul_eq_one_iff_of_lt_of_lt x (by linarith [hx.1, Real.pi_pos])
      (by linarith [hx.2, Real.pi_pos])]
    intro h
    simp only [h, abs_zero] at h'x
    linarith
  have hnzero : n ≠ 0 := by
    intro h
    simp only [h, eq_comm, Nat.ceil_eq_zero, inv_nonpos] at hn
    linarith
  rw [dirichletApprox_eq_add_dirichletApproxAux hexpx hnzero, dist_eq_norm, add_sub_right_comm]
  apply (norm_add_le _ _).trans
  have A : ‖(1 - exp (I * x))⁻¹ - {y | |y| ∈ Ico r 1}.indicator k x‖ ≤ 2 * niceKernel r x := by
    apply norm_sub_indicator_k h'x _ rpos hr.2
    simpa only [Real.norm_eq_abs, abs_le] using hx
  have B : ‖dirichletApproxAux n x‖ ≤ 10 * niceKernel r x := by
    apply norm_dirichletApproxAux_le hexpx h'x _ _ hr.1 hr.2
    · simp [abs_le, hx.1, hx.2]
    · rw [hn]
      apply Nat.le_ceil
  linarith

/-- As the kernel of the Hilbert transform is well approximated by `dirichletApprox`, up to an
error controlled by `12 * niceKernel r`, we may bound `czOperator K` in terms of these. As the
approximation only works in the interval `[-π, π]`, this statement is only true for a
point `x` in `[2, 3]` and a function supported in `[1, 4]`, as this means all values of the
approximation that will show up will be in `[-2, 2] ⊆ [-π, π]`. -/
lemma norm_czOperator_le_add
    {g : ℝ → ℂ} {r x : ℝ} (hr : r ∈ Ioo 0 1) {n : ℕ} (hn : n = ⌈r⁻¹⌉₊)
    (hg : MemLp g ∞ volume)
    (hx : 2 ≤ x) (h'x : x ≤ 3)
    (h'g : support g ⊆ Icc 1 4) :
    ‖czOperator K r g x‖ ≤ ‖∫ y in (0)..(2 * π), g y * dirichletApprox n (x - y)‖
      + 12 * ∫ y in Ioc 0 (2 * π), ‖g y‖ * niceKernel r (x - y) := by
  have rpos : 0 < r := hr.1
  have := Real.pi_gt_three
  let U := {y : ℝ | |y| ∈ Ico r 1}.indicator k - dirichletApprox n
  have A : czOperator K r g x =
      ∫ y in Ioc 0 (2 * π), g y * {y : ℝ | |y| ∈ Ico r 1}.indicator k (x - y) := by
    simp only [czOperator, K, mul_comm]
    rw [← integral_indicator measurableSet_ball.compl]
    rw [← integral_indicator measurableSet_Ioc]
    congr with y
    rw [indicator_mul_right, indicator_mul_left]
    congr 1
    · simp only [indicator, mem_Ioc, left_eq_ite_iff]
      intro h
      contrapose! h
      exact ⟨by linarith [(h'g h).1, (h'g h).2], by linarith [(h'g h).1, (h'g h).2]⟩
    · simp only [indicator, mem_compl_iff, Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        abs_sub_comm, not_lt, mem_Ico, mem_setOf_eq]
      by_cases h : r ≤ |x - y|
      · simpa only [↓reduceIte, h, true_and, left_eq_ite_iff, not_lt] using k_of_one_le_abs
      simp [h]
  have B : {y : ℝ | |y| ∈ Ico r 1}.indicator k = dirichletApprox n + U := by simp [U]
  simp only [A, B, Pi.add_apply, mul_add]
  have I0 : IntegrableOn (fun y ↦ ‖g y‖ * niceKernel r (x - y)) (Ioc 0 (2 * π)) := by
    apply (MemLp.restrict _ _).integrable le_top
    apply MemLp.mul (q := ⊤) (p := ⊤) _ hg.norm
    · suffices A : MemLp (niceKernel r) ⊤ volume from
        A.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
      apply memLp_top_of_bound (by fun_prop) (r⁻¹) (Eventually.of_forall (fun y ↦ ?_))
      simp [abs_of_nonneg (niceKernel_pos hr.1).le, niceKernel_le_inv]
  have J (y) : ‖g y * U (x - y)‖ ≤ 12 * (‖g y‖ * niceKernel r (x - y)) := by
    rcases eq_or_ne (g y) 0 with hy | hy
    · simp [hy]
    simp only [norm_mul]
    rw [mul_comm 12, mul_assoc, mul_comm _ 12]
    gcongr
    simp only [U, Pi.sub_apply, ← dist_eq_norm]
    rw [dist_comm]
    apply dist_dirichletApprox_le hr hn _
    exact ⟨by linarith [(h'g hy).1, (h'g hy).2], by linarith [(h'g hy).1, (h'g hy).2]⟩
  have I1 : IntegrableOn (fun y ↦ g y * U (x - y)) (Ioc 0 (2 * π)) := by
    apply (I0.const_mul 12).mono
    · apply (hg.restrict _).aestronglyMeasurable.mul
      apply AEStronglyMeasurable.restrict
      apply AEStronglyMeasurable.comp_measurePreserving ?_
        (Measure.measurePreserving_sub_left volume x)
      apply AEStronglyMeasurable.sub ?_ (by fun_prop)
      exact AEStronglyMeasurable.indicator (by fun_prop) (measurable_norm measurableSet_Ico)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y h'y
      simpa [abs_of_nonneg (niceKernel_pos hr.1).le] using J y
  rw [integral_add _ I1]; rotate_left
  · rw [restrict_Ioc_eq_restrict_Icc]
    exact IntegrableOn.mul_continuousOn ((hg.restrict _).integrable le_top ) (by fun_prop)
      isCompact_Icc
  apply (norm_add_le _ _).trans
  rw [intervalIntegral.integral_of_le (by linarith)]
  gcongr
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  exact setIntegral_mono_on I1.norm (I0.const_mul _) measurableSet_Ioc (fun y hy ↦ J y)

/-- The operator `czOperator K r` is bounded from `L^2 ([1, 4])` to `L^2 ([2, 3])`,
uniformly in `r`. This follows from the fact, proved in `norm_czOperator_le_add`, that it is
bounded by the sum of two operators which are both bounded: one is the convolution
with `dirichletApprox`, bounded as it is an average of Fourier projections, and the other one has
a kernel uniformly bounded in `L^1` and is therefore controlled by Young inequality.

In this version, we assume that the function is supported in `[1, 4]`, but we will drop this
assumption just after this lemma, in `eLpNorm_czOperator_restrict_two_three`.
-/
lemma eLpNorm_czOperator_restrict_two_three_of_support_subset {g : ℝ → ℂ} {r : ℝ}
    (hr : r ∈ Ioo 0 1) (hg : MemLp g ∞ volume) (h'g : support g ⊆ Icc 1 4) :
    eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc 2 3)) ≤
      2 ^ 8 * eLpNorm g 2 (volume.restrict (Ioc 1 4)) := by
  have I : 0 ≤ 2 * π := by linarith [Real.pi_nonneg]
  set n := ⌈r⁻¹⌉₊ with hn
  calc
  eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc 2 3))
  _ ≤ eLpNorm (fun x ↦ ‖∫ y in (0)..(2 * π), g y * dirichletApprox n (x - y)‖
      + 12 * ∫ y in Ioc 0 (2 * π), ‖g y‖ * niceKernel r (x - y)) 2 (volume.restrict (Ioc 2 3)) := by
    apply eLpNorm_mono_ae_real
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    apply norm_czOperator_le_add hr  hn hg hx.1.le hx.2 h'g
  _ ≤ eLpNorm (fun x ↦ ‖∫ y in (0)..(2 * π), g y * dirichletApprox n (x - y)‖
      + 12 * ∫ y in Ioc 0 (2 * π), ‖g y‖ * niceKernel r (x - y)) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
    apply eLpNorm_mono_measure
    apply Measure.restrict_mono _ le_rfl
    apply Ioc_subset_Ioc (by norm_num)
    linarith [Real.pi_gt_three]
  _ ≤ eLpNorm (fun x ↦ ‖∫ y in (0)..(2 * π), g y * dirichletApprox n (x - y)‖) 2
      (volume.restrict (Ioc 0 (2 * π)))
     + eLpNorm (fun x ↦ 12 * ∫ y in Ioc 0 (2 * π), ‖g y‖ * niceKernel r (x - y)) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
    apply eLpNorm_add_le _ _ one_le_two
    · apply AEStronglyMeasurable.norm
      simp_rw [intervalIntegral.integral_of_le I]
      let L := ContinuousLinearMap.mul ℂ ℂ
      let w : ℝ × ℝ → ℂ := fun p ↦ L (g p.2) (dirichletApprox n (p.1 - p.2))
      change AEStronglyMeasurable (fun x ↦ ∫ (y : ℝ) in Ioc 0 (2 * π), w (x, y) ∂volume)
        (volume.restrict (Ioc 0 (2 * π)))
      apply AEStronglyMeasurable.integral_prod_right'
      apply (hg.restrict _).aestronglyMeasurable.convolution_integrand'
      fun_prop
    · apply AEStronglyMeasurable.const_mul
      let L := ContinuousLinearMap.mul ℝ ℝ
      let w : ℝ × ℝ → ℝ := fun p ↦ L (‖g p.2‖) (niceKernel r (p.1 - p.2))
      change AEStronglyMeasurable (fun x ↦ ∫ (y : ℝ) in Ioc 0 (2 * π), w (x, y) ∂volume)
        (volume.restrict (Ioc 0 (2 * π)))
      apply AEStronglyMeasurable.integral_prod_right'
      apply (hg.norm.restrict _).aestronglyMeasurable.convolution_integrand'
      fun_prop
  _ ≤ 7 * eLpNorm g 2 (volume.restrict (Ioc 0 (2 * π))) +
      12 * (17 * eLpNorm g 2 (volume.restrict (Ioc 0 (2 * π)))) := by
    gcongr
    · rw [eLpNorm_norm]
      exact eLpNorm_convolution_dirichletApprox hg
    change eLpNorm ((12 : ℝ) • fun x ↦  ∫ (y : ℝ) in Ioc 0 (2 * π), ‖g y‖ * niceKernel r (x - y)) 2
      (volume.restrict (Ioc 0 (2 * π))) ≤ _
    rw [eLpNorm_const_smul]
    gcongr
    · simp [enorm]
    have W := integrable_bump_convolution (f := fun x ↦ ‖g x‖) (g := fun x ↦ niceKernel r x)
      hg.norm ?_ ?_ ?_ (r := r) ?_
    · simpa [intervalIntegral.integral_of_le I] using W
    · apply memLp_top_of_bound (by fun_prop) (r⁻¹) (Eventually.of_forall (fun y ↦ ?_))
      simp [abs_of_nonneg (niceKernel_pos hr.1).le, niceKernel_le_inv]
    · apply niceKernel_periodic
    · exact ⟨hr.1, hr.2.trans (by linarith [Real.pi_gt_three])⟩
    · simp [abs_of_nonneg (niceKernel_pos hr.1).le]
  _ = 211 * eLpNorm g 2 (volume.restrict (Ioc 0 (2 * π))) := by ring
  _ ≤ 2 ^ 8 * eLpNorm g 2 (volume.restrict (Ioc 0 (2 * π))) := by
    gcongr
    norm_num
  _ = 2 ^ 8 * eLpNorm g 2 (volume.restrict (Ioc 1 4)) := by
    congr 1
    rw [restrict_Ioc_eq_restrict_Icc, restrict_Ioc_eq_restrict_Icc]
    have : volume.restrict (Icc 1 4) = (volume.restrict (Icc 0 (2 * π))).restrict (Icc 1 4) := by
      rw [Measure.restrict_restrict_of_subset]
      apply Icc_subset_Icc (by norm_num) (by linarith [Real.pi_gt_three])
    rw [this]
    apply (eLpNorm_restrict_eq_of_support_subset h'g).symm

/-- The operator `czOperator K r` is bounded from `L^2 [1, 4]` to `L^2 [2, 3]`,
uniformly in `r`. This follows from the fact, proved in `norm_czOperator_le_add`, that it is
bounded by the sum of two operators which are both bounded: one is the convolution
with `dirichletApprox`, bounded as it is an average of Fourier projections, and the other one has
a kernel uniformly bounded in `L^1` and is therefore controlled by Young inequality. -/
lemma eLpNorm_czOperator_restrict_two_three {g : ℝ → ℂ} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hg : MemLp g ∞ volume) :
    eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc 2 3)) ≤
      2 ^ 8 * eLpNorm g 2 (volume.restrict (Ioc 1 4)) := by
  let g' := (indicator (Icc 1 4)) g
  have A : eLpNorm g 2 (volume.restrict (Ioc 1 4)) = eLpNorm g' 2 (volume.restrict (Ioc 1 4)) := by
    apply eLpNorm_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    simp only [g']
    rw [indicator_of_mem]
    exact ⟨hy.1.le, hy.2⟩
  have B : eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc 2 3)) =
      eLpNorm (czOperator K r g') 2 (volume.restrict (Ioc 2 3)) := by
    apply eLpNorm_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    simp only [czOperator, g']
    congr with z
    by_cases hz : z ∈ Icc 1 4
    · rw [indicator_of_mem hz]
    · suffices K y z = 0 by simp [this]
      apply k_of_one_le_abs
      simp only [mem_Icc, not_and, not_le] at hz
      rcases lt_or_ge z 1 with h'z | h'z
      · linarith [le_abs_self (y - z), hy.1]
      · linarith [neg_le_abs (y - z), hy.2, hz h'z]
  rw [A, B]
  exact eLpNorm_czOperator_restrict_two_three_of_support_subset hr (hg.indicator measurableSet_Icc)
    support_indicator_subset

/-- The operator `czOperator K r` is bounded from `L^2 [a - 1, a + 2]` to `L^2 [a, a + 1]`,
uniformly in `r` and `a`. This follows from the same fact from `L^2 [1, 4]` to `L^2 [2, 3]`
proved using Fourier series, and translation invariance. -/
lemma eLpNorm_czOperator_restrict {g : ℝ → ℂ} {r a : ℝ} (hr : r ∈ Ioo 0 1)
    (hg : MemLp g ∞ volume) :
    eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc a (a + 1))) ≤
      2 ^ 8 * eLpNorm g 2 (volume.restrict (Ioc (a - 1) (a + 2))) := by
  let g' := g ∘ (fun x ↦ x + (a - 2))
  have A : eLpNorm g 2 (volume.restrict (Ioc (a - 1) (a + 2))) =
      eLpNorm g' 2 (volume.restrict (Ioc 1 4)) := by
    rw [eLpNorm_comp_measurePreserving (hg.restrict _).aestronglyMeasurable]
    have : MeasurePreserving (fun x ↦ x + (a - 2)) := measurePreserving_add_right volume (a - 2)
    convert this.restrict_preimage (s := Ioc (a - 1) (a + 2)) measurableSet_Ioc
    simp
    norm_num
  have B : eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc a (a + 1))) =
      eLpNorm (czOperator K r g') 2 (volume.restrict (Ioc 2 3)) := by
    have : czOperator K r g' = (czOperator K r g) ∘ (fun x ↦ x + (a - 2)) := by
      rw [K_def, ← czOperator_comp_add]
    rw [this, eLpNorm_comp_measurePreserving]
    · apply AEStronglyMeasurable.restrict
      apply czOperator_aestronglyMeasurable' Hilbert_kernel_measurable hg.aestronglyMeasurable
    · have : MeasurePreserving (fun x ↦ x + (a - 2)) := measurePreserving_add_right volume (a - 2)
      convert this.restrict_preimage (s := Ioc a (a + 1)) measurableSet_Ioc
      simp
      norm_num
  rw [A, B]
  apply eLpNorm_czOperator_restrict_two_three hr
  exact hg.comp_measurePreserving (measurePreserving_add_right volume (a - 2))

open Measure

lemma eLpNorm_czOperator_sq {g : ℝ → ℂ} {r : ℝ} (hr : r ∈ Ioo 0 1) (hg : MemLp g ∞ volume) :
    (eLpNorm (czOperator K r g) 2) ^ 2 ≤ 2 ^ 18 * (eLpNorm g 2) ^ 2 := by
  have A : (volume : Measure ℝ) =
      Measure.sum (fun (n : ℤ) ↦ volume.restrict (Ioc (n : ℝ) (n + 1))) := by
    rw [← restrict_iUnion (Set.pairwise_disjoint_Ioc_intCast _) (fun n ↦ measurableSet_Ioc),
      iUnion_Ioc_intCast, restrict_univ]
  /- There is a weird calc bug here: if one omits the implicit argument `volume` from the first
  or the last line, `calc` loops forever... -/
  calc
  (eLpNorm (czOperator K r g) 2 volume) ^ 2
  _ = ∫⁻ x, ‖czOperator K r g x‖ₑ ^ 2 := by rw [sq_eLpNorm_two]
  _ = ∑' n : ℤ, ∫⁻ x in Ioc (n : ℝ) (n + 1), ‖czOperator K r g x‖ₑ ^ 2 := by
    conv_lhs => rw [A, lintegral_sum_measure]
  _ = ∑' n : ℤ, (eLpNorm (czOperator K r g) 2 (volume.restrict (Ioc n (n + 1)))) ^ 2 := by
    simp [sq_eLpNorm_two]
  _ ≤ ∑' n : ℤ, (2 ^ 8 * eLpNorm g 2 (volume.restrict (Ioc (n - 1) (n + 2)))) ^ 2 := by
    gcongr with n
    apply eLpNorm_czOperator_restrict hr hg
  _ = 2 ^ 16 * ∑' n : ℤ, ∫⁻ x in Ioc (n - 1 : ℝ) (n + 2), ‖g x‖ₑ ^ 2 := by
    simp only [mul_pow, ← pow_mul, Nat.reduceMul, ENNReal.tsum_mul_left, sq_eLpNorm_two]
  _ = 2 ^ 16 * ∑' n : ℤ, ((∫⁻ x in Ioc (n - 1 : ℝ) n, ‖g x‖ₑ ^ 2) +
      (∫⁻ x in Ioc (n : ℝ) (n + 1), ‖g x‖ₑ ^ 2) + ∫⁻ x in Ioc (n + 1 : ℝ) (n + 2), ‖g x‖ₑ ^ 2) := by
    congr with n
    rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one, Ioc_union_Ioc_eq_Ioc]
    rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [Ioc_union_Ioc_eq_Ioc] <;> linarith
  _ = 2 ^ 16 * ((∑' n : ℤ, ∫⁻ x in Ioc (n - 1 : ℝ) n, ‖g x‖ₑ ^ 2) +
        (∑' n : ℤ, ∫⁻ x in Ioc (n : ℝ) (n + 1), ‖g x‖ₑ ^ 2) +
        (∑' n : ℤ, ∫⁻ x in Ioc (n + 1 : ℝ) (n + 2), ‖g x‖ₑ ^ 2)) := by simp [ENNReal.tsum_add]
  _ = 2 ^ 16 * ((∑' n : ℤ, ∫⁻ x in Ioc (n : ℝ) (n + 1), ‖g x‖ₑ ^ 2) +
        (∑' n : ℤ, ∫⁻ x in Ioc (n : ℝ) (n + 1), ‖g x‖ₑ ^ 2) +
        (∑' n : ℤ, ∫⁻ x in Ioc (n : ℝ) (n + 1), ‖g x‖ₑ ^ 2)) := by
    congr 2
    · rw [← (Equiv.addRight 1).tsum_eq]
      simp
    · rw [← (Equiv.subRight 1).tsum_eq]
      simp only [Equiv.subRight_apply, Int.cast_sub, Int.cast_one, sub_add_cancel]
      ring_nf
  _ = 2 ^ 16 * (3 * (eLpNorm g 2) ^ 2) := by
    simp only [sq_eLpNorm_two]
    conv_rhs => rw [A, lintegral_sum_measure]
    ring
  _ ≤ 2 ^ 18 * (eLpNorm g 2 volume) ^ 2 := by
    rw [← mul_assoc]
    gcongr
    norm_num

lemma eLpNorm_czOperator {g : ℝ → ℂ} {r : ℝ} (hr : 0 < r) (hg : MemLp g ∞ volume) :
    eLpNorm (czOperator K r g) 2 ≤ 2 ^ 9 * eLpNorm g 2 := by
  rcases le_or_gt 1 r with h'r | h'r
  · have : czOperator K r g = 0 := by
      ext x
      simp only [czOperator, Nat.reducePow, Nat.cast_ofNat, K, Pi.zero_apply]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      have : k (x - y) = 0 := by
        apply k_of_one_le_abs
        simp only [mem_compl_iff, Metric.mem_ball, dist_eq_norm', Real.norm_eq_abs, not_lt] at hy
        linarith
      simp [this]
    simp [this]
  · have := ENNReal.rpow_le_rpow (z := 2⁻¹) (eLpNorm_czOperator_sq ⟨hr, h'r⟩ hg) (by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul, ← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at this
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
      ENNReal.rpow_one] at this
    convert this
    norm_num

/- Lemma 11.1.6.
This verifies the assumption on the operators T_r in two-sided metric space Carleson.

Note: we might be able to simplify the proof in the blueprint by using real interpolation
`MeasureTheory.exists_hasStrongType_real_interpolation`.
-/
lemma Hilbert_strong_2_2 ⦃r : ℝ⦄ (hr : 0 < r) :
    HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts 4) := by
  intro g hg
  refine ⟨czOperator_aestronglyMeasurable' Hilbert_kernel_measurable hg.aestronglyMeasurable, ?_⟩
  apply (eLpNorm_czOperator hr hg.memLp_top).trans
  gcongr
  simp [C_Ts]
  norm_num
