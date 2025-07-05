import Carleson.Classical.DirichletKernel
import Carleson.Classical.HilbertKernel
import Carleson.Classical.SpectralProjectionBound
import Carleson.Defs
import Carleson.ToMathlib.Algebra.BigOperators.Pi
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.Real.Pi.Bounds

/- This file contains the proof that the Hilbert kernel is a bounded operator. -/

noncomputable section

open scoped Real ENNReal
open Complex ComplexConjugate MeasureTheory Bornology Set
-- open MeasureTheory Function Metric Bornology Real ENNReal MeasureTheory.ENNReal MeasureTheory



section
@[reducible]
def doublingMeasure_real_two : DoublingMeasure ℝ 2 :=
  InnerProductSpace.DoublingMeasure.mono (by simp)

instance doublingMeasure_real_16 : DoublingMeasure ℝ (2 ^ 4 : ℕ) :=
  doublingMeasure_real_two.mono (by norm_num)
end

/-- The modulation operator `M_n g`, defined in (11.3.1) -/
def modulationOperator (n : ℤ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x * Complex.exp (.I * n * x)

lemma Measurable.modulationOperator (n : ℤ) {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (modulationOperator n g) :=
  hg.mul (measurable_const.mul measurable_ofReal).cexp

/-- The approximate Hilbert transform `L_N g`, defined in (11.3.2).
defined slightly differently. -/
def approxHilbertTransform (n : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n),
    modulationOperator (-k) (partialFourierSum k (modulationOperator k g)) x

/-- The kernel `k_r(x)` defined in (11.3.11).
When used, we may assume that `r ∈ Ioo 0 1`.
Todo: find better name? -/
def niceKernel (r : ℝ) (x : ℝ) : ℝ :=
  if Complex.exp (.I * x) = 1 then r⁻¹ else
    min r⁻¹ (1 + r / normSq (1 - Complex.exp (.I * x)))

lemma niceKernel_pos {r x : ℝ} (hr : r > 0) : 0 < niceKernel r x := by
  unfold niceKernel
  split
  · positivity
  · apply lt_min (by positivity)
    apply lt_add_of_lt_of_nonneg zero_lt_one
    apply div_nonneg (by positivity) (normSq_nonneg _)

lemma niceKernel_neg {r x : ℝ} : niceKernel r (-x) = niceKernel r x := by
  simp only [niceKernel, ofReal_neg, mul_neg, Complex.exp_neg, inv_eq_one]
  congr 4
  rw [← normSq_conj, inv_eq_conj (norm_exp_I_mul_ofReal x), map_sub, map_one, conj_conj]

lemma niceKernel_periodic (r : ℝ) : Function.Periodic (niceKernel r) (2 * π) := by
  simp [niceKernel, mul_add, mul_comm I (2 * π), Complex.exp_add]

lemma niceKernel_intervalIntegrable {r : ℝ} (a b : ℝ) (hr : r > 0) :
    IntervalIntegrable (niceKernel r) volume a b := by
  apply intervalIntegrable_const (c := r⁻¹) |>.mono_fun
  · classical
    refine AEStronglyMeasurable.piecewise ?_ (by fun_prop) (by fun_prop)
    exact isClosed_eq (by fun_prop) continuous_const |>.measurableSet
  · refine Filter.Eventually.of_forall <| fun y ↦ ?_
    simp_rw [Real.norm_eq_abs, abs_of_pos (niceKernel_pos hr), abs_inv, abs_of_pos hr, niceKernel]
    split <;> simp

lemma niceKernel_lowerBound {r x : ℝ} (hr : 0 < r ∧ r < π) (hx : 0 ≤ x ∧ x ≤ r) :
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

lemma niceKernel_upperBound {r x : ℝ} (hr : 0 < r) (hx : r ≤ x ∧ x ≤ π) :
    niceKernel r x ≤ 1 + 4 * r / x ^ 2 := calc
  _ ≤ 1 + r / (x / 2) ^ 2 := by
    have : cexp (I * x) ≠ 1 := fun h ↦ by
      have : Real.cos x = 1 := by simpa [mul_comm I x] using congr(($h).re)
      rw [Real.cos_eq_one_iff_of_lt_of_lt] at this <;> linarith
    simp only [niceKernel, this, ↓reduceIte, inf_le_iff]
    right
    gcongr 1 + ?_
    have : 0 < x := by linarith
    grw [normSq_eq_norm_sq, lower_secant_bound ⟨?_, ?_⟩ (le_abs_self x)] <;> linarith
  _  = 1 + 4 * r / x ^ 2 := by ring

/-- Lemma 11.1.8 -/
lemma mean_zero_oscillation {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0)..2 * π, Complex.exp (.I * n * x) = 0 := by
  rw [integral_exp_mul_complex (by simp [hn])]
  simp [sub_eq_zero, Complex.exp_eq_one_iff, hn, ← mul_assoc, mul_comm Complex.I,
    mul_right_comm _ Complex.I]


/-- Lemma 11.5.1
Note: might not be used if we can use `spectral_projection_bound_lp` below.
-/
lemma partial_sum_projection {f : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π)) {x : ℝ} :
    partialFourierSum n (partialFourierSum n f) x = partialFourierSum n f x := by
  sorry

/-- Lemma 11.5.2.
Note: might not be used if we can use `spectral_projection_bound_lp` below.
-/
lemma partial_sum_selfadjoint {f g : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π)) :
    ∫ x in (0)..2 * π, conj (partialFourierSum n f x) * g x =
    ∫ x in (0)..2 * π, conj (f x) * partialFourierSum n g x := by
  sorry


--lemma eLpNorm_eq_norm {f : ℝ → ℂ} {p : ENNReal} (hf : MemLp f p) :
--    ‖MemLp.toLp f hf‖ = eLpNorm f p := by
--  sorry

theorem AddCircle.haarAddCircle_eq_smul_volume {T : ℝ} [hT : Fact (0 < T)] :
    (@haarAddCircle T _) = (ENNReal.ofReal T)⁻¹ • (volume : Measure (AddCircle T)) := by
  rw [volume_eq_smul_haarAddCircle, ← smul_assoc, smul_eq_mul,
    ENNReal.inv_mul_cancel (by simp [hT.out]) ENNReal.ofReal_ne_top, one_smul]

open AddCircle in
/-- Lemma 11.1.10.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
-- todo: add lemma that relates `eLpNorm ((Ioc a b).indicator f)` to `∫ x in a..b, _`
lemma spectral_projection_bound {f : ℝ → ℂ} {n : ℕ} (hmf : Measurable f) :
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
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma modulated_averaged_projection {g : ℝ → ℂ} {n : ℕ} (hmg : Measurable g) :
    eLpNorm ((Ioc 0 (2 * π)).indicator (approxHilbertTransform n g)) 2 ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator g) 2 := by
  unfold approxHilbertTransform
  by_cases hn : n = 0
  · simp [hn]
  rw [funext (indicator_const_mul _ _ _)]
  change eLpNorm ((n : ℂ)⁻¹ • _) _ _ ≤ _
  rw [eLpNorm_const_smul _ _ _ _, ← Finset.sum_fn, ← sum_indicator_eq_indicator_sum,
    enorm_inv (Nat.cast_ne_zero.mpr hn), ← one_mul (eLpNorm (indicator _ _) _ _),
    ← ENNReal.inv_mul_cancel (by simp [hn]) (enorm_ne_top (x := (n : ℂ))), mul_assoc]
  refine mul_le_mul_left' (le_trans (eLpNorm_sum_le ?_ one_le_two) ?_) _
  · refine fun i _ ↦ Measurable.indicator ?_ measurableSet_Ioc |>.aestronglyMeasurable
    exact partialFourierSum_uniformContinuous.continuous.measurable.modulationOperator _
  trans ∑ i ∈ Finset.Ico n (2 * n), eLpNorm ((Ioc 0 (2 * π)).indicator g) 2 volume; swap
  · simp [← ofReal_norm_eq_enorm, Nat.sub_eq_of_eq_add (two_mul n)]
  refine Finset.sum_le_sum (fun i _ ↦ ?_)
  rw [eLpNorm_indicator_modulationOperator, ← eLpNorm_indicator_modulationOperator g i]
  exact spectral_projection_bound (hmg.modulationOperator i)

/- Lemma 11.3.2 `periodic-domain-shift` is in Mathlib. -/

/-- Lemma 11.3.3.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma young_convolution {f g : ℝ → ℂ} (hmf : AEMeasurable f) (periodic_f : f.Periodic (2 * π))
    (hmg : AEMeasurable g) (periodic_g : g.Periodic (2 * π)) :
    eLpNorm ((Ioc 0 (2 * π)).indicator fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 * eLpNorm ((Ioc 0 (2 * π)).indicator g) 1  := by
  have : Fact (0 < 2 * π) := ⟨mul_pos two_pos Real.pi_pos⟩
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by exact one_le_two
  simpa [zero_add] using ENNReal.eLpNorm_Ioc_convolution_le_of_norm_le_mul
    (ContinuousLinearMap.mul ℝ ℂ) 0 h2 (le_refl 1) h2 (by rw [inv_one])
    periodic_f periodic_g hmf.aestronglyMeasurable hmg.aestronglyMeasurable 1 (by simp)

/-- Lemma 11.3.4.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma integrable_bump_convolution {f g : ℝ → ℂ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π))
    {r : ℝ} (hr : r ∈ Ioo 0 π) (hle : ∀ x, ‖g x‖ ≤ niceKernel r x) :
    eLpNorm ((Ioc 0 (2 * π)).indicator fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 ≤
    2 ^ (5 : ℝ) * eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 := by
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

  grw [young_convolution hf.1.aemeasurable periodic_f hg.1.aemeasurable periodic_g, mul_comm]
  gcongr
  have {a b} : eLpNorm ((Ioc a b).indicator g) 1 volume ≠ ⊤ := by
    grw [← lt_top_iff_ne_top, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc,
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (OrderTop.le_top 1) (hg.restrict _).1]
    exact ENNReal.mul_lt_top (hg.restrict _).eLpNorm_lt_top (by norm_num)
  rw [← ENNReal.toReal_le_toReal this (by norm_num)]

  calc
    _ ≤ ∫ x in (0)..2 * π, niceKernel r x := by
      simp_rw [eLpNorm_one_eq_lintegral_enorm, enorm_indicator_eq_indicator_enorm,
        lintegral_indicator (measurableSet_Ioc)]
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
        exact niceKernel_lowerBound ⟨hr0, hrπ⟩ hx
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
    _ ≤ (2 ^ (5 : ℝ) : ENNReal).toReal := by
      rw [mul_sub, mul_inv_cancel_right₀ hr0.ne.symm]
      grw [sub_le_self 8 (by positivity), Real.pi_lt_four]
      norm_num

/-- The function `L'`, defined in the Proof of Lemma 11.3.5. -/
def dirichletApprox (n : ℕ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n), dirichletKernel k x * Complex.exp (- Complex.I * k * x)

/-- Lemma 11.3.5, part 1. -/
lemma continuous_dirichletApprox {n : ℕ} : Continuous (dirichletApprox n) := by
  sorry

/-- Lemma 11.3.5, part 2. -/
lemma periodic_dirichletApprox (n : ℕ) : (dirichletApprox n).Periodic (2 * π) := by
  sorry

/-- Lemma 11.3.5, part 3.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma approxHilbertTransform_eq_dirichletApprox {f : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    {n : ℕ} {x : ℝ} :
    approxHilbertTransform n f x =
    (2 * π)⁻¹ * ∫ y in (0)..2 * π, f y * dirichletApprox n (x - y) := by
  sorry

/-- Lemma 11.3.5, part 4.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma dist_dirichletApprox_le {f : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    {r : ℝ} (hr : r ∈ Ioo 0 1) {n : ℕ} (hn : n = ⌈r⁻¹⌉₊) {x : ℝ} :
    dist (dirichletApprox n x) ({y : ℂ | ‖y‖ ∈ Ioo r 1}.indicator 1 x) ≤
    2 ^ (5 : ℝ) * niceKernel r x := by
  sorry

/- Lemma 11.1.6.
This verifies the assumption on the operators T_r in two-sided metric space Carleson.
Its proof is done in Section 11.3 (The truncated Hilbert transform) and is yet to be formalized.

Note: we might be able to simplify the proof in the blueprint by using real interpolation
`MeasureTheory.exists_hasStrongType_real_interpolation`.
Note: In the blueprint we have the condition `r < 1`.
Can we get rid of that condition or otherwise fix `two_sided_metric_carleson`?
-/
lemma Hilbert_strong_2_2 ⦃r : ℝ⦄ (hr : 0 < r) :
    HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts 4) :=
  sorry
