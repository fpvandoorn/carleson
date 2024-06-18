/- The arguments in this file replace section 10.2 (Piecewise constant functions) from the paper. -/

import Carleson.MetricCarleson
import Carleson.Theorem1_1.Basic

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.PSeries

noncomputable section

open BigOperators
open Finset

section
open Metric
variable {α : Type} {β : Type}
--might be generalized
--TODO : choose better name
lemma uniformContinuous_iff_bounded [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} {b : ℝ} (bpos : b > 0):
  UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, δ < b ∧ ∀ {x y : α}, dist x y < δ → dist (f x) (f y) < ε := by
  rw [Metric.uniformContinuous_iff]
  constructor
  . intro h ε εpos
    obtain ⟨δ', δ'pos, hδ'⟩ := h ε εpos
    use min δ' (b / 2)
    constructor
    . exact (lt_min δ'pos (by linarith)).gt
    constructor
    . apply min_lt_of_right_lt
      linarith
    . exact fun hxy ↦ hδ' (lt_of_lt_of_le hxy (min_le_left δ' (b / 2)))
  . intro h ε εpos
    obtain ⟨δ, δpos, _, hδ⟩ := h ε εpos
    use δ
end section

/- TODO: might be generalized. -/
lemma closeSmoothApprox {f : ℝ → ℂ} (unicontf : UniformContinuous f) {ε : ℝ} (εpos : ε > 0):
    ∃ (f₀ : ℝ → ℂ), ContDiff ℝ ⊤ f₀ ∧ ∀ x, Complex.abs (f x - f₀ x) ≤ ε := by
  obtain ⟨δ, δpos, hδ⟩ := (Metric.uniformContinuous_iff.mp unicontf) ε εpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ/2, δ, by linarith, by linarith⟩
  let f₀ := MeasureTheory.convolution (φ.normed MeasureTheory.volume) f
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
  refine ⟨f₀, ?_, fun x ↦ ?_⟩
  . exact HasCompactSupport.contDiff_convolution_left _ φ.hasCompactSupport_normed
      φ.contDiff_normed unicontf.continuous.locallyIntegrable
  . rw [← Complex.dist_eq, dist_comm]
    exact ContDiffBump.dist_normed_convolution_le unicontf.continuous.aestronglyMeasurable
      fun y hy ↦ (hδ hy).le

/- Slightly different version-/
lemma closeSmoothApproxPeriodic {f : ℝ → ℂ} (unicontf : UniformContinuous f)
  (periodicf : Function.Periodic f (2 * Real.pi)) {ε : ℝ} (εpos : ε > 0):
    ∃ (f₀ : ℝ → ℂ), ContDiff ℝ ⊤ f₀ ∧ Function.Periodic f₀ (2 * Real.pi) ∧
      ∀ x, Complex.abs (f x - f₀ x) ≤ ε := by
  obtain ⟨δ, δpos, hδ⟩ := (Metric.uniformContinuous_iff.mp unicontf) ε εpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ/2, δ, by linarith, by linarith⟩
  set f₀ := MeasureTheory.convolution (φ.normed MeasureTheory.volume) f
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with f₀def
  refine ⟨f₀, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  . exact HasCompactSupport.contDiff_convolution_left _ φ.hasCompactSupport_normed
      φ.contDiff_normed unicontf.continuous.locallyIntegrable
  . /-TODO: improve this. -/
    rw [f₀def, MeasureTheory.convolution, MeasureTheory.convolution]
    congr with t
    congr 1
    convert periodicf (x - t) using 2
    ring
  . rw [← Complex.dist_eq, dist_comm]
    exact ContDiffBump.dist_normed_convolution_le unicontf.continuous.aestronglyMeasurable fun y hy ↦ (hδ hy).le

/- Inspired by mathlib : NNReal.summable_of_le-/
lemma Real.summable_of_le {β : Type} {f g : β → ℝ} (hgpos : 0 ≤ g) (hgf : ∀ (b : β), g b ≤ f b) (summablef : Summable f) :
    Summable g := Summable.of_nonneg_of_le hgpos hgf summablef
  /-
  set g' : β → NNReal := fun b ↦ ⟨g b, hgpos b⟩ with g'def
  set f' : β → NNReal := fun b ↦ ⟨f b, (hgpos b).trans (hgf b)⟩ with f'def
  have hf'f: f = (fun b ↦ (f' b : ℝ)) := by norm_cast
  have hg'g: g = (fun b ↦ (g' b : ℝ)) := by norm_cast
  rw [hg'g, NNReal.summable_coe]
  have : ∀ b : β, g' b ≤ f' b := by
    intro b
    rw [f'def, g'def, ←NNReal.coe_le_coe]
    simp
    exact hgf b
  apply NNReal.summable_of_le this
  rwa [←NNReal.summable_coe, ←hf'f]
  -/

-- local lemma
lemma summable_of_le_on_nonzero {f g : ℤ → ℝ} (hgpos : 0 ≤ g) (hgf : ∀ i ≠ 0, g i ≤ f i) (summablef : Summable f) : Summable g := by
  set f' : ℤ → ℝ := fun i ↦ if i = 0 then g i else f i with f'def
  have : ∀ i, g i ≤ f' i := by
    intro i
    rw [f'def]
    by_cases h : i = 0
    . simp [h]
    . simp only [h, ↓reduceIte]
      exact hgf i h
  apply Real.summable_of_le hgpos this
  let s : Finset ℤ := {0}
  rw [← s.summable_compl_iff]
  apply (summable_congr _).mpr (s.summable_compl_iff.mpr summablef)
  intro ⟨b, hb⟩
  rw [mem_singleton] at hb
  simp [f'def, hb]

lemma continuous_bounded {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 (2 * Real.pi))) : ∃ C, ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (f x) ≤ C := by
  have interval_compact := (isCompact_Icc (a := 0) (b := 2 * Real.pi))
  obtain ⟨a, _, ha⟩ := interval_compact.exists_isMaxOn (Set.nonempty_Icc.mpr Real.two_pi_pos.le)
    (Complex.continuous_abs.comp_continuousOn hf)
  refine ⟨Complex.abs (f a), fun x hx ↦ ?_⟩
  rw [isMaxOn_iff] at ha
  exact ha x hx

/-TODO: might be generalized assumptions might be weakened, and constant given explicitely -/
lemma fourierCoeffOn_bound {f : ℝ → ℂ} (f_continuous : Continuous f) : ∃ C, ∀ n, Complex.abs (fourierCoeffOn Real.two_pi_pos f n) ≤ C := by
  obtain ⟨C, f_bounded⟩ := continuous_bounded f_continuous.continuousOn
  use C
  intro n
  simp only [fourierCoeffOn_eq_integral, sub_zero, one_div, mul_inv_rev, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv, map_mul, map_inv₀, Complex.abs_ofReal, Complex.abs_ofNat]
  field_simp
  rw [abs_of_nonneg Real.pi_pos.le, mul_comm Real.pi, div_le_iff Real.two_pi_pos, ←Complex.norm_eq_abs]
  calc ‖∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * n * x / (2 * Real.pi))) * f x‖
    _ = ‖∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), (starRingEnd ℂ) (Complex.exp (Complex.I * n * x)) * f x‖ := by
      congr with x
      congr
      ring_nf
      rw [mul_comm, ←mul_assoc, ←mul_assoc, ←mul_assoc, inv_mul_cancel]
      . ring
      . simp [ne_eq, Complex.ofReal_eq_zero, Real.pi_pos.ne.symm]
    _ ≤ ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), ‖(starRingEnd ℂ) (Complex.exp (Complex.I * n * x)) * f x‖ := by
      exact intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ = ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), ‖(Complex.exp (Complex.I * n * x)) * f x‖ := by
      simp
    _ = ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), ‖f x‖ := by
      congr with x
      simp only [norm_mul, Complex.norm_eq_abs]
      rw_mod_cast [mul_assoc, mul_comm Complex.I, Complex.abs_exp_ofReal_mul_I]
      ring
    _ ≤ ∫ (_ : ℝ) in (0 : ℝ)..(2 * Real.pi), C := by
      refine intervalIntegral.integral_mono_on Real.two_pi_pos.le ?_ intervalIntegrable_const
        fun x hx ↦ f_bounded x hx
      /-Could specify `aestronglyMeasurable` and `intervalIntegrable` intead of `f_continuous`. -/
      exact IntervalIntegrable.intervalIntegrable_norm_iff f_continuous.aestronglyMeasurable |>.mpr
        (f_continuous.intervalIntegrable _ _)
    _ = C * (2 * Real.pi) := by simp; ring

/-TODO: Assumptions might be weakened. -/
lemma periodic_deriv {𝕜 : Type} [NontriviallyNormedField 𝕜] {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {T : 𝕜} (diff_f : ContDiff 𝕜 1 f) (periodic_f : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro x
  set g : 𝕜 → 𝕜 := fun x ↦ x + T with gdef
  have diff_g : Differentiable 𝕜 g := differentiable_id.add_const _
  have : deriv (f ∘ g) x = ((deriv f) ∘ g) x := by
    calc deriv (f ∘ g) x
      _ = deriv g x • deriv f (g x) := deriv.scomp x (diff_f.differentiable (by norm_num)).differentiableAt diff_g.differentiableAt
      _ = deriv f (g x) := by rw [gdef, deriv_add_const, deriv_id'']; simp
  rw [gdef] at this
  simp only [Function.comp_apply] at this
  convert this.symm
  ext y
  simp [(periodic_f y).symm]

/-TODO: might be generalized. -/
/-TODO: Assumption periodicf is probably not needed actually. -/
lemma fourierCoeffOn_ContDiff_two_bound {f : ℝ → ℂ} (periodicf : Function.Periodic f (2 * Real.pi)) (fdiff : ContDiff ℝ 2 f): ∃ C, ∀ n ≠ 0, Complex.abs (fourierCoeffOn Real.two_pi_pos f n) ≤ C / n ^ 2 := by
--#check IsCompact.exists_isMaxOn
  --TODO: improve this
  have h : ∀ x ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt f (deriv f x) x := by
    intro x _
    rw [hasDerivAt_deriv_iff]
    exact fdiff.differentiable (by norm_num) _
  have h' : ∀ x ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x _
    rw [hasDerivAt_deriv_iff]
    exact (contDiff_succ_iff_deriv.mp fdiff).2.differentiable (by norm_num) _
  /-Get better representation for the fourier coefficients of f. -/
  have fourierCoeffOn_eq {n : ℤ} (hn : n ≠ 0): (fourierCoeffOn Real.two_pi_pos f n) = - 1 / (n^2) * fourierCoeffOn Real.two_pi_pos (fun x ↦ deriv (deriv f) x) n := by
    rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h, fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h']
    . have h1 := periodicf 0
      have periodic_deriv_f : Function.Periodic (deriv f) (2 * Real.pi) := periodic_deriv (fdiff.of_le one_le_two) periodicf
      have h2 := periodic_deriv_f 0
      simp at h1 h2
      simp [h1, h2]
      ring_nf
      simp [mul_inv_cancel, one_mul, Real.pi_pos.ne.symm]
    . exact (contDiff_one_iff_deriv.mp (contDiff_succ_iff_deriv.mp fdiff).2).2.intervalIntegrable _ _
    . exact (contDiff_succ_iff_deriv.mp fdiff).2.continuous.intervalIntegrable _ _
  obtain ⟨C, hC⟩ := fourierCoeffOn_bound (contDiff_one_iff_deriv.mp (contDiff_succ_iff_deriv.mp fdiff).2).2
  refine ⟨C, fun n hn ↦ ?_⟩
  simp only [fourierCoeffOn_eq hn, Nat.cast_one, Int.cast_pow, map_mul, map_div₀, map_neg_eq_map,
  map_one, map_pow, Complex.abs_intCast, sq_abs, one_div, div_eq_mul_inv C, mul_comm _ (Complex.abs _)]
  gcongr
  exact hC n

open Topology Filter

/-TODO : Assumptions might be weakened-/
lemma int_sum_nat {β : Type} [AddCommGroup β] [TopologicalSpace β] [ContinuousAdd β] {f : ℤ → β} {a : β} (hfa : HasSum f a) :
    Filter.Tendsto (fun N ↦ ∑ n in Icc (-Int.ofNat ↑N) N, f n) Filter.atTop (𝓝 a) := by
  have := hfa.nat_add_neg.tendsto_sum_nat
  have := (Filter.Tendsto.add_const (- (f 0))) this
  simp at this
  /-Need to start at 1 instead of zero for the base case to be true. -/
  rw [←tendsto_add_atTop_iff_nat 1] at this
  convert this using 1
  ext N
  induction' N with N ih
  . simp
  . have : Icc (- Int.ofNat (Nat.succ N)) (Nat.succ N) = insert (↑(Nat.succ N)) (insert (-Int.ofNat (Nat.succ N)) (Icc (-Int.ofNat N) N)) := by
      rw [←Ico_insert_right, ←Ioo_insert_left]
      . congr with n
        simp only [Int.ofNat_eq_coe, mem_Ioo, mem_Icc]
        push_cast
        rw [Int.lt_add_one_iff, neg_add, ←sub_eq_add_neg, Int.sub_one_lt_iff]
      . norm_num
        linarith
      . norm_num
        linarith
    rw [this, sum_insert, sum_insert, ih, ← add_assoc]
    symm
    rw [sum_range_succ, add_comm, ←add_assoc, add_comm]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg, Nat.succ_eq_add_one,
      Int.ofNat_eq_coe, add_right_inj, add_comm]
    . simp
    . norm_num
      linarith

--theorem HasSum.nat_add_neg {f : ℤ → M} (hf : HasSum f m) :
--    HasSum (fun n : ℕ ↦ f n + f (-n)) (m + f 0) := by

/-TODO: Weaken statement to pointwise convergence to simplify proof?-/
lemma fourierConv_ofTwiceDifferentiable {f : ℝ → ℂ} (periodicf : Function.Periodic f (2 * Real.pi)) (fdiff : ContDiff ℝ 2 f) {ε : ℝ} (εpos : ε > 0) :
    ∃ N₀, ∀ N > N₀, ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
  have fact_two_pi_pos : Fact (0 < 2 * Real.pi) := by
    rw [fact_iff]
    exact Real.two_pi_pos
  set g : C(AddCircle (2 * Real.pi), ℂ) := ⟨AddCircle.liftIco (2*Real.pi) 0 f, AddCircle.liftIco_continuous ((periodicf 0).symm) fdiff.continuous.continuousOn⟩ with g_def
  have two_pi_pos' : 0 < 0 + 2 * Real.pi := by linarith [Real.two_pi_pos]
  have fourierCoeff_correspondence {i : ℤ} : fourierCoeff g i = fourierCoeffOn two_pi_pos' f i := fourierCoeff_liftIco_eq f i
  simp at fourierCoeff_correspondence
  have function_sum : HasSum (fun (i : ℤ) => fourierCoeff g i • fourier i) g := by
    apply hasSum_fourier_series_of_summable
    obtain ⟨C, hC⟩ := fourierCoeffOn_ContDiff_two_bound periodicf fdiff
    set maj : ℤ → ℝ := fun i ↦ 1 / (i ^ 2) * C with maj_def
    have summable_maj : Summable maj := by
      by_cases Ceq0 : C = 0
      . simp [maj_def, Ceq0, one_div, mul_zero, summable_zero]
      . rw [← summable_div_const_iff Ceq0]
        convert Real.summable_one_div_int_pow.mpr one_lt_two using 1
        simp [maj_def, mul_div_cancel_right₀, Ceq0]
    rw [summable_congr @fourierCoeff_correspondence, ←summable_norm_iff]
    apply summable_of_le_on_nonzero _ _ summable_maj
    . intro i
      simp
    . intro i ine0
      field_simp [maj_def, Complex.norm_eq_abs, hC i ine0]
  have := int_sum_nat function_sum
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at this
  have := this ε εpos
  rw [Filter.eventually_atTop] at this
  obtain ⟨N₀, hN₀⟩ := this
  use N₀
  intro N hN x hx
  have := hN₀ N hN.le x
  simp only [Complex.dist_eq, ContinuousMap.coe_sum, sum_apply] at this
  convert this.le using 2
  congr 1
  . rw [g_def, ContinuousMap.coe_mk]
    by_cases h : x = 2 * Real.pi
    . conv => lhs; rw [h, ← zero_add  (2 * Real.pi), periodicf]
      have := AddCircle.coe_add_period (2 * Real.pi) 0
      rw [zero_add] at this
      rw [h, this, AddCircle.liftIco_coe_apply]
      simp [Real.pi_pos]
    . have : x ∈ Set.Ico 0 (2 * Real.pi) := by
        use hx.1
        exact lt_of_le_of_ne hx.2 h
      simp [AddCircle.liftIco_coe_apply, zero_add, this]
  . simp [partialFourierSum, fourierCoeff_correspondence]
