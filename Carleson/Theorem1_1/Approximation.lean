/- The arguments in this file replace section 10.2 (Piecewise constant functions) from the paper. -/

import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic
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
    . intro x y hxy
      exact hδ' (lt_of_lt_of_le hxy (min_le_left δ' (b / 2)))
  . intro h ε εpos
    obtain ⟨δ, δpos, _, hδ⟩ := h ε εpos
    use δ
end section

/- TODO: might be generalized. -/
lemma closeSmoothApprox {f : ℝ → ℂ} (unicontf : UniformContinuous f) {ε : ℝ} (εpos : ε > 0):
    ∃ (f₀ : ℝ → ℂ), ContDiff ℝ ⊤ f₀ ∧ ∀ x, Complex.abs (f x - f₀ x) ≤ ε := by
  obtain ⟨δ, δpos, hδ⟩ := (Metric.uniformContinuous_iff.mp unicontf) ε εpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ/2, δ, by linarith, by linarith⟩
  let f_0 := MeasureTheory.convolution (φ.normed MeasureTheory.volume) f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
  use f_0
  constructor
  . /-TODO: improve this-/
    apply HasCompactSupport.contDiff_convolution_left
    . exact ContDiffBump.hasCompactSupport_normed φ
    . exact ContDiffBump.contDiff_normed φ
    . refine Continuous.locallyIntegrable ?h.left.hg.hf
      exact unicontf.continuous
  . intro x
    rw [← Complex.dist_eq, dist_comm]
    apply ContDiffBump.dist_normed_convolution_le
    . exact unicontf.continuous.aestronglyMeasurable
    . intro y hy
      simp at hy
      exact (hδ hy).le

/- Slightly different version-/
lemma closeSmoothApproxPeriodic {f : ℝ → ℂ} (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) {ε : ℝ} (εpos : ε > 0):
    ∃ (f₀ : ℝ → ℂ), ContDiff ℝ ⊤ f₀ ∧ Function.Periodic f₀ (2 * Real.pi) ∧ ∀ x, Complex.abs (f x - f₀ x) ≤ ε := by
  obtain ⟨δ, δpos, hδ⟩ := (Metric.uniformContinuous_iff.mp unicontf) ε εpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ/2, δ, by linarith, by linarith⟩
  set f₀ := MeasureTheory.convolution (φ.normed MeasureTheory.volume) f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with f₀def
  use f₀
  constructor
  . /-TODO: improve this-/
    apply HasCompactSupport.contDiff_convolution_left
    . exact ContDiffBump.hasCompactSupport_normed φ
    . exact ContDiffBump.contDiff_normed φ
    . refine Continuous.locallyIntegrable ?h.left.hg.hf
      exact unicontf.continuous
  constructor
  . /-TODO: improve this. -/
    intro x
    rw [f₀def, MeasureTheory.convolution, MeasureTheory.convolution]
    congr
    ext t
    congr 1
    convert periodicf (x - t) using 2
    ring
  . intro x
    rw [← Complex.dist_eq, dist_comm]
    apply ContDiffBump.dist_normed_convolution_le
    . exact unicontf.continuous.aestronglyMeasurable
    . intro y hy
      simp at hy
      exact (hδ hy).le

/- Inspired by mathlib : NNReal.summable_of_le-/
lemma Real.summable_of_le {β : Type} {f g : β → ℝ} (hgpos : 0 ≤ g) (hgf : ∀ (b : β), g b ≤ f b) (summablef : Summable f) :
    Summable g := by
  exact Summable.of_nonneg_of_le hgpos hgf summablef
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
    . simp [h]
      exact hgf i h
  apply Real.summable_of_le hgpos this

  let s : Finset ℤ := {0}
  rw [←s.summable_compl_iff]
  apply (summable_congr _).mpr (s.summable_compl_iff.mpr summablef)
  intro ⟨b, hb⟩
  simp
  rw [mem_singleton] at hb
  rw [f'def]
  simp [hb]


  lemma continuous_bounded {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 (2 * Real.pi))) : ∃ C, ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (f x) ≤ C := by
    have interval_compact := (@isCompact_Icc ℝ _ _ _ 0 (2 * Real.pi))
    have abs_f_continuousOn := Complex.continuous_abs.comp_continuousOn hf
    obtain ⟨a, _, ha⟩ := interval_compact.exists_isMaxOn (Set.nonempty_Icc.mpr Real.two_pi_pos.le) abs_f_continuousOn
    set C := Complex.abs (f a) with C_def
    use C
    intro x hx
    rw [C_def]
    rw [isMaxOn_iff] at ha
    exact ha x hx

/-TODO: might be generalized assumptions might be weakened, and constant given explicitely -/
lemma fourierCoeffOn_bound {f : ℝ → ℂ} (f_continuous : Continuous f) : ∃ C, ∀ n, Complex.abs (fourierCoeffOn Real.two_pi_pos f n) ≤ C := by
  obtain ⟨C, f_bounded⟩ := continuous_bounded f_continuous.continuousOn
  use C
  intro n
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, mul_inv_rev, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv, map_mul, map_inv₀, Complex.abs_ofReal, Complex.abs_ofNat]
  field_simp
  rw [abs_of_nonneg Real.pi_pos.le, mul_comm Real.pi, div_le_iff Real.two_pi_pos, ←Complex.norm_eq_abs]
  calc ‖∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * n * x / (2 * Real.pi))) * f x‖
    _ = ‖∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), (starRingEnd ℂ) (Complex.exp (Complex.I * n * x)) * f x‖ := by
      congr
      ext x
      congr
      ring_nf
      rw [mul_comm, ←mul_assoc, ←mul_assoc, ←mul_assoc, inv_mul_cancel]
      . ring
      . simp
        exact Real.pi_pos.ne.symm
    _ ≤ ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), ‖(starRingEnd ℂ) (Complex.exp (Complex.I * n * x)) * f x‖ := by
      apply intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ = ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), ‖(Complex.exp (Complex.I * n * x)) * f x‖ := by
      simp
    _ = ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), ‖f x‖ := by
      congr
      ext x
      simp
      rw [mul_assoc, mul_comm Complex.I]
      norm_cast
      rw [Complex.abs_exp_ofReal_mul_I]
      ring
    _ ≤ ∫ (_ : ℝ) in (0 : ℝ)..(2 * Real.pi), C := by
      apply intervalIntegral.integral_mono_on
      . exact Real.two_pi_pos.le
      . rw [IntervalIntegrable.intervalIntegrable_norm_iff]
        /-Could specify these two specific requirements intead of f_continuous. -/
        . apply f_continuous.intervalIntegrable
        . apply f_continuous.aestronglyMeasurable
      . apply intervalIntegrable_const
      . intro x hx
        rw [Complex.norm_eq_abs]
        exact f_bounded x hx
    _ = C * (2 * Real.pi) := by
      rw [intervalIntegral.integral_const]
      simp
      ring

/-TODO: Assumptions might be weakened. -/
lemma periodic_deriv {𝕜 : Type} [NontriviallyNormedField 𝕜] {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {T : 𝕜} (diff_f : ContDiff 𝕜 1 f) (periodic_f : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro x
  set g : 𝕜 → 𝕜 := fun x ↦ x + T with gdef
  have diff_g : Differentiable 𝕜 g := by
    apply differentiable_id.add_const
  have : deriv (f ∘ g) x = ((deriv f) ∘ g) x := by
    calc deriv (f ∘ g) x
      _ = deriv g x • deriv f (g x) := deriv.scomp x (diff_f.differentiable (by norm_num)).differentiableAt diff_g.differentiableAt
      _ = deriv f (g x) := by rw [gdef, deriv_add_const, deriv_id'']; simp
  rw [gdef] at this
  simp at this
  convert this.symm
  ext y
  simp
  exact (periodic_f y).symm

/-TODO: might be generalized. -/
/-TODO: Assumption periodicf is probably not needed actually. -/
lemma fourierCoeffOn_ContDiff_two_bound {f : ℝ → ℂ} (periodicf : Function.Periodic f (2 * Real.pi)) (fdiff : ContDiff ℝ 2 f): ∃ C, ∀ n ≠ 0, Complex.abs (fourierCoeffOn Real.two_pi_pos f n) ≤ C / n ^ 2 := by
--#check IsCompact.exists_isMaxOn
  --TODO: improve this
  have h : ∀ x ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt f (deriv f x) x := by
    intro x _
    rw [hasDerivAt_deriv_iff]
    apply fdiff.differentiable (by norm_num)
  have h' : ∀ x ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x _
    rw [hasDerivAt_deriv_iff]
    apply (contDiff_succ_iff_deriv.mp fdiff).2.differentiable (by norm_num)
  /-Get better representation for the fourier coefficients of f. -/
  have fourierCoeffOn_eq {n : ℤ} (hn : n ≠ 0): (fourierCoeffOn Real.two_pi_pos f n) = - 1 / (n^2) * fourierCoeffOn Real.two_pi_pos (fun x ↦ deriv (deriv f) x) n := by
    rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h, fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h']
    . have := periodicf 0
      simp at this
      simp [this]
      have periodic_deriv_f : Function.Periodic (deriv f) (2 * Real.pi) := periodic_deriv (fdiff.of_le one_le_two) periodicf
      have := periodic_deriv_f 0
      simp at this
      simp [this]
      ring_nf
      simp
      left
      rw [mul_inv_cancel, one_mul]
      simp
      exact Real.pi_pos.ne.symm
    . apply Continuous.intervalIntegrable
      exact (contDiff_one_iff_deriv.mp (contDiff_succ_iff_deriv.mp fdiff).2).2
    . apply Continuous.intervalIntegrable
      exact (contDiff_succ_iff_deriv.mp fdiff).2.continuous

  obtain ⟨C, hC⟩ := fourierCoeffOn_bound (contDiff_one_iff_deriv.mp (contDiff_succ_iff_deriv.mp fdiff).2).2
  use C
  intro n hn
  rw [fourierCoeffOn_eq hn]
  simp only [Nat.cast_one, Int.cast_pow, map_mul, map_div₀, map_neg_eq_map, map_one, map_pow,
    Complex.abs_intCast, sq_abs, one_div]
  rw [div_eq_mul_inv, mul_comm]
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
      . congr
        ext n
        simp only [Int.ofNat_eq_coe, mem_Ioo, mem_Icc]
        push_cast
        rw [Int.lt_add_one_iff, neg_add, ←sub_eq_add_neg, Int.sub_one_lt_iff]
      . norm_num
        linarith
      . norm_num
        linarith
    rw [this, sum_insert, sum_insert, ih, ←add_assoc]
    symm
    rw [sum_range_succ, add_comm, ←add_assoc, add_comm]
    simp
    rw [add_comm]
    . simp
    . norm_num
      linarith


--theorem HasSum.nat_add_neg {f : ℤ → M} (hf : HasSum f m) :
--    HasSum (fun n : ℕ ↦ f n + f (-n)) (m + f 0) := by

/-TODO: Weaken statement to pointwise convergence to simplify proof?-/
lemma fourierConv_ofTwiceDifferentiable {f : ℝ → ℂ} (periodicf : Function.Periodic f (2 * Real.pi)) (fdiff : ContDiff ℝ 2 f) {ε : ℝ} (εpos : ε > 0) :
    ∃ N₀, ∀ N > N₀, ∀ x ∈ Set.Ico 0 (2 * Real.pi), Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
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
      . rw [maj_def, Ceq0]
        simp
        exact summable_zero
      . rw [← summable_div_const_iff Ceq0]
        convert Real.summable_one_div_int_pow.mpr one_lt_two using 1
        rw [maj_def]
        ext i
        simp
        rw [mul_div_cancel_right₀]
        exact Ceq0
    rw [summable_congr @fourierCoeff_correspondence, ←summable_norm_iff]

    apply summable_of_le_on_nonzero _ _ summable_maj
    . intro i
      simp
    . intro i ine0
      rw [maj_def, Complex.norm_eq_abs]
      field_simp
      exact hC i ine0

  have := int_sum_nat function_sum
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at this
  have := this ε εpos
  rw [Filter.eventually_atTop] at this
  obtain ⟨N₀, hN₀⟩ := this
  use N₀
  intro N hN x hx
  have := hN₀ N hN.le x
  rw [Complex.dist_eq] at this
  simp only [ContinuousMap.coe_sum, sum_apply] at this
  convert this.le using 2
  congr 1
  . rw [g_def]
    simp
    rw [AddCircle.liftIco_coe_apply]
    rw [zero_add]
    exact hx
  . rw [partialFourierSum]
    congr
    ext n
    rw [fourierCoeff_correspondence]
    simp
