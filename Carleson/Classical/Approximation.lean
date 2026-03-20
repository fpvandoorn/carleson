module

public import Carleson.Classical.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.PSeries

@[expose] public section

/- This file contains the arguments from section 11.2 (smooth functions) from the blueprint. -/

noncomputable section

open Finset Real

local notation "S_" => partialFourierSum

open scoped ContDiff

lemma close_smooth_approx_periodic {f : ℝ → ℂ} (unicontf : UniformContinuous f)
  (periodicf : f.Periodic (2 * π)) {ε : ℝ} (εpos : ε > 0) :
    ∃ (f₀ : ℝ → ℂ), ContDiff ℝ ∞ f₀ ∧ f₀.Periodic (2 * π) ∧
      ∀ x, ‖f x - f₀ x‖ ≤ ε := by
  obtain ⟨δ, δpos, hδ⟩ := (Metric.uniformContinuous_iff.mp unicontf) ε εpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ/2, δ, by linarith, by linarith⟩
  set f₀ := MeasureTheory.convolution (φ.normed MeasureTheory.volume) f
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with f₀def
  refine ⟨f₀, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact HasCompactSupport.contDiff_convolution_left _ φ.hasCompactSupport_normed
      φ.contDiff_normed unicontf.continuous.locallyIntegrable
  · rw [f₀def, MeasureTheory.convolution, MeasureTheory.convolution]
    congr with t
    congr 1
    convert periodicf (x - t) using 2
    ring
  · rw [← Complex.dist_eq, dist_comm]
    exact ContDiffBump.dist_normed_convolution_le unicontf.continuous.aestronglyMeasurable
      fun y hy ↦ (hδ hy).le

-- local lemma
lemma summable_of_le_on_nonzero {f g : ℤ → ℝ} (hgpos : 0 ≤ g) (hgf : ∀ i ≠ 0, g i ≤ f i)
    (summablef : Summable f) : Summable g := by
  set f' : ℤ → ℝ := fun i ↦ if i = 0 then g i else f i with f'def
  have : ∀ i, g i ≤ f' i := by
    intro i
    rw [f'def]
    by_cases h : i = 0
    · simp [h]
    · simp only [h]; exact hgf i h
  apply Summable.of_nonneg_of_le hgpos this
  let s : Finset ℤ := {0}
  rw [← s.summable_compl_iff]
  refine (summable_congr fun ⟨b, hb⟩ ↦ ?_).mpr (s.summable_compl_iff.mpr summablef)
  rw [mem_singleton] at hb
  exact if_neg hb

lemma continuous_bounded {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 (2 * π))) :
    ∃ C, ∀ x ∈ Set.Icc 0 (2 * π), ‖f x‖ ≤ C := by
  have interval_compact := (isCompact_Icc (a := 0) (b := 2 * π))
  obtain ⟨a, _, ha⟩ := interval_compact.exists_isMaxOn (Set.nonempty_Icc.mpr Real.two_pi_pos.le)
    (continuous_norm.comp_continuousOn hf)
  refine ⟨‖f a‖, fun x hx ↦ ?_⟩
  rw [isMaxOn_iff] at ha
  exact ha x hx

/-TODO: might be generalized assumptions might be weakened, and constant given explicitely -/
lemma fourierCoeffOn_bound {f : ℝ → ℂ} (f_continuous : Continuous f) :
    ∃ C, ∀ n, ‖fourierCoeffOn Real.two_pi_pos f n‖ ≤ C := by
  obtain ⟨C, f_bounded⟩ := continuous_bounded f_continuous.continuousOn
  refine ⟨C, fun n ↦ ?_⟩
  simp only [fourierCoeffOn_eq_integral, sub_zero, one_div, mul_inv_rev, Complex.real_smul,
    Complex.norm_real, Complex.norm_mul, norm_eq_abs, abs_mul, abs_inv, Nat.abs_ofNat]
  field_simp
  rw [abs_of_nonneg pi_pos.le, mul_comm π]
  calc
    _ = ‖∫ (x : ℝ) in (0 : ℝ)..(2 * π), (starRingEnd ℂ) (Complex.exp (2 * π * Complex.I * n * x / (2 * π))) * f x‖ := by simp
    _ = ‖∫ (x : ℝ) in (0 : ℝ)..(2 * π), (starRingEnd ℂ) (Complex.exp (Complex.I * n * x)) * f x‖ := by
      congr with x
      congr
      ring_nf
      rw [mul_comm, ←mul_assoc, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀]
      · ring
      · simp [pi_pos.ne.symm]
    _ ≤ ∫ (x : ℝ) in (0 : ℝ)..(2 * π), ‖(starRingEnd ℂ) (Complex.exp (Complex.I * n * x)) * f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ = ∫ (x : ℝ) in (0 : ℝ)..(2 * π), ‖(Complex.exp (Complex.I * n * x)) * f x‖ := by simp
    _ = ∫ (x : ℝ) in (0 : ℝ)..(2 * π), ‖f x‖ := by
      congr with x
      simp only [norm_mul]
      rw_mod_cast [mul_assoc, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
      ring
    _ ≤ ∫ (_ : ℝ) in (0 : ℝ)..(2 * π), C := by
      refine intervalIntegral.integral_mono_on Real.two_pi_pos.le ?_ intervalIntegrable_const
        fun x hx ↦ f_bounded x hx
      /-Could specify `aestronglyMeasurable` and `intervalIntegrable` intead of `f_continuous`. -/
      exact IntervalIntegrable.intervalIntegrable_norm_iff f_continuous.aestronglyMeasurable |>.mpr
        (f_continuous.intervalIntegrable ..)
    _ = _ := by simp

/-TODO: Assumptions might be weakened. -/
lemma periodic_deriv {𝕜 : Type} [NontriviallyNormedField 𝕜] {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {T : 𝕜} (diff_f : ContDiff 𝕜 1 f) (periodic_f : f.Periodic T) : (deriv f).Periodic T := by
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
/-TODO: The assumption periodicf is probably not needed actually. -/
lemma fourierCoeffOn_ContDiff_two_bound {f : ℝ → ℂ} (periodicf : f.Periodic (2 * π)) (fdiff : ContDiff ℝ 2 f) :
    ∃ C, ∀ n ≠ 0, ‖fourierCoeffOn Real.two_pi_pos f n‖ ≤ C / n ^ 2 := by
  have h : ∀ x ∈ Set.uIcc 0 (2 * π), HasDerivAt f (deriv f x) x := by
    intro x _
    rw [hasDerivAt_deriv_iff]
    exact fdiff.differentiable (by norm_num) _
  have h' : ∀ x ∈ Set.uIcc 0 (2 * π), HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x _
    rw [hasDerivAt_deriv_iff]
    exact ((contDiff_succ_iff_deriv (n := 1)).mp fdiff).2.2.differentiable (by norm_num) _
  /-Get better representation for the fourier coefficients of f. -/
  have fourierCoeffOn_eq {n : ℤ} (hn : n ≠ 0): (fourierCoeffOn Real.two_pi_pos f n) = - 1 / (n^2) * fourierCoeffOn Real.two_pi_pos (fun x ↦ deriv (deriv f) x) n := by
    rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h, fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h']
    · have h1 := periodicf 0
      have periodic_deriv_f : (deriv f).Periodic (2 * π) := periodic_deriv (fdiff.of_le one_le_two) periodicf
      have h2 := periodic_deriv_f 0
      simp at h1 h2
      simp [h1, h2]
      ring_nf
      simp [pi_pos.ne.symm]
    · exact (contDiff_one_iff_deriv.mp ((contDiff_succ_iff_deriv (n := 1)).mp
        fdiff).2.2).2.intervalIntegrable ..
    · exact ((contDiff_succ_iff_deriv (n := 1)).mp fdiff).2.2.continuous.intervalIntegrable ..
  obtain ⟨C, hC⟩ := fourierCoeffOn_bound (contDiff_one_iff_deriv.mp
    ((contDiff_succ_iff_deriv (n := 1)).mp fdiff).2.2).2
  refine ⟨C, fun n hn ↦ ?_⟩
  simp only [fourierCoeffOn_eq hn, Complex.norm_mul, Complex.norm_div, norm_neg, norm_one, norm_pow,
    Complex.norm_intCast, sq_abs, one_div, div_eq_mul_inv C, mul_comm C]
  gcongr
  exact hC n

open Topology Filter

/-TODO : Assumptions might be weakened-/
lemma int_sum_nat {β : Type*} [AddCommGroup β] [TopologicalSpace β] [ContinuousAdd β] {f : ℤ → β} {a : β} (hfa : HasSum f a) :
    Filter.Tendsto (fun N ↦ ∑ n ∈ Icc (-Int.ofNat ↑N) N, f n) Filter.atTop (𝓝 a) := by
  have := Filter.Tendsto.add_const (- (f 0)) hfa.nat_add_neg.tendsto_sum_nat
  simp only [add_neg_cancel_right] at this
  /- Need to start at 1 instead of zero for the base case to be true. -/
  rw [←tendsto_add_atTop_iff_nat 1] at this
  convert this using 1
  ext N
  induction N with
  | zero => simp
  | succ N ih =>
    have : Icc (- Int.ofNat (N.succ)) (N.succ) = insert (↑(N.succ)) (insert (-Int.ofNat (N.succ)) (Icc (-Int.ofNat N) N)) := by
      rw [←Ico_insert_right, ←Ioo_insert_left]
      · congr 2 with n
        simp only [Int.ofNat_eq_natCast, mem_Ioo, mem_Icc]
        push_cast
        rw [Int.lt_add_one_iff, neg_add, ←sub_eq_add_neg, Int.sub_one_lt_iff]
      · norm_num
        linarith
      · norm_num
        linarith
    rw [this, sum_insert, sum_insert, ih, ← add_assoc]
    · symm
      rw [sum_range_succ, add_comm, ←add_assoc, add_comm]
      simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg, Nat.succ_eq_add_one,
        Int.ofNat_eq_natCast, add_comm]
    · simp
    · norm_num
      linarith

lemma fourierConv_ofTwiceDifferentiable {f : ℝ → ℂ} (periodicf : f.Periodic (2 * π))
    (fdiff : ContDiff ℝ 2 f) {ε : ℝ} (εpos : ε > 0) :
    ∃ N₀, ∀ N > N₀, ∀ x ∈ Set.Icc 0 (2 * π), ‖f x - S_ N f x‖ ≤ ε := by
  have fact_two_pi_pos : Fact (0 < 2 * π) := by
    rw [fact_iff]
    exact Real.two_pi_pos
  set g : C(AddCircle (2 * π), ℂ) := ⟨AddCircle.liftIco (2*π) 0 f, AddCircle.liftIco_continuous ((periodicf 0).symm) fdiff.continuous.continuousOn⟩ with g_def
  have two_pi_pos' : 0 < 0 + 2 * π := by linarith [Real.two_pi_pos]
  have fourierCoeff_correspondence {i : ℤ} : fourierCoeff g i = fourierCoeffOn two_pi_pos' f i := fourierCoeff_liftIco_eq f i
  simp only [zero_add] at fourierCoeff_correspondence
  have function_sum : HasSum (fun (i : ℤ) => fourierCoeff g i • fourier i) g := by
    apply hasSum_fourier_series_of_summable
    obtain ⟨C, hC⟩ := fourierCoeffOn_ContDiff_two_bound periodicf fdiff
    set maj : ℤ → ℝ := fun i ↦ 1 / (i ^ 2) * C with maj_def
    have summable_maj : Summable maj := by
      by_cases Ceq0 : C = 0
      · simp [maj_def, Ceq0, one_div, mul_zero, summable_zero]
      · rw [← summable_div_const_iff Ceq0]
        convert Real.summable_one_div_int_pow.mpr one_lt_two using 1
        simp [maj_def, mul_div_cancel_right₀, Ceq0]
    rw [summable_congr @fourierCoeff_correspondence, ←summable_norm_iff]
    apply summable_of_le_on_nonzero _ _ summable_maj <;> intro i
    · simp
    · intro ine0; simpa only [maj_def, one_div_mul_eq_div] using hC i ine0
  have := int_sum_nat function_sum
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at this
  have := this ε εpos
  rw [Filter.eventually_atTop] at this
  obtain ⟨N₀, hN₀⟩ := this
  refine ⟨N₀, fun N hN x hx ↦ ?_⟩
  have := hN₀ N hN.le x
  simp only [Complex.dist_eq, ContinuousMap.coe_sum, sum_apply] at this
  convert this.le using 2
  congr 1
  · rw [g_def, ContinuousMap.coe_mk]
    by_cases h : x = 2 * π
    · conv => lhs; rw [h, ← zero_add  (2 * π), periodicf]
      have := AddCircle.coe_add_period (2 * π) 0
      rw [zero_add] at this
      rw [h, this, AddCircle.liftIco_coe_apply]
      simp [pi_pos]
    · have : x ∈ Set.Ico 0 (2 * π) := ⟨hx.1, lt_of_le_of_ne hx.2 h⟩
      simp [AddCircle.liftIco_coe_apply, this]
  · simp [partialFourierSum, fourierCoeff_correspondence]
