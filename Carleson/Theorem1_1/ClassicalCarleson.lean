import Carleson.Carleson
import Carleson.HomogeneousType

--import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.PSeries

--TODO: add local notation for f₀


noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

--def K : ℝ → ℝ → ℂ := fun x y ↦ 1 / (x - y)




#check Complex.abs

#check Finset.range

#check AddCircle (2 * Real.pi)

--variable [IsSpaceOfHomogeneousType ℝ 2] (μ : MeasureTheory.Measure ℝ)

open BigOperators
open Finset

#check fourier
--def stdCircle : AddCircle (2 * Real.pi)

#check Finset.Icc

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


def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
#check partialFourierSum

variable {f : ℝ → ℂ} {N : ℕ}

--TODO : add reasonable notation
--local notation "S_" => partialFourierSum f

/- TODO: might be generalized. -/
lemma closeSmoothApprox {f : ℝ → ℂ} (unicontf : UniformContinuous f) {ε : ℝ} (εpos : ε > 0) [HasContDiffBump ℝ] :
    ∃ (f₀ : ℝ → ℂ), ContDiff ℝ ⊤ f₀ ∧ ∀ x, Complex.abs (f x - f₀ x) ≤ ε := by
  obtain ⟨δ, δpos, hδ⟩ := (Metric.uniformContinuous_iff.mp unicontf) ε εpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ/2, δ, by linarith, by linarith⟩
  let f_0 := convolution (φ.normed MeasureTheory.volume) f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
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

/-TODO: might go to mathlib-/

--def fourierOn : Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑x / ↑T)

/-
/-Adapted from hasSum_fourier_series_of_summable in mathlib. -/
theorem hasSum_fourier_series_of_summable'  {a : ℝ} {b : ℝ} (hab : a < b) {f : ℝ → ℂ} (h : Summable (fourierCoeffOn hab f)) :
    HasSum (fun i => fourierCoeffOn hab f i • fourier i) f := by
  have sum_L2 := hasSum_fourier_series_L2 (toLp (E := ℂ) 2 haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one]
  exact h.norm
-/

/-Adapted from mathlib. -/
theorem has_pointwise_sum_fourier_series_of_summable' {T : ℝ} [hT : Fact (0 < T)] {f : C(AddCircle T, ℂ)}
  (h : Summable (fourierCoeff ⇑f)) (x : AddCircle T) : HasSum (fun i ↦ fourierCoeff (⇑f) i • (fourier i) x) (f x)
 := by
  have := (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_fourier_series_of_summable h)
  exact this
  --convert (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_fourier_series_of_summable h)

/- Inspired by mathlib : NNReal.summable_of_le-/
lemma Real.summable_of_le {β : Type} {f g : β → ℝ} (hgpos : 0 ≤ g) (hgf : ∀ (b : β), g b ≤ f b) (summablef : Summable f) :
    Summable g := by
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

--open intervalIntegral

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
  obtain ⟨C, f_bounded⟩  := continuous_bounded f_continuous.continuousOn
  use C
  intro n
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, mul_inv_rev, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv, map_mul, map_inv₀, Complex.abs_ofReal, Complex.abs_ofNat]
  --rw [mul_assoc (2 * Real.pi)]
  field_simp
  rw [abs_of_nonneg Real.pi_pos.le, mul_comm Real.pi, div_le_iff Real.two_pi_pos, ←Complex.norm_eq_abs]
  --calc ‖@intervalIntegral ℂ Complex.instNormedAddCommGroupComplex NormedSpace.complexToReal (fun x ↦ (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * ↑x / (2 * ↑Real.pi))) * f x) 0 (2 * Real.pi) MeasureTheory.volume‖
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
    _ ≤ ∫ (x : ℝ) in (0 : ℝ)..(2 * Real.pi), C := by
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

/-TODO: might be generalized. -/
/-TODO: Assumption periodicf is probably not needed actually. -/
lemma fourierCoeffOn_ContDiff_two_bound {f : ℝ → ℂ} (periodicf : Function.Periodic f (2 * Real.pi)) (fdiff : ContDiff ℝ 2 f): ∃ C, ∀ n ≠ 0, Complex.abs (fourierCoeffOn Real.two_pi_pos f n) ≤ C / n ^ 2 := by
--#check IsCompact.exists_isMaxOn
  --TODO: improve this
  have h : ∀ x ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [hasDerivAt_deriv_iff]
    apply fdiff.differentiable (by norm_num)
  have h' : ∀ x ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x hx
    rw [hasDerivAt_deriv_iff]
    apply (contDiff_succ_iff_deriv.mp fdiff).2.differentiable (by norm_num)
  /-Get better representation for the fourier coefficients of f. -/
  have fourierCoeffOn_eq {n : ℤ} (hn : n ≠ 0): (fourierCoeffOn Real.two_pi_pos f n) = - 1 / (n^2) * fourierCoeffOn Real.two_pi_pos (fun x ↦ deriv (deriv f) x) n := by
    rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h, fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn h']
    . have := periodicf 0
      simp at this
      simp [this]
      have periodic_deriv_f : Function.Periodic (deriv f) (2 * Real.pi) := by
        sorry
      have := periodic_deriv_f 0
      simp at this
      simp [this]
      --field_simp
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


/-TODO: Weaken statement to pointwise convergence to simplify proof?-/
lemma fourierConv_ofTwiceDifferentiable {f : ℝ → ℂ} (periodicf : Function.Periodic f (2 * Real.pi)) (fdiff : ContDiff ℝ 2 f) {ε : ℝ} (εpos : ε > 0) : ∃ N₀, ∀ N > N₀, ∀ x, Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
  have fact_two_pi_pos : Fact (0 < 2 * Real.pi) := by
    rw [fact_iff]
    exact Real.two_pi_pos
  set g : C(AddCircle (2 * Real.pi), ℂ) := ⟨AddCircle.liftIco (2*Real.pi) 0 f, AddCircle.liftIco_continuous ((periodicf 0).symm) fdiff.continuous.continuousOn⟩ with g_def
  have two_pi_pos' : 0 < 0 + 2 * Real.pi := by linarith [Real.two_pi_pos]
  have fourierCoeff_correspondence {i : ℤ} : fourierCoeff g i = fourierCoeffOn two_pi_pos' f i := fourierCoeff_liftIco_eq f i
  simp at fourierCoeff_correspondence
  have : HasSum (fun (i : ℤ) => fourierCoeff g i • fourier i) g := by
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
      norm_cast
      exact hC i ine0

  /-TODO: remove next line.-/
  have next_try := this.nat_add_neg.tendsto_sum_nat

  rw [HasSum, tendsto_atTop_nhds] at this
  obtain ⟨s, hs⟩ := this (Metric.ball g ε) (Metric.mem_ball_self εpos) (Metric.isOpen_ball)
  --apply Int.isUnit_iff_abs_eq
  by_cases h : s.Nonempty
  . use max (Int.natAbs (s.max' h)) (Int.natAbs (s.min' h))
    intro N hN
    have : s ≤ Icc (-Int.ofNat ↑N) N := by sorry
    have := hs (Icc (-Int.ofNat ↑N) N) this
    simp at this
    intro x
    have := ContinuousMap.dist_le_iff_of_nonempty.mp this.le x
    rw [←Complex.dist_eq, partialFourierSum]
    calc dist (f x) (∑ n in Icc (-Int.ofNat N) ↑N, fourierCoeffOn Real.two_pi_pos f n * (fourier n) ↑x)
    _ = dist ((∑ b in Icc (-↑N) ↑N, fourierCoeff g b • fourier b) x) (g x) := by
      rw [dist_comm]
      congr 1
      . simp
        congr
        ext n
        rw [fourierCoeff_correspondence]
      . --apply AddCircle.coe_equivIco_mk_apply
        rw [g_def]
        simp
        apply (AddCircle.liftIco_coe_apply _).symm
        --TODO: Add assumption or do something nice here.
        sorry
    _ ≤ ε := this
  . use 0
    sorry


/-
lemma fourierConv_ofTwiceDifferentiable' {f : (AddCircle (2 * Real.pi)) → ℂ} (fdiff : ContDiff (AddCircle (2 * Real.pi)) 2 f) {ε : ℝ} (εpos : ε > 0) : ∃ N₀, ∀ N > N₀, ∀ x, Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
  sorry
-/

#check fourierCoeff_liftIco_eq

--TODO : seems like theorem1_1 is actually Theorem 1.2 from the paper
theorem classical_carleson --{f : ℝ → ℂ}
  (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
  {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
  --need condition E ⊆ Set.Icc 0 (2 * Real.pi) to ensure the E has finite volume
  ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
  ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
  Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
    --Choose some δ.
    --TODO : use some scaled ε for the choose
    obtain ⟨δ, δpos, δltpi, hδ⟩ := (uniformContinuous_iff_bounded Real.pi_pos).mp unicontf (ε / 2) (by linarith)
    --definitions from section 10.1 depending on the choice of δ
    set K := Nat.floor ((2 * Real.pi) / δ) + 1 with Kdef
    have Kgt2 : (2 : ℝ) < K := by
      rw [Kdef]
      have : 2 < 2 * Real.pi / δ := (lt_div_iff δpos).mpr ((mul_lt_mul_left (by norm_num)).mpr δltpi)
      convert this.trans (Nat.lt_floor_add_one ((2 * Real.pi) / δ))
      simp
    let f₀ : ℝ → ℂ := fun x ↦ f ((2 * Real.pi * Int.floor ((K * x) / (2 * Real.pi))) / K)

    --TODO : correct size of N₀
    let N₀ := Nat.ceil (K^2 / ε^3)
    --Lemma 10.2 from the paper
    --changed interval to Icc to match the interval in the theorem
    have piecePartialFourierSumApprox {N : ℕ} (hN : N > N₀) :
      ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (f₀ x - partialFourierSum f₀ N x) ≤ ε / 4:= by
      -- use has_pointwise_sum_fourier_series_of_summable or hasSum_fourier_series_L2 from mathlib?
      -- search for more convergence theorems
      sorry
    --Lemma 10.3 from the paper
    --TODO : review measurability assumption
    --added subset assumption
    --changed interval to match the interval in the theorem
    /-
    have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      sSup {Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) | N : ℕ} ≤ ε / 4 := by
      sorry
    -/
    --simplified statement so that we do not have to worry about a sSup
    have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      ∀ N, Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) ≤ ε / 4 := by
      sorry
    obtain ⟨E₂, E₂subset, E₂measurable, E₂volume, hE₂⟩ := diffPartialFourierSums


    --TODO : change definition of E₁ to be able to prove this
    have E₁subset : E₁ ⊆ Set.Icc 0 (2 * Real.pi) := by
      rw [Set.iUnion_subset_iff]
      simp
      intro k klt x
      simp
      intro lex xle
      sorry

    --set E := E₁ ∪ E₂

    --Definition of E
    use E₁ ∪ E₂
    use Set.union_subset E₁subset E₂subset
    use E₁measurable.union E₂measurable
    constructor
    . calc MeasureTheory.volume.real (E₁ ∪ E₂)
      _ ≤ MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := by apply MeasureTheory.measureReal_union_le
      _ ≤ ε / 2 + ε / 2 := by
          apply add_le_add E₁volume E₂volume
      _ = ε := by simp
    . use N₀
      intro x hx N NgtN₀
      --use "telescope" sum
      calc Complex.abs (f x - partialFourierSum f N x)
      _ = Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x) + (partialFourierSum f₀ N x - partialFourierSum f N x)) := by congr; ring
      _ ≤ Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x)) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
        apply AbsoluteValue.add_le
      _ ≤ Complex.abs (f x - f₀ x) + Complex.abs (f₀ x - partialFourierSum f₀ N x) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
        apply add_le_add_right
        apply AbsoluteValue.add_le
      _ ≤ (ε / 2) + (ε / 4) + (ε/4) := by
        gcongr
        . -- here, we use the definitions of δ, K and f₀
          apply le_of_lt
          apply hδ
          rw [Real.dist_eq]
          calc |x - 2 * Real.pi * ⌊K * x / (2 * Real.pi)⌋ / K|
          _ = |2 * Real.pi * (K * x / (2 * Real.pi)) / K - 2 * Real.pi * ⌊K * x / (2 * Real.pi)⌋ / K| := by congr; field_simp; ring
          _ = |2 * Real.pi * (K * x / (2 * Real.pi) - ⌊K * x / (2 * Real.pi)⌋) / K| := by
            ring_nf
          _ = 2 * Real.pi * |K * x / (2 * Real.pi) - ⌊K * x / (2 * Real.pi)⌋| / K := by
            rw [abs_div, abs_mul, abs_eq_self.mpr Real.two_pi_pos.le, abs_eq_self.mpr ((zero_lt_two).trans Kgt2).le]
          _ ≤ 2 * Real.pi * 1 / K := by
            apply (div_le_div_right ((zero_lt_two).trans Kgt2)).mpr
            apply (mul_le_mul_left Real.two_pi_pos).mpr
            rw [abs_eq_self.mpr]
            apply le_of_lt
            rw [sub_lt_iff_lt_add, add_comm]
            apply Int.lt_floor_add_one
            rw [le_sub_iff_add_le, zero_add]
            apply Int.floor_le
          _ < δ := by
            rw [div_lt_iff, mul_one, ← div_lt_iff' δpos]
            . push_cast
              apply Nat.lt_floor_add_one
            exact (zero_lt_two).trans Kgt2
        . have : x ∈ Set.Icc 0 (2 * Real.pi) \ E₁ := ⟨hx.1, fun xE₁ ↦ hx.2 (Set.mem_union_left E₂ xE₁)⟩
          apply piecePartialFourierSumApprox NgtN₀ x this
        . have : x ∈ Set.Icc 0 (2 * Real.pi) \ E₂ := ⟨hx.1, fun xE₂ ↦ hx.2 (Set.mem_union_right E₁ xE₂)⟩
          apply hE₂ x this N
      _ ≤ ε := by linarith


#check classical_carleson
