/- This file contains the proof of the classical Carleson theorem from Section 11.1. -/

import Carleson.Classical.Approximation
import Carleson.Classical.ControlApproximationEffect

import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory Real

noncomputable section

local notation "S_" => partialFourierSum

/- Theorem 1.1 (Classical Carleson) -/
theorem exceptional_set_carleson {f : ℝ → ℂ}
    (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π))
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ E ⊆ Set.Icc 0 (2 * π), MeasurableSet E ∧ volume.real E ≤ ε ∧
    ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * π)) \ E, ∀ N > N₀,
    ‖f x - S_ N f x‖ ≤ ε := by
  set ε' := ε / 4 / C_control_approximation_effect ε with ε'def
  have ε'pos : ε' > 0 := div_pos (div_pos εpos (by norm_num))
    (C_control_approximation_effect_pos εpos)

  /- Approximate f by a smooth f₀. -/
  have unicont_f : UniformContinuous f := periodic_f.uniformContinuous_of_continuous
    Real.two_pi_pos cont_f.continuousOn
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ := close_smooth_approx_periodic unicont_f periodic_f ε'pos
  have ε4pos : ε / 4 > 0 := by linarith
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀
    ((contDiff_infty.mp (contDiff_f₀)) 2) ε4pos
  set h := f₀ - f with hdef
  have h_measurable : Measurable h := (Continuous.sub contDiff_f₀.continuous cont_f).measurable
  have h_periodic : h.Periodic (2 * π) := periodic_f₀.sub periodic_f
  have h_bound : ∀ x, ‖h x‖ ≤ ε' := by
    intro x
    simp only [hdef, Pi.sub_apply, Complex.norm_eq_abs]
    rw [← Complex.dist_eq, dist_comm, Complex.dist_eq]
    exact hf₀ x

  /- Control approximation effect: Get a bound on the partial Fourier sums of h. -/
  obtain ⟨E, Esubset, Emeasurable, Evolume, hE⟩ := control_approximation_effect εpos ε'pos
    h_measurable h_periodic h_bound

  /- This is a classical "epsilon third" argument. -/
  use E, Esubset, Emeasurable, Evolume, N₀
  intro x hx N NgtN₀
  calc ‖f x - S_ N f x‖
  _ = ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x) + (S_ N f₀ x - S_ N f x)‖ := by ring_nf
  _ ≤ ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x)‖ + ‖S_ N f₀ x - S_ N f x‖ := norm_add_le ..
  _ ≤ ‖f x - f₀ x‖ + ‖f₀ x - S_ N f₀ x‖ + ‖S_ N f₀ x - S_ N f x‖ :=
    add_le_add_right (norm_add_le ..) _
  _ ≤ ε' + (ε / 4) + (ε / 4) := by
    gcongr
    · exact hf₀ x
    · exact hN₀ N NgtN₀ x hx.1
    · have := hE x hx N
      rw [hdef, partialFourierSum_sub (contDiff_f₀.continuous.intervalIntegrable 0 (2 * π))
        (cont_f.intervalIntegrable 0 (2 * π))] at this
      apply le_trans this
      rw [ε'def, mul_div_cancel₀ _ (C_control_approximation_effect_pos εpos).ne.symm]
  _ ≤ (ε / 2) + (ε / 4) + (ε / 4) := by
    gcongr
    rw [ε'def, div_div]
    apply div_le_div_of_nonneg_left εpos.le (by norm_num)
    rw [← div_le_iff₀' (by norm_num)]
    exact le_trans' (lt_C_control_approximation_effect εpos).le (by linarith [Real.two_le_pi])
  _ ≤ ε := by linarith



theorem carleson_interval {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
    ∀ᵐ x ∂volume.restrict (Set.Icc 0 (2 * π)),
      Filter.Tendsto (S_ · f x) Filter.atTop (nhds (f x)) := by

  let δ (k : ℕ) : ℝ := 1 / (k + 1) --arbitrary sequence tending to zero
  have δconv : Filter.Tendsto δ Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have δpos (k : ℕ) : 0 < δ k := by apply div_pos zero_lt_one (by linarith)

  -- ENNReal version to be comparable to volumes
  let δ' (k : ℕ) := ENNReal.ofReal (δ k)
  have δ'conv : Filter.Tendsto δ' Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal δconv

  set ε := fun k n ↦ (1 / 2) ^ n * 2⁻¹ * δ k with εdef
  have εpos (k n : ℕ) : 0 < ε k n := by positivity
  have εsmall (k : ℕ) {e : ℝ} (epos : 0 < e) : ∃ n, ε k n < e := by
    have : Filter.Tendsto (ε k) Filter.atTop (nhds 0) := by
      rw [εdef]
      simp_rw [mul_assoc]
      rw [← zero_mul (2⁻¹ * δ k)]
      apply Filter.Tendsto.mul_const
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    rw [Metric.tendsto_atTop] at this
    rcases (this e epos) with ⟨n, hn⟩
    use n
    convert (hn n (by simp))
    simp_rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (εpos k n).le]

  have δ'_eq {k : ℕ} : δ' k = ∑' n, ENNReal.ofReal (ε k n) := by
    rw [εdef]
    conv => rhs; pattern ENNReal.ofReal _; rw [ENNReal.ofReal_mul' (δpos k).le,
      ENNReal.ofReal_mul' (by norm_num), ENNReal.ofReal_pow (by norm_num)]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul' (by norm_num)]
    conv => pattern ENNReal.ofReal _; ring_nf; rw [ENNReal.ofReal_one]
    rw [one_mul]
    norm_num

  -- Main step: Apply exceptional_set_carleson to get a family of exceptional sets parameterized by ε.
  choose Eε hEε_subset _ hEε_measure hEε using (@exceptional_set_carleson f cont_f periodic_f)

  have Eεmeasure {ε : ℝ} (hε : 0 < ε) : volume (Eε hε) ≤ ENNReal.ofReal ε := by
    rw [ENNReal.le_ofReal_iff_toReal_le _ hε.le]
    · exact hEε_measure hε
    · rw [← lt_top_iff_ne_top]
      apply lt_of_le_of_lt (measure_mono (hEε_subset hε)) measure_Icc_lt_top

  -- Define exceptional sets parameterized by δ.
  let Eδ (k : ℕ) := ⋃ (n : ℕ), Eε (εpos k n)
  have Eδmeasure (k : ℕ) : volume (Eδ k) ≤ δ' k := by
    apply le_trans (measure_iUnion_le _)
    rw [δ'_eq]
    exact ENNReal.tsum_le_tsum (fun n ↦ Eεmeasure (εpos k n))

  -- Define final exceptional set.
  let E := ⋂ (k : ℕ), Eδ k

  -- Show that it has the desired property.
  have hE : ∀ x ∈ (Set.Icc 0 (2 * π)) \ E, Filter.Tendsto (S_ · f x) Filter.atTop (nhds (f x)) := by
    intro x hx
    rw [Set.diff_iInter, Set.mem_iUnion] at hx
    rcases hx with ⟨k,hk⟩
    rw [Set.diff_iUnion, Set.mem_iInter] at hk

    rw [Metric.tendsto_atTop']
    intro e epos
    rcases (εsmall k epos) with ⟨n, lt_e⟩

    rcases (hEε (εpos k n)) with ⟨N₀,hN₀⟩
    use N₀
    intro N hN
    rw [dist_comm, dist_eq_norm]
    exact (hN₀ x (hk n) N hN).trans_lt lt_e

  -- Show that is has measure zero.
  have Emeasure : volume E ≤ 0 := by
    have : ∀ k, volume E ≤ δ' k := by
      intro k
      apply le_trans' (Eδmeasure k)
      apply measure_mono
      apply Set.iInter_subset
    exact ge_of_tendsto' δ'conv this

  -- Use results to prove the statement.
  rw [ae_restrict_iff' measurableSet_Icc]
  apply le_antisymm _ (zero_le _)
  apply le_trans' Emeasure
  apply measure_mono
  intro x hx
  simp only [and_imp, Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_imp] at hx
  by_contra h
  exact hx.2 (hE x ⟨hx.1, h⟩)



section
open Pointwise

--TODO: might be generalized
lemma Function.Periodic.ae_of_ae_restrict {T : ℝ} (hT : 0 < T) {a : ℝ} {P : (x : ℝ) → Prop}
    (hP : Function.Periodic P T)
    (h : ∀ᵐ x ∂volume.restrict (Set.Ico a (a + T)), P x) : ∀ᵐ x, P x := by
  rw [ae_restrict_iff' measurableSet_Ico, ae_iff] at h
  set E_interval := {x | ¬(x ∈ Set.Ico a (a + T) → P x)} with E_interval_def
  -- Define exceptional set as countable union of translations of the exceptional set on the interval
  set E := ⋃ (k : ℤ), k • T +ᵥ E_interval with Edef
  have hE : E = {a | ¬P a} := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · intro h
      rcases h with ⟨k, hk⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, ← sub_eq_neg_add, E_interval_def] at hk
      simp only [and_imp, Classical.not_imp, Set.mem_setOf_eq, hP.sub_zsmul_eq k] at hk
      exact hk.2
    · dsimp
      rcases (hP.exists_mem_Ico' hT x a) with ⟨n, hn, hxn⟩
      rw [hxn]
      refine fun h ↦ ⟨n, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, ← sub_eq_neg_add, E_interval_def]
      simp only [and_imp, Classical.not_imp, Set.mem_setOf_eq]
      exact ⟨hn, h⟩
  -- The union still has measure zero
  have Emeasure : volume E = 0 := by
    rw [Edef, measure_iUnion_null]
    refine fun k ↦ measure_vadd_null h ..
  rw [ae_iff, ← hE]
  exact Emeasure

end section

/- Carleson's theorem asserting a.e. convergence of the partial Fourier sums for continous functions. -/
theorem classical_carleson {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
    ∀ᵐ x, Filter.Tendsto (S_ · f x) Filter.atTop (nhds (f x)) := by
  -- Reduce to a.e. convergence on [0,2π]
  apply @Function.Periodic.ae_of_ae_restrict _ Real.two_pi_pos 0
  · rw [Function.Periodic]
    intro x
    conv => pattern S_ _ _ _; rw [partialFourierSum_periodic]
    conv => pattern f _; rw [periodic_f]
  apply ae_restrict_of_ae_eq_of_ae_restrict Ico_ae_eq_Icc.symm
  rw [zero_add]

  -- Show a.e. convergence on [0,2π]
  exact carleson_interval cont_f periodic_f
