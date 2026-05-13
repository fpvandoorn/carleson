module

public import Carleson.Classical.Approximation
public import Carleson.Classical.ControlApproximationEffect

public section

/- This file contains the proof of the classical Carleson theorem from Section 11.1. -/

open MeasureTheory Real

noncomputable section

local notation "S_" => partialFourierSum

/- Theorem 1.1 (Classical Carleson) -/
theorem exceptional_set_carleson {f : ℝ → ℂ} (periodic_f : f.Periodic (2 * π))
  {q : ENNReal} (hq : 1 < q) (hf : MemLp f q (volume.restrict (Set.Ioc 0 (2 * π))))
  {δ ε : NNReal} (δpos : 0 < δ) (εpos : 0 < ε) :
    ∃ N₀, distribution (fun x ↦ ⨆ N > N₀, ‖f x - S_ N f x‖ₑ) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  set p := (min (3 / 2) q).toNNReal with p_def
  have : min (3 / 2) q ≠ ⊤ := by
    apply ne_of_lt
    rw [min_lt_iff]
    left
    refine ENNReal.div_lt_top (by simp) (by simp)
  have hp : p ∈ Set.Ioo 1 2 := by
    rw [p_def]
    simp only [Set.mem_Ioo]
    constructor
    · rw [← ENNReal.coe_lt_iff_lt_toNNReal this, lt_min_iff]
      simp only [ENNReal.coe_one]
      symm
      use hq
      exact (ENNReal.lt_div_iff_mul_lt (by simp) (by simp)).mpr (by simp; norm_num)
    · apply ENNReal.toNNReal_lt_of_lt_coe
      simp only [ENNReal.coe_ofNat, inf_lt_iff]
      left
      refine ENNReal.div_lt_of_lt_mul ?_
      norm_num
  have hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
    apply MemLp.mono_exponent hf
    rw [p_def, ENNReal.coe_toNNReal this]
    exact min_le_right _ _
  have one_lt_p : (1 : ENNReal) < p := by simp [hp.1]
  have δ2pos : 0 < δ / 2 := by positivity
  have δ4pos : 0 < δ / 4 := by positivity
  have ε2pos : 0 < ε / 2 := by positivity
  have ε4pos : 0 < ε / 4 := by positivity
  /- Approximate f by a smooth f₀. -/
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ := close_smooth_approx_periodic periodic_f one_lt_p hf
    (lt_min (C_distribution_le_of_eLpNorm_le_pos (p := p) δ4pos ε2pos)
      (C_control_approximation_effect_pos (p := p) δ2pos ε2pos))
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀
    ((contDiff_infty.mp (contDiff_f₀)) 2) δ4pos
  set h := f₀ - f with hdef
  have h_measurable : AEStronglyMeasurable h := sorry --(Continuous.sub contDiff_f₀.continuous cont_f).measurable
  have h_periodic : h.Periodic (2 * π) := periodic_f₀.sub periodic_f
  /- This is a classical "epsilon third" argument. -/
  use N₀
  have : ∀ᶠx in (ae (volume.restrict (Set.Ioc 0 (2 * π)))), ⨆ N > N₀, ‖f x - S_ N f x‖ₑ
      ≤ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    apply iSup_le
    intro N
    apply iSup_le
    intro hN
    calc ‖f x - S_ N f x‖ₑ
      _ = ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x) + (S_ N f₀ x - S_ N f x)‖ₑ := by ring_nf
      _ ≤ ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x)‖ₑ + ‖S_ N f₀ x - S_ N f x‖ₑ := enorm_add_le ..
      _ ≤ ‖f x - f₀ x‖ₑ + ‖f₀ x - S_ N f₀ x‖ₑ + ‖S_ N f₀ x - S_ N f x‖ₑ :=
        add_le_add_left (enorm_add_le ..) _
      _ ≤ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ := by
        gcongr
        · refine le_iSup₂_of_le N hN ?_
          rfl
        · apply le_iSup_of_le N
          rw [partialFourierSum_sub sorry sorry]
          rfl
  calc _
    _ ≤ distribution
        (fun x ↦ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ)
        ((δ / 4) + (δ / 4) + (δ / 2)) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_mono
      · filter_upwards [this] with x hx
        simp only [gt_iff_lt, enorm_eq_self, hx]
      · sorry
    _ ≤ distribution (fun x ↦ ‖f x - f₀ x‖ₑ) (δ / 4) (volume.restrict (Set.Ioc 0 (2 * π)))
        + distribution (fun x ↦ ⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) (δ / 4) (volume.restrict (Set.Ioc 0 (2 * π)))
        + distribution (fun x ↦ ⨆ N, ‖S_ N (f₀ - f) x‖ₑ) (δ / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_add_le.trans
      gcongr
      exact distribution_add_le
    _ ≤ ε / 2 + 0 + ε / 2 := by
      gcongr
      · norm_cast
        apply distribution_le_of_eLpNorm_le (p := p) (by positivity) (by positivity [hp.1]) sorry
        simp only [eLpNorm_enorm]
        apply hf₀.trans
        simp
      · simp only [gt_iff_lt, nonpos_iff_eq_zero]
        rw [distribution_eq_zero_iff]
        apply essSup_le_of_ae_le
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with x hx
        simp only [enorm_eq_self, iSup_le_iff]
        intro N hN
        rw [enorm_eq_nnnorm]
        norm_cast
        rw [← nnnorm_norm]
        calc _
          _ ≤ ‖((δ / 4) : ℝ)‖₊ := by
            apply Real.nnnorm_le_nnnorm (by simp)
            exact hN₀ N hN x (Set.Ioc_subset_Icc_self hx)
          _ = δ / 4 := by simp
      · norm_cast
        apply control_approximation_effect ε2pos δ2pos sorry h_periodic hp
        rw [eLpNorm_sub_comm]
        apply hf₀.trans
        simp
    _ = ε := by simp

--TODO: generalize and clean this up
lemma ae_tendsto_zero_of_distribution_le {μ : Measure ℝ} {f : ℝ → ℂ} {F : ℕ → ℝ → ℂ}
  (h : ∀ δ > (0 : NNReal), ∀ ε > (0 : NNReal), ∃ N₀,
    distribution (fun x ↦ ⨆ N > N₀, ‖f x - F N x‖ₑ) δ μ ≤ ε) :
    ∀ᵐ x ∂μ, Filter.Tendsto (F · x) Filter.atTop (nhds (f x)) := by
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
    · rw [one_mul]
    norm_num
  have h' : ∀ (δ: NNReal), ∀ (ε : NNReal), ∃ N₀, 0 < δ → 0 < ε →
      distribution (fun x ↦ ⨆ N > N₀, ‖f x - F N x‖ₑ) δ μ ≤ ε := by
    intro δ ε
    by_cases δpos : 0 < δ
    · by_cases εpos : 0 < ε
      · rcases h δ δpos ε εpos with ⟨N₀, hN₀⟩
        use N₀
        intros
        apply hN₀
      · simp [εpos]
    · simp [δpos]
  choose N₀s hN₀s using h'
  set Eε := fun ε ↦ superlevelSet (fun x ↦ ⨆ N > N₀s ε ε, ‖f x - F N x‖ₑ) ε
  have Eεmeasure {ε : NNReal} (εpos : 0 < ε) : μ (Eε ε) ≤ ε := by
    unfold Eε
    rw [← distribution_eq_measure_superlevelSet]
    exact hN₀s _ _ εpos εpos
  -- Define exceptional sets parameterized by δ.
  let Eδ (k : ℕ) := ⋃ (n : ℕ), Eε (ε k n).toNNReal
  have Eδmeasure (k : ℕ) : μ (Eδ k) ≤ δ' k := by
    apply le_trans (measure_iUnion_le _)
    rw [δ'_eq]
    exact ENNReal.tsum_le_tsum (fun n ↦ Eεmeasure (by simp [εpos k n]))
  -- Define final exceptional set.
  let E := ⋂ (k : ℕ), Eδ k
  -- Show that it has the desired property.
  have hE : ∀ x ∉ E, Filter.Tendsto (F · x) Filter.atTop (nhds (f x)) := by
    intro x hx
    unfold E at hx
    simp only [Set.mem_iInter, not_forall] at hx
    rcases hx with ⟨k, hk⟩
    unfold Eδ at hk
    simp only [Set.mem_iUnion, not_exists] at hk
    rw [Metric.tendsto_atTop']
    intro e epos
    rcases (εsmall k epos) with ⟨n, lt_e⟩
    use N₀s (ε k n).toNNReal (ε k n).toNNReal
    intro N hN
    rw [dist_comm, dist_eq_norm]
    apply lt_e.trans_le'
    have := hk n
    unfold Eε superlevelSet at this
    simp only [gt_iff_lt, enorm_eq_self, Set.mem_setOf_eq, not_lt, iSup_le_iff,
      enorm_le_coe] at this
    have := this N hN
    rw [← Real.toNNReal_le_toNNReal_iff (εpos _ _).le]
    apply this.trans'
    simp
  -- Show that is has measure zero.
  have Emeasure : μ E ≤ 0 := by
    have : ∀ k, μ E ≤ δ' k := by
      intro k
      apply le_trans' (Eδmeasure k)
      apply measure_mono
      apply Set.iInter_subset
    exact ge_of_tendsto' δ'conv this
  -- Use results to prove the statement.
  apply le_antisymm _ zero_le
  apply le_trans' Emeasure
  apply measure_mono
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
  contrapose! hx
  exact hE x hx

theorem carleson_interval {f : ℝ → ℂ} (periodic_f : f.Periodic (2 * π))
  {p : ENNReal} (hp : 1 < p) (hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π)))) :
    ∀ᵐ x ∂volume.restrict (Set.Ioc 0 (2 * π)),
      Filter.Tendsto (S_ · f x) Filter.atTop (nhds (f x)) := by
  apply ae_tendsto_zero_of_distribution_le
  intro δ δpos ε εpos
  exact exceptional_set_carleson periodic_f hp hf δpos εpos

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
      simp only [Classical.not_imp, Set.mem_setOf_eq, hP.sub_zsmul_eq k] at hk
      exact hk.2
    · dsimp
      rcases (hP.exists_mem_Ico' hT x a) with ⟨n, hn, hxn⟩
      rw [hxn]
      refine fun h ↦ ⟨n, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, ← sub_eq_neg_add, E_interval_def]
      simp only [Classical.not_imp, Set.mem_setOf_eq]
      exact ⟨hn, h⟩
  -- The union still has measure zero
  have Emeasure : volume E = 0 := by
    rw [Edef, measure_iUnion_null]
    refine fun k ↦ measure_vadd_null h ..
  rw [ae_iff, ← hE]
  exact Emeasure

end

/- **Carleson's theorem** asserting a.e. point-wise convergence of the partial Fourier sums for
periodic continuous functions. -/
theorem classical_carleson {f : ℝ → ℂ} (periodic_f : f.Periodic (2 * π))
  {p : ENNReal} (hp : 1 < p) (hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π)))) :
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
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  exact carleson_interval periodic_f hp hf

theorem classical_carleson_check : ClassicalCarleson := sorry --@classical_carleson

end
