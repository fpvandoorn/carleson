module

public import Carleson.Classical.Helper
public import Carleson.ToMathlib.Distribution
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Real.StarOrdered

public section

/- This file contains the proof of the classical Carleson theorem from Section 11.1. -/

open MeasureTheory Real NNReal ENNReal Topology Filter

noncomputable section

--TODO: generalize and clean this up
lemma ae_tendsto_zero_of_distribution_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  {f : α → ℂ} {F : ℕ → α → ℂ}
  (h : ∀ δ > (0 : NNReal), ∀ ε > (0 : NNReal), ∃ N₀,
    distribution (fun x ↦ ⨆ N > N₀, ‖f x - F N x‖ₑ) δ μ ≤ ε) :
    ∀ᵐ x ∂μ, Tendsto (F · x) atTop (𝓝 (f x)) := by
  let δ (k : ℕ) : ℝ := 1 / (k + 1) --arbitrary sequence tending to zero
  have δconv : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have δpos (k : ℕ) : 0 < δ k := by apply div_pos zero_lt_one (by linarith)
  -- ENNReal version to be comparable to volumes
  let δ' (k : ℕ) := ENNReal.ofReal (δ k)
  have δ'conv : Tendsto δ' atTop (𝓝 0) := by
    rw [← ofReal_zero]
    exact tendsto_ofReal δconv
  set ε := fun k n ↦ (1 / 2) ^ n * 2⁻¹ * δ k with εdef
  have εpos (k n : ℕ) : 0 < ε k n := by positivity
  have εsmall (k : ℕ) {e : ℝ} (epos : 0 < e) : ∃ n, ε k n < e := by
    have : Tendsto (ε k) atTop (𝓝 0) := by
      rw [εdef]
      simp_rw [mul_assoc]
      rw [← zero_mul (2⁻¹ * δ k)]
      apply Filter.Tendsto.mul_const
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    rw [Metric.tendsto_atTop] at this
    rcases (this e epos) with ⟨n, hn⟩
    use n
    convert (hn n (by simp))
    simp_rw [dist_zero_right, norm_eq_abs, abs_of_nonneg (εpos k n).le]
  have δ'_eq {k : ℕ} : δ' k = ∑' n, ENNReal.ofReal (ε k n) := by
    rw [εdef]
    conv => rhs; pattern ENNReal.ofReal _; rw [ofReal_mul' (δpos k).le,
      ofReal_mul' (by norm_num), ofReal_pow (by norm_num)]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
      ← ofReal_one, ← ofReal_sub, ← ofReal_inv_of_pos (by norm_num),
      ← ofReal_mul' (by norm_num)]
    conv => pattern ENNReal.ofReal _; ring_nf; rw [ofReal_one]
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
  have hE : ∀ x ∉ E, Tendsto (F · x) atTop (𝓝 (f x)) := by
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
    rw [← toNNReal_le_toNNReal_iff (εpos _ _).le]
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

end
