import Carleson.MetricCarleson.Basic
import Carleson.MetricCarleson.Truncation

open scoped NNReal
open MeasureTheory Set ENNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
variable [KernelProofData a K] {Q : SimpleFunc X (Θ X)} {f : X → ℂ}

variable (K Q f) in
/-- A monotone sequence of functions converging to `linearizedCarlesonOperator`. -/
def lcoConvergent (n : ℕ) (x : X) : ℝ≥0∞ :=
  ⨆ R₁ ∈ Ioo (2 ^ n)⁻¹ (2 ^ n), ⨆ R₂ ∈ Ioo R₁ (2 ^ n), ‖T_R K Q R₁ R₂ (2 ^ n) f x‖ₑ

lemma monotone_lcoConvergent : Monotone (lcoConvergent K Q f) := fun i j hl x ↦ by
  refine iSup₂_le fun R₁ mR₁ ↦ iSup₂_le fun R₂ mR₂ ↦ ?_
  have lb : (2 ^ j : ℝ)⁻¹ ≤ (2 ^ i)⁻¹ := inv_pow_le_inv_pow_of_le one_le_two hl
  have ub : (2 ^ i : ℝ) ≤ 2 ^ j := pow_le_pow_right₀ one_le_two hl
  have mR₁' : R₁ ∈ Ioo (2 ^ j)⁻¹ (2 ^ j) := Ioo_subset_Ioo lb ub mR₁
  have mR₂' : R₂ ∈ Ioo R₁ (2 ^ j) := Ioo_subset_Ioo le_rfl ub mR₂
  calc
    _ ≤ ‖T_R K Q R₁ R₂ (2 ^ j) f x‖ₑ := by
      simp_rw [T_R, enorm_indicator_eq_indicator_enorm]
      exact indicator_le_indicator_of_subset (Metric.ball_subset_ball ub) (zero_le _) _
    _ ≤ ⨆ R₂ ∈ Ioo R₁ (2 ^ j), ‖T_R K Q R₁ R₂ (2 ^ j) f x‖ₑ := by apply le_biSup _ mR₂'
    _ ≤ _ := by apply le_biSup _ mR₁'

lemma iSup_lcoConvergent : ⨆ n, lcoConvergent K Q f n = linearizedCarlesonOperator Q K f := by
  ext x; rw [iSup_apply]; unfold lcoConvergent linearizedCarlesonOperator
  apply le_antisymm
  · refine iSup_le fun n ↦ iSup₂_le fun R₁ mR₁ ↦ iSup₂_le fun R₂ mR₂ ↦ ?_
    rw [T_R, enorm_indicator_eq_indicator_enorm]
    conv_rhs => enter [1, R₁]; rw [iSup_comm]
    have b₁ : 0 < R₁ := lt_trans (by positivity) mR₁.1
    have b₂ := mR₂.1
    calc
      _ ≤ _ := indicator_enorm_le_enorm_self _ x
      _ ≤ ⨆ R₂, ⨆ (_ : R₁ < R₂), ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ₑ := by
        apply le_iSup₂ R₂ b₂
      _ ≤ _ := by apply le_iSup₂ R₁ b₁
  · refine iSup₂_le fun R₁ R₂ ↦ iSup₂_le fun lR₁ lR₂ ↦ ?_
    suffices ∃ n, (2 ^ n)⁻¹ < R₁ ∧ R₂ < 2 ^ n ∧ dist x (cancelPt X) < 2 ^ n by
      obtain ⟨n, hn₁, hn₂, hn₃⟩ := this
      have b₁ : R₁ ∈ Ioo (2 ^ n)⁻¹ (2 ^ n) := ⟨hn₁, lR₂.trans hn₂⟩
      have b₂ : R₂ ∈ Ioo R₁ (2 ^ n) := ⟨lR₂, hn₂⟩
      calc
        _ = ‖T_R K Q R₁ R₂ (2 ^ n) f x‖ₑ := by
          rw [T_R, enorm_indicator_eq_indicator_enorm, indicator_of_mem (Metric.mem_ball.mpr hn₃)]
        _ ≤ ⨆ R₂ ∈ Ioo R₁ (2 ^ n), ‖T_R K Q R₁ R₂ (2 ^ n) f x‖ₑ := by apply le_iSup₂ _ b₂
        _ ≤ ⨆ R₁ ∈ Ioo (2 ^ n)⁻¹ (2 ^ n), ⨆ R₂ ∈ Ioo R₁ (2 ^ n), ‖T_R K Q R₁ R₂ (2 ^ n) f x‖ₑ := by
          apply le_iSup₂ _ b₁
        _ ≤ _ := by apply le_iSup _ n
    obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt R₁⁻¹ one_lt_two
    replace hn₁ := inv_lt_of_inv_lt₀ lR₁ hn₁
    obtain ⟨n₂, hn₂⟩ := pow_unbounded_of_one_lt (max R₂ (dist x (cancelPt X))) one_lt_two
    refine ⟨max n₁ n₂, ?_, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hn₁
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (le_max_left ..))
    · exact ((le_max_left ..).trans_lt hn₂).trans_le
        (pow_le_pow_right₀ one_le_two (le_max_right ..))
    · exact ((le_max_right ..).trans_lt hn₂).trans_le
        (pow_le_pow_right₀ one_le_two (le_max_right ..))

lemma measurable_lcoConvergent {n : ℕ} (mf : Measurable f) :
    Measurable (lcoConvergent K Q f n) := by
  refine measurable_of_Ioi fun c ↦ ?_
  let T : Set (ℝ × ℝ) := {p | (2 ^ n)⁻¹ < p.1 ∧ p.1 < p.2 ∧ p.2 < 2 ^ n}
  have sepT := TopologicalSpace.IsSeparable.of_separableSpace T
  obtain ⟨J, sJ, countJ, denseJ⟩ := sepT.exists_countable_dense_subset
  suffices lcoConvergent K Q f n ⁻¹' Ioi c = ⋃ j ∈ J, {x | c < ‖T_R K Q j.1 j.2 (2 ^ n) f x‖ₑ} by
    rw [this]; refine MeasurableSet.biUnion countJ fun j mj ↦ ?_
    exact measurableSet_lt measurable_const
      ((measurable_carlesonOperatorIntegrand mf).indicator measurableSet_ball).enorm
  ext x
  simp_rw [mem_preimage, mem_Ioi, lcoConvergent, lt_biSup_iff, mem_iUnion₂, mem_setOf_eq,
    exists_prop]
  symm; constructor <;> intro h
  · obtain ⟨⟨R₁, R₂⟩, mR, hR⟩ := h; specialize sJ mR; simp only [T, mem_setOf_eq] at sJ
    use R₁, ⟨sJ.1, sJ.2.1.trans sJ.2.2⟩, R₂, ⟨sJ.2.1, sJ.2.2⟩
  · obtain ⟨R₁, mR₁, R₂, mR₂, hR⟩ := h
    suffices ContinuousOn (fun j ↦ ‖T_R K Q j.1 j.2 (2 ^ n) f x‖ₑ) T by
      have mR : (R₁, R₂) ∈ T := ⟨mR₁.1, mR₂.1, mR₂.2⟩
      rw [continuousOn_iff] at this; specialize this _ mR (Ioi c) isOpen_Ioi hR
      obtain ⟨u, ou, mu, hu⟩ := this
      specialize denseJ mR; rw [mem_closure_iff] at denseJ
      specialize denseJ u ou mu; obtain ⟨j, mj⟩ := denseJ; use j, mj.2
      simpa using (inter_subset_inter subset_rfl sJ).trans hu mj
    apply ContinuousOn.enorm; unfold T_R
    by_cases mx : x ∈ Metric.ball (cancelPt X) (2 ^ n); swap
    · simp_rw [indicator_of_notMem mx]; fun_prop
    simp_rw [indicator_of_mem mx]
    sorry

variable [IsCancellative X (defaultτ a)]

/-- Theorem 1.0.3 -/
theorem linearized_metric_carleson
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  calc
    _ = ∫⁻ x, ⨆ n, G.indicator (lcoConvergent K Q f n) x := by
      rw [← lintegral_indicator mG]; congr! 2 with x
      rw [← iSup_apply, iSup_indicator rfl monotone_lcoConvergent monotone_const, iUnion_const,
        iSup_lcoConvergent]
    _ = ⨆ n, ∫⁻ x, G.indicator (lcoConvergent K Q f n) x :=
      lintegral_iSup (fun _ ↦ (measurable_lcoConvergent mf).indicator mG)
        (fun _ _ hl ↦ indicator_mono (monotone_lcoConvergent hl))
    _ ≤ _ := by
      refine iSup_le fun n ↦ ?_
      unfold lcoConvergent; rw [lintegral_indicator mG]
      exact R_truncation hq hqq' mF mG mf nf rfl hT

end
