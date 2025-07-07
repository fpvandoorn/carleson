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

lemma measurable_lcoConvergent {n : ℕ} (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) :
    Measurable (lcoConvergent K Q f n) := by
  refine measurable_of_Ioi fun c ↦ ?_
  let J : Set (ℚ × ℚ) := {p | (2 ^ n)⁻¹ < p.1 ∧ p.1 < p.2 ∧ p.2 < 2 ^ n}
  suffices lcoConvergent K Q f n ⁻¹' Ioi c = ⋃ j ∈ J, {x | c < ‖T_R K Q j.1 j.2 (2 ^ n) f x‖ₑ} by
    rw [this]; refine MeasurableSet.biUnion J.to_countable fun j mj ↦ ?_
    exact measurableSet_lt measurable_const
      ((measurable_carlesonOperatorIntegrand mf).indicator measurableSet_ball).enorm
  ext x
  simp_rw [mem_preimage, mem_Ioi, lcoConvergent, lt_biSup_iff, mem_iUnion₂, mem_setOf_eq,
    exists_prop]
  constructor <;> intro h
  · obtain ⟨R₁, mR₁, R₂, mR₂, hR⟩ := h; unfold T_R at hR ⊢
    by_cases mx : x ∈ Metric.ball (cancelPt X) (2 ^ n); swap
    · simp [indicator_of_notMem mx] at hR
    simp_rw [indicator_of_mem mx] at hR ⊢
    lift c to ℝ≥0 using hR.ne_top
    simp_rw [coe_lt_enorm, ← NNReal.coe_lt_coe, coe_nnnorm] at hR ⊢
    let ε := ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ - c
    have εpos : 0 < ε := by linarith only [hR]
    have hR₁ : 0 < R₁ := lt_of_le_of_lt (by positivity) mR₁.1
    have hR₂ : R₁ < R₂ := mR₂.1
    obtain ⟨q₁, q₂, lq₁, lq, lq₂, dq⟩ :=
      exists_rat_near_carlesonOperatorIntegrand (Q x) x mf nf hR₁ hR₂ εpos
    have qmJ : (q₁, q₂) ∈ J := by
      refine ⟨?_, Rat.cast_lt.mp lq, ?_⟩
      · simp_rw [← Rat.cast_lt (K := ℝ), Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
        exact mR₁.1.trans lq₁
      · simp_rw [← Rat.cast_lt (K := ℝ), Rat.cast_pow, Rat.cast_ofNat]
        exact lq₂.trans mR₂.2
    use (q₁, q₂), qmJ
    simp_rw [ε, lt_sub_comm, dist_eq_norm'] at dq; apply dq.trans_le
    rw [sub_le_comm]; exact norm_sub_norm_le ..
  · obtain ⟨⟨R₁, R₂⟩, ⟨bR₁, bR₂, bR₃⟩, hR⟩ := h; dsimp only at hR
    simp_rw [← Rat.cast_lt (K := ℝ), Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] at bR₁ bR₂ bR₃
    use R₁, ⟨bR₁, bR₂.trans bR₃⟩, R₂, ⟨bR₂, bR₃⟩

/-- Theorem 1.0.3 -/
theorem linearized_metric_carleson [IsCancellative X (defaultτ a)]
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  have nf' : (‖f ·‖) ≤ 1 := nf.trans (indicator_le_self' (by simp))
  calc
    _ = ∫⁻ x, ⨆ n, G.indicator (lcoConvergent K Q f n) x := by
      rw [← lintegral_indicator mG]; congr! 2 with x
      rw [← iSup_apply, iSup_indicator rfl monotone_lcoConvergent monotone_const, iUnion_const,
        iSup_lcoConvergent]
    _ = ⨆ n, ∫⁻ x, G.indicator (lcoConvergent K Q f n) x :=
      lintegral_iSup (fun _ ↦ (measurable_lcoConvergent mf nf').indicator mG)
        (fun _ _ hl ↦ indicator_mono (monotone_lcoConvergent hl))
    _ ≤ _ := by
      refine iSup_le fun n ↦ ?_
      unfold lcoConvergent; rw [lintegral_indicator mG]
      exact R_truncation hq hqq' mF mG mf nf rfl hT

end
