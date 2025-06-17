import Carleson.FinitaryCarleson
import Carleson.MetricCarleson.Basic

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Bornology Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {C : ℝ} {F G : Set X} {K : X → X → ℂ}
variable [KernelProofData a K] {x : X} {θ : Θ X} {R₁ R₂ : ℝ} {Q : SimpleFunc X (Θ X)}
variable {F G : Set X} {f : X → ℂ} {s : ℤ} {σ₁ σ₂ : X → ℤ} [IsCancellative X (defaultτ a)]

/-- The operator T_{2, σ₁, σ₂} introduced in Lemma 3.0.4. -/
def T_lin (Q : SimpleFunc X (Θ X)) (σ₁ σ₂ : X → ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ s ∈ Finset.Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)

theorem finitary_carleson_step (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (bG : IsBounded G) (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mσ₁ : Measurable σ₁) (mσ₂ : Measurable σ₂) (rσ₁ : (range σ₁).Finite) (rσ₂ : (range σ₂).Finite)
    (lσ : σ₁ ≤ σ₂) (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1) :
    ∃ G' ⊆ G, IsBounded G' ∧ MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∫⁻ x in G \ G', ‖T_lin Q σ₁ σ₂ f x‖ₑ ≤
    C2_0_1 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  rcases eq_zero_or_pos (volume G) with vG | vG
  · use ∅, empty_subset _, isBounded_empty, MeasurableSet.empty
    simp only [measure_empty, mul_zero, zero_le, diff_empty, true_and]
    rw [setLIntegral_measure_zero _ _ vG]; exact zero_le _
  rcases eq_zero_or_pos (volume F) with vF | vF
  · use ∅, empty_subset _, isBounded_empty, MeasurableSet.empty
    simp only [measure_empty, mul_zero, zero_le, diff_empty, true_and]
    suffices ∀ x, ‖T_lin Q σ₁ σ₂ f x‖ₑ = 0 by
      rw [lintegral_congr this, lintegral_zero]; exact zero_le _
    intro x; rw [enorm_eq_zero]; refine Finset.sum_eq_zero fun s ms ↦ integral_eq_zero_of_ae ?_
    classical
    convert ite_ae_eq_of_measure_zero (fun y ↦ Ks s x y * f y * exp (I * Q x y)) 0 F vF using 1
    ext y; symm; rw [ite_eq_left_iff]; intro ny
    specialize nf y; simp_rw [indicator_of_notMem ny, norm_le_zero_iff] at nf
    simp [nf]
  rename_i msx kpd cancel
  haveI PD : ProofData a q K σ₁ σ₂ F G :=
    ⟨cancel, bF, bG, mF, mG, vF, vG, mσ₁, mσ₂, rσ₁, rσ₂, lσ, Q, hq⟩
  have : kpd = PD.toKernelProofData := by
    sorry
  obtain ⟨G₁, mG₁, vG₁, hG₁⟩ := finitary_carleson X
  refine ⟨G ∩ G₁, inter_subset_left, bG.subset inter_subset_left, mG.inter (by convert mG₁), ?_, ?_⟩
  · refine le_trans ?_ (by convert vG₁); gcongr
    convert measure_mono (μ := volume) (@inter_subset_right _ G G₁) <;> exact this.symm
  · simp_rw [diff_self_inter, T_lin]
    specialize hG₁ f (by convert mf; exact this.symm) nf
    simp_rw [toFinset_Icc, show nnq = q by rfl] at hG₁
    convert hG₁ using 1
    · rfl
    · congr; rw [eq_sub_iff_add_eq]; norm_cast
      exact hqq'.symm.inv_add_inv_eq_one

/-- The constant used in `linearized_truncation`.
Has value `2 ^ (445 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C3_0_4 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (445 * a ^ 3) / (q - 1) ^ 6

/-- Lemma 3.0.4. -/
lemma linearized_truncation (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (bG : IsBounded G) (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1) (mσ₁ : Measurable σ₁) (mσ₂ : Measurable σ₂)
    (rσ₁ : (range σ₁).Finite) (rσ₂ : (range σ₂).Finite) (lσ : σ₁ ≤ σ₂) :
    ∫⁻ x in G, ‖T_lin Q σ₁ σ₂ f x‖ₑ ≤
    C3_0_4 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  rcases eq_zero_or_pos (volume G) with vG | vG
  · rw [setLIntegral_measure_zero _ _ vG]; exact zero_le _
  rcases eq_zero_or_pos (volume F) with vF | vF
  · sorry
  haveI PD : ProofData a q K σ₁ σ₂ F G :=
    ⟨‹_›, bF, bG, mF, mG, vF, vG, mσ₁, mσ₂, rσ₁, rσ₂, lσ, Q, hq⟩
  obtain ⟨G₁, mG₁, vG₁, hG₁⟩ := finitary_carleson X
  specialize hG₁ f (by convert mf; sorry) nf -- PD.toKernelProofData = inst✝¹
  sorry

/-- The operator T_{s₁, s₂} introduced in Lemma 3.0.3. -/
def T_S (Q : SimpleFunc X (Θ X)) (s₁ s₂ : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y, ∑ s ∈ Finset.Icc s₁ s₂, Ks s x y * f y * exp (I * Q x y)

/-- The constant used in `S_truncation`.
Has value `2 ^ (446 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C3_0_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (446 * a ^ 3) / (q - 1) ^ 6

/- `S'` is `S` in the blueprint. -/
lemma S_truncation {S' : ℤ}
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : IsBounded F) (hG : IsBounded G)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1) :
    ∫⁻ x in G, ⨆ (s₁ : ℤ) (s₂ : ℤ) (_ : - S' < s₁) (_ : s₁ < s₂) (_ : s₂ < S'), ‖T_S Q s₁ s₂ f x‖ₑ ≤
    C3_0_3 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  sorry

/-- The operator T_{R₁, R₂, R} introduced in Lemma 3.0.2. -/
def T_R (K : X → X → ℂ) (Q : SimpleFunc X (Θ X)) (R₁ R₂ R : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  (ball o R).indicator (fun x ↦ carlesonOperatorIntegrand K (Q x) R₁ R₂ f x) x

/-- The constant used in `metric_carleson` and `R_truncation`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C1_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

lemma C1_0_2_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C1_0_2 a q := by
  rw [C1_0_2]
  apply div_pos
  · positivity
  · exact pow_pos (tsub_pos_of_lt hq) _


lemma R_truncation
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : volume F < ∞) (hG : volume G < ∞)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1)
    {n : ℤ} {R : ℝ} (hR : R = 2 ^ n) :
    ∫⁻ x in G, ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R⁻¹ < R₁) (_ : R₁ < R₂) (_ : R₂ < R), ‖T_R K Q R₁ R₂ R f x‖ₑ ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  sorry
