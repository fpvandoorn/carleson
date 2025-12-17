import Carleson.Discrete.ExceptionalSet
import Carleson.Discrete.ForestComplement
import Carleson.Discrete.ForestUnion

open MeasureTheory NNReal Set
open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

/-! ## Proposition 2.0.2 -/

/-- The constant used in Proposition 2.0.2.
Has value `2 ^ (442 * a ^ 3) / (q - 1) ^ 5` in the blueprint. -/
noncomputable def C2_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 :=
    2 ^ ((3 * 𝕔 + 17 + 5 * (𝕔 / 4)) * a ^ 3) / (q - 1) ^ 5

lemma le_C2_0_2 (ha : 4 ≤ a) {q : ℝ≥0} (hq : q ∈ Ioc 1 2) :
    C5_1_2 a q + C5_1_3 a q ≤ C2_0_2 a q := by
  have h'q : 0 < q - 1 := tsub_pos_of_lt hq.1
  simp only [C5_1_2, C5_1_3, C2_0_2, ge_iff_le]
  have : (q - 1) ^ 4 ≥ (q - 1) ^ 5 := by
    apply pow_le_pow_of_le_one h'q.le ?_ (by norm_num)
    rw [tsub_le_iff_left]
    convert hq.2
    norm_num
  grw [this]
  simp only [← add_div, ge_iff_le]
  gcongr
  apply (add_le_pow_two_add_cube ha le_rfl ?_).trans_eq (by ring)
  have : 𝕔 / 8 ≤ 𝕔 / 4 := by lia
  grw [this]
  ring_nf
  lia

omit [TileStructure Q D κ S o] in
lemma C2_0_2_pos : 0 < C2_0_2 a nnq := by
  apply (add_pos (C5_1_2_pos (X := X)) (C5_1_3_pos (X := X))).trans_le
  apply le_C2_0_2 (four_le_a X) (q_mem_Ioc X)

variable (X) in
theorem discrete_carleson :
    ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖carlesonSum univ f x‖ₑ ≤
    C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  have exc := exceptional_set (X := X)
  rw [zpow_neg_one, ← ENNReal.div_eq_inv_mul] at exc
  use G', measurable_G', ENNReal.mul_le_of_le_div' exc; intro f measf hf
  classical
  calc
    _ ≤ ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ + ‖carlesonSum 𝔓₁ᶜ f x‖ₑ := by
      refine setLIntegral_mono (by fun_prop) fun x _ ↦ ?_
      rw [carlesonSum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ 𝔓₁ (X := X))]
      simp_rw [Finset.filter_filter, mem_univ, true_and, carlesonSum, mem_compl_iff]
      apply enorm_add_le
    _ = (∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ) + ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ :=
      lintegral_add_left (by fun_prop) _
    _ ≤ C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ +
        C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ :=
      add_le_add (forest_union hf measf) (forest_complement hf measf)
    _ ≤ _ := by
      simp_rw [mul_assoc, ← add_mul]
      gcongr
      norm_cast
      apply le_C2_0_2 (four_le_a X) (q_mem_Ioc X)
