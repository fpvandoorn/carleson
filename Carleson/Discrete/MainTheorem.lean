import Carleson.Discrete.ExceptionalSet
import Carleson.Discrete.ForestComplement
import Carleson.Discrete.ForestUnion

open MeasureTheory NNReal Set Classical
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

/-! ## Proposition 2.0.2 -/

/-- The constant used in Proposition 2.0.2,
which has value `2 ^ (440 * a ^ 3) / (q - 1) ^ 5` in the blueprint. -/
def C2_0_2 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := C5_1_2 a q + C5_1_3 a q

lemma C2_0_2_pos : C2_0_2 a nnq > 0 := add_pos C5_1_2_pos C5_1_3_pos

variable (X) in
theorem discrete_carleson :
    ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖carlesonSum univ f x‖₊ ≤
    C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  have exc := exceptional_set (X := X)
  rw [zpow_neg_one, ← ENNReal.div_eq_inv_mul] at exc
  use G', measurable_G', ENNReal.mul_le_of_le_div' exc; intro f measf hf
  calc
    _ ≤ ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖₊ + ‖carlesonSum 𝔓₁ᶜ f x‖₊ := by
      refine setLIntegral_mono ?_ fun x _ ↦ ?_
      · exact ((measurable_carlesonSum measf).nnnorm.add
          (measurable_carlesonSum measf).nnnorm).coe_nnreal_ennreal
      · norm_cast
        rw [carlesonSum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ 𝔓₁ (X := X))]
        simp_rw [Finset.filter_filter, mem_univ, true_and, carlesonSum, mem_compl_iff]
        exact nnnorm_add_le ..
    _ = (∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖₊) + ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖₊ :=
      lintegral_add_left ((measurable_carlesonSum measf).nnnorm).coe_nnreal_ennreal _
    _ ≤ C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ +
        C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ :=
      add_le_add (forest_union hf) (forest_complement hf)
    _ = _ := by simp_rw [mul_assoc, ← add_mul]; congr
