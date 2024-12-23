import Carleson.ForestOperator.LargeSeparation
import Carleson.ForestOperator.RemainingTiles

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Lemmas 7.4.4 -/

/-- The constant used in `correlation_separated_trees`.
Has value `2 ^ (550 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_4 (a n : ℕ) : ℝ≥0 := 2 ^ (550 * (a : ℝ) ^ 3 - 3 * n)

lemma correlation_separated_trees_of_subset (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-- Lemma 7.4.4. -/
lemma correlation_separated_trees (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry


/-! ## Section 7.7 -/

/-- The row-decomposition of a tree, defined in the proof of Lemma 7.7.1.
The indexing is off-by-one compared to the blueprint. -/
def rowDecomp (t : Forest X n) (j : ℕ) : Row X n := sorry

/-- Part of Lemma 7.7.1 -/
@[simp]
lemma biUnion_rowDecomp : ⋃ j < 2 ^ n, t.rowDecomp j = (t : Set (𝔓 X)) := by
  sorry

/-- Part of Lemma 7.7.1 -/
lemma pairwiseDisjoint_rowDecomp :
    (Iio (2 ^ n)).PairwiseDisjoint (rowDecomp t · : ℕ → Set (𝔓 X)) := by
  sorry

@[simp] lemma rowDecomp_apply : t.rowDecomp j u = t u := by
  sorry

/-- The constant used in `row_bound`.
Has value `2 ^ (156 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_1 (a n : ℕ) : ℝ≥0 := 2 ^ (156 * (a : ℝ) ^ 3 - n / 2)

/-- The constant used in `indicator_row_bound`.
Has value `2 ^ (257 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_2 (a n : ℕ) : ℝ≥0 := 2 ^ (257 * (a : ℝ) ^ 3 - n / 2)

/-- Part of Lemma 7.7.2. -/
lemma row_bound (hj : j < 2 ^ n) (hf : BoundedCompactSupport f) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) f) 2 volume ≤
    C7_7_2_1 a n * eLpNorm f 2 volume := by
  sorry

/-- Part of Lemma 7.7.2. -/
lemma indicator_row_bound (hj : j < 2 ^ n) (hf : BoundedCompactSupport f) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, F.indicator <| adjointCarlesonSum (t u) f) 2 volume ≤
    C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  sorry

/-- The constant used in `row_correlation`.
Has value `2 ^ (862 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_3 (a n : ℕ) : ℝ≥0 := 2 ^ (862 * (a : ℝ) ^ 3 - 2 * n)

/-- Lemma 7.7.3. -/
lemma row_correlation (hjj' : j < j') (hj' : j' < 2 ^ n)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) f₁ x) *
    (∑ u ∈ {p | p ∈ rowDecomp t j'}, adjointCarlesonSum (t u) f₂ x)‖₊ ≤
    C7_7_3 a n * eLpNorm f₁ 2 volume * eLpNorm f₂ 2 volume := by
  sorry

variable (t) in
/-- The definition of `Eⱼ` defined above Lemma 7.7.4. -/
def rowSupport (j : ℕ) : Set X := ⋃ (u ∈ rowDecomp t j) (p ∈ t u), E p

/-- Lemma 7.7.4 -/
lemma pairwiseDisjoint_rowSupport :
    (Iio (2 ^ n)).PairwiseDisjoint (rowSupport t) := by
  sorry

end TileStructure.Forest

/-! ## Proposition 2.0.4 -/

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := 2 ^ (432 * a ^ 3 - (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

lemma ennnorm_integral_starRingEnd_mul_eq_lintegral_ennnorm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) :
    ∫⁻ x, ‖f x‖₊ ∂μ = ‖∫ x, starRingEnd 𝕜 (f x / ‖f x‖) * f x ∂μ‖₊ := by
  have A x : starRingEnd 𝕜 (f x / ‖f x‖) * f x = ‖f x‖ := by
    simp only [div_eq_inv_mul, map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    norm_cast
    rcases eq_or_ne (‖f x‖) 0 with hx | hx
    · simp [hx]
    · rw [pow_two, inv_mul_cancel_left₀ hx]
  simp_rw [A, integral_ofReal, nnnorm_algebraMap']
  rw [lintegral_coe_eq_integral]; swap
  · simpa only [coe_nnnorm] using hf.norm
  simp only [coe_nnnorm, ENNReal.ofReal, ENNReal.coe_inj]
  have : |∫ (a : α), ‖f a‖ ∂μ| = ∫ (a : α), ‖f a‖ ∂μ := by
    apply abs_eq_self.2
    exact integral_nonneg (fun x ↦ by positivity)
  conv_lhs => rw [← this]
  simp only [Real.norm_eq_abs, Real.toNNReal_abs]
  rfl

/-- Verion of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function muliplied by another function. -/
theorem forest_operator' {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * (volume A) ^ (1/2 : ℝ) := by
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  rw [ennnorm_integral_starRingEnd_mul_eq_lintegral_ennnorm]; swap
  · apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.finset_sum (fun i hi ↦ ?_)
    apply BoundedCompactSupport.carlesonSum
    have : BoundedCompactSupport (F.indicator 1 : X → ℝ) := by
      apply BoundedCompactSupport.indicator_of_isBounded_range _ stronglyMeasurable_one _
        measurableSet_F
      · exact isBounded_range_iff_forall_norm_le.2 ⟨1, fun x ↦ by simp⟩
      · exact PreProofData.isBounded_F
    apply BoundedCompactSupport.mono this hf.stronglyMeasurable h2f
  rw [← integral_indicator hA]
  simp_rw [indicator_mul_left, ← comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  apply (forest_operator 𝔉 hf h2f ?_ ?_).trans; rotate_left
  · apply Measurable.indicator _ hA
    fun_prop
  · apply h'A.subset support_indicator_subset
  gcongr
  · have := (q_mem_Ioc (X := X)).2
    simp only [sub_nonneg, ge_iff_le, inv_le_inv₀ zero_lt_two (q_pos X)]
    exact (q_mem_Ioc (X := X)).2
  · exact le_rfl
  calc
  _ ≤ eLpNorm (A.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    simp only [indicator, norm_eq_abs, coe_algebraMap, Pi.one_apply, Real.norm_eq_abs]
    split_ifs
    · have A (x : ℝ) : x / x ≤ 1 := by
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · simp [hx]
      simpa using A _
    · simp
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact hA
    · norm_num
    · norm_num
