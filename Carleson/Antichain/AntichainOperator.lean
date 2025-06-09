import Carleson.Antichain.Basic
import Carleson.ToMathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open scoped ShortVariables
open scoped ComplexConjugate GridStructure
open Set Complex MeasureTheory NNReal ENNReal

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {𝔄 : Set (𝔓 X)} {f g : X → ℂ}

/-- Constant appearing in Lemma 6.1.4. -/
irreducible_def C6_1_4 (a : ℕ) : ℝ≥0 := 2 ^ (150 * a ^ 3)

/-- Lemma 6.1.4 -/
lemma dens1_antichain (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    (hfm : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ≤
    C6_1_4 a * dens₁ 𝔄 ^ (8 * a ^ 4 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-- The constant appearing in Proposition 2.0.3.
Has value `2 ^ (150 * a ^ 3) / (q - 1)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C2_0_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (150 * a ^ 3) / (q - 1)

--TODO: PR to Mathlib
theorem ENNReal.rpow_le_self_of_one_le {x : ℝ≥0∞} {y : ℝ} (h₁ : 1 ≤ x) (h₂ : y ≤ 1) :
    x ^ y ≤ x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le h₁ h₂

variable (X) in
omit [TileStructure Q D κ S o] in
private lemma ineq_aux_2_0_3 :
    ((2 ^ (150 * a ^ 3) : ℝ≥0) : ℝ≥0∞) ^ (q - 1) *
    (((2 ^ (111 * a ^ 3) : ℝ≥0) : ℝ≥0∞) * (nnq - 1)⁻¹) ^ (2 - q) ≤
    (2 ^ (150 * a ^ 3) / (nnq - 1) : ℝ≥0) := by
  have hq1 : 0 ≤ q - 1 := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (nnq_mem_Ioc X).1.le)
  have hq2 : 0 ≤ 2 - q := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (nnq_mem_Ioc X).2)
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  calc
    _ = ((2 ^ (150 * a ^ 3) : ℝ≥0) : ℝ≥0∞) ^ (q - 1) *
        (((2 ^ (111 * a ^ 3) : ℝ≥0) : ℝ≥0∞)) ^ (2 - q) * (nnq - 1)⁻¹ ^ (2 - q)  := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq2]; ring
    _ ≤ ((2 ^ (150 * a ^ 3) : ℝ≥0) : ℝ≥0∞) ^ (q - 1) *
        (((2 ^ (150 * a ^ 3) : ℝ≥0) : ℝ≥0∞)) ^ (2 - q) * (nnq - 1)⁻¹ := by
      have h11 : (1 + 1 : ℝ≥0) = 2 := by norm_num
      gcongr
      · norm_num
      · norm_num
      · refine ENNReal.rpow_le_self_of_one_le ?_ (by linarith)
        rw [one_le_coe_iff, one_le_inv₀ (tsub_pos_iff_lt.mpr (nnq_mem_Ioc X).1), tsub_le_iff_right,
          h11]; exact (nnq_mem_Ioc X).2
    _ ≤ _ := by
      rw [div_eq_mul_inv, ENNReal.coe_mul, ← ENNReal.rpow_add_of_nonneg _ _ hq1 hq2,
        sub_add_sub_cancel', h21, ENNReal.rpow_one]

/-- Proposition 2.0.3 -/
theorem antichain_operator (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (hf : Measurable f)
    (hf1 : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ≤
    C2_0_3 a nnq * dens₁ 𝔄 ^ ((q - 1) / (8 * a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hq : (nnq : ℝ) = q := rfl
  have h21 : (2 : ℝ) - 1 = 1 := by norm_cast
  have h21' : (2 : ℝ≥0) - 1 = 1 := by norm_cast
  -- Eq. 6.1.48
  have heq : (nnq'⁻¹ - 2⁻¹) * (2 - q) = q⁻¹ - 2⁻¹ := by
    have hq0 : q ≠ 0 := by rw [← hq, NNReal.coe_ne_zero]; exact (nnq_pos _).ne'
    simp only [inv_div, NNReal.coe_div, NNReal.coe_add, hq, NNReal.coe_one, NNReal.coe_mul,
      NNReal.coe_ofNat]
    calc
      _ = ((q + 1) / (2 * q) - q / (2 * q)) * (2 - q) := by
        congr; nth_rewrite 1 [inv_eq_one_div, ← one_mul q, mul_div_mul_right 1 2 hq0]; rfl
      _ = q⁻¹ - 2⁻¹ := by ring_nf; simp [hq0]
  push_cast at heq
  by_cases hq2 : q = 2
  · have hnnq2 : nnq = 2 := by simp only [← NNReal.coe_inj, NNReal.coe_ofNat, ← hq2]; rfl
    simp only [hq2, h21, one_div, sub_self, ENNReal.rpow_zero, mul_one]
    convert dens1_antichain h𝔄 hf hf1 hg1
    simp only [C2_0_3, hnnq2, h21', div_one, C6_1_4]
  · have hq2' : 0 < 2 - q :=
      sub_pos.mpr (lt_of_le_of_ne (NNReal.coe_le_coe.mpr (nnq_mem_Ioc X).2) hq2)
    -- Take the (2-q)-th power of 6.1.11
    have h2 := dens2_antichain h𝔄 hf1 hf hg1
    rw [← ENNReal.rpow_le_rpow_iff hq2'] at h2
    simp only [mul_assoc] at h2
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq2'.le, ENNReal.mul_rpow_of_nonneg _ _ hq2'.le,
      ← ENNReal.rpow_mul (dens₂ 𝔄), heq] at h2
    -- Take and the (q-1)-th power of 6.1.22
    have h1 := dens1_antichain h𝔄 hf hf1 hg1
    have h1q : 0 < q - 1 := sub_pos.mpr (NNReal.coe_lt_coe.mpr (nnq_mem_Ioc X).1)
    rw [← ENNReal.rpow_le_rpow_iff h1q] at h1
    simp only [mul_assoc] at h1
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1q.le, ENNReal.mul_rpow_of_nonneg _ _ h1q.le,
      ← ENNReal.rpow_mul (dens₁ 𝔄)] at h1
    calc
      _ = ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ^ (q - 1) *
          ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ^ (2 - q) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ h1q.le hq2'.le, sub_add_sub_cancel', h21,
          ENNReal.rpow_one]
      _ ≤ (C6_1_4 a ^ (q - 1) * (dens₁ 𝔄 ^ ((8 * ↑a ^ 4)⁻¹ * (q - 1)) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (q - 1))) *
          (C6_1_3 a nnq ^ (2 - q) * (dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (2 - q))) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C6_1_4 a ^ (q - 1) * C6_1_3 a nnq ^ (2 - q)) *
            dens₁ 𝔄 ^ ((8 * ↑a ^ 4)⁻¹ * (q - 1)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
          ((eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (q - 1) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (2 - q)) := by ring
      _ = (C6_1_4 a ^ (q - 1) * C6_1_3 a nnq ^ (2 - q)) *
            dens₁ 𝔄 ^ ((q - 1) / (8 * ↑a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
          eLpNorm f 2 volume * eLpNorm g 2 volume := by
        have hnorm : ((eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (q - 1) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (2 - q)) =
            eLpNorm f 2 volume * eLpNorm g 2 volume := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ h1q.le hq2'.le, sub_add_sub_cancel', h21,
            ENNReal.rpow_one]
        rw [div_eq_inv_mul, hnorm]
        ring
      _ ≤ _ := by
        gcongr
        simp only [C6_1_4, C6_1_3, ENNReal.coe_mul, C2_0_3]
        exact ineq_aux_2_0_3 X

/-- Version of the antichain operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function. -/
theorem antichain_operator' {A : Set X} (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : A ⊆ G) :
    ∫⁻ x in A, ‖carlesonSum 𝔄 f x‖ₑ ≤
    C2_0_3 a nnq * dens₁ 𝔄 ^ ((q - 1) / (8 * a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * volume G ^ (1/2 : ℝ) := by
  have I (x : ℝ) : x / x ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp [hx]
  apply (lintegral_mono_set hA).trans
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  rw [← enorm_integral_starRingEnd_mul_eq_lintegral_enorm]; swap
  · apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.restrict ?_
    apply BoundedCompactSupport.carlesonSum
    have : BoundedCompactSupport (F.indicator 1 : X → ℝ) := by
      apply BoundedCompactSupport.indicator_of_isCompact_closure (memLp_top_const _) _
        measurableSet_F
      · exact isBounded_F.isCompact_closure
    apply BoundedCompactSupport.mono_norm this hf.aestronglyMeasurable h2f
  rw [← integral_indicator measurableSet_G]
  simp_rw [indicator_mul_left, ← Function.comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  apply (antichain_operator h𝔄 hf h2f ?_).trans; rotate_left
  · intro x
    simp [indicator]
    split_ifs
    · simp [I]
    · simp
  gcongr
  calc
  _ ≤ eLpNorm (G.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    simp only [indicator, coe_algebraMap, Real.norm_eq_abs]
    split_ifs
    · simpa using I _
    · simp
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact measurableSet_G
    · norm_num
    · norm_num

/-- Version of the antichain operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function, and with the upper bound in terms
of `volume F` and `volume G`. -/
theorem antichain_operator_le_volume {A : Set X} (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : A ⊆ G) :
    ∫⁻ x in A, ‖carlesonSum 𝔄 f x‖ₑ ≤
    C2_0_3 a nnq * dens₁ 𝔄 ^ ((q - 1) / (8 * a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
    volume F ^ (1/2 : ℝ) * volume G ^ (1/2 : ℝ) := by
  apply (antichain_operator' h𝔄 hf h2f hA).trans
  gcongr
  calc
  _ ≤ eLpNorm (F.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    apply (h2f x).trans (le_abs_self _)
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact measurableSet_F
    · norm_num
    · norm_num
