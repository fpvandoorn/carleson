import Carleson.ForestOperator.LargeSeparation.LipschitzPartition
import Carleson.ForestOperator.LargeSeparation.TreeControl

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Lemmas 7.5.4, 7.5.11 and 7.4.5 -/

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ)  (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/-- The product on the right-hand side of Lemma 7.5.4. -/
def P7_5_4 (t : Forest X n) (u₁ u₂ : 𝔓 X) (f₁ f₂ : X → ℂ) (J : Grid X) : ℝ≥0∞ :=
  ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
  ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x)

/-- The support of `holderFunction` is in `𝓘 u₁`. -/
lemma support_holderFunction_subset (u₂ : 𝔓 X) (f₁ f₂ : X → ℂ) (J : Grid X) (hu₁ : u₁ ∈ t) :
    support (holderFunction t u₁ u₂ f₁ f₂ J) ⊆ 𝓘 u₁ := by
  rw [support_subset_iff']; intro x nx
  have : adjointCarlesonSum (t u₁) f₁ x = 0 := by
    refine Finset.sum_eq_zero fun p mp ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at mp
    rw [adjoint_tile_support2 hu₁ mp]
    exact indicator_of_not_mem nx _
  rw [holderFunction, this, mul_zero, mul_zero, zero_mul]

lemma enorm_holderFunction_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) :
    ‖holderFunction t u₁ u₂ f₁ f₂ J x‖ₑ ≤ C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J := by
  simp_rw [holderFunction, enorm_mul, RCLike.enorm_conj, enorm_mul, enorm_exp_I_mul_ofReal, one_mul,
    Complex.enorm_real, NNReal.enorm_eq]
  calc
    _ ≤ 1 * (⨆ z ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ z‖ₑ) *
        ⨆ z ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ z‖ₑ := by
      gcongr
      · rw [ENNReal.coe_le_one_iff]
        exact (χ_le_indicator hJ).trans ((indicator_le fun _ _ ↦ le_refl _) _)
      · apply le_biSup _ mx
      · apply le_biSup _ mx
    _ ≤ ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      rw [one_mul]; gcongr
      · exact global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inl rfl) hJ hf₁
      · exact global_tree_control2 hu₁ hu₂ hu h2u hJ hf₂
    _ ≤ _ := by
      rw [P7_5_4, mul_mul_mul_comm]
      conv_rhs => rw [mul_add, mul_add]
      gcongr <;> (nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff])
      · exact one_le_C7_5_9s
      · exact one_le_C7_5_10

lemma holder_correlation_tree_1 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ 𝓘 u₁) :
    edist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x') *
    ‖exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x‖ₑ *
    ‖exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x‖ₑ ≤
    C7_5_2 a * C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) := by
  simp_rw [enorm_mul, enorm_exp_I_mul_ofReal, one_mul]
  by_cases mu₁ : x ∉ 𝓘 u₁
  · have : adjointCarlesonSum (t u₁) f₁ x = 0 := by
      refine Finset.sum_eq_zero fun p mp ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at mp
      rw [adjoint_tile_support2 hu₁ mp]
      exact indicator_of_not_mem mu₁ _
    rw [this, enorm_zero, mul_zero, zero_mul]; exact zero_le _
  rw [not_not] at mu₁; rw [edist_dist]
  calc
    _ ≤ ENNReal.ofReal (C7_5_2 a * dist x x' / D ^ s J) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      gcongr
      · exact dist_χ_le hu₁ hu₂ hu h2u hJ mu₁ mx'
      · exact (le_biSup _ mx).trans <|
          global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inl rfl) hJ hf₁
      · exact (le_biSup _ mx).trans <| global_tree_control2 hu₁ hu₂ hu h2u hJ hf₂
    _ ≤ ENNReal.ofReal (C7_5_2 a * dist x x' / D ^ s J) *
        (C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J) := by
      rw [mul_assoc (ENNReal.ofReal _)]; gcongr _ * ?_
      rw [P7_5_4, mul_mul_mul_comm]
      conv_rhs => rw [mul_add, mul_add]
      gcongr <;> (nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff])
      · exact one_le_C7_5_9s
      · exact one_le_C7_5_10
    _ = _ := by
      rw [mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_div_of_pos (by unfold defaultD; positivity), ← edist_dist x x',
        ← Real.rpow_intCast, ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a), ENNReal.rpow_intCast,
        ENNReal.ofReal_natCast]
      ring

lemma holder_correlation_tree_2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    χ t u₁ u₂ J x' * edist (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x)
      (exp (.I * 𝒬 u₁ x') * adjointCarlesonSum (t u₁) f₁ x') *
    ‖exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x‖ₑ ≤
    C7_5_9d a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ :=
  calc
    _ ≤ 1 * (C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      gcongr
      · rw [ENNReal.coe_le_one_iff]
        exact (χ_le_indicator hJ).trans ((indicator_le fun _ _ ↦ le_refl _) _)
      · exact global_tree_control1_edist_left hu₁ hu₂ hu h2u hJ hf₁ mx mx'
      · rw [enorm_mul, enorm_exp_I_mul_ofReal, one_mul]
        exact (le_biSup _ mx).trans <| global_tree_control2 hu₁ hu₂ hu h2u hJ hf₂
    _ = (C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      ring
    _ ≤ (C7_5_9d a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_10 a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr
      · exact le_add_self
      · nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff]
        exact one_le_C7_5_10
    _ = _ := by rw [← mul_add, ← mul_add, mul_mul_mul_comm, P7_5_4]

lemma holder_correlation_tree_3 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    χ t u₁ u₂ J x' * ‖exp (.I * 𝒬 u₁ x') * adjointCarlesonSum (t u₁) f₁ x'‖ₑ *
    edist (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)
      (exp (.I * 𝒬 u₂ x') * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x') ≤
    C7_5_9s a * C7_5_9d a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ :=
  calc
    _ ≤ 1 * ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      gcongr
      · rw [ENNReal.coe_le_one_iff]
        exact (χ_le_indicator hJ).trans ((indicator_le fun _ _ ↦ le_refl _) _)
      · rw [enorm_mul, enorm_exp_I_mul_ofReal, one_mul]
        exact (le_biSup _ mx').trans <|
          global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inl rfl) hJ hf₁
      · exact global_tree_control1_edist_right hu₁ hu₂ hu h2u hJ hf₂ mx mx'
    _ = ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      ring
    _ ≤ (C7_5_9s a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_9d a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr
      · nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff]
        exact one_le_C7_5_9s
      · exact le_add_self
    _ = _ := by rw [← mul_add, ← mul_add, mul_mul_mul_comm, P7_5_4]

/-- An intermediate constant in Lemma 7.5.4. -/
def I7_5_4 (a : ℕ) : ℝ≥0 :=
  32 * C7_5_2 a * C7_5_9s a * C7_5_10 a + C7_5_9d a * C7_5_10 a + C7_5_9s a * C7_5_9d a

lemma edist_holderFunction_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    edist (holderFunction t u₁ u₂ f₁ f₂ J x) (holderFunction t u₁ u₂ f₁ f₂ J x') ≤
    I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
  by_cases mu₁ : x ∉ 𝓘 u₁ ∧ x' ∉ 𝓘 u₁
  · have h0 := support_subset_iff'.mp (support_holderFunction_subset u₂ f₁ f₂ J hu₁)
    rw [h0 _ mu₁.1, h0 _ mu₁.2, edist_self]; exact zero_le _
  rw [not_and_or, not_not, not_not] at mu₁
  wlog mu₁' : x' ∈ 𝓘 u₁ generalizing x x'
  · specialize this mx' mx mu₁.symm (mu₁.resolve_right mu₁')
    rwa [edist_comm, edist_comm x'] at this
  let CH := χ t u₁ u₂ J
  let T₁ := fun z ↦ exp (.I * 𝒬 u₁ z) * adjointCarlesonSum (t u₁) f₁ z
  let T₂ := fun z ↦ exp (.I * 𝒬 u₂ z) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ z
  change ‖CH x * T₁ x * conj (T₂ x) - CH x' * T₁ x' * conj (T₂ x')‖ₑ ≤ _
  calc
    _ ≤ _ := edist_triangle4 _ (CH x' * T₁ x * conj (T₂ x)) (CH x' * T₁ x' * conj (T₂ x)) _
    _ = edist (CH x) (CH x') * ‖T₁ x‖ₑ * ‖T₂ x‖ₑ + CH x' * edist (T₁ x) (T₁ x') * ‖T₂ x‖ₑ +
        CH x' * ‖T₁ x'‖ₑ * edist (T₂ x) (T₂ x') := by
      simp_rw [edist_eq_enorm_sub, ← sub_mul, ← mul_sub, enorm_mul, ← RingHom.map_sub,
        RCLike.enorm_conj, ← ofReal_sub, Complex.enorm_real, NNReal.enorm_eq]
      rfl
    _ ≤ C7_5_2 a * C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) +
        C7_5_9d a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ +
        C7_5_9s a * C7_5_9d a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr ?_ + ?_ + ?_
      · exact holder_correlation_tree_1 hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mu₁'
      · exact holder_correlation_tree_2 hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mx'
      · exact holder_correlation_tree_3 hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mx'
    _ ≤ C7_5_2 a * C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J *
          (32 * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹) +
        C7_5_9d a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ +
        C7_5_9s a * C7_5_9d a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr
      rcases le_or_lt (edist x x' / D ^ s J) 1 with h | h
      · nth_rw 1 [← one_mul (_ / _), ← ENNReal.rpow_one (_ / _)]
        refine mul_le_mul' (by norm_num) (ENNReal.rpow_le_rpow_of_exponent_ge h ?_)
        rw [inv_le_one_iff₀]; right; exact_mod_cast a_pos X
      · nth_rw 1 [← mul_one (_ / _), ← ENNReal.one_rpow (a : ℝ)⁻¹]
        refine mul_le_mul' (ENNReal.div_le_of_le_mul ?_) (ENNReal.rpow_le_rpow h.le (by positivity))
        have hc : 32 * (D : ℝ≥0∞) ^ s J = ENNReal.ofReal (32 * D ^ s J) := by
          rw [ENNReal.ofReal_mul (by norm_num), ← Real.rpow_intCast,
            ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a), ENNReal.rpow_intCast,
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        rw [edist_dist, hc]; apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ dist x (c J) + dist x' (c J) := dist_triangle_right ..
          _ ≤ 16 * D ^ s J + 16 * D ^ s J := add_le_add (mem_ball.mp mx).le (mem_ball.mp mx').le
          _ = _ := by ring
    _ = _ := by
      rw [← mul_assoc, mul_comm _ 32]; simp_rw [← mul_assoc]
      rw [← add_mul, ← add_mul]; congr
      rw [← add_mul, ← add_mul]; congr

/-- The constant used in `holder_correlation_tree`.
Has value `2 ^ (529 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_4 (a : ℕ) : ℝ≥0 := 2 ^ (529 * (a : ℝ) ^ 3)

lemma le_C7_5_4 (a4 : 4 ≤ a) : C7_5_9s a * C7_5_10 a + 16 ^ τ * I7_5_4 a ≤ C7_5_4 a :=
  calc
    _ ≤ C7_5_9s a * C7_5_10 a + 2 * I7_5_4 a := by
      gcongr
      rw [defaultτ, show (16 : ℝ≥0) = 2 ^ (4 : ℝ) by norm_num, ← NNReal.rpow_mul, ← div_eq_mul_inv]
      nth_rw 2 [← NNReal.rpow_one 2]; apply NNReal.rpow_le_rpow_of_exponent_le one_le_two
      rw [div_le_one_iff]; norm_cast; omega
    _ ≤ 32 * C7_5_2 a * C7_5_9s a * C7_5_10 a +
        2 * (32 * C7_5_2 a * C7_5_9s a * C7_5_10 a +
        8 * C7_5_2 a * C7_5_9s a * C7_5_10 a +
        8 * C7_5_2 a * C7_5_9s a * C7_5_10 a) := by
      unfold I7_5_4; gcongr ?_ + 2 * (_ + ?_ + ?_)
      · nth_rw 1 [← one_mul (_ * _), mul_assoc]; gcongr
        exact one_le_mul (by norm_num) one_le_C7_5_2
      · rw [show C7_5_9d a * C7_5_10 a = 1 * 1 * C7_5_9d a * C7_5_10 a by ring]; gcongr
        · norm_num
        · exact one_le_C7_5_2
        · exact C7_5_9d_le_C7_5_9s
      · rw [show C7_5_9s a * C7_5_9d a = 1 * 1 * C7_5_9d a * C7_5_9s a by ring]; gcongr
        · norm_num
        · exact one_le_C7_5_2
        · exact C7_5_9d_le_C7_5_9s
        · exact C7_5_9s_le_C7_5_10
    _ = 2 ^ 7 * C7_5_2 a * C7_5_9s a * C7_5_10 a := by ring
    _ ≤ 2 ^ 7 * C7_5_2 a * C7_5_9s a * (2 * C7_5_9s a) := by
      rw [C7_5_10, C7_5_9s, two_mul, C7_5_7, C7_5_5]; gcongr; norm_cast
      rw [← pow_add]; apply pow_le_pow_right' one_le_two; omega
    _ = 2 ^ 8 * C7_5_2 a * C7_5_9s a ^ 2 := by ring
    _ = 2 ^ (528 * a ^ 3 + 8 * a + 14) := by
      rw [C7_5_2, ← Nat.cast_pow, show (226 : ℝ) = (226 : ℕ) by rfl, ← Nat.cast_mul,
        NNReal.rpow_natCast, ← pow_add, C7_5_9s, C7_5_5, ← Nat.cast_pow,
        show (151 : ℝ) = (151 : ℕ) by rfl, ← Nat.cast_mul, NNReal.rpow_natCast]
      ring
    _ ≤ _ := by
      rw [C7_5_4, ← Nat.cast_pow, show (529 : ℝ) = (529 : ℕ) by rfl, ← Nat.cast_mul,
        NNReal.rpow_natCast, add_assoc, show 529 * a ^ 3 = 528 * a ^ 3 + a ^ 3 by ring]
      refine pow_le_pow_right' one_le_two (add_le_add_left ?_ _)
      calc
        _ ≤ 2 * 4 * a + 1 * 4 * 4 := by omega
        _ ≤ 2 * a * a + 2 * a * a := by gcongr; omega
        _ = 4 * a ^ 2 := by ring
        _ ≤ _ := by rw [pow_succ' _ 2]; gcongr

/-- Lemma 7.5.4. -/
lemma holder_correlation_tree (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂) :
    iHolENorm (holderFunction t u₁ u₂ f₁ f₂ J) (c J) (16 * D ^ s J) ≤
    C7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J := by
  unfold iHolENorm
  calc
    _ ≤ C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J +
        ENNReal.ofReal (16 * D ^ s J) ^ τ *
        ⨆ x ∈ ball (c J) (16 * D ^ s J), ⨆ y ∈ ball (c J) (16 * D ^ s J), ⨆ (_ : x ≠ y),
          (I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J * ((D : ℝ≥0∞) ^ s J)⁻¹ ^ (a : ℝ)⁻¹) := by
      gcongr with x mx x' mx' hn
      · exact iSup₂_le_iff.mpr fun x mx ↦ enorm_holderFunction_le hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx
      · calc
          _ ≤ I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J *
              (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ / edist x x' ^ τ :=
            ENNReal.div_le_div_right (edist_holderFunction_le hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mx') _
          _ = _ := by
            have dn0 : edist x x' ≠ 0 := by rw [← zero_lt_iff]; exact edist_pos.mpr hn
            rw [mul_div_assoc, defaultτ, ← ENNReal.div_rpow_of_nonneg _ _ (by positivity),
              div_eq_mul_inv, div_eq_mul_inv, ← mul_rotate _ (edist x x'),
              ENNReal.inv_mul_cancel dn0 (edist_ne_top x x'), one_mul]
    _ ≤ C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J +
        ENNReal.ofReal (16 * D ^ s J) ^ τ *
        (I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J * ((D : ℝ≥0∞) ^ s J)⁻¹ ^ (a : ℝ)⁻¹) := by
      gcongr; exact iSup₂_le fun _ _ ↦ iSup₂_le fun _ _ ↦ iSup_le fun _ ↦ le_rfl
    _ = (C7_5_9s a * C7_5_10 a + 16 ^ τ * I7_5_4 a) * P7_5_4 t u₁ u₂ f₁ f₂ J := by
      have dn0 : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ 0 := by
        rw [← pos_iff_ne_zero]; refine ENNReal.rpow_pos_of_nonneg ?_ (by positivity)
        exact ENNReal.zpow_pos (by unfold defaultD; positivity) (ENNReal.natCast_ne_top _) _
      have dnt : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ ⊤ := by
        apply ENNReal.rpow_ne_top_of_nonneg (τ_nonneg X)
        rw [← lt_top_iff_ne_top]
        exact ENNReal.zpow_lt_top (by unfold defaultD; positivity) (ENNReal.natCast_ne_top _) _
      rw [add_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.mul_rpow_of_nonneg _ _ (τ_nonneg X), ← Real.rpow_intCast,
        ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a), ENNReal.rpow_intCast, ENNReal.ofReal_natCast,
        ← mul_assoc, ← mul_rotate _ (_ ^ _), mul_assoc _ (_ ^ τ), defaultτ, ENNReal.inv_rpow,
        ENNReal.mul_inv_cancel dn0 dnt, mul_one, mul_rotate (_ ^ _)]
    _ ≤ _ := by
      gcongr
      rw [show (16 : ℝ≥0∞) = (16 : ℝ≥0) by rfl, ← ENNReal.coe_rpow_of_nonneg _ (τ_nonneg X),
        ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe]
      exact le_C7_5_4 (four_le_a X)

/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/

/-- The constant used in `lower_oscillation_bound`.
Has value `2 ^ (Z * n / 2 - 201 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_11 (a n : ℕ) : ℝ≥0 := 2 ^ (Z * n / 2 - 201 * (a : ℝ) ^ 3)

/-- Lemma 7.5.11 -/
lemma lower_oscillation_bound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    C7_5_11 a n ≤ dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
  have existsBiggerThanJ : ∃ (J' : Grid X), J ≤ J' ∧ s J' = s J + 1 := by
    apply Grid.exists_scale_succ
    obtain ⟨⟨Jin𝓙₀, _⟩, ⟨jIsSubset : (J : Set X) ⊆ 𝓘 u₁, smaller : s J ≤ s (𝓘 u₁)⟩⟩ := hJ
    obtain ⟨p, belongs⟩ := t.nonempty' hu₁
    apply lt_of_le_of_ne smaller
    by_contra! h
    have u₁In𝓙₀ : 𝓘 u₁ ∈ 𝓙₀ (t.𝔖₀ u₁ u₂) := by
      apply mem_of_eq_of_mem (h := Jin𝓙₀)
      rw [eq_comm]
      apply (eq_or_disjoint h).resolve_right
      have notDisjoint := IF_subset_THEN_not_disjoint jIsSubset
      rw [disjoint_comm] at notDisjoint
      exact notDisjoint
    cases u₁In𝓙₀ with
    | inl min =>
      have sameScale : s (𝓘 p) = s (𝓘 u₁) := by
        linarith [
          (scale_mem_Icc (i := 𝓘 p)).left,
          show s (𝓘 p) ≤ s (𝓘 u₁) by exact (𝓘_le_𝓘 t hu₁ belongs).2
        ]
      suffices s (𝓘 u₁) > s (𝓘 p) by linarith
      by_contra! smaller
      have pIsSubset := (𝓘_le_𝓘 t hu₁ belongs).1
      apply HasSubset.Subset.not_ssubset
        ((fundamental_dyadic smaller).resolve_right (IF_subset_THEN_not_disjoint pIsSubset))
      apply HasSubset.Subset.ssubset_of_ne pIsSubset
      by_contra! sameSet
      apply Forest.𝓘_ne_𝓘 (hu := hu₁) (hp := belongs)
      exact Grid.inj (Prod.ext sameSet sameScale)
    | inr avoidance =>
      have pIn𝔖₀ : p ∈ t.𝔖₀ u₁ u₂ :=
        𝔗_subset_𝔖₀ (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u) belongs
      apply avoidance p pIn𝔖₀
      calc (𝓘 p : Set X)
      _ ⊆ 𝓘 u₁ := (𝓘_le_𝓘 t hu₁ belongs).1
      _ ⊆ ball (c (𝓘 u₁)) (4 * D ^ s (𝓘 u₁)) := by
        exact Grid_subset_ball
      _ ⊆ ball (c (𝓘 u₁)) (100 * D ^ (s (𝓘 u₁) + 1)) := by
        intro x hx
        exact gt_trans (calculation_16 (X := X) (s := s (𝓘 u₁))) hx
  rcases existsBiggerThanJ with ⟨J', JleJ', scaleSmaller⟩
  have notIn𝓙₀ : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := by
    apply bigger_than_𝓙_is_not_in_𝓙₀ (sle := by linarith) (le := JleJ')
    exact mem_of_mem_inter_left hJ
  unfold 𝓙₀ at notIn𝓙₀
  simp only [mem_setOf_eq, not_or, not_forall, Classical.not_imp, Decidable.not_not] at notIn𝓙₀
  push_neg at notIn𝓙₀
  obtain ⟨_, ⟨ p, pIn, pSubset ⟩⟩ := notIn𝓙₀
  have thus :=
    calc 2 ^ ((Z : ℝ) * n / 2)
    _ ≤ dist_{𝔠 p, D ^ 𝔰 p / 4} (𝒬 u₁) (𝒬 u₂) := pIn.2
    _ ≤ dist_{c J, 128 * D^(s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      apply cdist_mono
      intro point pointIn
      calc dist point (c J)
      _ ≤ dist point (c J') + dist (c J') (c J) := dist_triangle ..
      _ ≤ 100 * D ^ (s J' + 1) + dist (c J') (c J) := by
        rw [ball, Set.subset_def] at pSubset
        have := pSubset point (ball_subset_Grid pointIn)
        rw [mem_setOf_eq] at this
        gcongr
      _ ≤ 100 * D ^ (s J' + 1) + 4 * D ^ (s J') := by
        have : dist (c J) (c J') < 4 * D ^ (s J') :=
          IF_subset_THEN_distance_between_centers (subset := JleJ'.1)
        rw [dist_comm] at this
        gcongr
      _ = 100 * D ^ (s J + 2) + 4 * D ^ (s J + 1) := by
        rw [scaleSmaller, add_assoc, show (1 : ℤ) + 1 = 2 by rfl]
      _ < 128 * D^(s J + 2) := by
        exact calculation_11 (s J) (X := X)
    _ ≤ 2 ^ (200 * (a^3) + 4 * a) * dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
      rw [show 128 * (D : ℝ)^(s J + 2) = 2^(200*a^2 + 4) * (8*D^(s J))
        by exact_mod_cast calculation_12 (s := s J)]
      rw [calculation_13]
      apply cdist_le_iterate
      have := defaultD_pos a
      positivity
  rw [C7_5_11]
  push_cast
  linarith [calculation_14 (X := X) (n := n), calculation_15 thus]

/-- The constant used in `correlation_distant_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_5 (a n : ℕ) : ℝ≥0 := 2 ^ (541 * (a : ℝ) ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))

/-- Lemma 7.4.5 -/
lemma correlation_distant_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)‖ₑ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) ·) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) ·) 2 volume := by
  sorry

end TileStructure.Forest
