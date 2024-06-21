import Carleson.GridStructure

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

noncomputable section

open scoped GridStructure ComplexConjugate
open Set Complex MeasureTheory

-- Lemma 6.1.1
lemma E_disjoint (σ σ' : X → ℤ) {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
     {p p' : 𝔓 X} (hp : p ∈ 𝔄) (hp' : p' ∈ 𝔄) (hE : (E p ∩ E p').Nonempty) : p = p' := by
  set x := hE.some
  have hx := hE.some_mem
  simp only [E, mem_inter_iff, mem_setOf_eq] at hx
  wlog h𝔰 : 𝔰 p ≤ 𝔰 p'
  · have hE' : (E p' ∩ E p).Nonempty := by simp only [inter_comm, hE]
    exact eq_comm.mp (this σ σ' h𝔄 hp' hp hE' hE'.some_mem (le_of_lt (not_le.mp h𝔰)))
  obtain ⟨⟨hx𝓓p, hxΩp, _⟩ , hx𝓓p', hxΩp', _⟩ := hx
  have h𝓓 : 𝓘 p ⊆ 𝓘 p' :=
    (or_iff_left (not_disjoint_iff.mpr ⟨x, hx𝓓p, hx𝓓p'⟩)).mp (fundamental_dyadic h𝔰)
  have hΩ : Ω p' ≤ Ω p :=
    (or_iff_right (not_disjoint_iff.mpr ⟨Q x, hxΩp, hxΩp'⟩)).mp (relative_fundamental_dyadic h𝓓)
  have hle : p ≤ p' := ⟨h𝓓, hΩ⟩
  exact IsAntichain.eq h𝔄 hp hp' hle

variable (K : X → X → ℂ) (σ₁ σ₂ : X → ℤ) (p : 𝔓 X)

open MeasureTheory Metric
open NNReal Real

noncomputable def C_6_1_2 (a : ℝ) : ℝ≥0 := (2 : ℝ≥0)^(107*a^3)

-- This doesn't work here?
--local notation "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
--B(c p, 8D^s p)


-- lemma 6.1.2
lemma MaximalBoundAntichain {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
    {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (x : X) :
    ‖∑ (p ∈ 𝔄), T p f x‖₊ ≤ (C_6_1_2 a) * MB (fun (𝔭 : 𝔄) ↦ (𝔠 𝔭.1, 8*D ^ 𝔰 𝔭.1)) f x := by
  by_cases hx : ∃ (p : 𝔄), T p f x ≠ 0
  · obtain ⟨p, hpx⟩ := hx
    have hne_p : ∀ (p' : 𝔄) (hp' : p' ≠ p), T (↑p') f x = 0 := by
      intro p' hpp'
      sorry
    sorry
  · simp only [ne_eq, Subtype.exists, exists_prop, not_exists, not_and, Decidable.not_not] at hx
    have h0 : (∑ (p ∈ 𝔄), T p f x) = (∑ (p ∈ 𝔄), 0) := Finset.sum_congr rfl (fun  p hp ↦ hx p hp)
    rw [h0]
    simp only [defaultA, defaultD, defaultκ, Finset.sum_const_zero, nnnorm_zero, ENNReal.coe_zero,
      zero_le]

lemma _root_.Set.eq_indicator_one_mul {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    f = (F.indicator 1) * f := by
  ext y
  simp only [Pi.mul_apply, indicator, Pi.one_apply, ite_mul, one_mul, zero_mul]
  split_ifs with hy
  · rfl
  · specialize hf y
    simp only [indicator, hy, ↓reduceIte] at hf
    rw [← norm_eq_zero]
    exact le_antisymm hf (norm_nonneg _)

noncomputable def C_6_1_3 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2^(111*a^3)*(q-1)⁻¹

-- lemma 6.1.3
lemma Dens2Antichain {a : ℝ} (ha : 4 ≤ a) {q : ℝ≥0} (hq1 : 1 < q) (hq2 : q ≤ 2) {𝔄 : Finset (𝔓 X)}
    (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X))) {F : Set X} {f : X → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) {G : Set X} {g : X → ℂ} (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (x : X) :
    ‖∫ x, ((starRingEnd ℂ) (g x)) * ∑ (p ∈ 𝔄), T p f x‖₊ ≤
      (C_6_1_3 a q) * (dens₂ (𝔄 : Set (𝔓 X))) * (snorm f 2 volume) * (snorm f 2 volume) := by
  have hf1 : f = (F.indicator 1) * f := eq_indicator_one_mul hf
  set q' := 2*q/(1 + q) with hq'
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have h1q' : 1 ≤ q' := by -- Better proof?
    rw [hq', one_le_div (add_pos_iff.mpr (Or.inl zero_lt_one)), two_mul, add_le_add_iff_right]
    exact le_of_lt hq1
  have hqq' : q' ≤ q := by -- Better proof?
    rw [hq', div_le_iff (add_pos (zero_lt_one) hq0), mul_comm, mul_le_mul_iff_of_pos_left hq0,
      ← one_add_one_eq_two, add_le_add_iff_left]
    exact le_of_lt hq1
  sorry

/-- Constant appearing in Proposition 2.0.3. -/
def C_2_0_3 (a q : ℝ) : ℝ := 2 ^ (150 * a ^ 3) / (q - 1)

/-- Proposition 2.0.3 -/
theorem antichain_operator {𝔄 : Set (𝔓 X)} {f g : X → ℂ} {q : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (h𝔄 : IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄)) :
    ‖∫ x, conj (g x) * ∑ᶠ p : 𝔄, T p f x‖ ≤
    C_2_0_3 a q * (dens₁ 𝔄).toReal ^ ((q - 1) / (8 * a ^ 4)) * (dens₂ 𝔄).toReal ^ (q⁻¹ - 2⁻¹) *
    (snorm f 2 volume).toReal * (snorm g 2 volume).toReal := sorry
