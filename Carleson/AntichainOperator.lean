import Carleson.GridStructure

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

open scoped GridStructure
open Set

-- Lemma 6.1.1
lemma E_disjoint (σ σ' : X → ℤ) {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (·≤·) 𝔄) {p p' : 𝔓 X}
    (hp : p ∈ 𝔄) (hp' : p' ∈ 𝔄) (hE : (E p ∩ E p').Nonempty) : p = p' := by
  set x := hE.some
  have hx := hE.some_mem
  simp only [E, mem_inter_iff, mem_setOf_eq] at hx
  wlog h𝔰 : 𝔰 p ≤ 𝔰 p'
  · have hE' : (E p' ∩ E p).Nonempty := by simp only [inter_comm, hE]
    exact eq_comm.mp (this σ σ' h𝔄 hp' hp hE' hE'.some_mem (le_of_lt (not_le.mp h𝔰)))
  obtain ⟨⟨hx𝓓p, hxΩp, _⟩ , hx𝓓p', hxΩp', _⟩ := hx
  have h𝓓 : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 p') :=
    (or_iff_left (not_disjoint_iff.mpr ⟨x, hx𝓓p, hx𝓓p'⟩)).mp (fundamental_dyadic h𝔰)
  have hΩ : Ω p' ≤ Ω p :=
    (or_iff_right (not_disjoint_iff.mpr ⟨Q x, hxΩp, hxΩp'⟩)).mp (relative_fundamental_dyadic h𝓓)
  have hle : p ≤ p' := ⟨h𝓓, hΩ⟩
  exact IsAntichain.eq h𝔄 hp hp' hle

variable (K : X → X → ℂ) (σ₁ σ₂ : X → ℤ) (ψ : ℝ → ℝ) (p : 𝔓 X)
--(f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)

-- lemma 6.1.2
-- Q : `p : 𝔄` or `p ∈ 𝔄`?
lemma MaximalBoundAntichain {a : ℝ} (ha : 4 ≤ a) {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (·≤·) 𝔄)
    {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (x : X) :
    Complex.abs (∑' (p : 𝔄), T K σ₁ σ₂ ψ p F f x) ≤ 2^(107*a^3)/-*M_B (f x)-/ := by
  by_cases hx : ∃ (p : 𝔄), T K σ₁ σ₂ ψ p F f x ≠ 0
  · obtain ⟨p, hpx⟩ := hx
    have hne_p : ∀ (p' : 𝔄) (hp' : p' ≠ p), T K σ₁ σ₂ ψ (↑p') F f x = 0 := by
      intro p' hpp'
      sorry
    sorry
  · simp only [ne_eq, Subtype.exists, exists_prop, not_exists, not_and, Decidable.not_not] at hx
    have h0 : (∑' (p : 𝔄), T K σ₁ σ₂ ψ p F f x) = (∑' (p : 𝔄), 0)  := by
      congr
      ext p
      exact hx p p.2
    rw [h0]
    sorry--simp only [tsum_zero, map_zero, ge_iff_le, Nat.ofNat_nonneg, pow_nonneg]

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

--  MeasureTheory.snorm
-- lemma 6.1.3
lemma Dens2Antichain  {a : ℝ} (ha : 4 ≤ a) {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) {𝔄 : Set (𝔓 X)}
    (h𝔄 : IsAntichain (·≤·) 𝔄) {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    {G : Set X} {g : X → ℂ} (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x) (x : X) :
    Complex.abs (∫ x, ((starRingEnd ℂ) (g x)) * ∑' (p : 𝔄), T K σ₁ σ₂ ψ p F f x) ≤
      2^(111*a^3)*(q-1)⁻¹/-* dens2(𝔄)^{1/q - 1/2} *‖f‖_2*‖g‖_2}-/  := by
  have hf1 : f = (F.indicator 1) * f := eq_indicator_one_mul hf
  set q' := 2*q/(1 + q) with hq'
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have h1q' : 1 ≤ q' := by -- Better proof?
    rw [hq', one_le_div]
    linarith
    exact add_pos (zero_lt_one) hq0
  have hqq' : q' ≤ q := by -- Better proof?
    rw [hq', div_le_iff (add_pos (zero_lt_one) hq0), mul_comm, mul_le_mul_iff_of_pos_left hq0]
    linarith
  sorry

-- ‖∫ x in G \ G', ∑' p, T K σ₁ σ₂ (ψ (D2_2 a)) p F 1 x‖₊ ≤
