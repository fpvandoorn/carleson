import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set TopologicalSpace Function
open scoped ENNReal
noncomputable section

/-! The function `ψ` -/

section D
variable {D x : ℝ} {s : ℤ}

def ψ (D x : ℝ) : ℝ :=
  max 0 <| min 1 <| min (4 * D * x - 1) (2 - 2 * x)

set_option hygiene false
scoped[ShortVariables] notation "ψ" => ψ (defaultD a)


lemma support_ψ : support (ψ D) = Ioo (4 * D)⁻¹ 2⁻¹ := sorry
lemma lipschitzWith_ψ (D : ℝ≥0) : LipschitzWith (4 * D) (ψ D) := sorry
lemma finsum_ψ : ∑ᶠ s : ℤ, ψ D (D ^ s * x) = 1 := sorry

/- the one or two numbers `s` where `ψ (D ^ s * x)` is possibly nonzero -/
variable (D) in def nonzeroS (x : ℝ) : Finset ℤ :=
  Finset.Icc ⌊- Real.logb D (4 * x)⌋ ⌈- (1 + Real.logb D (2 * x))⌉

lemma sum_ψ : ∑ s in nonzeroS D x, ψ D (D ^ s * x) = 1 := sorry

-- move
theorem Int.floor_le_iff (c : ℝ) (z : ℤ) : ⌊c⌋ ≤ z ↔ c < z + 1 := by
  rw_mod_cast [← Int.floor_le_sub_one_iff, add_sub_cancel_right]

theorem Int.le_ceil_iff (c : ℝ) (z : ℤ) : z ≤ ⌈c⌉ ↔ z - 1 < c := by
  rw_mod_cast [← Int.add_one_le_ceil_iff, sub_add_cancel]

lemma mem_nonzeroS_iff {i : ℤ} {x : ℝ} (hx : 0 < x) (hD : 1 < D) :
    i ∈ nonzeroS D x ↔ (D ^ i * x) ∈ Ioo (4 * D)⁻¹ 2⁻¹ := by
  rw [Set.mem_Ioo, nonzeroS, Finset.mem_Icc]
  simp only [Int.floor_le_iff, neg_add_rev, Int.le_ceil_iff, lt_add_neg_iff_add_lt, sub_add_cancel,
    mul_inv_rev]
  rw [← lt_div_iff hx, mul_comm D⁻¹, ← div_lt_div_iff hx (by positivity), ← Real.logb_inv,
    ← Real.logb_inv, div_inv_eq_mul, ← zpow_add_one₀ (by positivity)]
  simp_rw [← Real.rpow_intCast]
  rw [Real.lt_logb_iff_rpow_lt hD (by positivity), Real.logb_lt_iff_lt_rpow hD (by positivity)]
  simp [div_eq_mul_inv, mul_comm]

lemma psi_ne_zero_iff {x : ℝ} (hx : 0 < x) (hD : 1 < D) :
    ψ D (D ^ s * x) ≠ 0 ↔ s ∈ nonzeroS D x := by
  rw [← mem_support, support_ψ, mem_nonzeroS_iff hx hD]

lemma psi_eq_zero_iff {x : ℝ} (hx : 0 < x) (hD : 1 < D) :
    ψ D (D ^ s * x) = 0 ↔ s ∉ nonzeroS D x := by
  rw [← iff_not_comm, ← psi_ne_zero_iff hx hD]

end D

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
variable {s : ℤ} {x y : X}

/-- K_s in the blueprint -/
@[nolint unusedArguments]
def Ks [ProofData a q K σ₁ σ₂ F G] (s : ℤ) (x y : X) : ℂ :=
  K x y * ψ (D ^ s * dist x y)

lemma sum_Ks {t : Finset ℤ} (hs : nonzeroS D (dist x y) ⊆ t) (hD : 1 < D) (h : 0 < dist x y) :
    ∑ i in t, Ks i x y = K x y := by
  simp_rw [Ks, ← Finset.mul_sum]
  norm_cast
  suffices ∑ i in t, ψ (D ^ i * dist x y) = 1 by
    simp [-defaultD, this]
  rw [← Finset.sum_subset hs, sum_ψ]
  intros
  rwa [psi_eq_zero_iff h hD]

lemma sum_Ks' {s : Finset ℤ}
    (hs : ∀ i : ℤ, (D ^ i * dist x y) ∈ Ioo (4 * D)⁻¹ 2⁻¹ → i ∈ s)
    (hD : 1 < D) (h : x ≠ y) : ∑ i in s, Ks i x y = K x y := sorry
