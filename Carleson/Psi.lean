import Carleson.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Topology.CompletelyRegular
import Mathlib.Topology.EMetricSpace.Paracompact

open MeasureTheory Measure NNReal Metric Set TopologicalSpace Function DoublingMeasure
open scoped ENNReal
noncomputable section

/-! The function `ψ` -/

section D
variable {D : ℕ} {x : ℝ} {s : ℤ} (hD : 1 < (D : ℝ))

open Real

section -- We record here some trivial inequalities that are used repeatedly below.
private lemma fourD0' (hD : 1 ≤ D) : 0 < (4 * D : ℝ) := by positivity
private lemma four_x0 {x : ℝ} (hx : 0 < x) : 0 < 4 * x := mul_pos four_pos hx
include hD
private lemma D0 : 0 < (D : ℝ) := one_pos.trans hD
private lemma D2 : 2 ≤ (D : ℝ) := by exact_mod_cast hD
private lemma twoD0 : 0 < (2 * D : ℝ) := by linarith
private lemma fourD0 : 0 < (4 * D : ℝ) := by linarith
private lemma D_pow0 (r : ℝ) : 0 < (D : ℝ) ^ r := by positivity
private lemma D_pow0' (r : ℤ) : 0 < (D : ℝ) ^ r := by positivity
private lemma cDx0 {c x : ℝ} (hc : c > 0) (hx : 0 < x) : c * D * x > 0 := by positivity
end

def ψ (D : ℕ) (x : ℝ) : ℝ :=
  max 0 <| min 1 <| min (4 * D * x - 1) (2 - 4 * x)

set_option hygiene false
scoped[ShortVariables] notation "ψ" => ψ (defaultD a)

lemma zero_le_ψ (D : ℕ) (x : ℝ) : 0 ≤ ψ D x :=
  le_max_left 0 _

lemma ψ_le_one (D : ℕ) (x : ℝ) : ψ D x ≤ 1 :=
  max_le (one_pos.le) (min_le_left 1 _)

lemma abs_ψ_le_one (D : ℕ) (x : ℝ) : |ψ D x| ≤ 1 :=
  abs_le.2 ⟨by linarith [zero_le_ψ D x], ψ_le_one D x⟩

---------------------------------------------
/- `ψ_formula₀` through `ψ_formula₄` establish the piecewise formula for `ψ`. -/

lemma ψ_formula₀ {x : ℝ} (hx : x ≤ 1 / (4 * D : ℝ)) : ψ D x = 0 := by
  by_cases hD : D = 0
  · simp [ψ, hD]
  · exact max_eq_left <| (min_le_right 1 _).trans <| (min_le_left _ _).trans <|
      tsub_nonpos.2 <| (le_div_iff₀' (mul_pos four_pos
      (by exact_mod_cast Nat.zero_lt_of_ne_zero hD))).1 hx

include hD in
lemma ψ_formula₁ {x : ℝ} (hx : 1 / (4 * D) ≤ x ∧ x ≤ 1 / (2 * D)) :
    ψ D x = 4 * D * x - 1 := by
  have : x ≥ 0 := le_trans (one_div_nonneg.2 (fourD0 hD).le) hx.1
  have hx1 := (div_le_iff₀' (fourD0 hD)).1 hx.1
  have hx2 := (le_div_iff₀' (twoD0 hD)).1 hx.2
  have ineq₀ : 4 * D * x - 1 ≤ 2 - 4 * x := by
    suffices (2 * D + 2 * D + 4) * x ≤ 3 by linarith
    exact le_trans (by gcongr; linarith [D2 hD]) (by linarith: (2 * D + 2 * D + 2 * D) * x ≤ 3)
  have ineq₁ : 4 * D * x - 1 ≤ 1 := by linarith
  have ineq₂ : 0 ≤ 4 * D * x - 1 := by linarith
  rw [ψ, min_eq_left ineq₀, min_eq_right ineq₁, max_eq_right ineq₂]

include hD in
lemma ψ_formula₂ {x : ℝ} (hx : 1 / (2 * D) ≤ x ∧ x ≤ 1 / 4) : ψ D x = 1 := by
  unfold ψ
  suffices min 1 (min (4 * D * x - 1) (2 - 4 * x)) = 1 from this.symm ▸ max_eq_right_of_lt one_pos
  have := (div_le_iff₀' (twoD0 hD)).1 hx.1
  exact min_eq_left (le_min (by linarith) (by linarith))

include hD in
lemma ψ_formula₃ {x : ℝ} (hx : 1 / 4 ≤ x ∧ x ≤ 1 / 2) : ψ D x = 2 - 4 * x := by
  have ineq₀ : 2 - 4 * x ≤ 4 * D * x - 1 := by nlinarith [D2 hD]
  have ineq₁ : 2 - 4 * x ≤ 1 := by linarith
  have ineq₂ : 2 - 4 * x ≥ 0 := by linarith
  rw [ψ, min_eq_right ineq₀, min_eq_right ineq₁, max_eq_right ineq₂]

lemma ψ_formula₄ {x : ℝ} (hx : x ≥ 1 / 2) : ψ D x = 0 :=
  max_eq_left <| (min_le_right _ _).trans <| (min_le_right _ _).trans (by linarith)
---------------------------------------------

lemma psi_zero : ψ D 0 = 0 := ψ_formula₀ (by positivity)

lemma continuous_ψ : Continuous (ψ D) := by
  unfold ψ; fun_prop

include hD in
lemma support_ψ : support (ψ D) = Ioo (4 * D : ℝ)⁻¹ 2⁻¹ := by
  ext x
  by_cases hx₀ : x ≤ 1 / (4 * D)
  · suffices x ≤ (D : ℝ)⁻¹ * 4⁻¹ by simp [ψ_formula₀ hx₀, this]
    rwa [one_div, mul_inv_rev] at hx₀
  push_neg at hx₀
  have hx₀_inv : (D : ℝ)⁻¹ * 4⁻¹ < x := by convert hx₀ using 1; simp
  have ne₀ : 4 * D * x - 1 ≠ 0 := ne_of_gt (by rwa [sub_pos, ← div_lt_iff₀' (fourD0 hD)])
  by_cases hx₁ : x ≤ 1 / (2 * D)
  · suffices (D : ℝ)⁻¹ * 4⁻¹ < x ∧ x < 2⁻¹ by simpa [ne₀, ψ_formula₁ hD ⟨hx₀.le, hx₁⟩]
    exact ⟨hx₀_inv, lt_of_le_of_lt hx₁ (by simp [_root_.inv_lt_one_iff₀, hD])⟩
  push_neg at hx₁
  by_cases hx₂ : x ≤ 1 / 4
  · simpa [ψ_formula₂ hD ⟨hx₁.le, hx₂⟩, hx₀_inv] using lt_of_le_of_lt hx₂ (by norm_num)
  push_neg at hx₂
  by_cases hx₃ : x < 1 / 2
  · have : ¬ 2 - 4 * x = 0 := by linarith
    simpa [ψ_formula₃ hD ⟨hx₂.le, hx₃.le⟩, hx₀, hx₃, ← one_div]
  · rw [mem_support, ψ_formula₄ (not_lt.1 hx₃), ne_self_iff_false, false_iff, mem_Ioo, not_and,
      inv_eq_one_div 2]
    exact fun _ ↦ hx₃

lemma lipschitzWith_ψ (hD : 1 ≤ D) : LipschitzWith (4 * D) (ψ D) := by
  have max_eq_4D : max 0 (4 * D : ℝ≥0) = 4 * D := max_eq_right (fourD0' hD).le
  have max_eq_4D' : max (4 * D) 4 = 4 * D := by apply max_eq_left; linarith
  suffices LipschitzWith (4 * D) (fun (x : ℝ) ↦ min 1 <| min (4 * D * x - 1) (2 - 4 * x)) from
    max_eq_4D ▸ (LipschitzWith.const 0).max this
  suffices LipschitzWith (4 * D) (fun (x : ℝ) ↦ min (4 * D * x - 1) (2 - 4 * x)) from
    max_eq_4D ▸ (LipschitzWith.const 1).min this
  have lw1 : LipschitzWith (4 * D) (fun (x : ℝ) ↦ 4 * D * x - 1) := by
    refine LipschitzWith.of_le_add_mul (4 * D) (fun x y ↦ ?_)
    suffices 4 * D * (x - y) ≤ 4 * D * dist x y by norm_cast at this ⊢; linarith
    exact (mul_le_mul_left (fourD0' hD)).2 <| sub_le_dist x y
  have lw2 : LipschitzWith 4 (fun (x : ℝ) ↦ 2 - 4 * x) := by
    refine LipschitzWith.of_le_add_mul 4 (fun x y ↦ ?_)
    suffices 4 * (y - x) ≤ 4 * dist x y by norm_cast at this ⊢; linarith
    gcongr
    exact dist_comm x y ▸ sub_le_dist y x
  have := lw1.min lw2
  norm_cast at this ⊢
  convert max_eq_4D' ▸ this

-- Alternate version of `lipschitzWith_ψ` that avoids using `ENNReal`.
lemma lipschitzWith_ψ' (hD : 1 ≤ D) (a b : ℝ) : ‖ψ D a - ψ D b‖ ≤ 4 * D * dist a b := by
  have lipschitz := lipschitzWith_ψ hD a b
  rw [edist_dist, edist_dist, dist_eq_norm_sub] at lipschitz
  norm_cast at lipschitz
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by exact_mod_cast (fourD0' hD).le),
    ← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top] at lipschitz
  repeat rw [ENNReal.toReal_ofReal (by positivity)] at lipschitz
  norm_cast

/- the one or two numbers `s` where `ψ (D ^ (-s) * x)` is possibly nonzero -/
variable (D) in def nonzeroS (x : ℝ) : Finset ℤ :=
  Finset.Icc ⌊(1 + logb D (2 * x))⌋ ⌈logb D (4 * x)⌉

---------------------------------------------

section include_hD

/- The goal of the next several lemmas is to prove `sum_ψ`, which says that
`∑ s in nonzeroS D x, ψ D (D ^ (-s) * x) = 1`.

The first four lemmas prove some properties of the endpoints of `nonzeroS D x`, and in particular
show that `nonzeroS D x` has either 1 or 2 elements. The next two lemmas prove `sum_ψ` in the
1-element and 2-element cases, respectively, and then `sum_ψ` follows immediately.
-/

include hD

private lemma le_div_ceil_mul (hx : 0 < x) : 1 / (4 * D) ≤ D ^ (-⌈logb D (4 * x)⌉) * x := by
  rw [← div_le_iff₀ hx, div_div, ← rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD four_pos hx),
    ← inv_eq_one_div, (by norm_cast : (D : ℝ) ^ (-⌈logb D (4 * x)⌉) = D ^ (-⌈logb D (4 * x)⌉ : ℝ)),
    ← rpow_neg (D0 hD).le, rpow_le_rpow_left_iff hD, neg_le_neg_iff]
  apply le_of_le_of_eq <| calc
    (⌈logb D (4 * x)⌉ : ℝ) ≤ ⌊logb D (4 * x)⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one _
    _                     ≤ logb D (4 * x) + 1   := by gcongr; exact Int.floor_le (logb D (4 * x))
  rw [← logb_self_eq_one hD, ← logb_mul (mul_pos four_pos hx).ne.symm (ne_of_gt (D0 hD)),
    mul_assoc, mul_assoc, mul_comm _ x]

private lemma one_add_logb (hx : x > 0) : 1 + logb D (2 * x) = logb D (2 * D * x) := by
  rw [← logb_self_eq_one hD, ← logb_mul (D0 hD).ne.symm (mul_pos two_pos hx).ne.symm,
    ← mul_assoc, mul_comm (D : ℝ) 2]

-- If `D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)`, then the endpoints of `nonzeroS x` are equal.
private lemma eq_endpoints (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)) :
    ⌊(1 + logb D (2 * x))⌋ = ⌈logb D (4 * x)⌉ := by
  rw [Int.floor_eq_iff, one_add_logb hD hx]
  constructor
  · rw [← rpow_le_rpow_left_iff hD, ← inv_le_inv₀ (D_pow0 hD _) (D_pow0 hD _),
      rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD two_pos hx),
      ← rpow_neg (D0 hD).le, inv_eq_one_div]
    exact_mod_cast h.le
  · have : logb D (2 * D * x) < logb D (4 * D * x) := by
      refine (strictMonoOn_logb hD) ?_ ?_ (by linarith [(cDx0 hD two_pos hx)]) <;>
        exact mem_Ioi.2 (cDx0 hD (by norm_num) hx)
    apply lt_of_lt_of_le this
    rw [mul_comm, ← mul_assoc, mul_comm x 4, logb_mul (mul_pos four_pos hx).ne.symm (D0 hD).ne.symm,
      logb_self_eq_one hD, add_le_add_iff_right, mul_comm]
    exact Int.le_ceil _

-- If `D ^ (-⌈logb D (4 * x)⌉) < 1 / (2 * D * x)`, then the endpoints of `nonzeroS x` differ by 1.
private lemma endpoint_sub_one (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) < 1 / (2 * D * x)) :
    ⌊1 + logb D (2 * x)⌋ = ⌈logb D (4 * x)⌉ - 1 := by
  rw [one_add_logb hD hx]
  apply le_antisymm
  · rw [← inv_eq_one_div, zpow_neg, inv_lt_inv₀ (D_pow0' hD _) (cDx0 hD two_pos hx)] at h
    rw [Int.floor_le_sub_one_iff, ← rpow_lt_rpow_left_iff hD,
      rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD two_pos hx)]
    exact_mod_cast h
  · apply sub_le_iff_le_add.2 ∘ Int.ceil_le.2
    suffices logb D (4 * x) ≤ logb D (2 * D * x) by
      exact_mod_cast (lt_of_le_of_lt this (Int.lt_floor_add_one _)).le
    have : 4 * x ≤ 2 * D * x := (mul_le_mul_right hx).2 (by linarith [D2 hD])
    refine (strictMonoOn_logb hD).monotoneOn ?_ ?_ this <;> exact mem_Ioi.2 (by positivity)

-- Special case of `sum_ψ`, for the case where `nonzeroS D x` has one element.
private lemma sum_ψ₁ (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)) :
    ∑ s in nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  rw [nonzeroS, eq_endpoints hD hx h, Finset.Icc_self, Finset.sum_singleton]
  refine ψ_formula₂ hD ⟨le_of_eq_of_le (by field_simp) ((mul_le_mul_right hx).2 h), ?_⟩
  calc
    D ^ (-⌈logb D (4 * x)⌉) * x
      = D ^ (-⌈logb D (4 * x)⌉ : ℝ) * x := by norm_cast
    _ ≤ D ^ (-logb D (4 * x)) * x      := by
      gcongr
      · exact hD.le
      · exact Int.le_ceil (logb D (4 * x))
    _ = 1 / (4 * x) * x                := by
      rw [rpow_neg (D0 hD).le, inv_eq_one_div, rpow_logb (D0 hD) hD.ne.symm (by linarith)]
    _ = 1 / 4                          := by field_simp; exact mul_comm x 4

-- Special case of `sum_ψ`, for the case where `nonzeroS D x` has two elements.
private lemma sum_ψ₂ (hx : 0 < x)
    (h : D ^ (-⌈logb D (4 * x)⌉) < 1 / (2 * D * x)) :
    ∑ s in nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  -- Replace `nonzeroS D x` with `{s₀ - 1, s₀}`, where `s₀ := ⌈logb D (4 * x)⌉`
  have endpts := endpoint_sub_one hD hx h
  have ne : ⌈logb D (4 * x)⌉ - 1 ≠ ⌈logb D (4 * x)⌉ := pred_ne_self _
  have : nonzeroS D x = {⌈logb D (4 * x)⌉ - 1, ⌈logb D (4 * x)⌉} := by
    rw [nonzeroS, ← endpts]; exact Int.Icc_of_eq_sub_1 endpts
  set s₀ := ⌈logb D (4 * x)⌉
  rw [this, Finset.sum_insert ((Finset.not_mem_singleton).2 ne), Finset.sum_singleton]
  -- Now calculate the sum
  have Ds₀x_lt := (mul_lt_mul_right hx).2 h
  rw [← div_div, div_mul_cancel₀ _ (ne_of_gt hx)] at Ds₀x_lt
  have hs₀ := And.intro (le_div_ceil_mul hD hx) Ds₀x_lt.le
  suffices 1 / 4 ≤ D ^ (-(s₀ - 1)) * x ∧ D ^ (-(s₀ - 1)) * x ≤ 1 / 2 by
    rw [ψ_formula₁ hD hs₀, ψ_formula₃ hD this]
    suffices (D : ℝ) ^ (1 - s₀) = D * D ^ (-s₀) by rw [neg_sub, this]; ring
    rw [zpow_sub₀ (ne_of_gt (D0 hD)), zpow_neg, zpow_one, div_eq_mul_inv]
  rw [neg_sub, sub_eq_add_neg, zpow_add₀ (ne_of_gt (D0 hD)), zpow_one, mul_assoc]
  constructor
  · rw [← div_le_iff₀' (D0 hD), div_div]; exact hs₀.1
  · rw [← le_div_iff₀' (D0 hD), div_div]; exact hs₀.2

-- See `finsum_ψ` for the version that doesn't explicitly restrict to the support.
lemma sum_ψ (hx : 0 < x) : ∑ s in nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  by_cases h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)
  · exact sum_ψ₁ hD hx h
  · exact sum_ψ₂ hD hx (lt_of_not_ge h)

--------------------------------------------------
/- Now we prove that `nonzeroS D x` is the support of `s ↦ ψ D (D ^ (-s) * x)`. This converts
`sum_ψ` into `finsum_ψ`, which states that `∑ᶠ s : ℤ, ψ D (D ^ (-s) * x) = 1`. -/

lemma mem_nonzeroS_iff {i : ℤ} {x : ℝ} (hx : 0 < x) :
    i ∈ nonzeroS D x ↔ (D ^ (-i) * x) ∈ Ioo (4 * D : ℝ)⁻¹ 2⁻¹ := by
  rw [mem_Ioo, nonzeroS, Finset.mem_Icc, Int.floor_le_iff, Int.le_ceil_iff, mul_inv_rev,
    add_comm _ 1, Real.add_lt_add_iff_left, ← lt_div_iff₀ hx, mul_comm (D : ℝ)⁻¹,
    ← div_lt_div_iff hx (inv_pos.2 (D0 hD)), div_inv_eq_mul, ← zpow_add_one₀ ((D0 hD).ne.symm),
    zpow_neg, ← Real.rpow_intCast, ← Real.rpow_intCast, lt_logb_iff_rpow_lt hD (four_x0 hx),
    logb_lt_iff_lt_rpow hD (mul_pos two_pos hx), ← sub_eq_neg_add, ← neg_sub i 1, ← inv_mul',
    ← inv_mul', inv_lt_inv₀ (D_pow0 hD _) (mul_pos two_pos hx), Int.cast_neg, Int.cast_sub,
    Int.cast_one, rpow_neg (D0 hD).le, inv_lt_inv₀ (four_x0 hx) (D_pow0 hD _), and_comm]

lemma psi_ne_zero_iff {x : ℝ} (hx : 0 < x) :
    ψ D (D ^ (-s) * x) ≠ 0 ↔ s ∈ nonzeroS D x := by
  rw [← mem_support, support_ψ (by exact_mod_cast hD), mem_nonzeroS_iff hD hx]

lemma psi_eq_zero_iff {x : ℝ} (hx : 0 < x) : ψ D (D ^ (-s) * x) = 0 ↔ s ∉ nonzeroS D x := by
  rw [← iff_not_comm, ← psi_ne_zero_iff hD hx]

lemma support_ψS (hx : 0 < x) : support (fun (s : ℤ) ↦ ψ D (D ^ (-s) * x)) = nonzeroS D x := by
  ext; rw [mem_support]; exact psi_ne_zero_iff hD hx


lemma finsum_ψ (hx : 0 < x) : ∑ᶠ s : ℤ, ψ D (D ^ (-s) * x) = 1 := by
  refine Eq.trans ?_ (sum_ψ hD hx)
  apply Eq.trans <| finsum_eq_sum _ <| support_ψS hD hx ▸ Finset.finite_toSet (nonzeroS D x)
  congr
  ext
  rw [Finite.mem_toFinset, support_ψS hD hx, Finset.mem_coe]

end include_hD

end D


open Complex

open scoped ShortVariables
variable (X : Type*) {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
variable {s : ℤ} {x y : X}

section -- Again, we start by recording some trivial inequalities that will be needed repeatedly.
include q K σ₁ σ₂ F G
private lemma a0' : a > 0 := by linarith [four_le_a X]
private lemma a0 : (a : ℝ) > 0 := by exact_mod_cast (a0' X)
private lemma D1 : (D : ℝ) > 1 := by norm_cast; norm_num; exact (a0' X).ne.symm
private lemma D0' : (D : ℝ) > 0 := one_pos.trans (D1 X)
private lemma D0'' : D > 0 := by exact_mod_cast (D0' X)
private lemma Ds0 (s : ℤ) : (D : ℝ) ^ s > 0 := have := D0' X; by positivity
end

variable {X}

/-- K_s in the blueprint -/
@[nolint unusedArguments]
def Ks [ProofData a q K σ₁ σ₂ F G] (s : ℤ) (x y : X) : ℂ :=
  K x y * ψ (D ^ (-s) * dist x y)

lemma Ks_def (s : ℤ) (x y : X) : Ks s x y = K x y * ψ (D ^ (-s) * dist x y) := rfl

lemma sum_Ks {t : Finset ℤ} (hs : nonzeroS D (dist x y) ⊆ t) (hD : 1 < (D : ℝ)) (h : 0 < dist x y) :
    ∑ i in t, Ks i x y = K x y := by
  simp_rw [Ks, ← Finset.mul_sum]
  norm_cast
  suffices ∑ i in t, ψ (D ^ (-i) * dist x y) = 1 by rw [this, ofReal_one, mul_one]
  rw [← Finset.sum_subset hs, sum_ψ hD h]
  intros
  rwa [psi_eq_zero_iff hD h]

-- maybe this version is also useful?
-- lemma sum_Ks' {t : Finset ℤ}
--     (hs : ∀ i : ℤ, (D ^ i * dist x y) ∈ Ioo (4 * D)⁻¹ 2⁻¹ → i ∈ t)
--     (hD : 1 < D) (h : x ≠ y) : ∑ i in t, Ks i x y = K x y := by
--   sorry

lemma dist_mem_Icc_of_Ks_ne_zero {s : ℤ} {x y : X} (h : Ks s x y ≠ 0) :
    dist x y ∈ Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) := by
  simp only [Ks, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, ne_eq, mul_eq_zero, ofReal_eq_zero] at h
  have dist_mem_Icc := Ioo_subset_Icc_self (support_ψ (D1 X) ▸ mem_support.2 (not_or.1 h).2)
  rwa [mem_Icc, ← div_eq_inv_mul, le_div_iff₀ (D_pow0' (D1 X) s),
    div_le_iff₀ (D_pow0' (D1 X) s), mul_inv, mul_assoc, inv_mul_eq_div (4 : ℝ), ← zpow_neg_one,
    ← zpow_add₀ (D0' X).ne.symm, neg_add_eq_sub, ← div_eq_inv_mul] at dist_mem_Icc

/-- The constant appearing in part 2 of Lemma 2.1.3. -/
def C2_1_3 (a : ℝ) : ℝ := 2 ^ (102 * a ^ 3)
/-- The constant appearing in part 3 of Lemma 2.1.3. -/
def D2_1_3 (a : ℝ) : ℝ := 2 ^ (150 * a ^ 3)

--1.0.14.
lemma kernel_bound {s : ℤ} {x y : X} :
    ‖Ks s x y‖₊ ≤ 2 ^ a ^ 3 / volume.nnreal (ball x (dist x y)) := by
  change ‖K x y * ψ (D ^ (-s) * dist x y)‖ ≤ 2 ^ a ^ 3 / volume.real (ball x (dist x y))
  apply le_trans <| calc
    ‖K x y * ψ (D ^ (-s) * dist x y)‖
      = ‖K x y‖ * ‖(ψ (D ^ (-s) * dist x y) : ℂ)‖ := norm_mul ..
    _ ≤ ‖K x y‖ * 1               := by gcongr; rw [norm_eq_abs, abs_ofReal]; exact abs_ψ_le_one D _
    _ ≤ ‖K x y‖                   := by rw [mul_one]
  convert norm_K_le_vol_inv (K := K) x y
  unfold C_K
  norm_cast

variable (s)

/-- Apply `volume_ball_two_le_same` `n` times. -/
lemma DoublingMeasure.volume_ball_two_le_same_repeat (x : X) (r : ℝ) (n : ℕ) :
    volume.real (ball x (2 ^ n * r)) ≤ (defaultA a) ^ n * volume.real (ball x r) := by
  induction' n with d ih; · simp
  rw [add_comm, pow_add, pow_one, mul_assoc]
  apply (measure_real_ball_two_le_same x _).trans
  have A_cast: (defaultA a : ℝ≥0).toReal = (defaultA a : ℝ) := rfl
  rwa [A_cast, pow_add, mul_assoc, pow_one, mul_le_mul_left (by positivity)]

-- The special case of `volume_ball_two_le_same_repeat` needed to prove `norm_Ks_le`
private lemma DoublingMeasure.volume_ball_two_le_same_repeat' (x : X) :
    volume.real (ball x (D ^ s)) ≤
    (defaultA a) ^ (2 + 100 * a ^ 2) * volume.real (ball x (D ^ (s - 1) / 4)) := by
  convert volume_ball_two_le_same_repeat x (D ^ (s - 1) / 4) (2 + 100 * a ^ 2)
  rw [defaultD, zpow_sub₀ (by positivity)]
  field_simp
  rw [mul_comm (2 ^ _) (_ ^ s), add_comm, pow_add, (by norm_num : (2 : ℝ) ^ 2 = 4)]

lemma Metric.measure_ball_pos_nnreal (x : X) (r : ℝ) (hr : r > 0) : volume.nnreal (ball x r) > 0 :=
  ENNReal.toNNReal_pos (ne_of_gt (measure_ball_pos volume x hr)) (measure_ball_ne_top x _)

lemma Metric.measure_ball_pos_real (x : X) (r : ℝ) (hr : r > 0) : volume.real (ball x r) > 0 :=
  measure_ball_pos_nnreal x r hr

include a q K σ₁ σ₂ F G in
lemma K_eq_K_of_dist_eq_zero {x y y' : X} (hyy' : dist y y' = 0) :
    K x y = K x y' := by
  suffices ‖K x y - K x y'‖ = 0 by rwa [norm_eq_abs, AbsoluteValue.map_sub_eq_zero_iff] at this
  suffices ‖K x y - K x y'‖ ≤ 0 from le_antisymm this (norm_nonneg (K x y - K x y'))
  convert norm_K_sub_le (K := K) (x := x) (y := y) (y' := y')
    (by simp only [hyy', mul_zero, dist_nonneg])
  suffices (0 : ℝ) ^ (a : ℝ)⁻¹ = 0 by simp [hyy', this]
  simp [inv_ne_zero (show (a : ℝ) ≠ 0 by norm_cast; linarith [four_le_a X])]

include a q K σ₁ σ₂ F G in
lemma K_eq_zero_of_dist_eq_zero {x y : X} (hxy : dist x y = 0) :
    K x y = 0 :=
  norm_le_zero_iff.1 (by simpa [hxy, Real.vol] using norm_K_le_vol_inv x y)

variable {s}

private lemma div_vol_le {x y : X} {c : ℝ} (hc : c > 0) (hK : Ks s x y ≠ 0) :
    c / volume.real (ball x (dist x y)) ≤
    (2 ^ (2 * a + 100 * a ^ 3)) * c / volume.real (ball x (D ^ s)) := by
  have h : 0 ≠ dist x y := fun h0 ↦ by simp [Ks, K_eq_zero_of_dist_eq_zero h0.symm] at hK
  have v0₁ := measure_ball_pos_nnreal x (dist x y) <| lt_of_le_of_ne dist_nonneg h
  have v0₂ := measure_ball_pos_nnreal x (D ^ (s - 1) / 4) (by have := D0' X; positivity)
  have v0₃ := measure_ball_pos_real x (D ^ s) (zpow_pos (D0' X) _)
  have ball_subset := ball_subset_ball (x := x) (mem_Icc.1 (dist_mem_Icc_of_Ks_ne_zero hK)).1
  apply le_trans <| (div_le_div_left hc v0₁ v0₂).2 <|
    ENNReal.toNNReal_mono (measure_ball_ne_top x _) (OuterMeasureClass.measure_mono _ ball_subset)
  dsimp only
  rw_mod_cast [measureNNReal_val, div_le_div_iff (by exact_mod_cast v0₂) v0₃]
  apply le_of_le_of_eq <| (mul_le_mul_left hc).2 <|
    DoublingMeasure.volume_ball_two_le_same_repeat' s x
  simp_rw [defaultA, ← mul_assoc, mul_comm c]
  rw_mod_cast [← pow_mul]
  congr
  ring

private lemma norm_K_le {s : ℤ} {x y : X} (hK : Ks s x y ≠ 0):
    ‖K x y‖ ≤ C2_1_3 a / volume.real (ball x (D ^ s)) := by
  by_cases h : dist x y = 0
  · rw [K_eq_zero_of_dist_eq_zero h, norm_zero, C2_1_3]
    positivity
  have v0₃ := measure_ball_pos_real x (D ^ s) (zpow_pos (D0' X) _)
  apply (norm_K_le_vol_inv x y).trans
  unfold Real.vol C_K C2_1_3
  apply le_trans (div_vol_le (by positivity) hK)
  norm_cast
  rw [← pow_add]
  gcongr
  · norm_num
  · rw [(by norm_num : 102 = 1 + 100 + 1), add_mul, add_mul, one_mul, (by rfl : a ^ 3 = a ^ 2 * a)]
    gcongr
    nlinarith [four_le_a X]

-- 2.1.3
lemma norm_Ks_le {s : ℤ} {x y : X} :
    ‖Ks s x y‖ ≤ C2_1_3 a / volume.real (ball x (D ^ s)) := by
  have : 0 ≤ C2_1_3 a / volume.real (ball x (D ^ s)) := by unfold C2_1_3; positivity
  by_cases hK : Ks s x y = 0
  · rwa [hK, norm_zero]
  rw [Ks, norm_mul, norm_eq_abs (ofReal _), abs_ofReal, ← mul_one (_ / _)]
  gcongr
  · exact norm_K_le hK
  · exact abs_ψ_le_one D (D ^ (-s) * dist x y)

-- Needed to prove `ψ_ineq`
private lemma norm_ψ_sub_ψ_le_two {r s : ℝ} : ‖ψ r - ψ s‖ ≤ 2 :=
  (norm_sub_le _ _).trans <| le_of_le_of_eq (add_le_add (abs_ψ_le_one D r) (abs_ψ_le_one D s))
    one_add_one_eq_two

private lemma Ks_eq_Ks (x : X) {y y' : X} (hyy' : dist y y' = 0) :
    Ks s x y = Ks s x y' := by
  simp_rw [Ks, PseudoMetricSpace.dist_eq_of_dist_zero x hyy', K_eq_K_of_dist_eq_zero hyy']

-- Needed to prove `norm_Ks_sub_Ks_le`
include q K σ₁ σ₂ F G in
private lemma ψ_ineq {x y y' : X} :
    |ψ (D ^ (-s) * dist x y) - ψ (D ^ (-s) * dist x y')| ≤
    4 * D * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  by_cases hyy' : dist y y' = 0
  · rw [PseudoMetricSpace.dist_eq_of_dist_zero x hyy', _root_.sub_self, abs_zero]
    positivity
  by_cases h : dist y y' / D ^ s ≥ 1    -- If `dist y y'` is large, then the RHS is large while
  · apply le_trans norm_ψ_sub_ψ_le_two  -- the LHS remains bounded.
    rw [← mul_one 2]
    gcongr
    · linarith [D1 X]
    · exact Real.one_le_rpow h (inv_nonneg.2 (a0 X).le)
  push_neg at h
  -- If `dist y y'` is small, then `(dist y y') ^ (a : ℝ)⁻¹` is comparable with `dist y y'`,
  -- so the Lipschitz bound for `ψ` is enough to finish the proof.
  have D1 := one_le_D (a := a)
  apply (lipschitzWith_ψ' (by exact_mod_cast D1) (D ^ (-s) * dist x y) (D ^ (-s) * dist x y')).trans
  gcongr
  rw [zpow_neg, ← smul_eq_mul, ← smul_eq_mul, dist_smul₀]
  apply (mul_le_mul_of_nonneg_left (dist_dist_dist_le_right x y y') (norm_nonneg _)).trans
  rw [← Real.rpow_one (_ * _), Real.norm_of_nonneg (inv_pos.2 (Ds0 X s)).le, inv_mul_eq_div]
  exact Real.rpow_le_rpow_of_exponent_ge (by positivity) h.le (Nat.cast_inv_le_one a)

private lemma D_pow_a_inv : (D : ℝ) ^ (a : ℝ)⁻¹ = 2 ^ (100 * a) :=
  calc
    _ = ((2 : ℝ) ^ (100 * a ^ 2 : ℝ)) ^ (a : ℝ)⁻¹ := by rw [defaultD]; norm_cast
    _ = 2 ^ (100 * a ^ 2 * (a : ℝ)⁻¹) := by rw [← Real.rpow_mul two_pos.le]
    _ = 2 ^ (100 * (a * a * (a : ℝ)⁻¹)) := by rw [mul_assoc, sq]
    _ = _ := by rw [mul_self_mul_inv]; norm_cast

include q K σ₁ σ₂ F G in
private lemma four_D_rpow_a_inv : (4 * D : ℝ) ^ (a : ℝ)⁻¹ ≤ 2 ^ (1 + 100 * a) := by
  rw [pow_add, Real.mul_rpow four_pos.le (Nat.cast_nonneg D)]
  gcongr
  · suffices 4 ^ (a : ℝ)⁻¹ ≤ (4 : ℝ) ^ (2 : ℝ)⁻¹ by
      apply le_of_le_of_eq this
      rw [(by norm_num : (4 : ℝ) = 2 ^ (2 : ℝ)), ← Real.rpow_mul, mul_inv_cancel₀] <;> norm_num
    rw [Real.rpow_le_rpow_left_iff Nat.one_lt_ofNat, inv_le_inv₀ (a0 X) (by linarith)]
    norm_cast
    exact le_of_add_le_right (four_le_a X)
  · exact le_of_eq D_pow_a_inv

/-
The proof of `norm_Ks_sub_Ks_le` is divided into two cases `norm_Ks_sub_Ks_le₀` and
`norm_Ks_sub_Ks_le₁`, depending whether `2 * dist y y' ≤ dist x y` or `2 * dist y y' > dist x y`.

To prepare for the proof of `norm_Ks_sub_Ks_le₀`, we separate the main inequality into two subgoals
`norm_Ks_sub_Ks_le₀₀` and `norm_Ks_sub_Ks_le₀₁`.
-/

-- Part of the inequality needed for `norm_Ks_sub_Ks_le₀`.
private lemma norm_Ks_sub_Ks_le₀₀ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
     (hyy' : 2 * dist y y' ≤ dist x y) : ‖K x y - K x y'‖ * |ψ (D ^ (-s) * dist x y')| ≤
    (2 : ℝ) ^ (1 + 102 * a + 101 * a ^ 3) / volume.real (ball x (D ^ s)) *
    (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  have CKa0 : C_K a > 0 := by unfold C_K; positivity
  have D1 := D1 X
  have d0 : dist x y > 0 :=
    lt_of_lt_of_le (by positivity) (mem_Icc.1 (dist_mem_Icc_of_Ks_ne_zero hK)).1
  apply le_trans <| mul_le_mul_of_nonneg_left (abs_ψ_le_one D _) (norm_nonneg (K x y - K x y'))
  rw [mul_one]
  apply le_trans <| norm_K_sub_le hyy'
  rw [Ks] at hK
  have ψ_ne_0 : ψ (D ^ (-s) * dist x y) ≠ 0 := fun h ↦ hK (by rw [h, ofReal_zero, mul_zero])
  have mem_supp := (psi_ne_zero_iff D1 d0).1 ψ_ne_0
  rw [mem_nonzeroS_iff D1 d0, mem_Ioo] at mem_supp
  replace mem_supp := mem_supp.1
  rw [← div_lt_iff₀' (Ds0 X (-s)), zpow_neg, inv_div_inv, div_eq_inv_mul] at mem_supp
  have : dist y y' / dist x y ≤ (dist y y' / ((4 * D : ℝ)⁻¹ * D ^ s)) :=
    div_le_div_of_nonneg_left dist_nonneg (by positivity) mem_supp.le
  rw [← div_eq_inv_mul, ← div_mul] at this
  have : (dist y y' / dist x y) ^ (a : ℝ)⁻¹ ≤ (dist y y' / D ^ s * (4 * D)) ^ (a : ℝ)⁻¹ := by
    apply Real.rpow_le_rpow (div_nonneg dist_nonneg dist_nonneg) this (by positivity)
  rw [Real.mul_rpow (div_nonneg dist_nonneg (Ds0 X s).le) (fourD0 D1).le] at this
  apply le_trans <| mul_le_mul this (div_vol_le CKa0 hK) (by positivity) (by positivity)
  rw [(by ring : (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ * (4 * D) ^ (a : ℝ)⁻¹ *
      (2 ^ (2 * a + 100 * a ^ 3) * C_K a / volume.real (ball x (D ^ s))) =
      (4 * D) ^ (a : ℝ)⁻¹ * 2 ^ (2 * a + 100 * a ^ 3) * C_K a / volume.real (ball x (D ^ s)) *
      (dist y y' / D ^ s) ^ (a : ℝ)⁻¹)]
  gcongr
  have : (4 * D : ℝ) ^ (a : ℝ)⁻¹ * 2 ^ (2 * a + 100 * a ^ 3) * C_K a ≤
      2 ^ (1 + 100 * a) * 2 ^ (2 * a + 100 * a ^ 3) * 2 ^ a ^ 3 := by
    gcongr
    · exact four_D_rpow_a_inv (X := X)
    · unfold C_K; norm_cast
  apply le_of_le_of_eq this
  rw [← pow_add, ← pow_add]
  congr 1
  ring

-- Part of the inequality needed for `norm_Ks_sub_Ks_le₀`.
private lemma norm_Ks_sub_Ks_le₀₁ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0) :
    ‖K x y‖ * |(ψ (D ^ (-s) * dist x y)) - (ψ (D ^ (-s) * dist x y'))| ≤
    (2 : ℝ) ^ (2 + 2 * a + 100 * a ^ 2 + 101 * a ^ 3) / volume.real (ball x (D ^ s)) *
    (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  have : 2 ^ (2 + 2 * a + 100 * a ^ 2 + 101 * a ^ 3) / volume.real (ball x (D ^ s)) *
      (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ = 2 ^ (2 * a + 101 * a ^ 3) / volume.real (ball x (D ^ s)) *
      (4 * D * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹) := by
    field_simp; ring
  rw [this]
  refine mul_le_mul ?_ ψ_ineq (abs_nonneg _) (by positivity)
  apply le_trans <| norm_K_le_vol_inv x y
  unfold C_K
  apply le_of_le_of_eq <| div_vol_le (by positivity) hK
  rw_mod_cast [← pow_add, (show 2 * a + 100 * a ^ 3 + a ^ 3 = 2 * a + 101 * a ^ 3 by ring)]

-- Special case of `norm_Ks_sub_Ks_le`
private lemma norm_Ks_sub_Ks_le₀ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
    (h : 2 * dist y y' ≤ dist x y) : ‖Ks s x y - Ks s x y'‖ ≤
    D2_1_3 a / volume.real (ball x (D ^ s)) * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  unfold Ks
  trans ‖(K x y - K x y') * ψ (D ^ (-s) * dist x y') +
          K x y * (ψ (D ^ (-s) * dist x y) - ψ (D ^ (-s) * dist x y'))‖
  · apply le_of_eq; congr; ring
  apply le_trans (norm_add_le _ _)
  norm_cast
  simp_rw [D2_1_3, norm_mul, norm_eq_abs (ψ _), norm_eq_abs (ofReal _), abs_ofReal]
  apply le_trans (add_le_add (norm_Ks_sub_Ks_le₀₀ hK h) (norm_Ks_sub_Ks_le₀₁ hK))
  field_simp
  rw [← add_mul]
  gcongr
  norm_cast
  have : 1 + 102 * a + 101 * a ^ 3 ≤ 2 + 2 * a + 100 * a ^ 2 + 101 * a ^ 3 := by
    nlinarith [four_le_a X]
  apply le_trans <| Nat.add_le_add_right (pow_le_pow_right₀ one_lt_two.le this) _
  rw [← two_mul]
  nth_rewrite 1 [← pow_one 2]
  rw [← pow_add]
  gcongr
  · exact NeZero.one_le
  · nlinarith [four_le_a X]

-- Special case of `norm_Ks_sub_Ks_le`
private lemma norm_Ks_sub_Ks_le₁ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
    (h : ¬ 2 * dist y y' ≤ dist x y) : ‖Ks s x y - Ks s x y'‖ ≤
    D2_1_3 a / volume.real (ball x (D ^ s)) * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  have a4 : 4 ≤ (a : ℝ) := by exact_mod_cast four_le_a X
  have a_ineq : 0 ≤ 47 * (a : ℝ) ^ 2 - 100 := by nlinarith
  have a_ineq' : 0 ≤ (a : ℝ) ^ 3 - 2 := by nlinarith
  have := D0' X
  apply le_trans <| norm_sub_le (Ks s x y) (Ks s x y')
  apply le_trans <| add_le_add norm_Ks_le norm_Ks_le
  rw [div_mul_eq_mul_div, div_add_div_same, ← two_mul,
    div_le_div_right (measure_ball_pos_real x (D ^ s) (D_pow0' (D1 X) s)), ← pow_one 2]
  rw [not_le, ← div_lt_iff₀' two_pos] at h
  have dist_pos : dist y y' > 0 := lt_of_le_of_lt (div_nonneg dist_nonneg two_pos.le) h
  have := lt_of_le_of_lt
    ((div_le_div_right two_pos).2 ((mem_Icc.1 <| dist_mem_Icc_of_Ks_ne_zero hK).1)) h
  rw [div_div, (show (4 : ℝ) * 2 = 8 by norm_num), zpow_sub₀ (D0' X).ne.symm, div_div, zpow_one,
    div_lt_comm₀ (by positivity) dist_pos] at this
  have dist_div_Ds_gt := inv_strictAnti₀ (div_pos (Ds0 X s) dist_pos) this
  rw [inv_div] at dist_div_Ds_gt
  have : (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ > (2 : ℝ) ^ (- 100 * a + (-1 : ℤ)) := by
    have := a0' X
    have a_inv_pos : (a : ℝ)⁻¹ > 0 := inv_pos.2 (by exact_mod_cast this)
    refine lt_of_le_of_lt ?_ <| Real.rpow_lt_rpow (by positivity) dist_div_Ds_gt a_inv_pos
    rw [mul_inv, Real.mul_rpow (inv_nonneg.2 (D0' X).le) (by norm_num), zpow_add₀ two_ne_zero]
    gcongr
    · have : -100 * (a : ℤ) ^ 2 * (a : ℝ)⁻¹ = -100 * a := by field_simp; rw [sq, mul_assoc]
      exact le_of_eq <| calc
        (2 : ℝ) ^ (-100 * (a : ℤ))
          = 2 ^ (-100 * (a : ℤ) ^ 2 * (a : ℝ)⁻¹)    := by rw [this]; norm_cast
        _ = (2 ^ (-100 * a ^ 2 : ℝ)) ^ (a : ℝ)⁻¹    := Real.rpow_mul two_pos.le _ _
        _ = (2 ^ (100 * a ^ 2 : ℝ))⁻¹ ^ (a : ℝ)⁻¹   := by rw [← Real.rpow_neg two_pos.le]; norm_cast
        _ = ((2 ^ (100 * a ^ 2) : ℕ) : ℝ)⁻¹ ^ (a : ℝ)⁻¹ := by norm_cast
    · have a_inv_le : (a : ℝ)⁻¹ ≤ 3⁻¹ :=
        (inv_le_inv₀ (a0 X) three_pos).2 (by exact_mod_cast le_trans (Nat.le_succ 3) (four_le_a X))
      refine le_of_eq_of_le ?_ <|
        (Real.strictAnti_rpow_of_base_lt_one (by norm_num) (by norm_num)).antitone a_inv_le
      rw [← Real.rpow_left_inj (by positivity) (by positivity) three_pos.ne.symm]
      norm_num
      simp
  have : D2_1_3 (a : ℝ) * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ ≥
      D2_1_3 (a : ℝ) * (2 : ℝ) ^ (- 100 * a + (-1 : ℝ)) := by
    exact_mod_cast le_of_lt <| (mul_lt_mul_left (by unfold D2_1_3; positivity)).2 this
  refine le_trans ?_ this
  unfold C2_1_3 D2_1_3
  rw [(by norm_cast : 2 ^ 1 = (2 : ℝ) ^ (1 : ℝ)), ← Real.rpow_add two_pos,
    ← Real.rpow_add two_pos, Real.rpow_le_rpow_left_iff one_lt_two]
  linarith [add_nonneg (mul_nonneg a_ineq a.cast_nonneg) a_ineq']

-- 2.1.3
lemma norm_Ks_sub_Ks_le {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0) :
    ‖Ks s x y - Ks s x y'‖ ≤
    D2_1_3 a / volume.real (ball x (D ^ s)) * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  by_cases h : 2 * dist y y' ≤ dist x y
  · exact norm_Ks_sub_Ks_le₀ hK h
  · exact norm_Ks_sub_Ks_le₁ hK h

lemma aestronglyMeasurable_Ks {s : ℤ} : AEStronglyMeasurable (fun x : X × X ↦ Ks s x.1 x.2) := by
  unfold Ks _root_.ψ
  refine aestronglyMeasurable_K.mul ?_
  fun_prop

/-- The function `y ↦ Ks s x y` is integrable. -/
lemma integrable_Ks_x {s : ℤ} {x : X} (hD : 1 < (D : ℝ)) : Integrable (Ks s x) := by
  /- Define a measurable, bounded function `K₀` that is equal to `K x` on the support of
  `y ↦ ψ (D ^ (-s) * dist x y)`, so that `Ks s x y = K₀ y * ψ (D ^ (-s) * dist x y)`. -/
  let K₀ (y : X) : ℂ := ite (dist x y ≤ D ^ s / (4 * D)) 0 (K x y)
  have : Ks s x = fun y ↦ K₀ y * (ψ (D ^ (-s) * dist x y) : ℂ) := by
    ext y
    by_cases hy : dist x y ≤ D ^ s / (4 * D)
    · suffices D ^ (-s) * dist x y ≤ 1 / (4 * D) by simp [-defaultD, -zpow_neg, Ks, ψ_formula₀ this]
      apply le_of_le_of_eq <| (mul_le_mul_left (zpow_pos (one_pos.trans (D1 X)) (-s))).2 hy
      field_simp
    · simp [-defaultD, Ks, K₀, hy]
  rw [this]
  refine Integrable.bdd_mul ?_ (Measurable.aestronglyMeasurable ?_) ?_
  · apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_ofReal.comp <| continuous_ψ.comp <| (by fun_prop)
    · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (D ^ s / 2))
      intro y hy
      rw [mem_support, ne_eq, ofReal_eq_zero, ← ne_eq, ← mem_support, support_ψ (D1 X)] at hy
      replace hy := hy.2.le
      rw [zpow_neg, mul_comm, ← div_eq_mul_inv, div_le_iff₀ (Ds0 X s)] at hy
      rwa [mem_closedBall, dist_comm, div_eq_mul_inv, mul_comm]
  · refine Measurable.ite ?_ measurable_const measurable_K.of_uncurry_left
    convert measurableSet_closedBall (x := x) (ε := D ^ s / (4 * D))
    simp_rw [dist_comm x _, closedBall]
  · refine ⟨C_K a / volume.real (ball x (D ^ s / (4 * D))), fun y ↦ ?_⟩
    by_cases hy : dist x y ≤ D ^ s / (4 * D)
    · simp only [hy, reduceIte, norm_zero, C_K, K₀]
      positivity
    · simp only [hy, reduceIte, K₀]
      apply (norm_K_le_vol_inv x y).trans
      gcongr
      · exact (C_K_pos a).le
      · exact measure_ball_pos_real x _ (div_pos (Ds0 X s) (fourD0 hD))
      · exact ENNReal.toReal_mono (measure_ball_ne_top x (dist x y)) <|
          measure_mono <| ball_subset_ball (lt_of_not_ge hy).le
