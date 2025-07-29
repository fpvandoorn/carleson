import Carleson.Defs

open MeasureTheory Measure NNReal Metric Set TopologicalSpace Function DoublingMeasure Bornology
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

/-- The function `ψ` used as a basis for a dyadic partition of unity. -/
def ψ (D : ℕ) (x : ℝ) : ℝ :=
  max 0 <| min 1 <| min (4 * D * x - 1) (2 - 4 * x)

set_option hygiene false in
@[inherit_doc]
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

variable (D) in
/-- the one or two numbers `s` where `ψ (D ^ (-s) * x)` is possibly nonzero -/
def nonzeroS (x : ℝ) : Finset ℤ :=
  Finset.Icc ⌊(1 + logb D (2 * x))⌋ ⌈logb D (4 * x)⌉

---------------------------------------------

section include_hD

/- The goal of the next several lemmas is to prove `sum_ψ`, which says that
`∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1`.

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
    ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
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
    ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  -- Replace `nonzeroS D x` with `{s₀ - 1, s₀}`, where `s₀ := ⌈logb D (4 * x)⌉`
  have endpts := endpoint_sub_one hD hx h
  have ne : ⌈logb D (4 * x)⌉ - 1 ≠ ⌈logb D (4 * x)⌉ := pred_ne_self _
  have : nonzeroS D x = {⌈logb D (4 * x)⌉ - 1, ⌈logb D (4 * x)⌉} := by
    rw [nonzeroS, ← endpts]
    have Icc_of_eq_add_one {a b : ℤ} (h : a + 1 = b) : Finset.Icc a b = {a, b} := by
      subst h; exact Int.Icc_eq_pair a
    exact Icc_of_eq_add_one (add_eq_of_eq_sub endpts)
  set s₀ := ⌈logb D (4 * x)⌉
  rw [this, Finset.sum_insert ((Finset.notMem_singleton).2 ne), Finset.sum_singleton]
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
lemma sum_ψ (hx : 0 < x) : ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
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
    ← div_lt_div_iff₀ hx (inv_pos.2 (D0 hD)), div_inv_eq_mul, ← zpow_add_one₀ ((D0 hD).ne.symm),
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

lemma support_ψS_subset_Icc {b c : ℤ} {x : ℝ}
    (h : x ∈ Icc ((D : ℝ) ^ (b - 1) / 2) (D ^ c / 4)) :
    support (fun (s : ℤ) ↦ ψ D (D ^ (-s) * x)) ⊆ Icc b c := by
  intro i hi
  have hx : x > 0 := lt_of_lt_of_le (by positivity) h.1
  simp only [support_ψS hD hx, nonzeroS, Finset.coe_Icc, mem_Icc] at hi
  simp only [mem_Icc]
  refine ⟨le_trans ?_ hi.1, le_trans hi.2 ?_⟩
  · rw [← Nat.cast_one, Int.floor_natCast_add, Nat.cast_one, ← sub_le_iff_le_add', Int.le_floor,
      Real.le_logb_iff_rpow_le hD (mul_pos two_pos hx), mul_comm]
    exact_mod_cast (div_le_iff₀ two_pos).mp h.1
  · rw [Int.ceil_le, Real.logb_le_iff_le_rpow hD (mul_pos four_pos hx), mul_comm]
    exact_mod_cast (le_div_iff₀ four_pos).mp h.2

lemma finsum_ψ (hx : 0 < x) : ∑ᶠ s : ℤ, ψ D (D ^ (-s) * x) = 1 := by
  refine Eq.trans ?_ (sum_ψ hD hx)
  apply Eq.trans <| finsum_eq_sum _ <| support_ψS hD hx ▸ Finset.finite_toSet (nonzeroS D x)
  congr
  ext
  rw [Finite.mem_toFinset, support_ψS hD hx, Finset.mem_coe]

lemma sum_ψ_le (S : Finset ℤ) (hx : 0 < x) : ∑ s ∈ S, ψ D (D ^ (-s) * x) ≤ 1 := calc
  _ = ∑ s ∈ S ∩ (nonzeroS D x), ψ D (D ^ (-s) * x) := by
    refine (Finset.sum_subset Finset.inter_subset_left (fun s sS hs ↦ ?_)).symm
    exact (psi_eq_zero_iff hD hx).mpr (fun h ↦ hs <| Finset.mem_inter.mpr ⟨sS, h⟩)
  _ ≤ ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ ↦ zero_le_ψ ..)
  _ = 1 := sum_ψ hD hx

end include_hD

end D


open Complex

open scoped ShortVariables

section PseudoMetricSpace

variable (X : Type*) {a : ℕ} {K : X → X → ℂ} [PseudoMetricSpace X]
variable {s : ℤ} {x y : X}

section -- Again, we start by recording some trivial inequalities that will be needed repeatedly.
variable [KernelProofData a K]
include K
private lemma a0' : a > 0 := by linarith [four_le_a X]
private lemma a0 : (a : ℝ) > 0 := by exact_mod_cast (a0' X)
private lemma D1 : (D : ℝ) > 1 := one_lt_realD X
private lemma D0' : (D : ℝ) > 0 := one_pos.trans (D1 X)
private lemma D0'' : D > 0 := by exact_mod_cast (D0' X)
private lemma Ds0 (s : ℤ) : (D : ℝ) ^ s > 0 := have := D0' X; by positivity
end

variable {X} [KernelProofData a K]

/-- K_s in the blueprint -/
@[nolint unusedArguments]
def Ks [KernelProofData a K] (s : ℤ) (x y : X) : ℂ :=
  K x y * ψ (D ^ (-s) * dist x y)

lemma Ks_def (s : ℤ) (x y : X) : Ks s x y = K x y * ψ (D ^ (-s) * dist x y) := rfl

lemma sum_Ks {t : Finset ℤ} (hs : nonzeroS D (dist x y) ⊆ t) (hD : 1 < (D : ℝ)) (h : 0 < dist x y) :
    ∑ i ∈ t, Ks i x y = K x y := by
  simp_rw [Ks, ← Finset.mul_sum]
  norm_cast
  suffices ∑ i ∈ t, ψ (D ^ (-i) * dist x y) = 1 by rw [this, ofReal_one, mul_one]
  rw [← Finset.sum_subset hs, sum_ψ hD h]
  intros
  rwa [psi_eq_zero_iff hD h]

lemma dist_mem_Ioo_of_Ks_ne_zero {s : ℤ} {x y : X} (h : Ks s x y ≠ 0) :
    dist x y ∈ Ioo ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) := by
  simp only [Ks, zpow_neg, ne_eq, mul_eq_zero, ofReal_eq_zero] at h
  have dist_mem_Ioo := support_ψ (D1 X) ▸ mem_support.2 (not_or.1 h).2
  rwa [mem_Ioo, ← div_eq_inv_mul, lt_div_iff₀ (D_pow0' (D1 X) s),
    div_lt_iff₀ (D_pow0' (D1 X) s), mul_inv, mul_assoc, inv_mul_eq_div (4 : ℝ), ← zpow_neg_one,
    ← zpow_add₀ (D0' X).ne.symm, neg_add_eq_sub, ← div_eq_inv_mul] at dist_mem_Ioo

lemma dist_mem_Icc_of_Ks_ne_zero {s : ℤ} {x y : X} (h : Ks s x y ≠ 0) :
    dist x y ∈ Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) :=
  Ioo_subset_Icc_self (dist_mem_Ioo_of_Ks_ne_zero h)

lemma dist_mem_Icc_of_mem_tsupport_Ks {s : ℤ} {x : X × X}
    (h : x ∈ tsupport fun x ↦ (Ks s x.1 x.2)) :
    dist x.1 x.2 ∈ Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) := by
  set C := support fun (x : X × X) ↦ Ks s x.1 x.2
  have hcont : Continuous (fun (x : X × X) ↦ dist x.1 x.2) := by continuity
  have hC : (fun (x : X × X) ↦ dist x.1 x.2) '' C ⊆ Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) := by
    intro r hr
    simp only [mem_image, mem_support, C] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact dist_mem_Icc_of_Ks_ne_zero hx
  have hC' : (fun (x : X × X) ↦ dist x.1 x.2) '' (tsupport fun x ↦ Ks s x.1 x.2) ⊆
      Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) :=
    subset_trans (image_closure_subset_closure_image hcont)
      ((isClosed_Icc.closure_subset_iff).mpr hC)
  exact hC' (mem_image_of_mem (fun x ↦ dist x.1 x.2) h)

lemma dist_mem_Icc_of_mem_tsupport_Ks' {s : ℤ} {x y : X} (h : y ∈ tsupport fun z ↦ (Ks s x z)) :
    dist x y ∈ Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) := by
  set C := support fun (z : X) ↦ Ks s x z
  have hcont : Continuous (fun (z : X) ↦ dist x z) := continuous_const.dist continuous_id'
  have hC : (fun (z : X) ↦ dist x z) '' C ⊆ Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) := by
    intro r hr
    simp only [mem_image, mem_support, C] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact dist_mem_Icc_of_Ks_ne_zero hx
  have hC' : (fun z : X ↦ dist x z) '' (tsupport fun z ↦ Ks s x z) ⊆
      Icc ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2) :=
   subset_trans (image_closure_subset_closure_image hcont)
      ((isClosed_Icc.closure_subset_iff).mpr hC)
  exact hC' (mem_image_of_mem (fun y ↦ dist x y) h)

/-- The constant appearing in part 2 of Lemma 2.1.3. -/
def C2_1_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 2) * a ^ 3)
/-- The constant appearing in part 3 of Lemma 2.1.3. -/
def D2_1_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 2 + 𝕔/4) * a ^ 3)

-- 1.0.14.
lemma kernel_bound {s : ℤ} {x y : X} : ‖Ks s x y‖ₑ ≤ C_K a / vol x y := by
  change ‖K x y * ψ (D ^ (-s) * dist x y)‖ₑ ≤ C_K a / volume (ball x (dist x y))
  calc
    ‖K x y * ψ (D ^ (-s) * dist x y)‖ₑ
      = ‖K x y‖ₑ * ‖(ψ (D ^ (-s) * dist x y) : ℂ)‖ₑ := enorm_mul ..
    _ ≤ ‖K x y‖ₑ * 1               := by
        gcongr; rw [← ofReal_norm, norm_real]; norm_cast; exact abs_ψ_le_one D _
    _ ≤ ‖K x y‖ₑ                   := by rw [mul_one]
    _ ≤ _ := enorm_K_le_vol_inv x y

variable (s)

/-- Apply `volume_ball_two_le_same` `n` times. -/
lemma DoublingMeasure.volume_real_ball_two_le_same_repeat (x : X) (r : ℝ) (n : ℕ) :
    volume.real (ball x (2 ^ n * r)) ≤ (defaultA a) ^ n * volume.real (ball x r) := by
  induction' n with d ih; · simp
  rw [add_comm, pow_add, pow_one, mul_assoc]
  apply (measureReal_ball_two_le_same x _).trans
  have A_cast: (defaultA a : ℝ≥0).toReal = (defaultA a : ℝ) := rfl
  rwa [A_cast, pow_add, mul_assoc, pow_one, mul_le_mul_left (by positivity)]

-- Special case of `DoublingMeasure.volume_ball_two_le_same_repeat` used to prove `div_vol_le`
private lemma DoublingMeasure.volume_real_ball_two_le_same_repeat' (x : X) (n : ℕ) :
    volume.real (ball x (2 ^ n * D ^ s)) ≤
    (defaultA a) ^ (2 + n + 𝕔 * a ^ 2) * volume.real (ball x (D ^ (s - 1) / 4)) := by
  convert volume_real_ball_two_le_same_repeat x (D ^ (s - 1) / 4) (2 + n + 𝕔 * a ^ 2) using 3
  rw [defaultD, zpow_sub₀ (by positivity), pow_add, pow_add]
  field_simp
  ring

/-- Apply `volume_ball_two_le_same` `n` times. -/
lemma DoublingMeasure.volume_ball_two_le_same_repeat (x : X) (r : ℝ) (n : ℕ) :
    volume (ball x (2 ^ n * r)) ≤ (defaultA a) ^ n * volume (ball x r) := by
  induction' n with d ih; · simp
  rw [add_comm, pow_add, pow_one, mul_assoc]
  apply (measure_ball_two_le_same x _).trans
  have A_cast: ((defaultA a : ℝ≥0) : ℝ≥0∞) = (defaultA a : ℝ≥0∞) := rfl
  rw [A_cast, pow_add, mul_assoc, pow_one]
  gcongr

-- Special case of `DoublingMeasure.volume_ball_two_le_same_repeat` used to prove `div_vol_le`
private lemma DoublingMeasure.volume_ball_two_le_same_repeat' (x : X) (n : ℕ) :
    volume (ball x (2 ^ n * D ^ s)) ≤
    (defaultA a) ^ (2 + n + 𝕔 * a ^ 2) * volume (ball x (D ^ (s - 1) / 4)) := by
  convert volume_ball_two_le_same_repeat x (D ^ (s - 1) / 4) (2 + n + 𝕔 * a ^ 2) using 3
  rw [defaultD, zpow_sub₀ (by positivity), pow_add, pow_add]
  field_simp
  ring

lemma Metric.measure_ball_pos_nnreal (x : X) (r : ℝ) (hr : r > 0) :
    (volume (ball x r)).toNNReal > 0 :=
  ENNReal.toNNReal_pos (ne_of_gt (measure_ball_pos volume x hr)) measure_ball_ne_top

lemma Metric.measure_ball_pos_real (x : X) (r : ℝ) (hr : r > 0) : volume.real (ball x r) > 0 :=
  measure_ball_pos_nnreal x r hr

include a in
lemma K_eq_K_of_dist_eq_zero {x y y' : X} (hyy' : dist y y' = 0) :
    K x y = K x y' := by
  suffices ‖K x y - K x y'‖ₑ = 0 by rwa [enorm_eq_zero, sub_eq_zero] at this
  suffices ‖K x y - K x y'‖ₑ ≤ 0 from le_antisymm this (zero_le _)
  convert enorm_K_sub_le (K := K) (x := x) (y := y) (y' := y')
    (by simp only [hyy', mul_zero, dist_nonneg])
  replace hyy' : edist y y' = 0 := by rw [edist_dist, hyy', ENNReal.ofReal_zero]
  suffices (0 : ℝ≥0∞) ^ (a : ℝ)⁻¹ = 0 by simp [hyy', this]
  have : 0 < a := by linarith [four_le_a X]
  simp [this]

include a in
lemma K_eq_zero_of_dist_eq_zero {x y : X} (hxy : dist x y = 0) :
    K x y = 0 :=
  norm_le_zero_iff.1 <| by
    simpa [hxy, Real.vol, ENNReal.div_zero] using norm_K_le_vol_inv (K := K) x y

variable {s}

private lemma div_vol_le {x y : X} {c : ℝ} (hc : c > 0) (hxy : dist x y ≥ D ^ (s - 1) / 4)
    (n : ℕ) : c / volume.real (ball x (dist x y)) ≤
    (2 ^ ((2 + n) * a + 𝕔 * a ^ 3)) * c / volume.real (ball x (2 ^ n * D ^ s)) := by
  have h : 0 ≠ dist x y := (lt_of_lt_of_le (div_pos (defaultD_pow_pos a (s - 1)) four_pos) hxy).ne
  have v0₁ := measure_ball_pos_nnreal x (dist x y) <| lt_of_le_of_ne dist_nonneg h
  have v0₂ := measure_ball_pos_nnreal x (D ^ (s - 1) / 4) (by have := D0' X; positivity)
  have v0₃ := measure_ball_pos_real x _ (mul_pos (pow_pos two_pos n) (defaultD_pow_pos a s))
  have ball_subset := ball_subset_ball (x := x) hxy
  apply le_trans <| (div_le_div_iff_of_pos_left hc v0₁ v0₂).2 <|
    ENNReal.toNNReal_mono measure_ball_ne_top (OuterMeasureClass.measure_mono _ ball_subset)
  dsimp only
  rw [div_le_div_iff₀ (by exact_mod_cast v0₂) v0₃]
  apply le_of_le_of_eq <| (mul_le_mul_left hc).2 <|
    DoublingMeasure.volume_real_ball_two_le_same_repeat' s x n
  simp_rw [defaultA, ← mul_assoc, mul_comm c]
  rw_mod_cast [← pow_mul]
  congr
  ring

-- Useful special case of `div_vol_le`
private lemma div_vol_le₀ {x y : X} {c : ℝ} (hc : c > 0) (hK : Ks s x y ≠ 0) :
    c / volume.real (ball x (dist x y)) ≤
    (2 ^ (2 * a + 𝕔 * a ^ 3)) * c / volume.real (ball x (D ^ s)) := by
  simpa using div_vol_le hc (mem_Icc.1 (dist_mem_Icc_of_Ks_ne_zero hK)).1 0

-- preferably use `enorm_K_le`
lemma norm_K_le {s : ℤ} {x y : X} (n : ℕ) (hxy : dist x y ≥ D ^ (s - 1) / 4) :
    ‖K x y‖ ≤ 2 ^ ((2 + n) * a + (𝕔 + 1) * a ^ 3) / volume.real (ball x (2 ^ n * D ^ s)) := by
  by_cases h : dist x y = 0
  · rw [K_eq_zero_of_dist_eq_zero h, norm_zero]; positivity
  apply (norm_K_le_vol_inv x y).trans
  unfold C_K
  apply le_trans (div_vol_le (by norm_cast; positivity) hxy n)
  apply div_le_div_of_nonneg_right _ measureReal_nonneg
  exact_mod_cast le_of_eq (by ring)

lemma enorm_K_le {s : ℤ} {x y : X} (n : ℕ) (hxy : dist x y ≥ D ^ (s - 1) / 4) :
    ‖K x y‖ₑ ≤ 2 ^ ((2 + n) * a + (𝕔 + 1) * a ^ 3) / volume (ball x (2 ^ n * D ^ s)) := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_toReal measure_ball_ne_top,
    ← ENNReal.ofReal_div_of_pos, ← Measure.real, ← ofReal_norm]; swap
  · apply ENNReal.toReal_pos ?_ measure_ball_ne_top
    · refine (measure_ball_pos volume x ?_).ne.symm
      exact mul_pos (pow_pos two_pos n) (defaultD_pow_pos a s)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact norm_K_le n hxy

-- 2.1.3
lemma norm_Ks_le {s : ℤ} {x y : X} :
    ‖Ks s x y‖ ≤ C2_1_3 a / volume.real (ball x (D ^ s)) := by
  have : 0 ≤ C2_1_3 a / volume.real (ball x (D ^ s)) := by unfold C2_1_3; positivity
  by_cases hK : Ks s x y = 0
  · rwa [hK, norm_zero]
  rw [Ks, norm_mul, norm_real, ← mul_one (_ / _)]
  gcongr
  · apply le_trans <| norm_K_le 0 (mem_Icc.1 (dist_mem_Icc_of_Ks_ne_zero hK)).1
    rw [pow_zero, one_mul, add_zero]
    suffices 2 * (a : ℝ) + (𝕔 + 1) * a ^ 3 ≤ (𝕔 + 2) * a ^ 3 by
      gcongr; simpa [C2_1_3, ← Real.rpow_natCast, -Real.rpow_ofNat] using this
    suffices 2 * (a : ℝ) ≤ a ^ 2 * a by linarith
    nlinarith [show 4 ≤ (a : ℝ) by exact_mod_cast four_le_a X]
  · exact abs_ψ_le_one D (D ^ (-s) * dist x y)

-- 2.1.3 (ENNReal version)
lemma enorm_Ks_le {s : ℤ} {x y : X} :
    ‖Ks s x y‖ₑ ≤ C2_1_3 a / volume (ball x (D ^ s)) := by
  calc
    _ ≤ ‖C2_1_3 a / volume.real (ball x (D ^ s))‖ₑ := by
      rw [← enorm_norm]; exact Real.enorm_le_enorm (norm_nonneg _) norm_Ks_le
    _ = _ := by
      rw [div_eq_mul_inv, enorm_mul, enorm_inv]; swap
      · exact ENNReal.toReal_ne_zero.mpr
          ⟨(measure_ball_pos volume _ (defaultD_pow_pos a s)).ne', by finiteness⟩
      rw [enorm_eq, ← div_eq_mul_inv, Real.enorm_eq_ofReal measureReal_nonneg]; congr 1
      exact ENNReal.ofReal_toReal (by finiteness)

/-- Needed for Lemma 7.5.5. -/
lemma enorm_Ks_le' {s : ℤ} {x y : X} :
    ‖Ks s x y‖ₑ ≤ C2_1_3 a / volume (ball x (D ^ s)) * ‖ψ (D ^ (-s) * dist x y)‖ₑ := by
  by_cases hK : Ks s x y = 0
  · rw [hK, enorm_zero]; exact zero_le _
  rw [Ks, enorm_mul]; nth_rw 2 [← enorm_norm]; rw [norm_real, enorm_norm]
  gcongr; apply le_trans <| enorm_K_le 0 (mem_Icc.1 (dist_mem_Icc_of_Ks_ne_zero hK)).1
  rw [pow_zero, one_mul]; norm_cast; rw [add_zero, C2_1_3]; gcongr; norm_cast
  rw [show (𝕔 + 2) * a ^ 3 = a ^ 2 * a + (𝕔 + 1) * a ^ 3 by ring]; gcongr
  · exact one_le_two
  · nlinarith [four_le_a X]

/-- `Ks` is bounded uniformly in `x`, `y` assuming `x` is in a fixed closed ball. -/
lemma norm_Ks_le_of_dist_le {x y x₀ : X} {r₀ : ℝ} (hr₀ : 0 < r₀) (hx : dist x x₀ ≤ r₀) (s : ℤ) :
    ‖Ks s x y‖ ≤ C2_1_3 a * (As (defaultA a) (2*r₀/D^s)) / volume.real (ball x₀ r₀) := by
  let C := As (defaultA a) (2*r₀/D^s)
  have : 0 < C := As_pos (volume : Measure X) (2*r₀/D^s)
  have : 0 < volume.real (ball x₀ r₀) := measure_ball_pos_real _ _ hr₀
  suffices h : C⁻¹*volume.real (ball x₀ r₀) ≤ volume.real (ball x (D^s)) by
    apply norm_Ks_le.trans
    calc
      _ ≤ C2_1_3 a / (C⁻¹*volume.real (ball x₀ r₀)) := by gcongr
      _ = _ := by unfold defaultA defaultD C; field_simp
  have : volume.real (ball x (2*r₀)) ≤ C * volume.real (ball x (D^s)) := by
    have : (0:ℝ) < D := defaultD_pos _
    refine measureReal_ball_le_same x (by positivity) ?_
    apply le_of_eq; field_simp
  calc
    _ ≤ C⁻¹ * volume.real (ball x (2*r₀)) := by
      gcongr
      · exact measure_ball_ne_top
      · exact ball_subset_ball_of_le (by linarith)
    _ ≤ C⁻¹ * (C * volume.real (ball x (D^s))) := by gcongr
    _ = _ := by field_simp

/-- `‖Ks x y‖` is bounded if `x` is in a bounded set -/
lemma _root_.Bornology.IsBounded.exists_bound_of_norm_Ks
    {A : Set X} (hA : IsBounded A) (s : ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ x y, x ∈ A → ‖Ks s x y‖ ≤ C := by
  obtain x₀ : X := Classical.choice (by infer_instance)
  obtain ⟨r₀, hr₀, h⟩ := hA.subset_closedBall_lt 0 x₀
  use ?_; constructor; swap -- let Lean fill in the value of the ugly constant
  · intro x y hx
    convert norm_Ks_le_of_dist_le hr₀ (h hx) s
  · positivity

-- Needed to prove `ψ_ineq`
private lemma norm_ψ_sub_ψ_le_two {r s : ℝ} : ‖ψ r - ψ s‖ ≤ 2 :=
  (norm_sub_le _ _).trans <| le_of_le_of_eq (add_le_add (abs_ψ_le_one D r) (abs_ψ_le_one D s))
    one_add_one_eq_two

private lemma Ks_eq_Ks (x : X) {y y' : X} (hyy' : dist y y' = 0) :
    Ks s x y = Ks s x y' := by
  simp_rw [Ks, PseudoMetricSpace.dist_eq_of_dist_zero x hyy', K_eq_K_of_dist_eq_zero hyy']

-- Needed to prove `norm_Ks_sub_Ks_le`
include K in
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

private lemma D_pow_a_inv : (D : ℝ) ^ (a : ℝ)⁻¹ = 2 ^ (𝕔 * a) :=
  calc
    _ = ((2 : ℝ) ^ (𝕔 * a ^ 2 : ℝ)) ^ (a : ℝ)⁻¹ := by rw [defaultD]; norm_cast
    _ = 2 ^ (𝕔 * a ^ 2 * (a : ℝ)⁻¹) := by rw [← Real.rpow_mul two_pos.le]
    _ = 2 ^ (𝕔 * (a * a * (a : ℝ)⁻¹)) := by rw [mul_assoc, sq]
    _ = _ := by rw [mul_self_mul_inv]; norm_cast

include K in
private lemma four_D_rpow_a_inv : (4 * D : ℝ) ^ (a : ℝ)⁻¹ ≤ 2 ^ (1 + 𝕔 * a) := by
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

/-
-- Part of the inequality needed for `norm_Ks_sub_Ks_le₀`.
private lemma norm_Ks_sub_Ks_le₀₀ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
     (hyy' : 2 * dist y y' ≤ dist x y) : ‖K x y - K x y'‖ * |ψ (D ^ (-s) * dist x y')| ≤
    (2 : ℝ) ^ (1 + (𝕔 + 2) * a + (𝕔 + 1) * a ^ 3) / volume.real (ball x (D ^ s)) *
    (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
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
  apply le_trans <| mul_le_mul this (div_vol_le₀ C_K_pos_real hK)
    (by simp only [C_K, coe_rpow, NNReal.coe_ofNat, defaultA]; positivity) (by positivity)
  rw [(by ring : (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ * (4 * D) ^ (a : ℝ)⁻¹ *
      (2 ^ (2 * a + 𝕔 * a ^ 3) * C_K a / volume.real (ball x (D ^ s))) =
      (4 * D) ^ (a : ℝ)⁻¹ * 2 ^ (2 * a + 𝕔 * a ^ 3) * C_K a / volume.real (ball x (D ^ s)) *
      (dist y y' / D ^ s) ^ (a : ℝ)⁻¹)]
  gcongr
  have : (4 * D : ℝ) ^ (a : ℝ)⁻¹ * 2 ^ (2 * a + 𝕔 * a ^ 3) * C_K a ≤
      2 ^ (1 + 𝕔 * a) * 2 ^ (2 * a + 𝕔 * a ^ 3) * 2 ^ a ^ 3 := by
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
    (2 : ℝ) ^ (2 + 2 * a + 𝕔 * a ^ 2 + (𝕔 + 1) * a ^ 3) / volume.real (ball x (D ^ s)) *
    (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  have : 2 ^ (2 + 2 * a + 𝕔 * a ^ 2 + (𝕔 + 1) * a ^ 3) / volume.real (ball x (D ^ s)) *
      (dist y y' / D ^ s) ^ (a : ℝ)⁻¹ = 2 ^ (2 * a + (𝕔 + 1) * a ^ 3)
      / volume.real (ball x (D ^ s)) * (4 * D * (dist y y' / D ^ s) ^ (a : ℝ)⁻¹) := by
    field_simp; ring
  rw [this]
  refine mul_le_mul ?_ ψ_ineq (abs_nonneg _) (by positivity)
  apply le_trans <| norm_K_le_vol_inv x y
  apply le_of_le_of_eq <| div_vol_le₀ C_K_pos_real hK
  rw_mod_cast [C_K, ← pow_add, show 2 * a + 𝕔 * a ^ 3 + a ^ 3 = 2 * a + (𝕔 + 1) * a ^ 3 by ring]

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
  simp_rw [D2_1_3, norm_mul, norm_real]
  apply le_trans (add_le_add (norm_Ks_sub_Ks_le₀₀ hK h) (norm_Ks_sub_Ks_le₀₁ hK))
  field_simp
  rw [← add_mul]
  gcongr
  norm_cast
  have : 1 + (𝕔 + 2) * a + (𝕔 + 1) * a ^ 3 ≤ 2 + 2 * a + 𝕔 * a ^ 2 + (𝕔 + 1) * a ^ 3 := by
    ring_nf
    gcongr
    · norm_num
    · nlinarith [four_le_a X]
  apply (Nat.add_le_add_right (pow_le_pow_right₀ one_lt_two.le this) _).trans
  rw [← two_mul, ← pow_succ']; gcongr
  · exact one_le_two
  · have a4 := four_le_a X
    have a3 : 3 ≤ a := by linarith
    calc
      _ = (𝕔 + 1) * a ^ 3 + 𝕔 * a ^ 2 + 2 * a + 3 := by ring
      _ ≤ (𝕔 + 1) * a ^ 3 + (4 * (𝕔/4) + 3) * a ^ 2 + 2 * a + a := by gcongr; omega
      _ = (𝕔 + 1) * a ^ 3 + (𝕔/4) * 4 * a * a + 3 * a ^ 2 + 3 * a := by ring
      _ ≤ (𝕔 + 1) * a ^ 3 + (𝕔/4) * a * a * a + 3 * a ^ 2 + a * a := by gcongr
      _ = (𝕔 + 1 + 𝕔/4) * a ^ 3 + 4 * a ^ 2 := by ring
      _ ≤ (𝕔 + 1 + 𝕔/4) * a ^ 3 + a * a ^ 2 := by gcongr
      _ = (𝕔 + 2 + 𝕔/4) * a ^ 3 := by ring
-/

-- Special case of `norm_Ks_sub_Ks_le`
private lemma enorm_Ks_sub_Ks_le₀ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
    (h : 2 * edist y y' ≤ edist x y) : ‖Ks s x y - Ks s x y'‖ₑ ≤
    D2_1_3 a / volume (ball x (D ^ s)) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  unfold Ks
  sorry

-- First case of `norm_Ks_sub_Ks_le` in blueprint
private lemma enorm_Ks_sub_Ks_le₁ {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
    (h : ¬ 2 * edist y y' ≤ edist x y) : ‖Ks s x y - Ks s x y'‖ₑ ≤
      D2_1_3 a / volume (ball x (D ^ s)) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  -- triangle inequality combined with 2.1.3 (`enorm_Ks_le`)
  apply enorm_sub_le.trans <| add_le_add enorm_Ks_le enorm_Ks_le |>.trans _
  rw [← ENNReal.mul_div_right_comm,
    ENNReal.div_add_div_same, ← two_mul, ← pow_one 2]
  apply ENNReal.div_le_div_right
  replace h := ENNReal.div_lt_of_lt_mul' <| not_le.mp h
  have edist_pos : 0 < edist y y' := zero_le _ |>.trans_lt h
  have : D ^ (s - 1) / 8 < edist y y' := by --lower bound 2.1.2 combined with `h`
    apply lt_of_le_of_lt _ h
    have : (2 : ℝ≥0∞) / 8 = 1 / 4 := by apply ENNReal.div_eq_div_iff .. |>.mpr (by norm_num) <;> simp
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), ENNReal.mul_comm_div, this,
      ← ENNReal.mul_comm_div, mul_one, edist_dist, ENNReal.le_ofReal_iff_toReal_le ?fin dist_nonneg,
      ENNReal.toReal_div, ← ENNReal.toReal_zpow]
    case fin => finiteness_nonterminal; apply ENNReal.zpow_ne_top <;> simp
    exact_mod_cast (mem_Icc.1 <| dist_mem_Icc_of_Ks_ne_zero hK).1
  -- apply `this`
  have : ↑(D2_1_3 a) * (1 / (8 * D) ) ^ (a : ℝ)⁻¹ ≤ ↑(D2_1_3 a) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
    gcongr 2
    refine (ENNReal.div_le_iff' (by unfold defaultD; positivity) (by finiteness)).mpr ?_
    trans 8 * ↑D * (D ^ (s - 1) / 8 / ↑D ^ s)
    on_goal 2 => gcongr
    apply le_of_eq
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← ENNReal.zpow_neg (by simp) (by simp)]
    suffices 1 = (8 * (8 : ℝ≥0∞)⁻¹) * (D ^ (1 : ℤ) * D ^ (-s) * D ^ (s - 1)) by
      apply this.trans
      rw [zpow_one]
      ring
    rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, mul_assoc,
      ← ENNReal.zpow_add (by simp) (by simp), ← ENNReal.zpow_add (by simp) (by simp)]
    ring_nf
    simp
  apply le_trans _ this
  -- constant manipulation
  rw [one_div, ENNReal.inv_rpow, ← ENNReal.rpow_neg, C2_1_3, D2_1_3, defaultD]
  push_cast
  rw [show 8 * (2 : ℝ≥0∞) ^ (𝕔 * a ^ 2) = 2 ^ (𝕔 * a ^ 2 + 3) by ring, ← pow_add,
    ← ENNReal.rpow_natCast_mul]
  simp_rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
  apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
  simp only [mul_neg, le_add_neg_iff_add_le]
  have _ := four_le_a X
  have _ := seven_le_c
  rw [← mul_le_mul_iff_of_pos_right (a := (a : ℝ)) (by positivity)]
  ring_nf
  rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  norm_cast
  ring_nf
  apply le_of_eq_of_le (show _ = 𝕔 * a ^ 4 + a ^ 4 * 2 + (3 + a + 𝕔 * a ^ 2) by ring)
  gcongr
  calc _
    _ ≤ 2 * a ^ 2 * 𝕔 := by
      nth_rw 1 [mul_comm]
      rw [mul_assoc, two_mul]
      gcongr
      apply le_trans (b := a * 2) (by linarith)
      gcongr <;> linarith [Nat.le_pow zero_lt_two (a := a)]
    _ ≤ (2 * a ^ 2) * (2 * a * (𝕔 / 4)) := by
      gcongr
      rw [mul_assoc]
      apply le_trans (b := (4 + 4) * (𝕔 / 4)) (by omega) (by rw [← mul_assoc, two_mul]; gcongr)
    _ = 4 * a ^ 3 * (𝕔 / 4) := by ring
    _ ≤ a * a ^ 3 * (𝕔 / 4) := by gcongr
  linarith

lemma enorm_Ks_sub_Ks_le_of_nonzero {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0) :
    ‖Ks s x y - Ks s x y'‖ₑ ≤
      D2_1_3 a / volume (ball x (D ^ s)) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  by_cases h : 2 * edist y y' ≤ edist x y
  · exact enorm_Ks_sub_Ks_le₀ hK h
  · exact enorm_Ks_sub_Ks_le₁ hK h

-- 2.1.3
lemma enorm_Ks_sub_Ks_le {s : ℤ} {x y y' : X} :
    ‖Ks s x y - Ks s x y'‖ₑ ≤
      D2_1_3 a / volume (ball x (D ^ s)) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  by_cases h : Ks s x y ≠ 0 ∨ Ks s x y' ≠ 0
  · rcases h with hy | hy'
    · exact enorm_Ks_sub_Ks_le_of_nonzero hy
    · rw [← neg_sub, enorm_neg, edist_comm]
      exact enorm_Ks_sub_Ks_le_of_nonzero hy'
  · simp only [ne_eq, not_or, Decidable.not_not] at h
    rw [h.1, h.2, sub_zero, enorm_zero]
    positivity

lemma stronglyMeasurable_Ks {s : ℤ} : StronglyMeasurable (fun x : X × X ↦ Ks s x.1 x.2) := by
  unfold Ks _root_.ψ
  refine stronglyMeasurable_K.mul ?_
  apply Continuous.stronglyMeasurable
  fun_prop

@[fun_prop]
lemma measurable_Ks {s : ℤ} : Measurable (fun x : X × X ↦ Ks s x.1 x.2) := by
  unfold Ks _root_.ψ
  exact measurable_K.mul (by fun_prop)

lemma aestronglyMeasurable_Ks {s : ℤ} : AEStronglyMeasurable (fun x : X × X ↦ Ks s x.1 x.2) :=
  measurable_Ks.aestronglyMeasurable

/-- The function `y ↦ Ks s x y` is integrable. -/
lemma integrable_Ks_x {s : ℤ} {x : X} (hD : 1 < (D : ℝ)) : Integrable (Ks s x) := by
  let r := D ^ s * ((D : ℝ)⁻¹ * (4 : ℝ)⁻¹)
  have hr : 0 < r := by positivity
  rw [← integrableOn_iff_integrable_of_support_subset (s := (ball x r)ᶜ)]
  · refine integrableOn_K_mul ?_ x hr (subset_refl _)
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_ofReal.comp <| continuous_ψ.comp <| (by fun_prop)
    · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (D ^ s / 2))
      intro y hy
      rw [mem_support, ne_eq, ofReal_eq_zero, ← ne_eq, ← mem_support, support_ψ (D1 X)] at hy
      replace hy := hy.2.le
      rw [zpow_neg, mul_comm, ← div_eq_mul_inv, div_le_iff₀ (Ds0 X s)] at hy
      rwa [mem_closedBall, dist_comm, div_eq_mul_inv, mul_comm]
  · intro y hy
    rw [mem_compl_iff, mem_ball', not_lt]
    have : «ψ» D (((D : ℝ) ^ s)⁻¹ * dist x y) ≠ 0 := by simp_all [Ks]
    rw [← Function.mem_support, support_ψ hD, mul_inv_rev] at this
    exact le_inv_mul_iff₀ (defaultD_pow_pos a s) |>.mp this.1.le

end PseudoMetricSpace

section MetricSpace

variable (X : Type*) {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] {s : ℤ} {x y : X}

lemma Ks_eq_zero_of_dist_le {s : ℤ} {x y : X} (hxy : x ≠ y)
    (h : dist x y ≤ defaultD a ^ (s - 1) / 4) :
    Ks s x y = 0 := by
  rw [Ks_def]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  rw [psi_eq_zero_iff (one_lt_D (X := X)) (dist_pos.mpr hxy),
    mem_nonzeroS_iff (one_lt_D (X := X)) (dist_pos.mpr hxy)]
  simp only [mem_Ioo, not_and_or, not_lt]
  left
  rw [mul_comm]
  apply mul_le_of_le_mul_inv₀ (by positivity) (by positivity)
  simp only [mul_inv_rev, zpow_neg, inv_inv]
  have heq : (D : ℝ)⁻¹ * 4⁻¹ * ↑D ^ s = defaultD a ^ (s - 1) / 4 := by
    ring_nf
    rw [← zpow_neg_one, zpow_add₀ (by simp)]
  exact heq ▸ h

lemma Ks_eq_zero_of_le_dist {s : ℤ} {x y : X} (h : D ^ s / 2 ≤ dist x y) : Ks s x y = 0 := by
  have hxy : x ≠ y := by
    rw [← dist_pos]
    apply lt_of_lt_of_le _ h
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact defaultD_pow_pos a s
  rw [Ks_def]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  rw [psi_eq_zero_iff (one_lt_D (X := X)) (dist_pos.mpr hxy),
    mem_nonzeroS_iff (one_lt_D (X := X)) (dist_pos.mpr hxy)]
  simp only [mem_Ioo, not_and_or, not_lt]
  right
  rw [zpow_neg, le_inv_mul_iff₀ (defaultD_pow_pos a s)]
  exact h

end MetricSpace
