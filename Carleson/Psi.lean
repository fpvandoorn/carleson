import Carleson.ProofData
import Mathlib.Tactic.Field

open MeasureTheory Measure NNReal Metric Set TopologicalSpace Function DoublingMeasure Bornology
open scoped ENNReal
noncomputable section

/-! The function `ψ` -/

/- Note: In this section, `D` is an arbitrary real and not equal to `defaultD`
Instead, hypothesis `hD` is used.
-/
section D
variable {D : ℕ} {x : ℝ} {s : ℤ} (hD : 1 < (D : ℝ))

open Real

section -- We record here some trivial inequalities that are used repeatedly below.
include hD
private lemma D0 : 0 < (D : ℝ) := one_pos.trans hD
private lemma D2 : 2 ≤ (D : ℝ) := by exact_mod_cast hD
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

lemma enorm_ψ_le_one (D : ℕ) (x : ℝ) : ‖ψ D x‖ₑ ≤ 1 := by
  rw [← enorm_one (G := ℝ)]; exact enorm_le_enorm (zero_le_ψ ..) (ψ_le_one ..)

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
  have : x ≥ 0 := le_trans (one_div_nonneg.2 (by linarith)) hx.1
  have hx1 := (div_le_iff₀' (by linarith)).1 hx.1
  have hx2 := (le_div_iff₀' (by linarith)).1 hx.2
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
  have := (div_le_iff₀' (by linarith)).1 hx.1
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
  by_cases! hx₀ : x ≤ 1 / (4 * D)
  · suffices x ≤ (D : ℝ)⁻¹ * 4⁻¹ by simp [ψ_formula₀ hx₀, this]
    rwa [one_div, mul_inv_rev] at hx₀
  have hx₀_inv : (D : ℝ)⁻¹ * 4⁻¹ < x := by convert hx₀ using 1; simp
  have ne₀ : 4 * D * x - 1 ≠ 0 := ne_of_gt (by rwa [sub_pos, ← div_lt_iff₀' (by linarith)])
  by_cases! hx₁ : x ≤ 1 / (2 * D)
  · suffices (D : ℝ)⁻¹ * 4⁻¹ < x ∧ x < 2⁻¹ by simpa [ne₀, ψ_formula₁ hD ⟨hx₀.le, hx₁⟩]
    exact ⟨hx₀_inv, lt_of_le_of_lt hx₁ (by simp [_root_.inv_lt_one_iff₀, hD])⟩
  by_cases! hx₂ : x ≤ 1 / 4
  · simpa [ψ_formula₂ hD ⟨hx₁.le, hx₂⟩, hx₀_inv] using lt_of_le_of_lt hx₂ (by norm_num)
  by_cases hx₃ : x < 1 / 2
  · have : ¬ 2 - 4 * x = 0 := by linarith
    simpa [ψ_formula₃ hD ⟨hx₂.le, hx₃.le⟩, hx₀, hx₃, ← one_div]
  · rw [mem_support, ψ_formula₄ (not_lt.1 hx₃), ne_self_iff_false, false_iff, mem_Ioo, not_and,
      inv_eq_one_div 2]
    exact fun _ ↦ hx₃

lemma lipschitzWith_ψ (hD : 1 ≤ D) : LipschitzWith (4 * D) (ψ D) := by
  have max_eq_4D : max 0 (4 * D : ℝ≥0) = 4 * D := max_eq_right (by positivity)
  have max_eq_4D' : max (4 * D) 4 = 4 * D := by apply max_eq_left; linarith
  suffices LipschitzWith (4 * D) (fun (x : ℝ) ↦ min 1 <| min (4 * D * x - 1) (2 - 4 * x)) from
    max_eq_4D ▸ (LipschitzWith.const 0).max this
  suffices LipschitzWith (4 * D) (fun (x : ℝ) ↦ min (4 * D * x - 1) (2 - 4 * x)) from
    max_eq_4D ▸ (LipschitzWith.const 1).min this
  have lw1 : LipschitzWith (4 * D) (fun (x : ℝ) ↦ 4 * D * x - 1) := by
    refine LipschitzWith.of_le_add_mul (4 * D) (fun x y ↦ ?_)
    suffices 4 * D * (x - y) ≤ 4 * D * dist x y by norm_cast at this ⊢; linarith
    exact (mul_le_mul_iff_right₀ (by positivity)).2 <| sub_le_dist x y
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
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
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
  · rw [← rpow_le_rpow_left_iff hD, ← inv_le_inv₀ (by positivity) (by positivity),
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
  · rw [← inv_eq_one_div, zpow_neg, inv_lt_inv₀ (by positivity) (cDx0 hD two_pos hx)] at h
    rw [Int.le_sub_one_iff, Int.floor_lt, ← rpow_lt_rpow_left_iff hD,
      rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD two_pos hx)]
    exact_mod_cast h
  · apply sub_le_iff_le_add.2 ∘ Int.ceil_le.2
    suffices logb D (4 * x) ≤ logb D (2 * D * x) by
      exact_mod_cast (lt_of_le_of_lt this (Int.lt_floor_add_one _)).le
    have : 4 * x ≤ 2 * D * x := (mul_le_mul_iff_left₀ hx).2 (by linarith [D2 hD])
    refine (strictMonoOn_logb hD).monotoneOn ?_ ?_ this <;> exact mem_Ioi.2 (by positivity)

-- Special case of `sum_ψ`, for the case where `nonzeroS D x` has one element.
private lemma sum_ψ₁ (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)) :
    ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  rw [nonzeroS, eq_endpoints hD hx h, Finset.Icc_self, Finset.sum_singleton]
  refine ψ_formula₂ hD ⟨le_of_eq_of_le (by field_simp) ((mul_le_mul_iff_left₀ hx).2 h), ?_⟩
  calc
    D ^ (-⌈logb D (4 * x)⌉) * x
      = D ^ (-⌈logb D (4 * x)⌉ : ℝ) * x := by norm_cast
    _ ≤ D ^ (-logb D (4 * x)) * x := by gcongr; exacts [hD.le, Int.le_ceil _]
    _ = 1 / (4 * x) * x := by
      rw [rpow_neg (D0 hD).le, inv_eq_one_div, rpow_logb (D0 hD) hD.ne.symm (by linarith)]
    _ = 1 / 4 := by field_simp

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
  have Ds₀x_lt := (mul_lt_mul_iff_left₀ hx).2 h
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
    add_comm _ 1, add_lt_add_iff_left, ← lt_div_iff₀ hx, mul_comm (D : ℝ)⁻¹,
    ← div_lt_div_iff₀ hx (inv_pos.2 (D0 hD)), div_inv_eq_mul, ← zpow_add_one₀ ((D0 hD).ne.symm),
    zpow_neg, ← Real.rpow_intCast, ← Real.rpow_intCast, lt_logb_iff_rpow_lt hD (by positivity),
    logb_lt_iff_lt_rpow hD (mul_pos two_pos hx), ← sub_eq_neg_add, ← neg_sub i 1, ← inv_mul',
    ← inv_mul', inv_lt_inv₀ (by positivity) (mul_pos two_pos hx), Int.cast_neg, Int.cast_sub,
    Int.cast_one, rpow_neg (D0 hD).le, inv_lt_inv₀ (by positivity) (by positivity), and_comm]

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
  have hfin : HasFiniteSupport (fun s : ℤ ↦ ψ D (D ^ (-s) * x)) := by
    have h := Finset.finite_toSet (nonzeroS D x)
    rwa [← support_ψS hD hx] at h
  apply Eq.trans <| finsum_eq_sum _ hfin
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

private lemma zpow_realD_pos (s : ℤ) : 0 < (D : ℝ) ^ s := by positivity [realD_pos a]

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
  have dist_mem_Ioo := support_ψ (one_lt_realD X) ▸ mem_support.2 (not_or.1 h).2
  rwa [mem_Ioo, ← div_eq_inv_mul, lt_div_iff₀ (zpow_realD_pos s),
    div_lt_iff₀ (zpow_realD_pos s), mul_inv, mul_assoc, inv_mul_eq_div (4 : ℝ), ← zpow_neg_one,
    ← zpow_add₀ (realD_pos a).ne.symm, neg_add_eq_sub, ← div_eq_inv_mul] at dist_mem_Ioo

/-- Lemma 2.1.3 part 1, equation (2.1.2) -/
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

private lemma lowerBound_edist_of_Ks_ne_zero {s : ℤ} {x y : X} (h : Ks s x y ≠ 0) :
    D ^ (s - 1) / 4 ≤ edist x y := by
  rw [edist_dist, ENNReal.le_ofReal_iff_toReal_le ?fin dist_nonneg]
  case fin =>
    finiteness_nonterminal
    apply ENNReal.zpow_ne_top <;> simp
  apply le_trans _ <| dist_mem_Icc_of_Ks_ne_zero h |>.1
  rw [ENNReal.toReal_div, ← ENNReal.toReal_zpow]
  simp

/-- The constant appearing in part 2 of Lemma 2.1.3.
Equal to `2 ^ (102 * a ^ 3)` in the blueprint. -/
def C2_1_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 2) * a ^ 3)

/-- The constant appearing in part 3 of Lemma 2.1.3.
Equal to `2 ^ (127 * a ^ 3)` in the blueprint. -/
def D2_1_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 2 + 𝕔 / 4) * a ^ 3)

/-- Equation (1.1.11) in the blueprint -/
lemma kernel_bound {s : ℤ} {x y : X} : ‖Ks s x y‖ₑ ≤ C_K a / vol x y := by
  unfold Ks vol
  calc _
    _ = ‖K x y‖ₑ * ‖(ψ (D ^ (-s) * dist x y) : ℂ)‖ₑ := enorm_mul ..
    _ ≤ ‖K x y‖ₑ * 1 := by
        gcongr; rw [← ofReal_norm, norm_real]; exact_mod_cast abs_ψ_le_one D _
    _ ≤ ‖K x y‖ₑ := by rw [mul_one]
    _ ≤ _ := enorm_K_le_vol_inv x y

variable (s)

/-- Apply `volume_ball_two_le_same` `n` times. -/
private lemma DoublingMeasure.volume_real_ball_two_le_same_repeat (x : X) (r : ℝ) (n : ℕ) :
    volume.real (ball x (2 ^ n * r)) ≤ (defaultA a) ^ n * volume.real (ball x r) := by
  induction n with
  | zero => simp
  | succ d ih =>
  rw [add_comm, pow_add, pow_one, mul_assoc]
  apply (measureReal_ball_two_le_same x _).trans
  have A_cast : (defaultA a : ℝ≥0).toReal = (defaultA a : ℝ) := rfl
  rwa [A_cast, pow_add, mul_assoc, pow_one, mul_le_mul_iff_right₀ (by positivity)]

-- Special case of `DoublingMeasure.volume_ball_two_le_same_repeat` used to prove `div_vol_le`
private lemma DoublingMeasure.volume_real_ball_two_le_same_repeat' (x : X) (n : ℕ) :
    volume.real (ball x (2 ^ n * D ^ s)) ≤
    (defaultA a) ^ (2 + n + 𝕔 * a ^ 2) * volume.real (ball x (D ^ (s - 1) / 4)) := by
  convert volume_real_ball_two_le_same_repeat x (D ^ (s - 1) / 4) (2 + n + 𝕔 * a ^ 2) using 3
  rw [defaultD, zpow_sub₀ (by positivity), pow_add, pow_add]
  simp
  field

/-- Apply `volume_ball_two_le_same` `n` times. -/
lemma DoublingMeasure.volume_ball_two_le_same_repeat (x : X) (r : ℝ) (n : ℕ) :
    volume (ball x (2 ^ n * r)) ≤ (defaultA a) ^ n * volume (ball x r) := by
  induction n with
  | zero => simp
  | succ d ih =>
  rw [add_comm, pow_add, pow_one, mul_assoc]
  apply (measure_ball_two_le_same x _).trans
  have A_cast : ((defaultA a : ℝ≥0) : ℝ≥0∞) = (defaultA a : ℝ≥0∞) := rfl
  rw [A_cast, pow_add, mul_assoc, pow_one]
  gcongr

-- Special case of `DoublingMeasure.volume_ball_two_le_same_repeat` used to prove `div_vol_le'`
private lemma DoublingMeasure.volume_ball_two_le_same_repeat' (x : X) (n : ℕ) :
    volume (ball x (2 ^ n * D ^ s)) ≤
    (defaultA a) ^ (2 + n + 𝕔 * a ^ 2) * volume (ball x (D ^ (s - 1) / 4)) := by
  convert volume_ball_two_le_same_repeat x (D ^ (s - 1) / 4) (2 + n + 𝕔 * a ^ 2) using 3
  rw [defaultD, zpow_sub₀ (by positivity)]
  simp
  field

lemma Metric.measure_ball_pos_nnreal (x : X) (r : ℝ) (hr : r > 0) :
    (volume (ball x r)).toNNReal > 0 :=
  ENNReal.toNNReal_pos (ne_of_gt (measure_ball_pos volume x hr)) measure_ball_ne_top

lemma Metric.measure_ball_pos_real (x : X) (r : ℝ) (hr : r > 0) : volume.real (ball x r) > 0 :=
  measure_ball_pos_nnreal x r hr

variable {s}

private lemma div_vol_le {x y : X} {c : ℝ} (hc : c > 0) (hxy : dist x y ≥ D ^ (s - 1) / 4) (n : ℕ) :
     c / Real.vol x y ≤
      (2 ^ ((2 + n) * a + 𝕔 * a ^ 3)) * c / volume.real (ball x (2 ^ n * D ^ s)) := by
  have h : 0 ≠ dist x y := (lt_of_lt_of_le (div_pos (defaultD_pow_pos a (s - 1)) four_pos) hxy).ne
  have v0₁ := measure_ball_pos_nnreal x (dist x y) <| lt_of_le_of_ne dist_nonneg h
  have v0₂ := measure_ball_pos_nnreal x (D ^ (s - 1) / 4) (by have := realD_pos a; positivity)
  have v0₃ := measure_ball_pos_real x _ (mul_pos (pow_pos two_pos n) (defaultD_pow_pos a s))
  have ball_subset := ball_subset_ball (x := x) hxy
  apply le_trans <| (div_le_div_iff_of_pos_left hc v0₁ v0₂).2 <|
    ENNReal.toNNReal_mono measure_ball_ne_top (OuterMeasureClass.measure_mono _ ball_subset)
  dsimp only
  rw [div_le_div_iff₀ (by exact_mod_cast v0₂) v0₃]
  apply le_of_le_of_eq <| (mul_le_mul_iff_right₀ hc).2 <|
    DoublingMeasure.volume_real_ball_two_le_same_repeat' s x n
  simp_rw [defaultA, ← mul_assoc, mul_comm c]
  rw_mod_cast [← pow_mul]
  congr
  ring

private lemma div_vol_le' {x y : X} {c : ℝ≥0∞} (hxy : dist x y ≥ D ^ (s - 1) / 4) (n : ℕ) :
    c / vol x y ≤ (2 ^ ((2 + n) * a + 𝕔 * a ^ 3)) * c / volume (ball x (2 ^ n * D ^ s)) := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_div_right_comm]
  apply mul_le_mul_left
  rw [ENNReal.inv_le_iff_inv_le, ENNReal.inv_div (by left; finiteness) (by right; positivity)]
  unfold vol
  apply le_trans _ <| measure_mono <| ball_subset_ball <| hxy
  rw [ENNReal.div_le_iff_le_mul (by left; positivity) (by left; finiteness),
    show (2 : ℝ≥0∞) ^ ((2 + n) * a + 𝕔 * a ^ 3) = (2 ^ a) ^ (2 + n + 𝕔 * a ^ 2) by ring]
  nth_rw 2 [mul_comm]
  simpa using DoublingMeasure.volume_ball_two_le_same_repeat' s x n

-- Useful special case of `div_vol_le`
private lemma div_vol_le₀ {x y : X} {c : ℝ≥0∞} (hK : Ks s x y ≠ 0) :
    c / vol x y ≤ (2 ^ (2 * a + 𝕔 * a ^ 3)) * c / volume (ball x (D ^ s)) := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_div_right_comm]
  apply mul_le_mul_left
  rw [ENNReal.inv_le_iff_inv_le, ENNReal.inv_div (by left; finiteness) (by right; positivity)]
  unfold vol
  apply le_trans _ <| measure_mono <| ball_subset_ball <| dist_mem_Icc_of_Ks_ne_zero hK |>.1
  rw [ENNReal.div_le_iff_le_mul (by left; positivity) (by left; finiteness), mul_comm,
    show (2 : ℝ≥0∞) ^ (2 * a + 𝕔 * a ^ 3) = (2 ^ a) ^ (2 + 𝕔 * a ^ 2) by ring]
  simpa using DoublingMeasure.volume_ball_two_le_same_repeat' s x 0

-- preferably use `enorm_K_le`
private lemma norm_K_le {s : ℤ} {x y : X} (n : ℕ) (hxy : dist x y ≥ D ^ (s - 1) / 4) :
    ‖K x y‖ ≤ 2 ^ ((2 + n) * a + (𝕔 + 1) * a ^ 3) / volume.real (ball x (2 ^ n * D ^ s)) := by
  apply le_trans <| norm_K_le_vol_inv x y
  unfold C_K
  apply le_trans (div_vol_le (by norm_cast; positivity) hxy n)
  gcongr
  exact_mod_cast le_of_eq (by ring)

lemma enorm_K_le {s : ℤ} {x y : X} (n : ℕ) (hxy : dist x y ≥ D ^ (s - 1) / 4) :
    ‖K x y‖ₑ ≤ 2 ^ ((2 + n) * a + (𝕔 + 1) * a ^ 3) / volume (ball x (2 ^ n * D ^ s)) := by
  apply le_trans <| enorm_K_le_vol_inv x y
  unfold C_K
  apply le_trans (div_vol_le' hxy n)
  gcongr
  exact_mod_cast le_of_eq (by ring)

/-- Lemma 2.1.3 part 2 (Real version). Prefer `enorm_Ks_le` -/
private lemma norm_Ks_le {s : ℤ} {x y : X} :
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
  · exact abs_ψ_le_one D _

/-- Lemma 2.1.3 part 2, equation (2.1.3) -/
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
  gcongr
  apply le_trans <| enorm_K_le 0 (mem_Icc.1 (dist_mem_Icc_of_Ks_ne_zero hK)).1
  rw [pow_zero, one_mul]; norm_cast; rw [add_zero, C2_1_3]; gcongr; norm_cast
  rw [show (𝕔 + 2) * a ^ 3 = a ^ 2 * a + (𝕔 + 1) * a ^ 3 by ring]
  gcongr; exacts [one_le_two, by nlinarith [four_le_a X]]

/-- `Ks` is bounded uniformly in `x`, `y` assuming `x` is in a fixed closed ball. -/
private lemma norm_Ks_le_of_dist_le {x y x₀ : X} {r₀ : ℝ} (hr₀ : 0 < r₀) (hx : dist x x₀ ≤ r₀) (s : ℤ) :
    ‖Ks s x y‖ ≤ C2_1_3 a * (As (defaultA a) (2 * r₀ / D ^ s)) / volume.real (ball x₀ r₀) := by
  let C := As (defaultA a) (2 * r₀ / D ^ s)
  have : 0 < C := As_pos (volume : Measure X) (2 * r₀ / D ^ s)
  have : 0 < volume.real (ball x₀ r₀) := measure_ball_pos_real _ _ hr₀
  suffices h : C⁻¹ * volume.real (ball x₀ r₀) ≤ volume.real (ball x (D ^ s)) by
    apply norm_Ks_le.trans
    calc
      _ ≤ C2_1_3 a / (C⁻¹ * volume.real (ball x₀ r₀)) := by gcongr
      _ = _ := by unfold defaultA defaultD C; simp; field
  have : volume.real (ball x (2*r₀)) ≤ C * volume.real (ball x (D^s)) := by
    have : (0:ℝ) < D := realD_pos _
    refine measureReal_ball_le_same x (by positivity) ?_
    apply le_of_eq; field_simp
  calc
    _ ≤ C⁻¹ * volume.real (ball x (2 * r₀)) := by
      gcongr; exacts [measure_ball_ne_top, ball_subset_ball_of_le (by linarith)]
    _ ≤ C⁻¹ * (C * volume.real (ball x (D ^ s))) := by gcongr
    _ = _ := by simp [ne_of_gt ‹0 < C›]

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
private lemma enorm_ψ_sub_ψ_le_two {r s : ℝ} : ‖ψ r - ψ s‖ₑ ≤ 2 := by
  rw [show 2 = ‖(2 : ℝ)‖ₑ by rw [Real.enorm_eq_ofReal zero_le_two]; simp,
    enorm_le_iff_norm_le, Real.norm_ofNat]
  exact norm_sub_le _ _ |>.trans <|
    add_le_add (abs_ψ_le_one D r) (abs_ψ_le_one D s) |>.trans_eq one_add_one_eq_two

-- Needed to prove `enorm_Ks_sub_Ks_le`
include K in
private lemma ψ_ineq {x y y' : X} :
    ‖ψ (D ^ (-s) * dist x y) - ψ (D ^ (-s) * dist x y')‖ₑ ≤
    4 * D * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  by_cases! h : edist y y' / D ^ s ≥ 1    -- If `dist y y'` is large, then the RHS is large while
  · apply le_trans enorm_ψ_sub_ψ_le_two  -- the LHS remains bounded.
    rw [← mul_one 2]
    gcongr
    · norm_cast; linarith [defaultD_pos a]
    · apply ENNReal.one_le_rpow h <| inv_pos_of_pos <| Nat.cast_pos.mpr (by linarith [four_le_a X])
  -- If `dist y y'` is small, then `(dist y y') ^ (a : ℝ)⁻¹` is comparable with `dist y y'`,
  -- so the Lipschitz bound for `ψ` is enough to finish the proof.
  have D1 : 1 ≤ D := by exact_mod_cast one_le_realD (a := a)
  rw [← edist_eq_enorm_sub]
  apply le_trans <| lipschitzWith_ψ D1 _ _
  norm_cast
  gcongr
  simp_rw [zpow_neg, ← smul_eq_mul, edist_smul₀, ENNReal.smul_def, ← enorm_eq_nnnorm, smul_eq_mul]
  calc _
    _ ≤ ‖((D : ℝ) ^ s)⁻¹‖ₑ * edist y y' := by
      apply mul_le_mul_right
      rw [edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)]
      exact dist_dist_dist_le_right ..
    _ = (edist y y' / D ^ s) ^ (1 : ℝ) := by
      rw [ENNReal.rpow_one, ENNReal.div_eq_inv_mul, Real.enorm_of_nonneg, ENNReal.ofReal_inv_of_pos,
        ENNReal.ofReal_zpow, ENNReal.ofReal_natCast]
      all_goals positivity
    _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_ge h.le (Nat.cast_inv_le_one a)

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
    rw [Real.rpow_le_rpow_left_iff Nat.one_lt_ofNat,
      inv_le_inv₀ (by exact_mod_cast a_pos X) (by linarith)]
    norm_cast
    exact le_of_add_le_right (four_le_a X)
  · exact le_of_eq D_pow_a_inv

/-
The proof of `norm_Ks_sub_Ks_le` is divided into two cases `norm_Ks_sub_Ks_le_y'close` and
`norm_Ks_sub_Ks_le_y'far`, depending if `2 * dist y y' ≤ dist x y` or `2 * dist y y' > dist x y`.

To prepare for the proof of `norm_Ks_sub_Ks_le_y'close`, we separate the main inequality into two
subgoals `_pt1` and `_pt2`.
-/

private lemma enorm_Ks_sub_Ks_le_close_pt1 {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
     (hyy' : 2 * edist y y' ≤ edist x y) : ‖K x y - K x y'‖ₑ * ‖ψ (D ^ (-s) * dist x y')‖ₑ ≤
    2 ^ (1 + (𝕔 + 2) * a + (𝕔 + 1) * a ^ 3) / volume (ball x (D ^ s)) *
    (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  have D0 : (D : ℝ≥0∞) ≠ 0 := by unfold defaultD; positivity
  apply le_trans <| mul_le_mul_right (enorm_ψ_le_one D _) _
  rw [mul_one]
  have : 2 * dist y y' ≤ dist x y := by
    simp_rw [dist_edist, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
    apply ENNReal.toReal_le_toReal _ _ |>.mpr hyy' <;> finiteness
  apply le_trans <| enorm_K_sub_le this
  calc _
    _ ≤ (edist y y' / (D ^ (s - 1) / 4)) ^ (a : ℝ)⁻¹ * (C_K a / vol x y) := by
      gcongr; exact lowerBound_edist_of_Ks_ne_zero hK
  have : (edist y y' / (D ^ (s - 1) / 4)) ^ (a : ℝ)⁻¹ =
      (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ * (2 ^ (𝕔 * a ^ 2 + 2)) ^ (a : ℝ)⁻¹ := by
    rw [← ENNReal.mul_rpow_of_ne_top ?hx (by finiteness)]
    case hx => finiteness_nonterminal; exact ENNReal.zpow_pos D0 (by finiteness) _ |>.ne.symm
    simp_rw [ENNReal.div_eq_inv_mul, mul_comm, mul_assoc]
    congr
    rw [ENNReal.zpow_sub D0 (by finiteness), zpow_one, ENNReal.mul_inv (by simp) (by simp),
      ENNReal.mul_inv (by simp) (by simp), mul_comm, mul_assoc]
    congr; simp; ring
  apply le_trans <| mul_le_mul_right (div_vol_le₀ hK) _
  rw [this]
  nth_rw 2 [mul_comm]
  rw [mul_assoc, ← ENNReal.mul_comm_div]
  nth_rw 2 [ENNReal.mul_comm_div]
  nth_rw 3 [mul_comm]
  rw [← mul_assoc]
  gcongr
  -- constant manipulation
  have : (4 * D : ℝ≥0∞) ^ (a : ℝ)⁻¹ * 2 ^ (2 * a + 𝕔 * a ^ 3) * C_K a ≤
      2 ^ (1 + 𝕔 * a) * 2 ^ (2 * a + 𝕔 * a ^ 3) * 2 ^ a ^ 3 := by
    gcongr
    · have := four_D_rpow_a_inv (X := X)
      norm_cast
      rw [← ENNReal.coe_natCast, ← ENNReal.coe_rpow_of_nonneg, ← ENNReal.coe_natCast]
      · exact_mod_cast this
      · rw [inv_nonneg]
        linarith
    · unfold C_K; norm_cast
  apply le_of_eq_of_le _ <| le_of_le_of_eq this (by ring)
  rw [mul_assoc, defaultD]
  congr
  push_cast
  ring

private lemma enorm_Ks_sub_Ks_le_close_pt2 {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0) :
    ‖K x y‖ₑ * ‖(ψ (D ^ (-s) * dist x y)) - (ψ (D ^ (-s) * dist x y'))‖ₑ ≤
    2 ^ (2 + 2 * a + 𝕔 * a ^ 2 + (𝕔 + 1) * a ^ 3) / volume (ball x (D ^ s)) *
    (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  apply le_of_le_of_eq _ <| show 2 ^ (2 * a + (𝕔 + 1) * a ^ 3) /
        volume (ball x (D ^ s)) * (4 * D * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹) = _ by
    field_simp; rw [← mul_assoc, ← ENNReal.mul_div_right_comm]; congr; simp; ring
  apply mul_le_mul' _ ψ_ineq
  apply le_trans <| enorm_K_le_vol_inv x y
  apply le_of_le_of_eq <| div_vol_le₀ hK
  rw_mod_cast [C_K, ← pow_add, show 2 * a + 𝕔 * a ^ 3 + a ^ 3 = 2 * a + (𝕔 + 1) * a ^ 3 by ring]

-- Second case of `norm_Ks_sub_Ks_le` in blueprint
private lemma enorm_Ks_sub_Ks_le_close {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
    (h : 2 * edist y y' ≤ edist x y) : ‖Ks s x y - Ks s x y'‖ₑ ≤
    D2_1_3 a / volume (ball x (D ^ s)) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  unfold Ks
  apply le_of_eq_of_le <| show _ = ‖(K x y - K x y') * ψ (D ^ (-s) * dist x y') +
          K x y * (ψ (D ^ (-s) * dist x y) - ψ (D ^ (-s) * dist x y'))‖ₑ by congr; ring
  apply le_trans <| enorm_add_le _ _
  simp_rw [enorm_mul, ← Complex.ofReal_sub]
  nth_rw 2 [← enorm_norm]; nth_rw 4 [← enorm_norm]
  simp_rw [norm_real, enorm_norm]
  apply le_trans <| add_le_add (enorm_Ks_sub_Ks_le_close_pt1 hK h)
    (enorm_Ks_sub_Ks_le_close_pt2 hK (y' := y'))
  rw [← add_mul, ← ENNReal.add_div]
  gcongr
  -- constant manipulation
  have _ := four_le_a X; have _ := seven_le_c
  unfold D2_1_3
  norm_cast
  trans 2 ^ (2 + 2 * a + 𝕔 * a ^ 2 + (𝕔 + 1) * a ^ 3 + 1)
  · nth_rw 4 [pow_succ]
    rw [mul_two, add_le_add_iff_right, Nat.pow_le_pow_iff_right (by simp)]
    ring_nf
    gcongr <;> simp [Nat.le_pow]
  apply Nat.pow_le_pow_right (by simp)
  trans a ^ 3 + 𝕔 / 4 * a ^ 3 + (𝕔 + 1 ) * a ^ 3
  · rw [add_comm]
    simp_rw[← add_assoc, Nat.reduceAdd, add_le_add_iff_right]
    calc _
      _ = (3 + 2 * a + 3 * a ^ 2) + (𝕔 - 3) * a ^ 2 := by
        conv_rhs => rw [add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (by linarith)]
    apply add_le_add (by nlinarith)
    trans (𝕔 / 4 * 4) * a ^ 2
    · rw [Nat.div_mul_self_eq_mod_sub_self]; gcongr; rw [← Nat.lt_succ_iff]; simp [Nat.mod_lt]
    rw [mul_assoc]; gcongr; nlinarith
  linarith

-- First case of `norm_Ks_sub_Ks_le` in blueprint
private lemma enorm_Ks_sub_Ks_le_far {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0)
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
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← ENNReal.zpow_neg]
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
  -- only `𝕔` and `a` terms
  have _ := four_le_a X
  have _ := seven_le_c
  rw [← mul_le_mul_iff_of_pos_right (a := (a : ℝ)) (by positivity)]
  ring_nf
  rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  norm_cast
  ring_nf
  apply le_of_eq_of_le <| show _ = 𝕔 * a ^ 4 + a ^ 4 * 2 + (3 + a + 𝕔 * a ^ 2) by ring
  gcongr
  calc _
    _ ≤ 2 * a ^ 2 * 𝕔 := by nlinarith
    _ ≤ (2 * a ^ 2) * (2 * a * (𝕔 / 4)) := by
      gcongr; rw [mul_assoc]
      apply le_trans (b := (4 + 4) * (𝕔 / 4)) (by lia) (by rw [← mul_assoc, two_mul]; gcongr)
    _ = 4 * a ^ 3 * (𝕔 / 4) := by ring
    _ ≤ a * a ^ 3 * (𝕔 / 4) := by gcongr
  linarith

lemma enorm_Ks_sub_Ks_le_of_nonzero {s : ℤ} {x y y' : X} (hK : Ks s x y ≠ 0) :
    ‖Ks s x y - Ks s x y'‖ₑ ≤
      D2_1_3 a / volume (ball x (D ^ s)) * (edist y y' / D ^ s) ^ (a : ℝ)⁻¹ := by
  by_cases h : 2 * edist y y' ≤ edist x y
  · exact enorm_Ks_sub_Ks_le_close hK h
  · exact enorm_Ks_sub_Ks_le_far hK h

/-- Lemma 2.1.3 part 3, equation (2.1.4) -/
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

@[fun_prop]
lemma aestronglyMeasurable_Ks {s : ℤ} : AEStronglyMeasurable (fun x : X × X ↦ Ks s x.1 x.2) :=
  measurable_Ks.aestronglyMeasurable

/-- The function `y ↦ Ks s x y` is integrable. -/
lemma integrable_Ks_x {s : ℤ} {x : X} (hD : 1 < (D : ℝ)) : Integrable (Ks s x) := by
  let r := D ^ s * ((D : ℝ)⁻¹ * (4 : ℝ)⁻¹)
  have hr : 0 < r := by positivity
  rw [← integrableOn_iff_integrable_of_support_subset (s := (ball x r)ᶜ)]
  · refine integrableOn_K_mul ?_ x hr (subset_refl _)
    apply Continuous.integrable_of_hasCompactSupport
    · unfold «ψ»; fun_prop
    · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (D ^ s / 2))
      intro y hy
      rw [mem_support, ne_eq, ofReal_eq_zero, ← ne_eq, ← mem_support, support_ψ (one_lt_realD X)] at hy
      replace hy := hy.2.le
      rw [zpow_neg, mul_comm, ← div_eq_mul_inv, div_le_iff₀ (zpow_realD_pos s)] at hy
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
  rw [psi_eq_zero_iff (one_lt_realD (X := X)) (dist_pos.mpr hxy),
    mem_nonzeroS_iff (one_lt_realD (X := X)) (dist_pos.mpr hxy)]
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
  rw [psi_eq_zero_iff (one_lt_realD (X := X)) (dist_pos.mpr hxy),
    mem_nonzeroS_iff (one_lt_realD (X := X)) (dist_pos.mpr hxy)]
  simp only [mem_Ioo, not_and_or, not_lt]
  right
  rw [zpow_neg, le_inv_mul_iff₀ (defaultD_pow_pos a s)]
  exact h

end MetricSpace
