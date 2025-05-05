import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


/-!
# Power functions `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.
* `x` and `y` are both numbers from `[0, +∞]`.

We also prove basic properties of these functions.
-/

noncomputable section

open Real ENNReal ComplexConjugate Finset Function Set
open scoped NNReal

namespace ENNReal

/-- The real power function `x ^ y` on extended nonnegative reals, defined for `x y : ℝ≥0∞`
as the restriction of the real power function if `0 < x < ∞`, and with the natural values
for `0` and `∞`:
* `0 ^ x = 0` for `x > 0` and `1` for `x = 0`
* `∞ ^ x = 1 / 0 ^ x`
* `x ^ ∞ = 0, 1, ∞` depending on whether `x < 1`, `x = 1`, or `x > 1`. -/
noncomputable def epow : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞
  | x, some y => x ^ y.toReal
  | x, none   => if x < 1 then 0 else if x = 1 then 1 else ∞

noncomputable instance : Pow ℝ≥0∞ ℝ≥0∞ := ⟨epow⟩

@[simp]
theorem epow_eq_pow {x y : ℝ≥0∞} : epow x y = x ^ y := rfl

@[simp, norm_cast]
theorem epow_coe {x : ℝ≥0∞} {y : ℝ≥0} : x ^ (y : ℝ≥0∞) = x ^ (y : ℝ) := by rfl

@[simp]
theorem epow_ofReal {x : ℝ≥0∞} {y : ℝ} (hy : 0 ≤ y) :
    x ^ ENNReal.ofReal y = x ^ y := by simp [ENNReal.ofReal, hy]

@[simp]
theorem rpow_toReal {x y : ℝ≥0∞} (hy : y ≠ ∞) :
    x ^ y.toReal = x ^ y := by
  cases y with
  | top   => contradiction
  | coe y => simp

theorem epow_top_def {x : ℝ≥0∞} : x ^ ∞ = if x < 1 then 0 else if x = 1 then 1 else ∞ := by rfl

@[simp]
theorem epow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ≥0∞) = 1 := by
  simpa using epow_coe (y := 0)

theorem top_epow_def {y : ℝ≥0∞} : (∞ : ℝ≥0∞) ^ y = if y ≠ 0 then ∞ else 1 := by
  cases y with
  | top   => rfl
  | coe y =>
    simp only [epow_coe, top_rpow_def, NNReal.coe_pos, NNReal.coe_eq_zero, ne_eq, coe_eq_zero,
      ite_not]
    split_ifs <;> [simp_all; rfl; rfl; simp_all]

@[simp]
theorem top_epow_of_pos {y : ℝ≥0∞} (h : y ≠ 0) : (∞ : ℝ≥0∞) ^ y = ∞ := by simp [top_epow_def, h]

theorem zero_epow_def (y : ℝ≥0∞) : (0 : ℝ≥0∞) ^ y = if y ≠ 0 then 0 else 1 := by
  cases y with
  | top   => simp [epow_top_def]
  | coe y =>
    simp only [epow_coe, zero_rpow_def, NNReal.coe_pos, NNReal.coe_eq_zero, ne_eq, coe_eq_zero,
      ite_not]
    split_ifs <;> [simp_all; rfl; rfl; simp_all]

@[simp]
theorem zero_epow_of_pos {y : ℝ≥0∞} (h : y ≠ 0) : (0 : ℝ≥0∞) ^ y = 0 := by
  simp [zero_epow_def, h]

@[simp]
theorem zero_epow_mul_self (y : ℝ≥0∞) : (0 : ℝ≥0∞) ^ y * (0 : ℝ≥0∞) ^ y = (0 : ℝ≥0∞) ^ y := by
  rw [zero_epow_def]
  split_ifs <;> norm_num

@[simp]
theorem epow_one (x : ℝ≥0∞) : x ^ (1 : ℝ≥0∞) = x := by
  simpa using epow_coe (y := 1)

@[simp]
theorem one_epow (y : ℝ≥0∞) : (1 : ℝ≥0∞) ^ y = 1 := by
  cases y with
  | top   => simp [epow_top_def]
  | coe y => simp

@[simp]
theorem epow_eq_zero_iff {x y : ℝ≥0∞} :
    x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 ∨ x < 1 ∧ y = ∞ := by
  cases y with
  | top   => simp +contextual [epow_top_def, apply_ite (f := (· = (0 : ℝ≥0∞)))]
  | coe y => simp [pos_iff_ne_zero]

lemma epow_eq_zero_iff_of_ne {x y : ℝ≥0∞} (h1y : y ≠ 0) (h2y : y ≠ ∞) : x ^ y = 0 ↔ x = 0 := by
  simp [h1y, h2y]

@[simp]
theorem epow_eq_top_iff {x y : ℝ≥0∞} : x ^ y = ∞ ↔ x = ∞ ∧ y ≠ 0 ∨ 1 < x ∧ y = ∞ := by
  cases y with
  | top => simp +contextual [epow_top_def, apply_ite (f := (· = ∞)), or_iff_right_of_imp,
      lt_iff_le_and_ne, eq_comm]
  | coe y => simp [pos_iff_ne_zero]

lemma epow_lt_top {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) : x ^ y < ∞ := by
  simp [lt_top_iff_ne_top, hx, hy]

theorem epow_add {x y z : ℝ≥0∞} (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  cases y with
  | top   =>
    simp [epow_top_def]; split_ifs <;> simp [*]
  | coe y =>
    cases z with
    | top   =>
      simp [epow_top_def]; split_ifs <;> simp [*]
    | coe z =>
      simp [← coe_add, rpow_add_of_nonneg]

theorem epow_sub {x y z : ℝ≥0∞} (hx : x ≠ 0) (h2x : x ≠ ∞) (h : z ≤ y) (hz : z ≠ ∞) :
    x ^ (y - z) = x ^ y / x ^ z := by
  rw [ENNReal.eq_div_iff, ← epow_add hx] <;> simp [*]

theorem epow_mul {x y z : ℝ≥0∞} (h1 : y = ⊤ → z ≠ 0) (h2 : z = ⊤ → y ≠ 0) :
    x ^ (y * z) = (x ^ y) ^ z := by
  cases y with
  | top   =>
    simp [epow_top_def]; split_ifs <;> simp [*] <;> right <;> order
  | coe y =>
    cases z with
    | top   =>
      simp [epow_top_def]; split_ifs <;> simp_all
    | coe z =>
      sorry -- simp [← coe_add, rpow_add_of_nonneg]

@[simp, norm_cast]
theorem epow_natCast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ≥0∞) = x ^ n := by
  simpa using epow_coe (y := n)

@[simp]
lemma epow_ofNat (x : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (OfNat.ofNat n) :=
  epow_natCast x n

theorem epow_two (x : ℝ≥0∞) : x ^ (2 : ℝ≥0∞) = x ^ 2 := epow_ofNat x 2

theorem mul_epow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ∞ ∨ x = ∞ ∧ y = 0) ∧ z < 0 then ∞ else x ^ z * y ^ z := by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_lt
  wlog hxy : x ≤ y
  · convert this y x z hz (le_of_not_le hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> rcases hz with hz | hz <;> simp [*, hz.not_lt]
  rcases eq_or_ne y 0 with (rfl | hy0)
  · exact (hx0 (bot_unique hxy)).elim
  induction x
  · rcases hz with hz | hz <;> simp [hz, top_unique hxy]
  induction y
  · rw [ne_eq, coe_eq_zero] at hx0
    rcases hz with hz | hz <;> simp [*]
  simp only [*, if_false]
  norm_cast at *
  rw [← coe_epow_of_ne_zero (mul_ne_zero hx0 hy0), NNReal.mul_epow]
  norm_cast

theorem mul_epow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_epow_eq_ite]

@[norm_cast]
theorem coe_mul_epow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = (x : ℝ≥0∞) ^ z * (y : ℝ≥0∞) ^ z :=
  mul_epow_of_ne_top coe_ne_top coe_ne_top z

theorem prod_coe_epow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i ∈ s, (f i : ℝ≥0∞) ^ r = ((∏ i ∈ s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_epow, coe_mul]

theorem mul_epow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_epow_eq_ite]

theorem mul_epow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_lt, mul_epow_eq_ite]

theorem prod_epow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_epow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_ne_top h2f

theorem prod_epow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← mul_epow_of_nonneg _ _ hr]

theorem inv_epow (x : ℝ≥0∞) (y : ℝ≥0∞) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [epow_zero, inv_one]
  replace hy := hy.lt_or_lt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ∞ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_epow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0, ENNReal.inv_mul_cancel h0 h_top,
    one_epow]

theorem div_epow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_epow_of_nonneg _ _ hz, inv_epow, div_eq_mul_inv]

theorem strictMono_epow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z := by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_epow_of_pos h, ← coe_epow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [← coe_epow_of_nonneg _ h.le, NNReal.epow_lt_epow (coe_lt_coe.1 hxy) h, coe_lt_coe]

theorem monotone_epow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [epow_zero, monotone_const]) fun h0 =>
    (strictMono_epow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0∞ => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0∞ => x ^ (1 / y)`. -/
@[simps! apply]
def orderIsoepow (y : ℝ≥0∞) (hy : y ≠ 0) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_epow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← epow_mul, one_div_mul_cancel hy.ne.symm, epow_one]

theorem orderIsoepow_symm_apply (y : ℝ≥0∞) (hy : y ≠ 0) :
    (orderIsoepow y hy).symm = orderIsoepow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoepow, one_div_one_div]
  rfl

@[gcongr] theorem epow_le_epow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_epow_of_nonneg h₂ h₁

@[gcongr] theorem epow_lt_epow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_epow_of_pos h₂ h₁

theorem epow_le_epow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_epow_of_pos hz).le_iff_le

theorem epow_lt_epow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_epow_of_pos hz).lt_iff_lt

theorem le_epow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  nth_rw 1 [← epow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [epow_mul, @epow_le_epow_iff _ _ z⁻¹ (by simp [hz])]

theorem epow_inv_lt_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_epow_inv_iff hz]

theorem lt_epow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  nth_rw 1 [← epow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [epow_mul, @epow_lt_epow_iff _ _ z⁻¹ (by simp [hz])]

theorem epow_inv_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  nth_rw 1 [← ENNReal.epow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.epow_mul, ENNReal.epow_le_epow_iff (inv_pos.2 hz)]

theorem epow_lt_epow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ∞) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_epow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
    NNReal.epow_lt_epow_of_exponent_lt hx hyz]

@[gcongr] theorem epow_le_epow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_epow_of_neg, top_epow_of_pos, le_refl] <;>
    linarith
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [← coe_epow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.epow_le_epow_of_exponent_le hx hyz]

theorem epow_lt_epow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_epow_of_ne_zero (ne_of_gt hx0), NNReal.epow_lt_epow_of_exponent_gt hx0 hx1 hyz]

theorem epow_le_epow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_epow_of_neg, zero_epow_of_pos, le_refl] <;>
    linarith
  · rw [coe_le_one_iff] at hx1
    simp [← coe_epow_of_ne_zero h,
      NNReal.epow_le_epow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]

theorem epow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  nth_rw 2 [← ENNReal.epow_one x]
  exact ENNReal.epow_le_epow_of_exponent_ge hx h_one_le

theorem le_epow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z := by
  nth_rw 1 [← ENNReal.epow_one x]
  exact ENNReal.epow_le_epow_of_exponent_le hx h_one_le

theorem epow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_epow_of_pos hp_pos]
    exact epow_lt_epow hx_pos hp_pos

theorem epow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ∞) : 0 < x ^ p := by
  rcases lt_or_le 0 p with hp_pos | hp_nonpos
  · exact epow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, epow_neg, ENNReal.inv_pos]
    exact epow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top

theorem epow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_epow_of_nonneg _ (le_of_lt hz), NNReal.epow_lt_one hx hz]

theorem epow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_epow_of_nonneg _ hz, NNReal.epow_le_one hx hz]

theorem epow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  cases x
  · simp [top_epow_of_neg hz, zero_lt_one]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [← coe_epow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.epow_lt_one_of_one_lt_of_neg hx hz]

theorem epow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 := by
  cases x
  · simp [top_epow_of_neg hz, zero_lt_one]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [← coe_epow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.epow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]

theorem one_lt_epow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  cases x
  · simp [top_epow_of_pos hz]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [← coe_epow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_epow hx hz]

theorem one_le_epow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z := by
  cases x
  · simp [top_epow_of_pos hz]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [← coe_epow_of_nonneg _ (le_of_lt hz), NNReal.one_le_epow hx (le_of_lt hz)]

theorem one_lt_epow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_epow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_epow_of_pos_of_lt_one_of_neg hx1 hx2 hz]

theorem one_le_epow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_epow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_epow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]

@[simp] lemma toNNReal_epow (x : ℝ≥0∞) (z : ℝ) : (x ^ z).toNNReal = x.toNNReal ^ z := by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x with
    | top   => simp [H, ne_of_lt]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, H, ne_of_lt]
      · simp [← coe_epow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_epow_of_nonneg _ (le_of_lt H)]

theorem toReal_epow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal, ENNReal.toReal, ← NNReal.coe_epow, ENNReal.toNNReal_epow]

theorem ofReal_epow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  simp_rw [ENNReal.ofReal]
  rw [← coe_epow_of_ne_zero, coe_inj, Real.toNNReal_epow_of_nonneg hx_pos.le]
  simp [hx_pos]

theorem ofReal_epow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_epow_of_pos (hx_nonneg.lt_of_ne hx0.symm)

@[simp] lemma epow_epow_inv {y : ℝ≥0∞} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y) ^ y⁻¹ = x := by
  rw [← epow_mul, mul_inv_cancel₀ hy, epow_one]

@[simp] lemma epow_inv_epow {y : ℝ≥0∞} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y⁻¹) ^ y = x := by
  rw [← epow_mul, inv_mul_cancel₀ hy, epow_one]

lemma pow_epow_inv_natCast {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0∞) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  rw [← epow_natCast, ← epow_mul, mul_inv_cancel₀ (by positivity), epow_one]

lemma epow_inv_natCast_pow {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0∞) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  rw [← epow_natCast, ← epow_mul, inv_mul_cancel₀ (by positivity), epow_one]

lemma epow_natCast_mul (x : ℝ≥0∞) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [epow_mul, epow_natCast]

lemma epow_mul_natCast (x : ℝ≥0∞) (y : ℝ≥0∞) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [epow_mul, epow_natCast]

lemma epow_intCast_mul (x : ℝ≥0∞) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [epow_mul, epow_intCast]

lemma epow_mul_intCast (x : ℝ≥0∞) (y : ℝ≥0∞) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [epow_mul, epow_intCast]

lemma epow_left_injective {x : ℝ} (hx : x ≠ 0) : Injective fun y : ℝ≥0∞ ↦ y ^ x :=
  HasLeftInverse.injective ⟨fun y ↦ y ^ x⁻¹, epow_epow_inv hx⟩

theorem epow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0∞ => y ^ x :=
  HasRightInverse.surjective ⟨fun y ↦ y ^ x⁻¹, epow_inv_epow hx⟩

theorem epow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0∞ => y ^ x :=
  ⟨epow_left_injective hx, epow_left_surjective hx⟩

lemma _root_.Real.enorm_epow_of_nonneg {x y : ℝ≥0∞} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x ^ y‖ₑ = ‖x‖ₑ ^ y := by simp [enorm, nnnorm_epow_of_nonneg hx, coe_epow_of_nonneg _ hy]

end ENNReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
-- section Tactics

-- /-!
-- ## Tactic extensions for powers on `ℝ≥0` and `ℝ≥0∞`
-- -/


-- namespace NormNum

-- theorem nnepow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, NNReal.epow_natCast]

-- theorem nnepow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, NNReal.epow_neg, NNReal.epow_natCast]

-- theorem ennepow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, ENNReal.epow_natCast]

-- theorem ennepow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, ENNReal.epow_neg, ENNReal.epow_natCast]

-- /-- Evaluate `NNReal.epow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_nnepow : expr → expr → tactic (expr × expr) :=
--   prove_epow' `` nnepow_pos `` nnepow_neg `` NNReal.epow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))

-- /-- Evaluate `ENNReal.epow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_ennepow : expr → expr → tactic (expr × expr) :=
--   prove_epow' `` ennepow_pos `` ennepow_neg `` ENNReal.epow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))

-- /-- Evaluates expressions of the form `epow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_nnepow_ennepow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnepow a b
--   | q(NNReal.epow $(a) $(b)) => b.to_int >> prove_nnepow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennepow a b
--   | q(ENNReal.epow $(a) $(b)) => b.to_int >> prove_ennepow a b
--   | _ => tactic.failed

-- end NormNum

-- namespace Tactic

-- namespace Positivity

-- private theorem nnepow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
--   NNReal.epow_pos ha

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals.
-- -/
-- unsafe def prove_nnepow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   match strictness_a with
--     | positive p => positive <$> mk_app `` nnepow_pos [p, b]
--     | _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0`
-- private theorem ennepow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
--   ENNReal.epow_pos_of_nonneg ha hb.le

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of extended
-- nonnegative reals. -/
-- unsafe def prove_ennepow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   let strictness_b ← core b
--   match strictness_a, strictness_b with
--     | positive pa, positive pb => positive <$> mk_app `` ennepow_pos [pa, pb]
--     | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.epow_pos_of_nonneg [pa, pb]
--     | _, _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0∞`
-- end Positivity

-- open Positivity

-- /-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
-- the base is nonnegative and positive when the base is positive. -/
-- @[positivity]
-- unsafe def positivity_nnepow_ennepow : expr → tactic strictness
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => prove_nnepow a b
--   | q(NNReal.epow $(a) $(b)) => prove_nnepow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => prove_ennepow a b
--   | q(ENNReal.epow $(a) $(b)) => prove_ennepow a b
--   | _ => failed

-- end Tactic

-- end Tactics
