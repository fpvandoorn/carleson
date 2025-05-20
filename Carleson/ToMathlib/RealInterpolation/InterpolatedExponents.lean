import Carleson.ToMathlib.ENorm

/-!
# Results about working with (interpolated) exponents

This files contains convenience results for working with interpolated exponents,
as well as results about a particular choice of exponent that we will use for the proof
of the real interpolation theorem.
-/
noncomputable section

open ENNReal Real Set MeasureTheory

-- Note (F): can we make `t : ℝ≥0∞` for a large part of the proof?
variable {p₀ q₀ p₁ q₁ p q : ℝ≥0∞} {t : ℝ}

/-! ## Convenience results for working with (interpolated) exponents -/
namespace ComputationsInterpolatedExponents

-- unused
lemma ofReal_mem_Ioo_0_1 (h : t ∈ Ioo 0 1) : ENNReal.ofReal t ∈ Ioo 0 1 :=
  ⟨ofReal_pos.mpr h.1, ofReal_lt_one.mpr h.2⟩

lemma ENNReal_preservation_positivity₀ (ht : t ∈ Ioo 0 1) (hpq : p ≠ ⊤ ∨ q ≠ ⊤) :
    0 < (1 - ENNReal.ofReal t) * p⁻¹ + ENNReal.ofReal t * q⁻¹ := by
  have t_mem : ENNReal.ofReal t ∈ Ioo 0 1 :=
    ⟨ofReal_pos.mpr ht.1, ENNReal.ofReal_one ▸ (ofReal_lt_ofReal_iff zero_lt_one).mpr ht.2⟩
  obtain dir|dir := hpq
  · exact Left.add_pos_of_pos_of_nonneg (mul_pos ((tsub_pos_of_lt t_mem.2).ne')
      (ENNReal.inv_ne_zero.mpr dir)) (zero_le _)
  · exact Right.add_pos_of_nonneg_of_pos (zero_le _)
      (mul_pos ((ofReal_pos.mpr ht.1).ne') (ENNReal.inv_ne_zero.mpr dir))

lemma ENNReal_preservation_positivity (ht : t ∈ Ioo 0 1) (hpq : p ≠ q) :
    0 < (1 - ENNReal.ofReal t) * p⁻¹ + ENNReal.ofReal t * q⁻¹ := by
  apply ENNReal_preservation_positivity₀ ht
  cases (lt_or_gt_of_ne hpq) <;> exact Ne.ne_or_ne ⊤ hpq

lemma ENNReal_preservation_positivity' (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 0 < p := by
  rw [← inv_inv p, hp]
  simp [ENNReal.mul_eq_top, sub_eq_zero, hp₀.ne', hp₁.ne']

lemma interp_exp_ne_top (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ≠ ⊤ :=
  ENNReal.inv_ne_zero.mp <| hp ▸ (ENNReal_preservation_positivity ht hp₀p₁).ne'

lemma interp_exp_ne_top2 {t : ℝ≥0∞} (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p ≠ ⊤ := sorry

lemma interp_exp_ne_top' (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ≠ ⊤ :=
  ENNReal.inv_ne_zero.mp (hp ▸ (ENNReal_preservation_positivity₀ ht hp₀p₁).ne')

lemma interp_exp_eq (hp₀p₁ : p₀ = p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀ = p := by
  rw [← inv_inv (a := p), hp, ← hp₀p₁, ← add_mul,
    tsub_add_cancel_of_le <| ofReal_lt_one.mpr ht.2 |>.le, one_mul, inv_inv]

lemma interp_exp_lt_top (hp₀p₁ : p₀ ≠ p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top hp₀p₁ ht hp

lemma interp_exp_lt_top' (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top' hp₀p₁ ht hp

lemma interp_exp_between (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ∈ Ioo p₀ p₁ := by
  refine ⟨?_, ?_⟩ <;> apply ENNReal.inv_lt_inv.mp
  · rw [hp]
    have : p₀⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₀⁻¹ := by
      rw [← add_mul, tsub_add_eq_max, max_eq_left_of_lt, one_mul]
      exact ofReal_lt_one.mpr ht.2
    nth_rw 2 [this]
    gcongr
    · exact mul_ne_top (sub_ne_top top_ne_one.symm) (inv_ne_top.mpr hp₀.ne')
    · exact (ofReal_pos.mpr ht.1).ne'
    · exact coe_ne_top
  · rw [hp]
    have : p₁⁻¹ = (1 - ENNReal.ofReal t) * p₁⁻¹ + ENNReal.ofReal t * p₁⁻¹ := by
      rw [← add_mul, tsub_add_eq_max, max_eq_left_of_lt, one_mul]
      exact ofReal_lt_one.mpr ht.2
    nth_rw 1 [this]
    gcongr
    · exact mul_ne_top coe_ne_top (inv_ne_top.mpr hp₁.ne')
    · exact (tsub_pos_iff_lt.mpr (ofReal_lt_one.mpr ht.2)).ne'
    · exact coe_ne_top

lemma one_le_interp_exp_aux (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 1 ≤ p :=
  hp₀.trans_lt
    (interp_exp_between (zero_lt_one.trans_le hp₀) (zero_lt_one.trans_le hp₁) hp₀p₁ ht hp).1 |>.le

lemma switch_exponents (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p⁻¹ = (1 - ENNReal.ofReal (1 - t)) * p₁⁻¹ + ENNReal.ofReal (1 - t) * p₀⁻¹ := by
  rw [add_comm, ← ofReal_one, ← ofReal_sub, _root_.sub_sub_cancel, ofReal_sub _ ht.1.le, ofReal_one]
  · exact hp
  · exact (Ioo.one_sub_mem ht).1.le

lemma one_le_toReal {a : ℝ≥0∞} (ha₁ : 1 ≤ a) (ha₂ : a < ⊤) : 1 ≤ a.toReal :=
  toReal_mono ha₂.ne_top ha₁

lemma one_le_interp (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 1 ≤ p := by
  rcases (lt_or_gt_of_ne hp₀p₁) with p₀lt_p₁ | p₁lt_p₀
  · exact one_le_interp_exp_aux hp₀ hp₁ p₀lt_p₁ ht hp
  · exact one_le_interp_exp_aux hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)

lemma one_le_interp_toReal (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 1 ≤ p.toReal :=
  one_le_toReal (one_le_interp hp₀ hp₁ hp₀p₁ ht hp) (Ne.lt_top (interp_exp_ne_top hp₀p₁ ht hp))

lemma coe_rpow_ne_top {a : ℝ} {q : ℝ} (hq : 0 ≤ q): ENNReal.ofReal a ^ q ≠ ⊤ :=
  rpow_ne_top_of_nonneg hq coe_ne_top

-- Note this lemma can directly be applied to elements of `ℝ≥0` as well
lemma coe_rpow_ne_top' {a : ℝ} {q : ℝ} (hq : 0 < q): ENNReal.ofReal a ^ q ≠ ⊤ :=
  coe_rpow_ne_top hq.le

lemma coe_pow_pos {a : ℝ} {q : ℝ} (ha : 0 < a) : 0 < ENNReal.ofReal a ^ q :=
  ENNReal.rpow_pos (ofReal_pos.mpr ha) coe_ne_top

lemma rpow_ne_top' {a : ℝ≥0∞} {q : ℝ} (ha : a ≠ 0) (ha' : a ≠ ⊤) : a ^ q ≠ ⊤ := by
  intro h
  rcases ENNReal.rpow_eq_top_iff.mp h with ⟨a_zero, _⟩ | ⟨a_top, _⟩
  · exact (ha a_zero).elim
  · exact (ha' a_top).elim

lemma exp_toReal_pos' {q : ℝ≥0∞} (hq : q ≥ 1) (hq' : q < ⊤) : 0 < q.toReal :=
  toReal_pos (lt_of_lt_of_le zero_lt_one hq).ne' hq'.ne_top

lemma ne_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q ≠ ⊤ := hq.2.ne_top

lemma lt_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q < ⊤ := (ne_top_of_Ico hq).lt_top

lemma ne_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ ⊤ := hq.2.ne_top

lemma lt_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q < ⊤ := (ne_top_of_Ioo hq).lt_top

lemma ne_top_of_Ioc {p q r : ℝ≥0∞} (hq : q ∈ Ioc p r) (hr : r < ⊤) : q ≠ ⊤ :=
  hq.2.trans_lt hr |>.ne_top

lemma pos_of_rb_Ioc {p q r : ℝ≥0∞} (hr : q ∈ Ioc p r) : 0 < r :=
  zero_le p |>.trans_lt hr.1 |>.trans_le hr.2

lemma exp_toReal_ne_zero {q : ℝ≥0∞} (hq : q ≥ 1) (hq' : q < ⊤) : q.toReal ≠ 0 :=
  (exp_toReal_pos' hq hq').ne'

-- TODO: remove the top one?
lemma exp_toReal_ne_zero' {q : ℝ≥0∞} (hq : 0 < q) (hq' : q ≠ ⊤) : q.toReal ≠ 0 :=
  (toReal_pos hq.ne' hq').ne'

lemma exp_toReal_ne_zero_of_Ico {q p : ℝ≥0∞} (hq : q ∈ Ico 1 p) : q.toReal ≠ 0 :=
  exp_toReal_ne_zero hq.1 (lt_top_of_Ico hq)

lemma pos_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : 0 < q := pos_of_gt hq.1

lemma ne_zero_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ 0 := (pos_of_gt hq.1).ne'

lemma pos_of_Icc_1 {p q : ℝ≥0∞} (hp : p ∈ Icc 1 q) : 0 < p := lt_of_lt_of_le zero_lt_one hp.1

lemma pos_of_ge_1 {p : ℝ≥0∞} (hp : 1 ≤ p) : 0 < p := lt_of_lt_of_le zero_lt_one hp

lemma pos_rb_of_Icc_1_inh {p q : ℝ≥0∞} (hp : p ∈ Icc 1 q) : 0 < q :=
  lt_of_lt_of_le zero_lt_one (le_trans hp.1 hp.2)

lemma toReal_pos_of_Ioo {q p r : ℝ≥0∞} (hp : p ∈ Ioo q r) : 0 < p.toReal :=
  toReal_pos (ne_zero_of_lt hp.1) hp.2.ne_top

lemma toReal_ne_zero_of_Ioo {q p r : ℝ≥0∞} (hp : p ∈ Ioo q r) : p.toReal ≠ 0 :=
  toReal_ne_zero.mpr ⟨ne_zero_of_lt hp.1, hp.2.ne_top⟩

-- TODO: check which ones are actually used
lemma eq_of_rpow_eq (a b: ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) (h : a ^ c = b ^ c) : a = b := by
  rw [← ENNReal.rpow_rpow_inv hc a, ← ENNReal.rpow_rpow_inv hc b]
  exact congrFun (congrArg HPow.hPow h) c⁻¹

lemma le_of_rpow_le {a b: ℝ≥0∞} {c : ℝ} (hc : 0 < c) (h : a ^ c ≤ b ^ c) : a ≤ b := by
  rw [← ENNReal.rpow_rpow_inv hc.ne' a, ← ENNReal.rpow_rpow_inv hc.ne' b]
  exact (ENNReal.rpow_le_rpow_iff (inv_pos_of_pos hc)).mpr h

-- TODO : decide if this is wanted
-- local instance : Coe ℝ ℝ≥0∞ where
--   coe x := ENNReal.ofReal x

lemma coe_inv_exponent (hp₀ : 0 < p₀) : ENNReal.ofReal (p₀⁻¹.toReal) = p₀⁻¹ :=
  ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₀.ne')

lemma inv_of_interpolated_pos' (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 0 < p⁻¹ :=
  ENNReal.inv_pos.mpr (interp_exp_ne_top hp₀p₁ ht hp)

-- TODO: remove, this is redundant, but for now mirror the development for reals...
lemma interpolated_pos' (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹): 0 < p :=
  ENNReal_preservation_positivity' hp₀ hp₁ hp

lemma interpolated_pos'2 {t : ℝ≥0∞} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹): 0 < p := sorry

lemma exp_toReal_pos (hp₀ : 0 < p₀) (hp₀' : p₀ ≠ ⊤) : 0 < p₀.toReal :=
  toReal_pos hp₀.ne' hp₀'

lemma interp_exp_in_Ioo_zero_top (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ∈ Ioo 0 ⊤ :=
  ⟨interpolated_pos' hp₀ hp₁ hp, interp_exp_lt_top' hp₀p₁ ht hp⟩

lemma inv_toReal_pos_of_ne_top (hp₀ : 0 < p₀) (hp' : p₀ ≠ ⊤) : 0 < p₀⁻¹.toReal :=
  toReal_inv _ ▸ inv_pos_of_pos (exp_toReal_pos hp₀ hp')

lemma inv_toReal_ne_zero_of_ne_top (hp₀ : 0 < p₀) (hp' : p₀ ≠ ⊤) : p₀⁻¹.toReal ≠ 0 :=
  (inv_toReal_pos_of_ne_top hp₀ hp').ne'

lemma interp_exp_toReal_pos (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 0 < p.toReal :=
  toReal_pos (interpolated_pos' hp₀ hp₁ hp).ne' (interp_exp_ne_top hp₀p₁ ht hp)

lemma interp_exp_toReal_pos' (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) : 0 < p.toReal :=
  toReal_pos (interpolated_pos' hp₀ hp₁ hp).ne' (interp_exp_ne_top' hp₀p₁ ht hp)

lemma interp_exp_toReal_pos'2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) : 0 < p.toReal :=
  sorry

lemma interp_exp_inv_pos (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    0 < p⁻¹.toReal :=
  toReal_inv _ ▸ inv_pos_of_pos (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp)

lemma interp_exp_inv_ne_zero (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p⁻¹.toReal ≠ 0 :=
  (interp_exp_inv_pos ht hp₀ hp₁ hp₀p₁ hp).ne'

lemma preservation_interpolation (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p⁻¹.toReal = (1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal := by
  rw [← toReal_one, ← toReal_ofReal ht.1.le, ← ENNReal.toReal_sub_of_le]
  · rw [← toReal_mul, ← toReal_mul, ← toReal_add]
    · exact congrArg ENNReal.toReal hp
    · exact mul_ne_top (sub_ne_top (top_ne_one.symm)) (inv_ne_top.mpr hp₀.ne')
    · exact mul_ne_top coe_ne_top (inv_ne_top.mpr hp₁.ne')
  · exact ofReal_le_one.mpr ht.2.le
  · exact top_ne_one.symm

lemma preservation_positivity_inv_toReal (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀p₁ : p₀ ≠ p₁) :
    0 < (1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal := by
  rcases (eq_or_ne p₀ ⊤) with p₀eq_top | p₀ne_top
  · rw [p₀eq_top]
    simp only [inv_top, toReal_zero, mul_zero, zero_add]
    apply mul_pos ht.1
    rw [toReal_inv]
    refine inv_pos_of_pos (exp_toReal_pos hp₁ ?_)
    rw [p₀eq_top] at hp₀p₁
    exact hp₀p₁.symm
  · exact add_pos_of_pos_of_nonneg (mul_pos (Ioo.one_sub_mem ht).1 (toReal_inv _ ▸ inv_pos_of_pos
      (exp_toReal_pos hp₀ p₀ne_top))) (mul_nonneg ht.1.le toReal_nonneg)

lemma ne_inv_toReal_exponents (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁) :
    (p₀⁻¹.toReal ≠ p₁⁻¹.toReal) := by
  refine fun h ↦ hp₀p₁ ?_
  rw [← inv_inv p₀, ← inv_inv p₁]
  apply congrArg Inv.inv
  rw [← ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₀.ne'),
    ← ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₁.ne')]
  exact congrArg ENNReal.ofReal h

lemma ne_inv_toReal_exp_interp_exp (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
  (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    (p₀⁻¹.toReal ≠ p⁻¹.toReal) := by
  rw [preservation_interpolation ht hp₀ hp₁ hp,
    ← sub_ne_zero, _root_.sub_mul, one_mul, add_comm_sub, sub_add_eq_sub_sub, sub_self, zero_sub,
    neg_sub, ← _root_.mul_sub]
  exact mul_ne_zero ht.1.ne' (sub_ne_zero_of_ne (ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁))

lemma ne_sub_toReal_exp (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁) :
    p₁⁻¹.toReal - p₀⁻¹.toReal ≠ 0 :=
  sub_ne_zero_of_ne (ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁).symm

lemma ne_toReal_exp_interp_exp (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀.toReal ≠ p.toReal := by
  refine fun h ↦ ne_inv_toReal_exp_interp_exp ht hp₀ hp₁ hp₀p₁ hp ?_
  repeat rw [toReal_inv _]
  exact congrArg Inv.inv h

lemma ne_toReal_exp_interp_exp₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p.toReal ≠ p₁.toReal :=
  (ne_toReal_exp_interp_exp (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁)
    (switch_exponents ht hp)).symm

lemma ofReal_inv_interp_sub_exp_pos₁ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ > 0 :=
  ofReal_pos.mpr (inv_pos_of_pos (abs_sub_pos.mpr (ne_toReal_exp_interp_exp₁ ht hq₀ hq₁ hq₀q₁ hq)))

lemma ofReal_inv_interp_sub_exp_pos₀ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq₀q₁ : q₀ ≠ q₁) (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ > 0 :=
  ofReal_pos.mpr (inv_pos_of_pos (abs_sub_pos.mpr (Ne.symm
    (ne_toReal_exp_interp_exp ht hq₀ hq₁ hq₀q₁ hq))))

lemma exp_lt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p < p₀ ↔ p₁ < p₀ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun h ↦ (not_le_of_gt h (le_of_lt (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1)).elim,
      fun h ↦ (not_le_of_gt h p₀lt_p₁.le).elim⟩
  · exact ⟨fun _ ↦ p₁lt_p₀,
      fun _ ↦ (interp_exp_between hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)).2⟩

lemma exp_gt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀ < p ↔ p₀ < p₁ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun _ ↦ p₀lt_p₁, fun _ ↦ (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1⟩
  · exact ⟨fun h ↦ (not_le_of_gt h (interp_exp_between hp₁ hp₀ p₁lt_p₀
      (Ioo.one_sub_mem ht) (switch_exponents ht hp)).2.le).elim,
      fun h ↦ (not_le_of_gt h p₁lt_p₀.le).elim⟩

lemma exp_lt_exp_gt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p < p₀ ↔ p₁ < p := by
  rw [exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_gt_iff (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁)
    (switch_exponents ht hp)]

lemma exp_gt_exp_lt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀ < p ↔ p < p₁ := by
  rw [exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_lt_iff (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁)
    (switch_exponents ht hp)]

lemma exp_lt_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p < p₁ ↔ p₀ < p₁ := by
  rw [← exp_gt_exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp

lemma exp_gt_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₁ < p ↔ p₁ < p₀ := by
  rw [← exp_lt_exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp

end ComputationsInterpolatedExponents

/-! ## Results about the particular choice of exponent

    The proof of the real interpolation theorem will estimate
    `distribution (trunc f A(t)) t` and `distribution (truncCompl f A(t)) t` for a
    function `A`. The function `A` can be given a closed-form expression that works for
    _all_ cases in the real interpolation theorem, because of the computation rules available
    for elements in `ℝ≥0∞` that avoid the need for a limiting procedure, e.g. `⊤⁻¹ = 0`.

    The function `A` will be of the form `A(t) = (t / d) ^ σ` for particular choices of `d` and
    `σ`. This section contatins results about the exponents `σ`.
-/
namespace ComputationsChoiceExponent

open ENNReal Real Set ComputationsInterpolatedExponents

variable {p₀ q₀ p₁ q₁ p q : ℝ≥0∞} {t : ℝ}

def ζ (p₀ q₀ p₁ q₁ : ℝ≥0∞) (t : ℝ) : ℝ :=
  (((1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal) * ((q₁⁻¹).toReal - (q₀⁻¹).toReal)) /
  (((1 - t) * (q₀⁻¹).toReal + t * (q₁⁻¹).toReal) * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))

lemma ζ_equality₁ (ht : t ∈ Ioo 0 1) :
    ζ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal) *
    ((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal) *
    ((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal - p₀⁻¹.toReal)) := by
  unfold ζ
  rw [← mul_div_mul_right _ _ ht.1.ne', mul_assoc _ _ t, mul_assoc _ _ t]
  congr <;> ring

lemma ζ_equality₂ (ht : t ∈ Ioo 0 1) :
    ζ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal) *
    ((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal - q₁⁻¹.toReal)) /
    (((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal) *
    ((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal - p₁⁻¹.toReal)) := by
  unfold ζ
  have : - (1 - t) < 0 := neg_neg_iff_pos.mpr (sub_pos.mpr ht.2)
  rw [← mul_div_mul_right _ _ this.ne, mul_assoc _ _ (-(1 - t)), mul_assoc _ _ (-(1 - t))]
  congr <;> ring

lemma ζ_symm :
    ζ p₀ q₀ p₁ q₁ t = ζ p₁ q₁ p₀ q₀ (1 - t) := by
  unfold ζ
  rw [← mul_div_mul_right (c := - 1), mul_assoc _ _ (-1), mul_assoc _ _ (-1)]; on_goal 2 => positivity
  simp only [mul_neg, mul_one, neg_sub, _root_.sub_sub_cancel]
  nth_rewrite 1 [add_comm]; nth_rw 2 [add_comm]

set_option linter.style.multiGoal false in
set_option linter.flexible false in
lemma ζ_equality₃ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t = (p₀.toReal * (q₀.toReal - q.toReal))  / (q₀.toReal * (p₀.toReal - p.toReal)) := by
  rw [ζ_equality₁ ht, ← preservation_interpolation, ← preservation_interpolation]
  have q_pos : 0 < q := interpolated_pos' hq₀ hq₁ hq
  have p_pos : 0 < p := interpolated_pos' hp₀ hp₁ hp
  have hne : p.toReal * q.toReal * p₀.toReal * q₀.toReal > 0 :=
    mul_pos (mul_pos (mul_pos (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp)
    (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq)) (exp_toReal_pos hp₀ hp₀'))
    (exp_toReal_pos hq₀ hq₀')
  rw [← mul_div_mul_right _ _ hne.ne']
  have eq₁ : p⁻¹.toReal * (q⁻¹.toReal - q₀⁻¹.toReal) *
      (p.toReal * q.toReal * p₀.toReal * q₀.toReal) =
      p₀.toReal * (p⁻¹.toReal * p.toReal) * ((q⁻¹.toReal * q.toReal) * q₀.toReal -
      (q₀⁻¹.toReal * q₀.toReal) * q.toReal) := by ring
  have eq₂ : q⁻¹.toReal * (p⁻¹.toReal - p₀⁻¹.toReal) *
      (p.toReal * q.toReal * p₀.toReal * q₀.toReal) =
      q₀.toReal * (q⁻¹.toReal * q.toReal) * ((p⁻¹.toReal * p.toReal) * p₀.toReal -
      (p₀⁻¹.toReal * p₀.toReal) * p.toReal) := by ring
  rw [eq₁, eq₂, ← @toReal_mul q⁻¹ q, ← @toReal_mul p⁻¹ p, ← @toReal_mul p₀⁻¹ p₀,
      ← @toReal_mul q₀⁻¹ q₀]
  all_goals try assumption
  -- TODO: why can below goals not be discharged?
  repeat rw [ENNReal.inv_mul_cancel] <;> try positivity
  all_goals simp <;> try assumption
  · apply interp_exp_ne_top hq₀q₁ ht hq
  · apply interp_exp_ne_top hp₀p₁ ht hp

lemma one_sub_coe_one_sub (ht : t ∈ Ioo 0 1) :
    (1 - ENNReal.ofReal (1 - t)) = ENNReal.ofReal t := by
  have := ht.2
  rw [← ofReal_one, ← ENNReal.ofReal_sub] <;> congr
  · linarith
  · linarith

lemma coe_one_sub (ht : t ∈ Ioo 0 1) :
    ENNReal.ofReal (1 - t) = 1 - ENNReal.ofReal t := by
  rw [← ofReal_one, ← ENNReal.ofReal_sub]; exact ht.1.le

lemma ζ_equality₄ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t =
    (p₁.toReal * (q₁.toReal - q.toReal)) / (q₁.toReal * (p₁.toReal - p.toReal)) := by
  rw [ζ_symm]
  have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
  rw [ζ_equality₃ one_sub_mem] <;> try assumption
  · exact hp₀p₁.symm
  · exact hq₀q₁.symm
  · rw [hp, one_sub_coe_one_sub ht, coe_one_sub ht]; ring
  · rw [hq, one_sub_coe_one_sub ht, coe_one_sub ht]; ring

lemma ζ_equality₅ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    p₀.toReal + (ζ p₀ q₀ p₁ q₁ t)⁻¹ * (q.toReal - q₀.toReal) * (p₀.toReal / q₀.toReal) = p.toReal := by
  rw [ζ_equality₃ ht] <;> try assumption
  simp only [inv_div]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  calc
  _ = p₀.toReal - (q₀.toReal⁻¹ * q₀.toReal) * (p₀.toReal - p.toReal) * (p₀.toReal⁻¹ * p₀.toReal) *
      ((q₀.toReal - q.toReal)⁻¹ * (q₀.toReal - q.toReal)) := by ring
  _ = _ := by
    rw [inv_mul_cancel₀, inv_mul_cancel₀, inv_mul_cancel₀]
    · simp only [one_mul, mul_one, _root_.sub_sub_cancel]
    · exact sub_ne_zero_of_ne (ne_toReal_exp_interp_exp ht hq₀ hq₁ hq₀q₁ hq)
    · exact (exp_toReal_pos hp₀ hp₀').ne'
    · exact (exp_toReal_pos hq₀ hq₀').ne'

lemma ζ_equality₅2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    p₀.toReal + (ζ p₀ q₀ p₁ q₁ t.toReal)⁻¹ * (q.toReal - q₀.toReal) * (p₀.toReal / q₀.toReal) = p.toReal := by
  sorry

lemma ζ_equality₆ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    p₁.toReal + (ζ p₀ q₀ p₁ q₁ t)⁻¹ * (q.toReal - q₁.toReal) * (p₁.toReal / q₁.toReal) = p.toReal := by
  rw [ζ_symm]
  exact ζ_equality₅ (Ioo.one_sub_mem ht) hp₁ hq₁ hp₀ hq₀ hp₀p₁.symm hq₀q₁.symm
    (switch_exponents ht hp) (switch_exponents ht hq) hp₁' hq₁'

lemma ζ_equality₆2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    p₁.toReal + (ζ p₀ q₀ p₁ q₁ t.toReal)⁻¹ * (q.toReal - q₁.toReal) * (p₁.toReal / q₁.toReal) = p.toReal := by
  sorry

lemma ζ_equality₇ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ = ⊤) :
    ζ p₀ q₀ p₁ q₁ t = p₀.toReal / (p₀.toReal - p.toReal) := by
  rw [ζ_equality₁ ht, ← preservation_interpolation ht hp₀ hp₁ hp,
    ← preservation_interpolation ht hq₀ hq₁ hq, hq₀']
  simp only [inv_top, toReal_zero, sub_zero, mul_zero, zero_add]
  have obs : p₀.toReal * p.toReal * q.toReal > 0 :=
    mul_pos (mul_pos (toReal_pos hp₀.ne' hp₀') (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp))
    (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq)
  rw [← mul_div_mul_right _ _ obs.ne']
  congr
  · calc
    _ = (p.toReal⁻¹ * p.toReal) * (q.toReal⁻¹ * q.toReal) * p₀.toReal := by
      rw [toReal_inv, toReal_inv]
      ring
    _ = _ := by
      rw [inv_mul_cancel₀, inv_mul_cancel₀, one_mul, one_mul]
      · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
      · exact (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp).ne'
  · calc
    _ = (q.toReal⁻¹ * q.toReal) * (p.toReal⁻¹ * p.toReal * p₀.toReal - p₀.toReal⁻¹ *
        p₀.toReal * p.toReal) := by
      rw [toReal_inv, toReal_inv, toReal_inv]
      ring
    _ = _ := by
      repeat rw [inv_mul_cancel₀, one_mul]
      · exact (toReal_pos hp₀.ne' hp₀').ne'
      · exact (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp).ne'
      · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'

lemma ζ_equality₈ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ = ⊤) :
    ζ p₀ q₀ p₁ q₁ t = p₁.toReal / (p₁.toReal - p.toReal) := by
    rw [ζ_symm]
    exact ζ_equality₇ (Ioo.one_sub_mem ht) hp₁ hq₁ hp₀ hq₀ hp₀p₁.symm hq₀q₁.symm
      (switch_exponents ht hp) (switch_exponents ht hq) hp₁' hq₁'

lemma ζ_eq_top_top (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ = ⊤)
    (hq₁' : q₁ = ⊤) :
    ζ p₀ q₀ p₁ q₁ t = 1 := by
  rw [ζ_equality₂ ht, ← preservation_interpolation ht hp₀ hp₁ hp,
    ← preservation_interpolation ht hq₀ hq₁ hq, hp₁', hq₁']
  simp only [inv_top, toReal_zero, sub_zero]
  rw [mul_comm, div_eq_mul_inv, mul_inv_cancel₀]
  exact (mul_pos (interp_exp_inv_pos ht hq₀ hq₁ hq₀q₁ hq)
    (interp_exp_inv_pos ht hp₀ hp₁ hp₀p₁ hp)).ne'

lemma ζ_pos_iff_aux (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) :
    ( 0 < p₀.toReal * (q₀.toReal - q.toReal) / (q₀.toReal * (p₀.toReal - p.toReal))) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg,
      neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma preservation_inequality (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) (hp₀' : p₀ ≠ ⊤) :
    p.toReal < p₀.toReal ↔ p < p₀ :=
  toReal_lt_toReal (interp_exp_ne_top hp₀p₁ ht hp) hp₀'

lemma preservation_inequality' (ht : t ∈ Ioo 0 1)(hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) (hp₀' : p₀ ≠ ⊤) :
    p₀.toReal < p.toReal ↔ p₀ < p :=
  toReal_lt_toReal hp₀' (interp_exp_ne_top hp₀p₁ ht hp)

lemma preservation_inequality_of_lt₀ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀q₁ : q₀ < q₁) :
    q₀.toReal < q.toReal :=
  (toReal_lt_toReal hq₀q₁.ne_top (interp_exp_ne_top hq₀q₁.ne ht hq)).mpr
    ((exp_gt_iff ht hq₀ hq₁ hq₀q₁.ne hq).mpr hq₀q₁)

lemma preservation_inequality_of_lt₁ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀q₁ : q₀ < q₁)
    (hq₁' : q₁ ≠ ⊤):
    q.toReal < q₁.toReal :=
  (toReal_lt_toReal (interp_exp_ne_top hq₀q₁.ne ht hq) hq₁').mpr
    ((exp_lt_iff₁ ht hq₀ hq₁ hq₀q₁.ne hq).mpr hq₀q₁)

lemma ζ_pos_toReal_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) : (0 < ζ p₀ q₀ p₁ q₁ t) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [ζ_equality₃ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_pos_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_pos_toReal_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    (0 < ζ p₀ q₀ p₁ q₁ t) ↔
    ((q.toReal < q₁.toReal) ∧ (p.toReal < p₁.toReal)) ∨
    ((q₁.toReal < q.toReal) ∧ (p₁.toReal < p.toReal)) := by
  rw [ζ_equality₄ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_pos_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_pos_iff_aux₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (0 < ζ p₀ q₀ p₁ q₁ t) ↔
    q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal ∨
    q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal := by
  unfold ζ
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg,
      neg_mul_eq_mul_neg, mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁

lemma inv_toReal_iff (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) :
    p₀⁻¹.toReal < p₁⁻¹.toReal ↔ p₁ < p₀ :=
  Iff.trans (toReal_lt_toReal (ne_of_lt (inv_lt_top.mpr hp₀))
    (ne_of_lt (inv_lt_top.mpr hp₁))) ENNReal.inv_lt_inv

lemma ζ_pos_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (0 < ζ p₀ q₀ p₁ q₁ t) ↔
    ((q₁ < q₀) ∧ (p₁ < p₀)) ∨ ((q₀ < q₁) ∧ (p₀ < p₁)) := by
  rw [ζ_pos_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁,
    inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
    inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_pos_iff' (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    0 < ζ p₀ q₀ p₁ q₁ t ↔ (q < q₀ ∧ p < p₀) ∨ (q₀ < q ∧ p₀ < p) := by
  rw [ζ_pos_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁,
    ← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq,
    ← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_pos_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    0 < ζ p₀ q₀ p₁ q₁ t ↔ q₀ < q := by
  rw [ζ_pos_iff' ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ hp₀p₁'.ne hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_pos_iff_of_lt₀2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    0 < ζ p₀ q₀ p₁ q₁ t.toReal ↔ q₀ < q := by
  sorry

lemma ζ_pos_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
  (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    0 < ζ p₀ q₀ p₁ q₁ t ↔ q < q₁ := by
  rw [← exp_gt_exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_pos_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_pos_iff_of_lt₁2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
  (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    0 < ζ p₀ q₀ p₁ q₁ t.toReal ↔ q < q₁ := by sorry

lemma ζ_neg_iff_aux₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (ζ p₀ q₀ p₁ q₁ t) < 0 ↔
      q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal ∨
      q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal := by
  unfold ζ
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁

lemma ζ_neg_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔ q₁ < q₀ ∧ p₀ < p₁ ∨ q₀ < q₁ ∧ p₁ < p₀ := by
  rw [ζ_neg_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁, inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
    inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_neg_iff' (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔ (q < q₀ ∧ p₀ < p) ∨ (q₀ < q ∧ p < p₀) := by
  rw [ζ_neg_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁, ← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp,
    ← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq, ← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp,
    ← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_neg_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔ q < q₀ := by
  rw [ζ_neg_iff' ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ hp₀p₁'.ne hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_neg_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_neg_iff_aux (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    (p₀.toReal * (q₀.toReal - q.toReal) / (q₀.toReal * (p₀.toReal - p.toReal)) < 0) ↔
    (q.toReal < q₀.toReal) ∧ (p₀.toReal < p.toReal) ∨
    (q₀.toReal < q.toReal) ∧ (p.toReal < p₀.toReal) := by
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg,
    mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
    mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma ζ_neg_toReal_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔
      (q.toReal < q₀.toReal ∧ p₀.toReal < p.toReal) ∨
      (q₀.toReal < q.toReal ∧ p.toReal < p₀.toReal) := by
  rw [ζ_equality₃ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_neg_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_neg_toReal_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔
      (q.toReal < q₁.toReal ∧ p₁.toReal < p.toReal) ∨
      (q₁.toReal < q.toReal ∧ p.toReal < p₁.toReal) := by
  rw [ζ_equality₄ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_neg_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_neg_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t < 0 ↔ (q < q₀ ∧ p₀ < p) ∨ (q₀ < q ∧ p < p₀) := by
  rw [ζ_neg_toReal_iff₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀',
    preservation_inequality ht hq₀q₁ hq hq₀', preservation_inequality ht hp₀p₁ hp hp₀',
    preservation_inequality' ht hq₀q₁ hq hq₀', preservation_inequality' ht hp₀p₁ hp hp₀']

lemma ζ_ne_zero (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    ζ p₀ q₀ p₁ q₁ t ≠ 0 := by
  refine div_ne_zero ?_ ?_
  · apply mul_ne_zero (preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁).ne'
    refine sub_ne_zero_of_ne (Ne.symm fun h ↦ hq₀q₁ ?_)
    rw [← inv_inv q₀, ← inv_inv q₁, ← coe_inv_exponent hq₀, ← coe_inv_exponent hq₁]
    exact congrArg Inv.inv (congrArg ENNReal.ofReal h)
  · apply mul_ne_zero (preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁).ne'
    refine sub_ne_zero_of_ne (Ne.symm fun h ↦ hp₀p₁ ?_)
    rw [← inv_inv p₀, ← inv_inv p₁, ← coe_inv_exponent hp₀, ← coe_inv_exponent hp₁]
    exact congrArg Inv.inv (congrArg ENNReal.ofReal h)

lemma ζ_le_zero_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t ≤ 0 ↔ q < q₀ := by
  constructor <;> intro h
  · rcases (Decidable.lt_or_eq_of_le h) with ζ_lt_0 | ζ_eq_0
    · exact (ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mp ζ_lt_0
    · exact False.elim <| (ζ_ne_zero ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁) ζ_eq_0
  · exact ((ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mpr h).le

lemma ζ_le_zero_iff_of_lt₀2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal ≤ 0 ↔ q < q₀ := by
  sorry

lemma ζ_le_zero_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t ≤ 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_le_zero_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_le_zero_iff_of_lt₁2 {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal ≤ 0 ↔ q₁ < q := by
  sorry

lemma eq_exponents₀ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal + q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₀.toReal)) = (1 - t) * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) =
        q.toReal * ((1 - t) * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
      calc
      _ = q₀.toReal * q₁⁻¹.toReal - q₀.toReal * q₀⁻¹.toReal +
          q₁⁻¹.toReal * q.toReal - q₁⁻¹.toReal *  q₀.toReal := by
        ring
      _ = q₁⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal := by
        rw [toReal_inv, toReal_inv, toReal_inv, mul_inv_cancel₀, inv_mul_cancel₀]
        · ring
        · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
        · exact (toReal_pos hq₀.ne' hq₀').ne'
      _ = q.toReal * (q₁⁻¹.toReal - q⁻¹.toReal) := by ring
      _ = _ := by
        rw [preservation_interpolation ht hq₀ hq₁ hq]
        congr
        ring
    rw [this, mul_div_assoc, mul_div_cancel_right₀]
    · ring
    exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₂ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal / p₀.toReal + p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₀.toReal)) = (1 - t) * p₀⁻¹.toReal * q.toReal := by
  rw [div_eq_inv_mul, mul_div_assoc, mul_assoc, toReal_inv, ← mul_add, mul_comm_div,
    ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) =
        q.toReal * ((1 - t) * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
      calc
      _ = q₀.toReal * q₁⁻¹.toReal - q₀.toReal * q₀⁻¹.toReal +
          q₁⁻¹.toReal * q.toReal - q₁⁻¹.toReal *  q₀.toReal := by
        ring
      _ = q₁⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal := by
        rw [toReal_inv, toReal_inv, toReal_inv, mul_inv_cancel₀, inv_mul_cancel₀]
        · ring
        · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
        · exact (toReal_pos hq₀.ne' hq₀').ne'
      _ = q.toReal * (q₁⁻¹.toReal - q⁻¹.toReal) := by ring
      _ = _ := by
        rw [preservation_interpolation ht hq₀ hq₁ hq]
        congr
        ring
    rw [this, mul_div_assoc, mul_div_cancel_right₀]
    · ring
    · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₁ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) = - t * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : q₀⁻¹.toReal * (q.toReal - q₀.toReal) = - t * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
    calc
    _ = (q₀⁻¹.toReal * q.toReal - q₀⁻¹.toReal * q₀.toReal) := by ring
    _ = (q₀⁻¹.toReal * q.toReal - 1) := by
      rw [toReal_inv, inv_mul_cancel₀]
      exact (exp_toReal_pos hq₀ hq₀').ne'
    _ = (q₀⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal) := by
      rw [toReal_inv, toReal_inv, inv_mul_cancel₀]
      exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
    _ = q.toReal * (q₀⁻¹.toReal - q⁻¹.toReal) := by ring
    _ = _ := by
      rw [preservation_interpolation ht hq₀ hq₁ hq]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

-- TODO: simplify these proofs with statements above
lemma eq_exponents₃ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) =
      - t * p₁⁻¹.toReal * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : (p₁⁻¹.toReal * q₀⁻¹.toReal) * (q.toReal - q₀.toReal) =
      - t * p₁⁻¹.toReal * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
    calc
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - q₀⁻¹.toReal * q₀.toReal) := by ring
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - 1) := by
      rw [toReal_inv, toReal_inv, inv_mul_cancel₀]
      apply (exp_toReal_pos hq₀ hq₀').ne'
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal) := by
      rw [toReal_inv, toReal_inv, toReal_inv, inv_mul_cancel₀]
      exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
    _ = p₁⁻¹.toReal * q.toReal * (q₀⁻¹.toReal - q⁻¹.toReal) := by ring
    _ = _ := by
      rw [preservation_interpolation ht hq₀ hq₁ hq]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₄ :
    q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) = - (q₀⁻¹.toReal / (q₀⁻¹.toReal - q₁⁻¹.toReal)) := calc
  _ = - (q₀⁻¹.toReal * (-(q₁⁻¹.toReal - q₀⁻¹.toReal)⁻¹)) := by
    rw [div_eq_mul_inv]; ring
  _ = _ := by congr; rw [neg_inv, neg_sub]

lemma eq_exponents₅ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    (q₁.toReal + -(q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal)))
      = t * q.toReal := by
  rw [eq_exponents₄, neg_mul, neg_neg, eq_exponents₀ (Ioo.one_sub_mem ht) hq₁ hq₀ (Ne.symm hq₀q₁)
    (switch_exponents ht hq) hq₁']
  ring

lemma eq_exponents₆ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) = (1 - t) * q.toReal := by
  rw [← neg_neg (a := q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)), ← eq_exponents₄, neg_mul,
    eq_exponents₁ (Ioo.one_sub_mem ht) hq₁ hq₀ (Ne.symm hq₀q₁) (switch_exponents ht hq) hq₁']
  ring

lemma eq_exponents₇ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    q₁.toReal / p₁.toReal + -(p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
    (q.toReal - q₁.toReal)) =
    t * p₁⁻¹.toReal * q.toReal := by
  rw [div_eq_mul_inv, toReal_inv]
  calc
  _ = p₁.toReal⁻¹ * (q₁.toReal + - (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₁.toReal))) := by ring
  _ = _ := by
    rw [eq_exponents₅ (ht := ht)] <;> try assumption
    ring

lemma eq_exponents₈ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) =
    (1 - t) * p₀⁻¹.toReal * q.toReal := calc
  _ = p₀⁻¹.toReal * (q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal)) := by ring
  _ = _ := by
    rw [eq_exponents₆] <;> try assumption
    ring

end ComputationsChoiceExponent
