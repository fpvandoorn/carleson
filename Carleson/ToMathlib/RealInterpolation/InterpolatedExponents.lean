import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Results about working with (interpolated) exponents

This files contains convenience results for working with interpolated exponents,
as well as results about a particular choice of exponent that we will use for the proof
of the real interpolation theorem.

Upstreaming status: mixed; some requires more design discussions
- the ENNReal section is ready to go
- the ComputationsInterpolatedExponents sections is also generally useful;
  need to find a better naming scheme for the lemmas (and address a few TODOs)
- the ComputationsChoiceExponent section is specific to this particular proof of real interpolation.
  If we prefer a proof about Lorentz spaces, using a different approach,
  it may not be worth upstreaming.
-/
noncomputable section

open ENNReal Real Set

variable {p₀ q₀ p₁ q₁ p q t : ℝ≥0∞}

namespace ENNReal

-- the Ioc version is true for r = ∞ also
theorem mem_sub_Ioo {q r : ℝ≥0∞} (hr : r ≠ ⊤) (hq : q ∈ Ioo 0 r) : r - q ∈ Ioo 0 r := by
  obtain (rfl | hr') := eq_zero_or_pos r
  · apply False.elim (by simp at hq)
  exact ⟨tsub_pos_of_lt hq.2, (ENNReal.sub_lt_self_iff hr).mpr ⟨hr', hq.1⟩⟩

lemma sub_toReal_of_le {t : ℝ≥0∞} (ht : t ≤ 1) : 1 - t.toReal = (1 - t).toReal := by
  rw [← toReal_one, toReal_sub_of_le ht one_ne_top]

lemma sub_sub_toReal_of_le {t : ℝ≥0∞} (ht : t ≤ 1) : t.toReal = 1 - (1 - t).toReal := by
  rw [← sub_toReal_of_le ht, _root_.sub_sub_cancel]

lemma one_sub_one_sub_eq {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) : 1 - (1 - t) = t :=
  sub_sub_cancel one_ne_top ht.2.le

lemma one_le_toReal {a : ℝ≥0∞} (ha₁ : 1 ≤ a) (ha₂ : a < ⊤) : 1 ≤ a.toReal :=
  toReal_mono ha₂.ne_top ha₁

lemma coe_rpow_ne_top {a : ℝ} {q : ℝ} (hq : 0 ≤ q) : ENNReal.ofReal a ^ q ≠ ⊤ := by finiteness

-- Note this lemma can directly be applied to elements of `ℝ≥0` as well
lemma coe_rpow_ne_top' {a : ℝ} {q : ℝ} (hq : 0 < q) : ENNReal.ofReal a ^ q ≠ ⊤ := by finiteness

lemma coe_pow_pos {a : ℝ} {q : ℝ} (ha : 0 < a) : 0 < ENNReal.ofReal a ^ q :=
  ENNReal.rpow_pos (ofReal_pos.mpr ha) coe_ne_top

lemma rpow_ne_top' {a : ℝ≥0∞} {q : ℝ} (ha : a ≠ 0) (ha' : a ≠ ⊤) : a ^ q ≠ ⊤ := by finiteness

-- unused (one reference in an also-unused lemma)
lemma exp_toReal_pos' {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q < ⊤) : 0 < q.toReal :=
  toReal_pos (lt_of_lt_of_le zero_lt_one hq).ne' hq'.ne_top

@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma ne_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q ≠ ⊤ := hq.2.ne_top

lemma lt_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q < ⊤ := by finiteness

@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma ne_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ ⊤ := hq.2.ne_top

lemma lt_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q < ⊤ := (ne_top_of_Ioo hq).lt_top

-- XXX: generalise interval bounds!
lemma toReal_mem_Ioo {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) : t.toReal ∈ Ioo 0 1 :=
  ⟨toReal_pos ht.1.ne' (ne_top_of_Ioo ht), toReal_lt_of_lt_ofReal (by simp [ht.2])⟩

-- XXX: generalise interval bounds!
lemma ofReal_mem_Ioo_0_1 (t : ℝ) (h : t ∈ Ioo 0 1) : ENNReal.ofReal t ∈ Ioo 0 1 :=
  ⟨ofReal_pos.mpr h.1, ofReal_lt_one.mpr h.2⟩

lemma ne_top_of_Ioc {p q r : ℝ≥0∞} (hq : q ∈ Ioc p r) (hr : r < ⊤) : q ≠ ⊤ :=
  hq.2.trans_lt hr |>.ne_top

lemma pos_of_rb_Ioc {p q r : ℝ≥0∞} (hr : q ∈ Ioc p r) : 0 < r :=
  zero_le p |>.trans_lt hr.1 |>.trans_le hr.2

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
lemma eq_of_rpow_eq (a b : ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) (h : a ^ c = b ^ c) : a = b := by
  rw [← ENNReal.rpow_rpow_inv hc a, ← ENNReal.rpow_rpow_inv hc b]
  exact congrFun (congrArg HPow.hPow h) c⁻¹

lemma le_of_rpow_le {a b : ℝ≥0∞} {c : ℝ} (hc : 0 < c) (h : a ^ c ≤ b ^ c) : a ≤ b := by
  rw [← ENNReal.rpow_rpow_inv hc.ne' a, ← ENNReal.rpow_rpow_inv hc.ne' b]
  exact (ENNReal.rpow_le_rpow_iff (inv_pos_of_pos hc)).mpr h

lemma coe_inv_exponent (hp₀ : 0 < p₀) : ENNReal.ofReal (p₀⁻¹.toReal) = p₀⁻¹ :=
  ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₀.ne')

-- TODO: find a better name for the next three lemmas!
lemma preservation_positivity₀ (ht : t ∈ Ioo 0 1) (hpq : p ≠ ⊤ ∨ q ≠ ⊤) :
    0 < (1 - t) * p⁻¹ + t * q⁻¹ := by
  obtain dir|dir := hpq
  · exact Left.add_pos_of_pos_of_nonneg (mul_pos ((tsub_pos_of_lt ht.2).ne')
      (ENNReal.inv_ne_zero.mpr dir)) (zero_le _)
  · exact Right.add_pos_of_nonneg_of_pos (zero_le _)
      <| ENNReal.mul_pos ht.1.ne' (ENNReal.inv_ne_zero.mpr dir)

lemma preservation_positivity (ht : t ∈ Ioo 0 1) (hpq : p ≠ q) :
    0 < (1 - t) * p⁻¹ + t * q⁻¹ := by
  apply preservation_positivity₀ ht
  cases (lt_or_gt_of_ne hpq) <;> exact Ne.ne_or_ne ⊤ hpq

lemma preservation_positivity' (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (ht : t ≠ ⊤)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 0 < p := by
  rw [← inv_inv p, hp]
  simp [ENNReal.mul_eq_top, hp₀.ne', hp₁.ne', ht]

lemma rpow_add_of_pos (a : ℝ≥0∞) (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    a ^ (c + d) = a ^ c * a ^ d := by
  have hcd : 0 < c + d := by linarith
  rcases (eq_or_ne a 0) with a_eq_zero | a_ne_zero
  · rw [a_eq_zero, zero_rpow_of_pos hcd, zero_rpow_of_pos hc, zero_rpow_of_pos hd, mul_zero]
  · rcases (eq_or_ne a ⊤) with a_eq_top | a_ne_top
    · rw [a_eq_top, top_rpow_of_pos hcd, top_rpow_of_pos hc, top_rpow_of_pos hd, top_mul_top]
    · rw [ENNReal.rpow_add c d a_ne_zero a_ne_top]

lemma eq_of_le_of_le (a b : ℝ≥0∞) (hab : a ≤ b) (hab' : b ≤ a) : a = b := by
  rcases (eq_or_ne a b) with a_eq_b | a_ne_b
  · exact a_eq_b
  · rcases lt_or_gt_of_ne a_ne_b with a_lt_b | b_lt_a
    · contrapose! a_lt_b; exact hab'
    · contrapose! b_lt_a; exact hab

open scoped NNReal

-- TODO: should some of the following lemmas be tagged with finiteness?
lemma rpow_apply_coe {x : ℝ≥0} {y : ℝ} :
    ENNReal.ofNNReal x ^ y = if x = 0 ∧ y < 0 then ∞ else (x ^ y : ℝ≥0) := rfl

lemma rpow_apply_coe' {x : ℝ≥0∞} {y : ℝ} (hx : x ≠ ⊤) :
    x ^ y = if x = 0 ∧ y < 0 then ∞ else (x.toNNReal ^ y : ℝ≥0) := by
  convert ENNReal.rpow_apply_coe
  · exact Eq.symm (coe_toNNReal hx)
  · rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hx]

lemma rpow_lt_rpow_iff_neg {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ ∞) (hxy : x < y) {z : ℝ} (hz : z < 0) :
    y ^ z < x ^ z := by
  rw [ENNReal.rpow_apply_coe' hy, ENNReal.rpow_apply_coe' hxy.ne_top]
  simpa [(pos_of_gt hxy).ne', hx] using
    NNReal.rpow_lt_rpow_of_neg (toNNReal_pos hx hxy.ne_top) (toNNReal_strict_mono hy hxy) hz

lemma div_lt_div {a b c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ∞) : a / c < b / c ↔ a < b := by
  rw [ENNReal.div_lt_iff (Or.inl hc.ne') (Or.inl hc'), ENNReal.div_mul_cancel hc.ne' hc']

lemma rpow_lt_top_of_neg {x : ℝ≥0∞} {y : ℝ} (hx : 0 < x) (hy : y < 0) : x ^ y < ⊤ := by
  refine ENNReal.inv_lt_inv.mp ?_
  have := hx.ne'
  have := hy.le
  simp only [inv_top, ENNReal.inv_pos, ne_eq, rpow_eq_top_iff, not_or, not_and, not_lt]
  tauto

lemma rpow_lt_top_of_pos_ne_top_ne_zero {x : ℝ≥0∞} {y : ℝ} (hx : x ≠ 0) (hx' : x ≠ ⊤) (hy : y ≠ 0) :
    x ^ y < ⊤ := by
  rcases lt_or_gt_of_ne hy with y_pos | y_neg
  · exact rpow_lt_top_of_neg (hx.bot_lt) y_pos
  · exact rpow_lt_top_of_nonneg (y_neg.le) hx'

lemma rpow_pos_of_pos_ne_top_ne_zero {x : ℝ≥0∞} {y : ℝ} (hx : x ≠ 0) (hx' : x ≠ ⊤) (hy : y ≠ 0) :
    0 < x ^ y := by
  refine ENNReal.inv_lt_inv.mp ?_
  rw [← rpow_neg, inv_zero]
  exact rpow_lt_top_of_pos_ne_top_ne_zero hx hx' (neg_ne_zero.mpr hy)

-- TODO: better name!
lemma power_estimate {a b t γ : ℝ} (hγ : 0 < γ) (htγ : γ ≤ t) (hab : a ≤ b) :
    (t / γ) ^ a ≤ (t / γ) ^ b := by
  gcongr
  exact (one_le_div hγ).mpr htγ

-- TODO: better name!
lemma power_estimate' {a b t γ : ℝ} (ht : 0 < t) (htγ : t ≤ γ) (hab : a ≤ b) :
    (t / γ) ^ b ≤ (t / γ) ^ a := by
  have γ_pos : 0 < γ := lt_of_lt_of_le ht htγ
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos ht (γ_pos)) (div_le_one_of_le₀ htγ γ_pos.le) hab

lemma rpow_le_rpow_of_exponent_le_base_le {a b t γ : ℝ} (ht : 0 < t) (htγ : t ≤ γ) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ b) ≤ ENNReal.ofReal (t ^ a) * ENNReal.ofReal (γ ^ (b - a)) := by
  rw [mul_comm]
  have γ_pos : 0 < γ := lt_of_lt_of_le ht htγ
  rw [Real.rpow_sub γ_pos]
  refine (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal (γ ^ (-b) )) ?_ coe_ne_top).mp ?_
  · exact (ofReal_pos.mpr (Real.rpow_pos_of_pos γ_pos (-b))).ne'
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, neg_add_cancel,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul (by positivity)]
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    exact ofReal_le_ofReal (power_estimate' ht htγ hab)

-- Note: this lemma is false if t = γ = ∞ and a < 0 ≤ b, as then t ^ a = ∞ ^ a = 0 and
-- the statement becomes ∞ ≤ 0 * ∞ = 0.
lemma rpow_le_rpow_of_exponent_le_base_le_enorm {a b : ℝ} {t γ : ℝ≥0∞} (ht : 0 < t) (ht' : t ≠ ∞) (htγ : t ≤ γ) (hab : a ≤ b) :
    t ^ b ≤ t ^ a * γ ^ (b - a) := by
  calc
  _ = t ^ (a + (b - a)) := by ring_nf
  _ = t ^ a * t ^ (b - a) := by rw [ENNReal.rpow_add _ _ ht.ne' ht']
  _ ≤ t ^ a * γ ^ (b - a) := by gcongr; linarith

-- TODO: there is a lot of overlap between above proof and below
lemma rpow_le_rpow_of_exponent_le_base_ge {a b t γ : ℝ} (hγ : 0 < γ) (htγ : γ ≤ t) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ a) ≤ ENNReal.ofReal (t ^ b) * ENNReal.ofReal (γ ^ (a - b)) := by
  rw [mul_comm]
  have t_pos : 0 < t := lt_of_le_of_lt' htγ hγ
  rw [Real.rpow_sub hγ]
  refine (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal (γ ^ (-a) )) ?_ coe_ne_top).mp ?_
  · exact (ofReal_pos.mpr (Real.rpow_pos_of_pos hγ (-a))).ne'
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, neg_add_cancel,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul (by positivity)]
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    exact ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le ((one_le_div hγ).mpr htγ) hab)

lemma rpow_le_rpow_of_exponent_le_base_ge_enorm {a b : ℝ} {t γ : ℝ≥0∞} (hγ : 0 < γ) (hγ' : γ ≠ ∞) (htγ : γ ≤ t) (hab : a ≤ b) :
    t ^ a ≤ (t ^ b) * (γ ^ (a - b)) := by
  by_cases ht' : t = ∞
  · simp_all only [le_top, top_rpow_def, ite_mul, sub_zero, one_mul, zero_mul]
    split_ifs with ha hb hb' ha'
    · simp_all
    · exact False.elim (by linarith [hb, hb'])
    · exact False.elim (by linarith [hb, hb'])
    · simp_all
    · simp_all
    · simpa using by order
    · rw [ENNReal.top_mul]
      · exact zero_le ⊤
      simp_all
    · positivity
    · simp
  have t_pos : 0 < t := lt_of_le_of_lt' htγ hγ
  rw [mul_comm, ← ENNReal.inv_mul_le_iff, ← ENNReal.rpow_neg, mul_comm, ENNReal.mul_le_iff_le_inv,
    ← ENNReal.rpow_neg, ← ENNReal.rpow_add, neg_sub, add_comm, sub_eq_add_neg]
  · gcongr
    linarith
  · positivity
  · assumption
  · simp_all only [ne_eq, ENNReal.rpow_eq_zero_iff, false_and, or_false, not_and, not_lt]
    contrapose
    exact fun _ ↦ t_pos.ne'
  · simpa [ht'] using fun hfalse ↦ by simp_all
  · simp_all
  · simpa using ⟨fun h ↦ by simp_all, fun h ↦ by simp_all⟩

end ENNReal

/-! ## Convenience results for working with (interpolated) exponents -/
namespace ComputationsInterpolatedExponents

lemma interp_exp_ne_top (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p ≠ ⊤ := by
  apply ENNReal.inv_ne_zero.mp
  refine hp ▸ (preservation_positivity₀ ht ?_).ne'
  by_contra! h
  exact hp₀p₁ (h.1.trans h.2.symm)

lemma interp_exp_ne_top' (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p ≠ ⊤ :=
  ENNReal.inv_ne_zero.mp (hp ▸ (preservation_positivity₀ ht hp₀p₁).ne')

lemma interp_exp_eq (hp₀p₁ : p₀ = p₁)
    (ht : t ∈ Ioo 0 1) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p₀ = p := by
  rw [← inv_inv (a := p), hp, ← hp₀p₁, ← add_mul]
  have : 1 - t + t = 1 := by rw [tsub_add_cancel_iff_le]; exact ht.2.le
  rw [this, one_mul, inv_inv]

lemma interp_exp_lt_top (hp₀p₁ : p₀ ≠ p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top hp₀p₁ ht hp

lemma interp_exp_lt_top' (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top' hp₀p₁ ht hp

lemma interp_exp_between (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p ∈ Ioo p₀ p₁ := by
  have ht' : t ≠ ∞ := (ht.2.trans one_lt_top).ne
  refine ⟨?_, ?_⟩ <;> apply ENNReal.inv_lt_inv.mp
  · rw [hp]
    have : p₀⁻¹ = (1 - t) * p₀⁻¹ + t * p₀⁻¹ := by
      rw [← add_mul, tsub_add_eq_max, max_eq_left_of_lt, one_mul]
      exact ht.2
    nth_rw 2 [this]
    gcongr
    · exact mul_ne_top (sub_ne_top top_ne_one.symm) (inv_ne_top.mpr hp₀.ne')
    · exact ht.1.ne'
    · exact ht'
  · rw [hp]
    have : p₁⁻¹ = (1 - t) * p₁⁻¹ + t * p₁⁻¹ := by
      rw [← add_mul, tsub_add_eq_max, max_eq_left_of_lt, one_mul]
      exact ht.2
    nth_rw 1 [this]
    gcongr
    · exact mul_ne_top ht' (inv_ne_top.mpr hp₁.ne')
    · exact (tsub_pos_iff_lt.mpr ht.2).ne'
    · exact (mem_sub_Ioo (one_ne_top) ht).2.trans one_lt_top |>.ne

lemma one_le_interp_exp_aux (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 1 ≤ p :=
  hp₀.trans_lt
    (interp_exp_between (zero_lt_one.trans_le hp₀) (zero_lt_one.trans_le hp₁) hp₀p₁ ht hp).1 |>.le

lemma switch_exponents (ht : t ∈ Ioo 0 1) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p⁻¹ = (1 - (1 - t)) * p₁⁻¹ + (1 - t) * p₀⁻¹ := by
  rwa [add_comm, one_sub_one_sub_eq ht]

lemma one_le_interp (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 1 ≤ p := by
  rcases (lt_or_gt_of_ne hp₀p₁) with p₀lt_p₁ | p₁lt_p₀
  · exact one_le_interp_exp_aux hp₀ hp₁ p₀lt_p₁ ht hp
  · exact one_le_interp_exp_aux hp₁ hp₀ p₁lt_p₀ (mem_sub_Ioo one_ne_top ht) (switch_exponents ht hp)

lemma one_le_interp_toReal (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 1 ≤ p.toReal :=
  one_le_toReal (one_le_interp hp₀ hp₁ hp₀p₁ ht hp) (interp_exp_ne_top hp₀p₁ ht hp).lt_top

-- unused
lemma exp_toReal_ne_zero_of_Ico {q p : ℝ≥0∞} (hq : q ∈ Ico 1 p) : q.toReal ≠ 0 :=
  (exp_toReal_pos' hq.1 (lt_top_of_Ico hq)).ne'

-- TODO : decide if this is wanted
-- local instance : Coe ℝ ℝ≥0∞ where
--   coe x := ENNReal.ofReal x

lemma inv_of_interpolated_pos' (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 0 < p⁻¹ :=
  ENNReal.inv_pos.mpr (interp_exp_ne_top hp₀p₁ ht hp)

-- TODO: remove, this is redundant, but for now mirror the development for reals...
lemma interpolated_pos' (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (ht : t ≠ ∞)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 0 < p :=
  preservation_positivity' hp₀ hp₁ ht hp

lemma exp_toReal_pos (hp₀ : 0 < p₀) (hp₀' : p₀ ≠ ⊤) : 0 < p₀.toReal :=
  toReal_pos hp₀.ne' hp₀'

lemma interp_exp_in_Ioo_zero_top (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p ∈ Ioo 0 ⊤ :=
  ⟨interpolated_pos' hp₀ hp₁ (ne_top_of_Ioo ht) hp, interp_exp_lt_top' hp₀p₁ ht hp⟩

lemma inv_toReal_pos_of_ne_top (hp₀ : 0 < p₀) (hp' : p₀ ≠ ⊤) : 0 < p₀⁻¹.toReal :=
  toReal_inv _ ▸ inv_pos_of_pos (exp_toReal_pos hp₀ hp')

lemma inv_toReal_ne_zero_of_ne_top (hp₀ : 0 < p₀) (hp' : p₀ ≠ ⊤) : p₀⁻¹.toReal ≠ 0 :=
  (inv_toReal_pos_of_ne_top hp₀ hp').ne'

lemma interp_exp_toReal_pos (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : 0 < p.toReal :=
  toReal_pos (interpolated_pos' hp₀ hp₁ (ne_top_of_Ioo ht) hp).ne' (interp_exp_ne_top hp₀p₁ ht hp)

lemma interp_exp_toReal_pos' (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) : 0 < p.toReal :=
  toReal_pos (interpolated_pos' hp₀ hp₁ (ne_top_of_Ioo ht) hp).ne' (interp_exp_ne_top' hp₀p₁ ht hp)

lemma interp_exp_inv_pos (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    0 < p⁻¹.toReal :=
  toReal_inv _ ▸ inv_pos_of_pos (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp)

lemma interp_exp_inv_ne_zero (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p⁻¹.toReal ≠ 0 :=
  (interp_exp_inv_pos ht hp₀ hp₁ hp₀p₁ hp).ne'

lemma preservation_interpolation (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p⁻¹.toReal = (1 - t).toReal * (p₀⁻¹).toReal + t.toReal * (p₁⁻¹).toReal := by
  rw [hp, ← toReal_mul, ← toReal_mul, toReal_add (by finiteness) (by finiteness)]

lemma preservation_positivity_inv_toReal (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₀p₁ : p₀ ≠ p₁) :
    0 < (1 - t.toReal) * (p₀⁻¹).toReal + t.toReal * (p₁⁻¹).toReal := by
  -- TODO: do we need aux' ever? if so, extract as general lemma!
  -- have aux' : 0 < (1 - t).toReal :=
  --   toReal_pos (tsub_pos_iff_lt.mpr ht.2).ne' (sub_ne_top top_ne_one.symm)
  have aux : 0 < 1 - t.toReal := by simpa using (toReal_mem_Ioo ht).2
  rcases (eq_or_ne p₀ ⊤) with p₀eq_top | p₀ne_top
  · rw [p₀eq_top]
    simp only [inv_top, toReal_zero, mul_zero, zero_add]
    apply mul_pos (toReal_mem_Ioo ht).1
    rw [toReal_inv]
    refine inv_pos_of_pos (exp_toReal_pos hp₁ ?_)
    rw [p₀eq_top] at hp₀p₁
    exact hp₀p₁.symm
  · exact add_pos_of_pos_of_nonneg
      (mul_pos aux <| toReal_inv _ ▸ inv_pos_of_pos (exp_toReal_pos hp₀ p₀ne_top))
      (mul_nonneg (toReal_mem_Ioo ht).1.le toReal_nonneg)

lemma ne_inv_toReal_exponents (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁) :
    p₀⁻¹.toReal ≠ p₁⁻¹.toReal := by
  refine fun h ↦ hp₀p₁ ?_
  rw [← inv_inv p₀, ← inv_inv p₁]
  apply congrArg Inv.inv
  rw [← ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₀.ne'),
    ← ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₁.ne')]
  exact congrArg ENNReal.ofReal h

lemma ne_inv_toReal_exp_interp_exp (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p₀⁻¹.toReal ≠ p⁻¹.toReal := by
  rw [preservation_interpolation ht hp₀ hp₁ hp, ← sub_ne_zero]
  convert mul_ne_zero (toReal_ne_zero_of_Ioo ht)
    (sub_ne_zero_of_ne (ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁)) using 1
  -- These lines used to be
  -- rw [ENNReal.sub_mul, one_mul, add_comm_sub, sub_add_eq_sub_sub, sub_self, zero_sub,
  -- neg_sub, ← _root_.mul_sub]
  rw [mul_sub, tsub_add_eq_tsub_tsub]
  nth_rw 1 [← one_mul p₀⁻¹.toReal]
  have : (1 - t) + t = 1 := by rw [tsub_add_cancel_iff_le]; exact ht.2.le
  rw [← sub_mul]
  congr
  rw [sub_eq_iff_eq_add', ← toReal_add (by finiteness) (by finiteness), this, ← ENNReal.toReal_one]

lemma ne_sub_toReal_exp (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁) :
    p₁⁻¹.toReal - p₀⁻¹.toReal ≠ 0 :=
  sub_ne_zero_of_ne (ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁).symm

lemma ne_toReal_exp_interp_exp (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) : p₀.toReal ≠ p.toReal := by
  refine fun h ↦ ne_inv_toReal_exp_interp_exp ht hp₀ hp₁ hp₀p₁ hp ?_
  repeat rw [toReal_inv _]
  exact congrArg Inv.inv h

lemma ne_toReal_exp_interp_exp₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p.toReal ≠ p₁.toReal :=
  (ne_toReal_exp_interp_exp (mem_sub_Ioo one_ne_top ht) hp₁ hp₀ hp₀p₁.symm (switch_exponents ht hp)).symm

lemma ofReal_inv_interp_sub_exp_pos₁ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) :
    ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ > 0 :=
  ofReal_pos.mpr (inv_pos_of_pos (abs_sub_pos.mpr (ne_toReal_exp_interp_exp₁ ht hq₀ hq₁ hq₀q₁ hq)))

lemma ofReal_inv_interp_sub_exp_pos₀ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq₀q₁ : q₀ ≠ q₁) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) :
    ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ > 0 :=
  ofReal_pos.mpr (inv_pos_of_pos (abs_sub_pos.mpr
    (ne_toReal_exp_interp_exp ht hq₀ hq₁ hq₀q₁ hq).symm))

lemma exp_lt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p < p₀ ↔ p₁ < p₀ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun h ↦ (not_le_of_gt h (le_of_lt (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1)).elim,
      fun h ↦ (not_le_of_gt h p₀lt_p₁.le).elim⟩
  · exact ⟨fun _ ↦ p₁lt_p₀,
      fun _ ↦ (interp_exp_between hp₁ hp₀ p₁lt_p₀ (mem_sub_Ioo one_ne_top ht) (switch_exponents ht hp)).2⟩

lemma exp_gt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p₀ < p ↔ p₀ < p₁ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun _ ↦ p₀lt_p₁, fun _ ↦ (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1⟩
  · exact ⟨fun h ↦ (not_le_of_gt h (interp_exp_between hp₁ hp₀ p₁lt_p₀
      (mem_sub_Ioo one_ne_top ht) (switch_exponents ht hp)).2.le).elim,
      fun h ↦ (not_le_of_gt h p₁lt_p₀.le).elim⟩

lemma exp_lt_exp_gt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p < p₀ ↔ p₁ < p := by
  rw [exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_gt_iff (mem_sub_Ioo one_ne_top ht) hp₁ hp₀ hp₀p₁.symm
    (switch_exponents ht hp)]

lemma exp_gt_exp_lt_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p₀ < p ↔ p < p₁ := by
  rw [exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_lt_iff (mem_sub_Ioo one_ne_top ht) hp₁ hp₀ hp₀p₁.symm
    (switch_exponents ht hp)]

lemma exp_lt_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
    p < p₁ ↔ p₀ < p₁ := by
  rw [← exp_gt_exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp

lemma exp_gt_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) :
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

variable {p₀ q₀ p₁ q₁ p q t : ℝ≥0∞}

def ζ (p₀ q₀ p₁ q₁ : ℝ≥0∞) (t : ℝ) : ℝ :=
  (((1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal) * ((q₁⁻¹).toReal - (q₀⁻¹).toReal)) /
  (((1 - t) * (q₀⁻¹).toReal + t * (q₁⁻¹).toReal) * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))

lemma ζ_equality₁ (ht : t ∈ Ioo 0 1) :
    ζ p₀ q₀ p₁ q₁ t.toReal =
    (((1 - t).toReal * p₀⁻¹.toReal + t.toReal * p₁⁻¹.toReal) *
    ((1 - t).toReal * q₀⁻¹.toReal + t.toReal * q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (((1 - t).toReal * q₀⁻¹.toReal + t.toReal * q₁⁻¹.toReal) *
    ((1 - t).toReal * p₀⁻¹.toReal + t.toReal * p₁⁻¹.toReal - p₀⁻¹.toReal)) := by
  unfold ζ
  have aux : t.toReal ≠ 0 := toReal_ne_zero_of_Ioo ht
  rw [← mul_div_mul_right _ _ aux, mul_assoc _ _ t.toReal, mul_assoc _ _ t.toReal,
    ← sub_toReal_of_le ht.2.le]
  congr <;> ring

lemma ζ_equality₂ (ht : t ∈ Ioo 0 1) :
    ζ p₀ q₀ p₁ q₁ t.toReal =
    (((1 - t).toReal * p₀⁻¹.toReal + t.toReal * p₁⁻¹.toReal) *
    ((1 - t).toReal * q₀⁻¹.toReal + t.toReal * q₁⁻¹.toReal - q₁⁻¹.toReal)) /
    (((1 - t).toReal * q₀⁻¹.toReal + t.toReal * q₁⁻¹.toReal) *
    ((1 - t).toReal * p₀⁻¹.toReal + t.toReal * p₁⁻¹.toReal - p₁⁻¹.toReal)) := by
  unfold ζ
  have : -(1 - t.toReal) < 0 := by
    rw [neg_neg_iff_pos, sub_pos, ← toReal_one]
    exact toReal_strict_mono one_ne_top ht.2
  rw [← mul_div_mul_right _ _ this.ne, mul_assoc _ _ (-(1 - t.toReal)),
    mul_assoc _ _ (-(1 - t.toReal)), ← sub_toReal_of_le ht.2.le]
  congr <;> ring

lemma ζ_symm (ht : t ∈ Ioo 0 1) : ζ p₀ q₀ p₁ q₁ t.toReal = ζ p₁ q₁ p₀ q₀ (1 - t).toReal := by
  unfold ζ
  rw [← mul_div_mul_right (c := - 1), mul_assoc _ _ (-1), mul_assoc _ _ (-1)]; on_goal 2 => positivity
  simp only [mul_neg, mul_one, neg_sub]
  nth_rewrite 1 [add_comm]; nth_rw 2 [add_comm]
  rw [sub_toReal_of_le ht.2.le, sub_sub_toReal_of_le ht.2.le,
    sub_sub_toReal_of_le (mem_sub_Ioo (by finiteness) ht).2.le]

set_option linter.style.multiGoal false in
set_option linter.flexible false in
lemma ζ_equality₃ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal = (p₀.toReal * (q₀.toReal - q.toReal))  / (q₀.toReal * (p₀.toReal - p.toReal)) := by
  rw [ζ_equality₁ ht, ← preservation_interpolation, ← preservation_interpolation]
  have q_pos : 0 < q := interpolated_pos' hq₀ hq₁ (ne_top_of_Ioo ht) hq
  have p_pos : 0 < p := interpolated_pos' hp₀ hp₁ (ne_top_of_Ioo ht) hp
  have aux := mul_pos (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp)
    (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq)
  have hne : 0 < p.toReal * q.toReal * p₀.toReal * q₀.toReal :=
    mul_pos (mul_pos aux (exp_toReal_pos hp₀ hp₀')) (exp_toReal_pos hq₀ hq₀')
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

lemma ζ_equality₄ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal =
    (p₁.toReal * (q₁.toReal - q.toReal)) / (q₁.toReal * (p₁.toReal - p.toReal)) := by
  rw [ζ_symm, ζ_equality₃ (mem_sub_Ioo one_ne_top ht)] <;> try assumption
  · exact hp₀p₁.symm
  · exact hq₀q₁.symm
  · rw [hp, add_comm, ENNReal.sub_sub_cancel one_ne_top ht.2.le]
  · rw [hq, add_comm, ENNReal.sub_sub_cancel one_ne_top ht.2.le]

lemma ζ_equality₅ {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    p₀.toReal + (ζ p₀ q₀ p₁ q₁ t.toReal)⁻¹ * (q.toReal - q₀.toReal) * (p₀.toReal / q₀.toReal) = p.toReal := by
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

lemma ζ_equality₆ {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    p₁.toReal + (ζ p₀ q₀ p₁ q₁ t.toReal)⁻¹ * (q.toReal - q₁.toReal) * (p₁.toReal / q₁.toReal) = p.toReal := by
  rw [ζ_symm ht]
  apply ζ_equality₅ (mem_sub_Ioo one_ne_top ht) hp₁ hq₁ hp₀ hq₀ hp₀p₁.symm hq₀q₁.symm _ _ hp₁' hq₁'
  · rw [add_comm, one_sub_one_sub_eq ht]; apply hp
  · rw [add_comm, one_sub_one_sub_eq ht]; exact hq

lemma ζ_equality₇ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ = ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal = p₀.toReal / (p₀.toReal - p.toReal) := by
  rw [ζ_equality₁ ht, ← preservation_interpolation ht hp₀ hp₁ hp,
    ← preservation_interpolation ht hq₀ hq₁ hq, hq₀']
  simp only [inv_top, toReal_zero, sub_zero]
  have obs : 0 < p₀.toReal * p.toReal * q.toReal :=
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
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ = ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal = p₁.toReal / (p₁.toReal - p.toReal) := by
    rw [ζ_symm ht]
    refine ζ_equality₇ (ENNReal.mem_sub_Ioo one_ne_top ht) hp₁ hq₁ hp₀ hq₀ hp₀p₁.symm hq₀q₁.symm
      ?_ ?_ hp₁' hq₁' (q₀ := q₁) (p := p) (q := q)
    · rw [one_sub_one_sub_eq ht, add_comm]; exact hp
    · rw [one_sub_one_sub_eq ht, add_comm]; exact hq

lemma ζ_eq_top_top (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ = ⊤)
    (hq₁' : q₁ = ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal = 1 := by
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
  · simp only [sub_pos]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma preservation_inequality (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hp₀' : p₀ ≠ ⊤) :
    p.toReal < p₀.toReal ↔ p < p₀ :=
  toReal_lt_toReal (interp_exp_ne_top hp₀p₁ ht hp) hp₀'

lemma preservation_inequality' (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hp₀' : p₀ ≠ ⊤) :
    p₀.toReal < p.toReal ↔ p₀ < p :=
  toReal_lt_toReal hp₀' (interp_exp_ne_top hp₀p₁ ht hp)

lemma preservation_inequality_of_lt₀ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₀q₁ : q₀ < q₁) :
    q₀.toReal < q.toReal :=
  (toReal_lt_toReal hq₀q₁.ne_top (interp_exp_ne_top hq₀q₁.ne ht hq)).mpr
    ((exp_gt_iff ht hq₀ hq₁ hq₀q₁.ne hq).mpr hq₀q₁)

lemma preservation_inequality_of_lt₁ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₀q₁ : q₀ < q₁)
    (hq₁' : q₁ ≠ ⊤) :
    q.toReal < q₁.toReal :=
  (toReal_lt_toReal (interp_exp_ne_top hq₀q₁.ne ht hq) hq₁').mpr
    ((exp_lt_iff₁ ht hq₀ hq₁ hq₀q₁.ne hq).mpr hq₀q₁)

lemma ζ_pos_toReal_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) : (0 < ζ p₀ q₀ p₁ q₁ t.toReal) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [ζ_equality₃ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_pos_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_pos_toReal_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    (0 < ζ p₀ q₀ p₁ q₁ t.toReal) ↔
    ((q.toReal < q₁.toReal) ∧ (p.toReal < p₁.toReal)) ∨
    ((q₁.toReal < q.toReal) ∧ (p₁.toReal < p.toReal)) := by
  rw [ζ_equality₄ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_pos_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_pos_iff_aux₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (0 < ζ p₀ q₀ p₁ q₁ t.toReal) ↔
    q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal ∨
    q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal := by
  unfold ζ
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg,
      neg_mul_eq_mul_neg, mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos]
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
    (0 < ζ p₀ q₀ p₁ q₁ t.toReal) ↔
    ((q₁ < q₀) ∧ (p₁ < p₀)) ∨ ((q₀ < q₁) ∧ (p₀ < p₁)) := by
  rw [ζ_pos_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁,
    inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
    inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_pos_iff' (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) :
    0 < ζ p₀ q₀ p₁ q₁ t.toReal ↔ (q < q₀ ∧ p < p₀) ∨ (q₀ < q ∧ p₀ < p) := by
  rw [ζ_pos_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁,
    ← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq,
    ← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_pos_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    0 < ζ p₀ q₀ p₁ q₁ t.toReal ↔ q₀ < q := by
  rw [ζ_pos_iff' ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ hp₀p₁'.ne hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_pos_iff_of_lt₁ {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
  (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    0 < ζ p₀ q₀ p₁ q₁ t.toReal ↔ q < q₁ := by
  rw [← exp_gt_exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_pos_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_neg_iff_aux₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (ζ p₀ q₀ p₁ q₁ t.toReal) < 0 ↔
      q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal ∨
      q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal := by
  unfold ζ
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos]
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁

lemma ζ_neg_iff (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔ q₁ < q₀ ∧ p₀ < p₁ ∨ q₀ < q₁ ∧ p₁ < p₀ := by
  rw [ζ_neg_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁, inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
    inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_neg_iff' (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔ (q < q₀ ∧ p₀ < p) ∨ (q₀ < q ∧ p < p₀) := by
  rw [ζ_neg_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁, ← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp,
    ← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq, ← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp,
    ← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_neg_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔ q < q₀ := by
  rw [ζ_neg_iff' ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ hp₀p₁'.ne hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_neg_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔ q₁ < q := by
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
  · simp only [sub_pos]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma ζ_neg_toReal_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔
      (q.toReal < q₀.toReal ∧ p₀.toReal < p.toReal) ∨
      (q₀.toReal < q.toReal ∧ p.toReal < p₀.toReal) := by
  rw [ζ_equality₃ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_neg_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_neg_toReal_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔
      (q.toReal < q₁.toReal ∧ p₁.toReal < p.toReal) ∨
      (q₁.toReal < q.toReal ∧ p.toReal < p₁.toReal) := by
  rw [ζ_equality₄ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_neg_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_neg_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    ζ p₀ q₀ p₁ q₁ t.toReal < 0 ↔ (q < q₀ ∧ p₀ < p) ∨ (q₀ < q ∧ p < p₀) := by
  rw [ζ_neg_toReal_iff₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀',
    preservation_inequality ht hq₀q₁ hq hq₀', preservation_inequality ht hp₀p₁ hp hp₀',
    preservation_inequality' ht hq₀q₁ hq hq₀', preservation_inequality' ht hp₀p₁ hp hp₀']

lemma ζ_ne_zero (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal ≠ 0 := by
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
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal ≤ 0 ↔ q < q₀ := by
  constructor <;> intro h
  · rcases (Decidable.lt_or_eq_of_le h) with ζ_lt_0 | ζ_eq_0
    · exact (ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mp ζ_lt_0
    · exact False.elim <| (ζ_ne_zero ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁) ζ_eq_0
  · exact ((ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mpr h).le

lemma ζ_le_zero_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁)
    (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    ζ p₀ q₀ p₁ q₁ t.toReal ≤ 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_le_zero_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

private lemma one_sub_ioo_toReal {t : ℝ≥0∞} (ht : t ∈ Ioo 0 1) :
    (1 - t).toReal = 1 - t.toReal := by
  have ht1 : t ≤ 1 := ht.2.le
  cases t
  · trivial
  · rw [ENNReal.toReal_sub_of_le] <;> simp [*]

lemma eq_exponents₀ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal + q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₀.toReal)) = (1 - t).toReal * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) =
        q.toReal * ((1 - t).toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
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
        rw [one_sub_ioo_toReal ht]
        ring
    rw [this, mul_div_assoc, mul_div_cancel_right₀]
    · ring
    exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₂ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal / p₀.toReal + p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₀.toReal)) = (1 - t).toReal * p₀⁻¹.toReal * q.toReal := by
  rw [div_eq_inv_mul, mul_div_assoc, mul_assoc, toReal_inv, ← mul_add, mul_comm_div,
    ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) =
        q.toReal * ((1 - t).toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
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
        rw [one_sub_ioo_toReal ht]
        ring
    rw [this, mul_div_assoc, mul_div_cancel_right₀]
    · ring
    · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₁ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) = - t.toReal * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : q₀⁻¹.toReal * (q.toReal - q₀.toReal) = - t.toReal * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
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
      rw [preservation_interpolation ht hq₀ hq₁ hq, one_sub_ioo_toReal ht]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

-- TODO: simplify these proofs with statements above
lemma eq_exponents₃ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) =
      - t.toReal * p₁⁻¹.toReal * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : (p₁⁻¹.toReal * q₀⁻¹.toReal) * (q.toReal - q₀.toReal) =
      - t.toReal * p₁⁻¹.toReal * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
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
      rw [preservation_interpolation ht hq₀ hq₁ hq, one_sub_ioo_toReal ht]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₄ :
    q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) = - (q₀⁻¹.toReal / (q₀⁻¹.toReal - q₁⁻¹.toReal)) := calc
  _ = - (q₀⁻¹.toReal * (-(q₁⁻¹.toReal - q₀⁻¹.toReal)⁻¹)) := by
    rw [div_eq_mul_inv]; ring
  _ = _ := by congr; rw [neg_inv, neg_sub]

lemma eq_exponents₅ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    (q₁.toReal + -(q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal)))
      = t.toReal * q.toReal := by
  rw [eq_exponents₄, neg_mul, neg_neg, eq_exponents₀ (mem_sub_Ioo one_ne_top ht) hq₁ hq₀ hq₀q₁.symm
    (switch_exponents ht hq) hq₁', one_sub_one_sub_eq ht]

lemma eq_exponents₆ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) = (1 - t).toReal * q.toReal := by
  rw [← neg_neg (a := q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)), ← eq_exponents₄, neg_mul,
    eq_exponents₁ (mem_sub_Ioo one_ne_top ht) hq₁ hq₀ hq₀q₁.symm (switch_exponents ht hq) hq₁',
    neg_mul, neg_neg]

lemma eq_exponents₇ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    q₁.toReal / p₁.toReal + -(p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
    (q.toReal - q₁.toReal)) =
    t.toReal * p₁⁻¹.toReal * q.toReal := by
  rw [div_eq_mul_inv, toReal_inv]
  calc
  _ = p₁.toReal⁻¹ * (q₁.toReal + - (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₁.toReal))) := by ring
  _ = _ := by
    rw [eq_exponents₅ (ht := ht)] <;> try assumption
    ring

lemma eq_exponents₈ (ht : t ∈ Ioo 0 1) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) =
    (1 - t).toReal * p₀⁻¹.toReal * q.toReal := calc
  _ = p₀⁻¹.toReal * (q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal)) := by ring
  _ = _ := by
    rw [eq_exponents₆] <;> try assumption
    ring

end ComputationsChoiceExponent
