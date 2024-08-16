import Carleson.WeakType
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Sign

noncomputable section

section computations_pq

open ENNReal Real Set

variable {p q t : ℝ}

lemma preservation_positivity  (hp : p > 0) (hq : q > 0) (ht : t ∈ Ioo 0 1) :
  0 < (1 - t) * p⁻¹ + t * q⁻¹ :=
  add_pos (mul_pos (sub_pos.mpr ht.2) (inv_pos_of_pos hp))
      (mul_pos ht.1 (inv_pos_of_pos hq))

lemma ENNReal_preservation_positivity {p q : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (hpq : p ≠ q) :
    0 < (1 - ENNReal.ofReal t) * p⁻¹ + (ENNReal.ofReal t) * q⁻¹ := by
  have t_mem : ENNReal.ofReal t ∈ Ioo 0 1 := by
    refine ⟨ofReal_pos.mpr ht.1, ?_⟩
    rw [← ENNReal.ofReal_one]; exact (ofReal_lt_ofReal_iff zero_lt_one).mpr ht.2
  cases (lt_or_gt_of_ne hpq) <;> rename_i dir
  · apply Left.add_pos_of_pos_of_nonneg
    · refine mul_pos ?_ ?_
      · apply (ne_of_gt)
        · apply tsub_pos_of_lt t_mem.2
      · exact ENNReal.inv_ne_zero.mpr (LT.lt.ne_top dir)
    · exact zero_le _
  · apply Right.add_pos_of_nonneg_of_pos
    · exact zero_le _
    · refine mul_pos ?_ ?_
      · apply ne_of_gt (ofReal_pos.mpr ht.1)
      · refine ENNReal.inv_ne_zero.mpr (LT.lt.ne_top dir)

lemma ENNReal_preservation_positivity' {p p₀ p₁ : ℝ≥0∞} (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : p > 0 := by
  apply inv_lt_top.mp
  rw [hp]
  apply Ne.lt_top
  refine add_ne_top.mpr ⟨?_, ?_⟩
  · refine mul_ne_top ?_ ?_
    · exact Ne.symm (ne_of_beq_false rfl)
    · refine inv_ne_top.mpr (ne_of_gt hp₀)
  · refine mul_ne_top ?_ ?_
    · exact coe_ne_top
    · refine inv_ne_top.mpr (ne_of_gt hp₁)

lemma interp_exp_ne_top {p p₀ p₁ : ℝ≥0∞} (hp₀p₁ : p₀ ≠ p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : p ≠ ⊤ := by
  refine ENNReal.inv_ne_zero.mp ?_
  rw [hp]
  apply ne_of_gt
  apply ENNReal_preservation_positivity ht hp₀p₁

lemma interp_exp_lt_top {p p₀ p₁ : ℝ≥0∞} (hp₀p₁ : p₀ ≠ p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top hp₀p₁ ht hp



-- lemma test_bijection :
--     Function.Bijective (fun x : ℝ≥0∞ ↦ x⁻¹) := by
--   refine Function.Involutive.bijective ?h
--   unfold Function.Involutive
--   intro x
--   simp only
--   exact inv_inv x

-- lemma test_bijection' {p q : ℝ≥0∞} :
--     (fun x : ℝ≥0∞ ↦ x⁻¹) '' (Ioo p q) = Ioo q⁻¹ p⁻¹ := by
--   unfold Set.image
--   ext x
--   simp only [mem_Ioo, mem_setOf_eq]
--   constructor
--   · intro h
--     rcases h with ⟨a, ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩
--     refine ⟨?_, ?_⟩
--     · rw [← ha₃]
--       exact ENNReal.inv_lt_inv' ha₂
--     · rw [← ha₃]
--       exact ENNReal.inv_lt_inv' ha₁
--   · intro ⟨h₁, h₂⟩
--     exists x⁻¹
--     refine ⟨⟨?_, ?_⟩, ?_⟩
--     · exact lt_inv_iff_lt_inv.mp h₂
--     · exact inv_lt_iff_inv_lt.mp h₁
--     · exact inv_inv x



-- lemma test' (a b: ℝ≥0∞) (hab : a < b) : ENNReal.toReal 1 = 1 := by rw?

-- lemma test'' {a b s t: ℝ≥0∞} (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1)
--   (hst : s < t) (hab : a < b) (hb : b ≠ ⊤) : (1 - s) * a + s * b < (1 - t) * a + t * b
--     := by
--   have := ht.2
--   refine (toReal_lt_toReal ?ha ?hb).mp ?_
--   · exact LT.lt.ne_top hab
--   · refine add_ne_top.mpr ⟨?_, ?_⟩
--     · apply mul_ne_top
--       · apply sub_ne_top
--         exact Ne.symm top_ne_one
--       · exact LT.lt.ne_top hab
--     · apply mul_ne_top
--       · exact LT.lt.ne_top ht.2
--       · exact hb
--   · have : s.toReal < t.toReal := by
--       refine toReal_strict_mono ?_ hst
--       exact LT.lt.ne_top ht.2
--     have : a.toReal < b.toReal := by
--       refine toReal_strict_mono ?_ hab
--       exact hb
--     have : 0 < t.toReal := by
--       refine toReal_pos (ne_of_gt ht.1) ?_
--       apply LT.lt.ne_top ht.2
--     have : 0 < s.toReal := by
--       refine toReal_pos (ne_of_gt hs.1) ?_
--       apply LT.lt.ne_top hs.2
--     have : t.toReal < 1 := by
--       refine toReal_lt_of_lt_ofReal ?_
--       rw [ofReal_one]
--       exact ht.2
--     have :s.toReal < 1 := by
--       refine toReal_lt_of_lt_ofReal ?_
--       rw [ofReal_one]
--       exact hs.2
--     rw [toReal_add, toReal_add, toReal_mul, toReal_mul, toReal_mul, toReal_mul, toReal_sub_of_le,
--         toReal_sub_of_le, one_toReal]


-- lemma interp_move_t {a b t: ℝ≥0∞} (ht : t ∈ Icc 0 1)
--   (hab : a ≤ b) (hb : b ≠ ⊤) : (1 - t) * a + t * b = a + t * (b - a)
--     := by
--   have := ht.2
--   have one_sub_t_le_one : 1 - t ≤ 1 := by
--     exact tsub_le_self
--   have t_ne_top : t ≠ ⊤ := by
--     apply (ne_of_lt)
--     apply lt_of_le_of_lt ht.2 one_lt_top
--   have one_sub_t_ne_top : 1 - t ≠ ⊤ := by
--     apply ne_of_lt
--     apply lt_of_le_of_lt one_sub_t_le_one one_lt_top
--   have a_ne_top : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
--   refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
--   · refine add_ne_top.mpr ⟨?_, ?_⟩
--     · apply mul_ne_top
--       · exact one_sub_t_ne_top
--       · exact ne_top_of_le_ne_top hb hab
--     · apply mul_ne_top
--       · exact t_ne_top
--       · exact hb
--   · refine add_ne_top.mpr ⟨?_, ?_⟩
--     · exact a_ne_top
--     · apply mul_ne_top
--       · exact t_ne_top
--       · exact sub_ne_top hb
--   · rw [toReal_add, toReal_add, toReal_mul, toReal_mul, toReal_mul, toReal_sub_of_le,
--         toReal_sub_of_le, one_toReal]; ring
--     · exact hab
--     · exact hb
--     · exact ht.2
--     · exact Ne.symm top_ne_one
--     · exact a_ne_top
--     · apply mul_ne_top
--       · exact t_ne_top
--       · exact sub_ne_top hb
--     · apply mul_ne_top
--       · exact one_sub_t_ne_top
--       · exact a_ne_top
--     · apply mul_ne_top
--       · exact t_ne_top
--       · exact hb




--   -- rw [ENNReal.sub_mul]
--   -- rw [ENNReal.mul_sub]
--   -- rw [one_mul]

-- lemma test_bijection'' {t a b : ℝ≥0∞} (hab : a < b) (hb : b ≠ ⊤) :
--     BijOn (fun t : ℝ≥0∞ ↦ (1 - t) * a + t * b) (Ioo 0 1) (Ioo a b) := by
--   have a_ne_top : a ≠ ⊤ := by exact LT.lt.ne_top hab
--   unfold BijOn
--   refine ⟨?_, ⟨?_, ?_⟩⟩
--   · intro t ⟨(ht₁ : t > 0), (ht₂ : t < 1)⟩
--     refine ⟨?_, ?_⟩
--     · simp only
--       have : a = (1 - t) * a + t * a := by
--         rw [← add_mul]
--         rw [@tsub_add_eq_max]
--         rw [max_eq_left_of_lt ht₂]
--         rw [one_mul]
--       nth_rw 1 [this]
--       gcongr
--       · apply mul_ne_top
--         · refine sub_ne_top ?_
--           exact Ne.symm top_ne_one
--         · exact LT.lt.ne_top hab
--       · exact LT.lt.ne_top ht₂
--     · simp only
--       have : b = (1 - t) * b + t * b := by
--         rw [← add_mul]
--         rw [@tsub_add_eq_max]
--         rw [max_eq_left_of_lt ht₂]
--         rw [one_mul]
--       nth_rw 2 [this]
--       gcongr
--       · apply mul_ne_top
--         · exact LT.lt.ne_top ht₂
--         · exact hb
--       · apply ne_of_gt
--         exact tsub_pos_of_lt ht₂
--       · apply sub_ne_top
--         exact Ne.symm top_ne_one
--   · refine StrictMonoOn.injOn ?refine_2.H
--     intro s hs t ht hst
--     simp only
--     rw [interp_move_t, interp_move_t]
--     gcongr
--     · exact a_ne_top
--     · apply ne_of_gt
--       exact tsub_pos_of_lt hab
--     · exact sub_ne_top hb
--     · exact mem_Icc_of_Ioo ht
--     · exact le_of_lt hab
--     · exact hb
--     · exact mem_Icc_of_Ioo hs
--     · exact le_of_lt hab
--     · exact hb
--   · unfold SurjOn
--     intro c hc
--     refine (mem_image (fun t ↦ (1 - t) * a + t * b) (Ioo 0 1) c).mpr ?_
--     use (c - a) / (b - a)
--     rw [interp_move_t]

-- lemma interp_bijective {p q : ℝ≥0∞} (hpq : p < q) :
--     BijOn (fun t : ℝ≥0∞ ↦ ((1 - t) * p⁻¹ + t * q⁻¹)⁻¹) (Ioo 0 1) (Ioo p q) := by
--   unfold BijOn
--   refine ⟨?_, ⟨?_, ?_⟩⟩
--   · intro t ht
--     simp only
--     refine ⟨?_, ?_⟩
--     · apply lt_inv_iff_lt_inv.mp
--       rw [ENNReal.sub_mul]



lemma interp_exp_between {p p₀ p₁ : ℝ≥0∞} (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : p ∈ Ioo p₀ p₁ := by
  refine ⟨?_, ?_⟩
  · apply ENNReal.inv_lt_inv.mp
    rw [hp]
    have : p₀⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₀⁻¹ := by
      rw [← add_mul]
      rw [@tsub_add_eq_max]
      rw [max_eq_left_of_lt]
      rw [one_mul]
      refine ofReal_lt_one.mpr ht.2
    nth_rw 2 [this]
    gcongr
    · apply mul_ne_top
      · apply sub_ne_top
        exact Ne.symm top_ne_one
      · refine inv_ne_top.mpr ?_
        apply (ne_of_gt hp₀)
    · exact Ne.symm (ne_of_lt (ofReal_pos.mpr ht.1))
    · exact coe_ne_top
  · apply ENNReal.inv_lt_inv.mp
    rw [hp]
    have : p₁⁻¹ = (1 - (ENNReal.ofReal t)) * p₁⁻¹ + (ENNReal.ofReal t) * p₁⁻¹ := by
      rw [← add_mul]
      rw [@tsub_add_eq_max]
      rw [max_eq_left_of_lt]
      rw [one_mul]
      refine ofReal_lt_one.mpr ht.2
    nth_rw 1 [this]
    gcongr
    · apply mul_ne_top
      · exact coe_ne_top
      · refine inv_ne_top.mpr ?_
        apply (ne_of_gt hp₁)
    · apply ne_of_gt
      refine tsub_pos_iff_lt.mpr ?_
      refine ofReal_lt_one.mpr ht.2
    · exact coe_ne_top

lemma one_le_interp_exp_aux {p p₀ p₁ : ℝ≥0∞} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : 1 ≤ p := by
  apply le_of_lt
  apply (lt_of_le_of_lt hp₀ _)
  refine (interp_exp_between (lt_of_lt_of_le zero_lt_one hp₀) (lt_of_lt_of_le zero_lt_one hp₁) hp₀p₁ ht hp).1

lemma switch_exponents {p p₀ p₁ : ℝ≥0∞} (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) :
    p⁻¹ = (1 - ENNReal.ofReal (1 - t)) * p₁⁻¹ + ENNReal.ofReal (1 - t) * p₀⁻¹ := by
  have : (1 - t) ∈ Ioo 0 1 := by exact Ioo.one_sub_mem ht
  rw [add_comm, ← ofReal_one, ← ofReal_sub, _root_.sub_sub_cancel, ofReal_sub, ofReal_one]
  · exact hp
  · exact (le_of_lt ht.1)
  · exact (le_of_lt this.1)

lemma one_le_toReal {a : ℝ≥0∞} (ha₁ : 1 ≤ a) (ha₂ : a < ⊤) : 1 ≤ a.toReal := by
  exact toReal_mono (LT.lt.ne_top ha₂) ha₁

lemma one_le_interp {p p₀ p₁ : ℝ≥0∞} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : 1 ≤ p := by
  rcases (lt_or_gt_of_ne hp₀p₁) with p₀lt_p₁ | p₁lt_p₀
  · exact one_le_interp_exp_aux hp₀ hp₁ p₀lt_p₁ ht hp
  · have : (1 - t) ∈ Ioo 0 1 := by exact Ioo.one_sub_mem ht
    apply one_le_interp_exp_aux hp₁ hp₀ p₁lt_p₀ this
    apply switch_exponents ht hp

lemma one_le_interp_toReal {p p₀ p₁ : ℝ≥0∞} (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : 1 ≤ p.toReal := by
  apply one_le_toReal
  · exact one_le_interp hp₀ hp₁ hp₀p₁ ht hp
  · apply Ne.lt_top
    apply interp_exp_ne_top hp₀p₁ ht hp

lemma ENNReal_preservation_positivity_real {p p₀ p₁ : ℝ≥0∞} (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) : p.toReal > 0 := by
  refine toReal_pos ?_ ?_
  · exact (ne_of_gt (ENNReal_preservation_positivity' hp₀ hp₁ hp))
  · exact interp_exp_ne_top hp₀p₁ ht hp

end computations_pq


noncomputable section
section tools

open Real ENNReal Set

lemma coe_pow_ne_top {a : ℝ} {q : ℝ} (hq : q ≥ 0): ENNReal.ofReal a ^ q ≠ ⊤ := by
  refine rpow_ne_top_of_nonneg hq coe_ne_top

-- Note this lemma can directly be applied to elements of `ℝ≥0` as well
lemma coe_pow_ne_top' {a : ℝ} {q : ℝ} (hq : q ≥ 1): ENNReal.ofReal a ^ q ≠ ⊤ := by
  exact coe_pow_ne_top (le_trans zero_le_one hq)

lemma coe_pow_pos {a : ℝ} {q : ℝ} (ha : a > 0) : ENNReal.ofReal a ^ q > 0 := by
  refine ENNReal.rpow_pos (ofReal_pos.mpr ha) coe_ne_top

lemma rpow_ne_top' {a : ℝ≥0∞} {q : ℝ} (ha : a ≠ 0) (ha' : a ≠ ⊤)  : a ^ q ≠ ⊤ := by
  intro h
  have : a = 0 ∧ q < 0 ∨ a = ⊤ ∧ 0 < q := ENNReal.rpow_eq_top_iff.mp h
  rcases this with ⟨a_zero, _⟩ | ⟨a_top, _⟩
  · exact False.elim (ha a_zero)
  · exact False.elim (ha' a_top)

lemma exp_toReal_pos' {q : ℝ≥0∞} (hq : q ≥ 1) (hq' : q < ⊤) : q.toReal > 0 := by
  refine toReal_pos ?_ ?_
  · apply ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  · exact LT.lt.ne_top hq'

lemma ne_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q ≠ ⊤ := LT.lt.ne_top hq.2

lemma lt_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q < ⊤ := Ne.lt_top (ne_top_of_Ico hq)

lemma ne_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ ⊤ := LT.lt.ne_top hq.2

lemma lt_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q < ⊤ := Ne.lt_top (ne_top_of_Ioo hq)

lemma exp_toReal_ne_zero {q : ℝ≥0∞} (hq : q ≥ 1) (hq' : q < ⊤) : q.toReal ≠ 0 := by
  apply ne_of_gt
  apply exp_toReal_pos' <;> assumption

lemma exp_toReal_ne_zero_of_Ico {q p : ℝ≥0∞} (hq : q ∈ Ico 1 p) : q.toReal ≠ 0 :=
  exp_toReal_ne_zero hq.1 (lt_top_of_Ico hq)

lemma pos_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q > 0 := pos_of_gt hq.1

lemma ne_zero_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ 0 := ne_of_gt (pos_of_gt hq.1)

lemma pos_of_Icc_1 {p q : ℝ≥0∞} (hp : p ∈ Icc 1 q) : p > 0 := lt_of_lt_of_le zero_lt_one hp.1

lemma pos_of_ge_1 {p : ℝ≥0∞} (hp : 1 ≤ p) : p > 0 := lt_of_lt_of_le zero_lt_one hp

lemma pos_rb_of_Icc_1_inh {p q : ℝ≥0∞} (hp : p ∈ Icc 1 q) : q > 0 :=
  lt_of_lt_of_le zero_lt_one (le_trans hp.1 hp.2)

lemma toReal_pos_of_Ioo {q p r : ℝ≥0∞} (hp : p ∈ Ioo q r) : p.toReal > 0 :=
  toReal_pos (ne_zero_of_lt hp.1) (LT.lt.ne_top hp.2)

lemma toReal_ne_zero_of_Ioo {q p r : ℝ≥0∞} (hp : p ∈ Ioo q r) : p.toReal ≠ 0 :=
  toReal_ne_zero.mpr ⟨ne_zero_of_lt hp.1, LT.lt.ne_top hp.2⟩

-- TODO : decide if this is wanted
-- local instance : Coe ℝ ℝ≥0∞ where
--   coe x := ENNReal.ofReal x

end tools

end

section computations

open Real Set

variable {p₀ q₀ p₁ q₁ p q t : ℝ} (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
  (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
  (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)

def σ :=
  (((1 - t) * p₀⁻¹ + t * p₁⁻¹) * (q₁⁻¹ - q₀⁻¹)) / (((1 - t) * q₀⁻¹ + t * q₁⁻¹) * (p₁⁻¹ - p₀⁻¹))

lemma inv_of_interpolated_pos : 0 < p⁻¹ := by
  rw [hp]; exact preservation_positivity hp₀ hp₁ ht

lemma interpolated_pos : 0 < p :=
  inv_pos.mp (inv_of_interpolated_pos hp₀ hp₁ ht hp)


lemma ne_exponents : q ≠ q₀ := by
  have obs : q⁻¹ ≠ q₀⁻¹ := by
    rw [hq, ← sub_ne_zero, sub_mul, one_mul, add_comm_sub, add_sub_cancel_left, ← mul_sub]
    exact mul_ne_zero (ne_of_gt ht.1) (sub_ne_zero_of_ne (Ne.symm (fun h ↦ hq₀q₁ (inv_inj.mp h))))
  exact fun h ↦ obs (inv_inj.mpr h)

lemma σ_equality_1 :
    @σ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹ + t * p₁⁻¹) * ((1 - t) * q₀⁻¹ + t * q₁⁻¹ - q₀⁻¹)) /
    (((1 - t) * q₀⁻¹ + t * q₁⁻¹) * ((1 - t) * p₀⁻¹ + t * p₁⁻¹ - p₀⁻¹)) := by
  unfold σ
  have t_pos : 0 < t := ht.1
  rw [← mul_div_mul_right _ _ (ne_of_gt t_pos), mul_assoc _ _ t, mul_assoc _ _ t]
  congr <;> ring

lemma σ_equality_2 :
    @σ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹ + t * p₁⁻¹) * ((1 - t) * q₀⁻¹ + t * q₁⁻¹ - q₁⁻¹)) /
    (((1 - t) * q₀⁻¹ + t * q₁⁻¹) * ((1 - t) * p₀⁻¹ + t * p₁⁻¹ - p₁⁻¹)) := by
  unfold σ
  have : - (1 - t) < 0 := neg_neg_iff_pos.mpr (sub_pos.mpr ht.2)
  rw [← mul_div_mul_right _ _ (ne_of_lt this), mul_assoc _ _ (-(1 - t)), mul_assoc _ _ (-(1 - t))]
  congr <;> ring

lemma σ_symm :
    @σ p₀ q₀ p₁ q₁ t = @σ p₁ q₁ p₀ q₀ (1 - t) := by
  unfold σ
  rw [← mul_div_mul_right (c := - 1), mul_assoc _ _ (-1), mul_assoc _ _ (-1)]; swap; positivity
  simp only [mul_neg, mul_one, neg_sub, _root_.sub_sub_cancel]
  nth_rewrite 1 [add_comm]; nth_rw 2 [add_comm]

lemma σ_equality_4 :
    @σ p₀ q₀ p₁ q₁ t =
    (p₀ * (q₀ - q)) / (q₀ * (p₀ - p)) := by
  rw [σ_equality_1 ht, ← hp, ← hq]
  have t_pos : 0 < t := ht.1
  have ineq : 0 < 1 - t := (Ioo.one_sub_mem ht).1
  have q_inv_pos : 0 < q⁻¹ := by rw [hq]; positivity
  have p_inv_pos : 0 < p⁻¹ := by rw [hp]; positivity
  have q_pos : 0 < q := by exact inv_pos.mp q_inv_pos
  have p_pos : 0 < p := by exact inv_pos.mp p_inv_pos
  have hne : p * q * p₀ * q₀ ≠ 0 := by positivity
  rw [← mul_div_mul_right _ _ hne]
  have eq₁ : p⁻¹ * (q⁻¹ - q₀⁻¹) * (p * q * p₀ * q₀) =
      p₀ * (p⁻¹ * p) * ((q⁻¹ * q) * q₀ - (q₀⁻¹ * q₀) * q) := by ring
  have eq₂ : q⁻¹ * (p⁻¹ - p₀⁻¹) * (p * q * p₀ * q₀) =
      q₀ * (q⁻¹ * q) * ((p⁻¹ * p) * p₀ - (p₀⁻¹ * p₀) * p) := by ring
  rw [eq₁, eq₂, inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, inv_mul_cancel] <;> try positivity
  simp only [mul_one, one_mul]

lemma σ_equality_5 :
    @σ p₀ q₀ p₁ q₁ t =
    (p₁ * (q₁ - q)) / (q₁ * (p₁ - p)) := by
  rw [σ_symm]
  have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
  rw [σ_equality_4 hp₁ hq₁ hp₀ hq₀ one_sub_mem]
  · rw [hp]; ring
  · rw [hq]; ring

lemma σ_equality_6 :
    p₀ + (@σ p₀ q₀ p₁ q₁ t)⁻¹ * (q - q₀) * (p₀ / q₀) = p := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  simp only [inv_div]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  have : q₀ - q ≠ 0 := sub_ne_zero_of_ne (id (Ne.symm (ne_exponents ht hq₀q₁ hq)))
  calc
  _ = p₀ - (q₀⁻¹ * q₀) * (p₀ - p) * (p₀⁻¹ * p₀) * ((q₀ - q)⁻¹ * (q₀ - q)) := by ring
  _ = _ := by
    rw [inv_mul_cancel (ne_of_gt hq₀), inv_mul_cancel (ne_of_gt hp₀),
        inv_mul_cancel (by positivity)]; ring

lemma σ_pos_iff_aux : ( 0 < p₀ * (q₀ - q) / (q₀ * (p₀ - p))) ↔
    ((q - q₀ < 0) ∧ (p - p₀ < 0)) ∨ ((0 < q - q₀) ∧ (0 < p - p₀))  := by
  rw [div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  -- from here, field_simp would also work
  rw [mul_pos_iff_of_pos_left hp₀, mul_pos_iff_of_pos_left hp₀,
      mul_pos_iff_of_pos_left hq₀, mul_pos_iff_of_pos_left hq₀, neg_sub, neg_sub]
  simp only [sub_pos, sub_neg]

lemma σ_pos_iff₀ : (0 < @σ p₀ q₀ p₁ q₁ t) ↔
    ((q - q₀ < 0) ∧ (p - p₀ < 0)) ∨ ((0 < q - q₀) ∧ (0 < p - p₀)) := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_pos_iff_aux hp₀ hq₀

lemma σ_pos_iff₁ : (0 < @σ p₀ q₀ p₁ q₁ t) ↔
    ((q - q₁ < 0) ∧ (p - p₁ < 0)) ∨ ((0 < q - q₁) ∧ (0 < p - p₁)) := by
  rw [σ_equality_5 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_pos_iff_aux hp₁ hq₁

lemma σ_neg_iff_aux : (p₀ * (q₀ - q) / (q₀ * (p₀ - p)) < 0) ↔
    ((q - q₀ < 0) ∧ (0 < p - p₀)) ∨ ((0 < q - q₀) ∧ (p - p₀ < 0)) := by
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  -- field_simp
  rw [mul_pos_iff_of_pos_left hp₀, mul_pos_iff_of_pos_left hp₀,
      mul_pos_iff_of_pos_left hq₀, mul_pos_iff_of_pos_left hq₀, neg_sub, neg_sub]
  simp only [sub_pos, sub_neg]

lemma σ_neg_iff₀ : (@σ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q - q₀ < 0) ∧ (0 < p - p₀)) ∨ ((0 < q - q₀) ∧ (p - p₀ < 0)) := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_neg_iff_aux hp₀ hq₀

lemma σ_neg_iff₁ : (@σ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q - q₁ < 0) ∧ (0 < p - p₁)) ∨ ((0 < q - q₁) ∧ (p - p₁ < 0)) := by
  rw [σ_equality_5 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_neg_iff_aux hp₁ hq₁

-- TODO: there is some dependence on hp which is unnecessary, but should it be removed?
lemma σ_ne_zero : (@σ p₀ q₀ p₁ q₁ t ≠ 0) := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero (ne_of_gt hp₀) ?_
    refine sub_ne_zero_of_ne (Ne.symm ?_)
    exact ne_exponents ht hq₀q₁ hq
  · refine mul_ne_zero (ne_of_gt hq₀) ?_
    refine sub_ne_zero_of_ne (Ne.symm ?_)
    exact ne_exponents ht hp₀p₁ hp

-- hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1

end computations

section sigma_ENNReal

open ENNReal Real Set

variable {p₀ q₀ p₁ q₁ p q : ℝ≥0∞} {t : ℝ} (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
  (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹)

def ζ := (((1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal) * ((q₁⁻¹).toReal - (q₀⁻¹).toReal)) /
        (((1 - t) * (q₀⁻¹).toReal + t * (q₁⁻¹).toReal) * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))


lemma coe_inv_exponent : ENNReal.ofReal (p₀⁻¹.toReal) = p₀⁻¹ := by
  refine ofReal_toReal_eq_iff.mpr ?_
  refine inv_ne_top.mpr ?_
  apply ne_of_gt hp₀

lemma inv_of_interpolated_pos' : 0 < p⁻¹ := by
  refine ENNReal.inv_pos.mpr ?_
  exact interp_exp_ne_top hp₀p₁ ht hp

-- TODO: remove, this is redundant, but for now mirror the development for reals...
lemma interpolated_pos' : 0 < p := by
  exact ENNReal_preservation_positivity' hp₀ hp₁ hp

lemma exp_toReal_pos (hp₀' : p₀ ≠ ⊤) : 0 < p₀.toReal := by
  refine toReal_pos (ne_of_gt hp₀) hp₀'



-- lemma ne_toReal_exponents : (q₀.toReal ≠ q.toReal) := by
--   rcases (eq_or_ne q₀ ⊤) with q₀eq_top | q₀ne_top
--   · rw [(toReal_eq_zero_iff q₀).mpr (Or.inr q₀eq_top)]
--     exact ne_of_lt (ENNReal_preservation_positivity_real hq₀ hq₁ hq₀q₁ ht hq)
--   · intro h
--     have eq : ENNReal.ofReal (q₀.toReal) = ENNReal.ofReal (q.toReal) := by
--       exact congrArg ENNReal.ofReal h
--     have coe_q : ENNReal.ofReal (q.toReal) = q :=
--       ofReal_toReal_eq_iff.mpr (interp_exp_ne_top hq₀q₁ ht hq)
--     have coe_q₀ : ENNReal.ofReal (q₀.toReal) = q₀ := by
--       refine ofReal_toReal_eq_iff.mpr q₀ne_top
--     rw [coe_q, coe_q₀] at eq



lemma interp_exp_toReal_pos : 0 < p.toReal := by
  refine toReal_pos ?_ ?_
  · refine ne_of_gt (interpolated_pos' hp₀ hp₁ hp)
  · exact interp_exp_ne_top hp₀p₁ ht hp

lemma preservation_interpolation :
    p⁻¹.toReal = (1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal := by
  rw [← one_toReal]
  have : ENNReal.toReal (ENNReal.ofReal t) = t := toReal_ofReal (le_of_lt ht.1)
  rw [← this]
  rw [← ENNReal.toReal_sub_of_le]
  · rw [← toReal_mul, ← toReal_mul, ← toReal_add]
    · exact congrArg ENNReal.toReal hp
    · apply mul_ne_top
      · apply sub_ne_top
        exact Ne.symm top_ne_one
      · refine inv_ne_top.mpr (ne_of_gt hp₀)
    · apply mul_ne_top
      · exact coe_ne_top
      · refine inv_ne_top.mpr (ne_of_gt hp₁)
  · exact ofReal_le_one.mpr (le_of_lt ht.2)
  · exact Ne.symm top_ne_one

lemma preservation_positivity_inv_toReal :
    0 < (1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal := by
  rcases (eq_or_ne p₀ ⊤) with p₀eq_top | p₀ne_top
  · rw [p₀eq_top]
    simp only [inv_top, zero_toReal, mul_zero, zero_add]
    apply Real.mul_pos
    · exact ht.1
    · rw [toReal_inv]
      apply inv_pos_of_pos
      refine exp_toReal_pos hp₁ ?_
      rw [p₀eq_top] at hp₀p₁
      exact Ne.symm hp₀p₁
  · apply add_pos_of_pos_of_nonneg
    · apply Real.mul_pos
      · exact (Ioo.one_sub_mem ht).1
      · rw [toReal_inv]
        apply inv_pos_of_pos
        exact exp_toReal_pos hp₀ p₀ne_top
    · apply mul_nonneg
      · exact le_of_lt ht.1
      · exact toReal_nonneg

lemma ne_inv_toReal_exponents : (p₀⁻¹.toReal ≠ p₁⁻¹.toReal) := by
  intro h
  apply hp₀p₁
  rw [← inv_inv p₀, ← inv_inv p₁]
  apply congrArg Inv.inv
  have coe_p₀ : ENNReal.ofReal (p₀⁻¹).toReal = p₀⁻¹ :=
    ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr (ne_of_gt hp₀))
  have coe_p₁ : ENNReal.ofReal (p₁⁻¹).toReal = p₁⁻¹ :=
    ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr (ne_of_gt hp₁))
  rw [← coe_p₀, ← coe_p₁]
  exact congrArg ENNReal.ofReal h

lemma ne_inv_toReal_exp_interp_exp : (p₀⁻¹.toReal ≠ p⁻¹.toReal) := by
  rw [preservation_interpolation ht hp₀ hp₁ hp]
  rw [← sub_ne_zero, _root_.sub_mul, one_mul, add_comm_sub, sub_add_eq_sub_sub, sub_self, zero_sub]
  rw [neg_sub, ← _root_.mul_sub]
  apply mul_ne_zero
  · exact ne_of_gt ht.1
  · refine sub_ne_zero_of_ne ?_
    exact ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁

lemma ne_sub_toReal_exp : p₁⁻¹.toReal - p₀⁻¹.toReal ≠ 0 := by
  apply sub_ne_zero_of_ne
  apply Ne.symm
  apply ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁

lemma ne_toReal_exp_interp_exp : p₀.toReal ≠ p.toReal := by
  intro h
  apply ne_inv_toReal_exp_interp_exp ht hp₀ hp₁ hp₀p₁ hp
  rw [toReal_inv, toReal_inv]
  apply congrArg Inv.inv h

lemma exp_lt_iff : p < p₀ ↔ p₁ < p₀ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · constructor
    · intro h
      exact False.elim <| not_le_of_gt h (le_of_lt (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1)
    · intro h
      exact False.elim <| not_le_of_gt h (le_of_lt p₀lt_p₁)
  · have hp' := switch_exponents ht hp
    constructor
    · intro h
      exact p₁lt_p₀
    · intro h
      exact (interp_exp_between hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) hp').2

lemma exp_gt_iff : p₀ < p ↔ p₀ < p₁ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun _ ↦ p₀lt_p₁, fun _ ↦ (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1⟩
  · exact ⟨fun h ↦ False.elim <| not_le_of_gt h (le_of_lt
        (interp_exp_between hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)).2),
        fun h ↦ False.elim <| not_le_of_gt h (le_of_lt p₁lt_p₀)⟩

lemma exp_lt_exp_gt_iff : p < p₀ ↔ p₁ < p := by
  rw [exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  rw [← exp_gt_iff (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁) (switch_exponents ht hp)]

lemma exp_gt_exp_lt_iff : p₀ < p ↔ p < p₁ := by
  rw [exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp]
  rw [← exp_lt_iff (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁) (switch_exponents ht hp)]

lemma exp_lt_iff₁ : p < p₁ ↔ p₀ < p₁ := by
  rw [← exp_gt_exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp

lemma exp_gt_iff₁ : p₁ < p ↔ p₁ < p₀ := by
  rw [← exp_lt_exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp

lemma ζ_equality_1 :
    @ζ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal) * ((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal) * ((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal - p₀⁻¹.toReal)) := by
  unfold ζ
  have t_pos : 0 < t := ht.1
  rw [← mul_div_mul_right _ _ (ne_of_gt t_pos), mul_assoc _ _ t, mul_assoc _ _ t]
  congr <;> ring

lemma ζ_equality_2 :
    @ζ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal) * ((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal - q₁⁻¹.toReal)) /
    (((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal) * ((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal - p₁⁻¹.toReal)) := by
  unfold ζ
  have : - (1 - t) < 0 := neg_neg_iff_pos.mpr (sub_pos.mpr ht.2)
  rw [← mul_div_mul_right _ _ (ne_of_lt this), mul_assoc _ _ (-(1 - t)), mul_assoc _ _ (-(1 - t))]
  congr <;> ring

lemma ζ_symm :
    @ζ p₀ q₀ p₁ q₁ t = @ζ p₁ q₁ p₀ q₀ (1 - t) := by
  unfold ζ
  rw [← mul_div_mul_right (c := - 1), mul_assoc _ _ (-1), mul_assoc _ _ (-1)]; swap; positivity
  simp only [mul_neg, mul_one, neg_sub, _root_.sub_sub_cancel]
  nth_rewrite 1 [add_comm]; nth_rw 2 [add_comm]

lemma ζ_equality_4 (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) :
  @ζ p₀ q₀ p₁ q₁ t = (p₀.toReal * (q₀.toReal - q.toReal))  / (q₀.toReal * (p₀.toReal - p.toReal)) := by
  rw [ζ_equality_1 ht, ← preservation_interpolation, ← preservation_interpolation]
  have q_pos : 0 < q := interpolated_pos' hq₀ hq₁ hq
  have p_pos : 0 < p := interpolated_pos' hp₀ hp₁ hp
  have hne : p.toReal * q.toReal * p₀.toReal * q₀.toReal > 0 := by
    refine mul_pos ?_ ?_
    · refine mul_pos ?_ ?_
      · refine mul_pos ?_ ?_
        · exact interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp
        · exact interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq
      · exact exp_toReal_pos hp₀ hp₀'
    · exact exp_toReal_pos hq₀ hq₀'
  rw [← mul_div_mul_right _ _ (ne_of_gt hne)]
  have eq₁ : p⁻¹.toReal * (q⁻¹.toReal - q₀⁻¹.toReal) * (p.toReal * q.toReal * p₀.toReal * q₀.toReal) =
      p₀.toReal * (p⁻¹.toReal * p.toReal) * ((q⁻¹.toReal * q.toReal) * q₀.toReal - (q₀⁻¹.toReal * q₀.toReal) * q.toReal) := by ring
  have eq₂ : q⁻¹.toReal * (p⁻¹.toReal - p₀⁻¹.toReal) * (p.toReal * q.toReal * p₀.toReal * q₀.toReal) =
      q₀.toReal * (q⁻¹.toReal * q.toReal) * ((p⁻¹.toReal * p.toReal) * p₀.toReal - (p₀⁻¹.toReal * p₀.toReal) * p.toReal) := by ring
  rw [eq₁, eq₂, ← @toReal_mul q⁻¹ q, ← @toReal_mul p⁻¹ p, ← @toReal_mul p₀⁻¹ p₀, ← @toReal_mul q₀⁻¹ q₀]
  -- TODO: why can below goals not be discharged?
  · repeat rw [ENNReal.inv_mul_cancel] <;> try positivity
    rw [one_toReal]
    repeat rw [one_mul]
    repeat rw [mul_one]
    · assumption
    · assumption
    · apply interp_exp_ne_top hq₀q₁ ht hq
    · apply interp_exp_ne_top hp₀p₁ ht hp
  · exact ht
  · assumption
  · assumption
  · assumption
  · exact ht
  · assumption
  · assumption
  · assumption

lemma one_sub_coe_one_sub : (1 - ENNReal.ofReal (1 - t)) = ENNReal.ofReal t := by
  have := ht.2
  rw [← ofReal_one, ← ENNReal.ofReal_sub]
  congr
  · linarith
  · linarith

lemma coe_one_sub : ENNReal.ofReal (1 - t) = 1 - ENNReal.ofReal t := by
  rw [← ofReal_one, ← ENNReal.ofReal_sub]; exact (le_of_lt ht.1)

lemma ζ_equality_5 (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ ≠ ⊤) :
    @ζ p₀ q₀ p₁ q₁ t =
    (p₁.toReal * (q₁.toReal - q.toReal)) / (q₁.toReal * (p₁.toReal - p.toReal)) := by
  rw [ζ_symm]
  have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
  rw [ζ_equality_4 one_sub_mem] <;> try assumption
  · exact Ne.symm hp₀p₁
  · exact Ne.symm hq₀q₁
  · rw [hp, one_sub_coe_one_sub ht, coe_one_sub ht]; ring
  · rw [hq, one_sub_coe_one_sub ht, coe_one_sub ht]; ring

lemma ζ_equality_6 (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) :
    p₀.toReal + (@ζ p₀ q₀ p₁ q₁ t)⁻¹ * (q.toReal - q₀.toReal) * (p₀.toReal / q₀.toReal) = p.toReal := by
  rw [ζ_equality_4 ht] <;> try assumption
  simp only [inv_div]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  calc
  _ = p₀.toReal - (q₀.toReal⁻¹ * q₀.toReal) * (p₀.toReal - p.toReal) * (p₀.toReal⁻¹ * p₀.toReal) * ((q₀.toReal - q.toReal)⁻¹ * (q₀.toReal - q.toReal)) := by ring
  _ = _ := by
    rw [inv_mul_cancel, inv_mul_cancel, inv_mul_cancel]
    · simp only [one_mul, mul_one, _root_.sub_sub_cancel]
    · apply sub_ne_zero_of_ne
      exact ne_toReal_exp_interp_exp ht hq₀ hq₁ hq₀q₁ hq
    · refine ne_of_gt (exp_toReal_pos hp₀ hp₀')
    · refine ne_of_gt (exp_toReal_pos hq₀ hq₀')

lemma ζ_pos_iff_aux (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) :
    ( 0 < p₀.toReal * (q₀.toReal - q.toReal) / (q₀.toReal * (p₀.toReal - p.toReal))) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma preservation_inequality (hp₀' : p₀ ≠ ⊤) :
    p.toReal < p₀.toReal ↔ p < p₀ := by
  refine toReal_lt_toReal (interp_exp_ne_top hp₀p₁ ht hp) hp₀'

lemma preservation_inequality' (hp₀' : p₀ ≠ ⊤) :
    p₀.toReal < p.toReal ↔ p₀ < p := by
  exact toReal_lt_toReal hp₀' (interp_exp_ne_top hp₀p₁ ht hp)

lemma test' (a b : ℝ) : a - b < 0 ↔ a < b := by exact sub_neg

lemma ζ_pos_toReal_iff₀ (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨ ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [ζ_equality_4 ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_pos_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_pos_toReal_iff₁ (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ ≠ ⊤) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q.toReal < q₁.toReal) ∧ (p.toReal < p₁.toReal)) ∨ ((q₁.toReal < q.toReal) ∧ (p₁.toReal < p.toReal)) := by
  rw [ζ_equality_5 ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_pos_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_pos_iff_aux₀ : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal ∨
    q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal := by
  unfold ζ
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg,
      neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  simp only [sub_pos, sub_neg]
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁

lemma inv_toReal_iff : p₀⁻¹.toReal < p₁⁻¹.toReal ↔ p₁ < p₀ :=
  Iff.trans (toReal_lt_toReal (ne_of_lt (inv_lt_top.mpr hp₀))
    (ne_of_lt (inv_lt_top.mpr hp₁))) ENNReal.inv_lt_inv

-- TODO: check where this is used, replace by ζ_pos_iff'
lemma ζ_pos_iff₀ (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q < q₀) ∧ (p < p₀)) ∨ ((q₀ < q) ∧ (p₀ < p)) := by
  rw [ζ_pos_toReal_iff₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  rw [preservation_inequality ht hq₀q₁ hq hq₀']
  rw [preservation_inequality ht hp₀p₁ hp hp₀']
  rw [preservation_inequality' ht hq₀q₁ hq hq₀']
  rw [preservation_inequality' ht hp₀p₁ hp hp₀']

lemma ζ_pos_iff : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q₁ < q₀) ∧ (p₁ < p₀)) ∨ ((q₀ < q₁) ∧ (p₀ < p₁)) := by
  rw [ζ_pos_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁]
  rw [inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
      inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_pos_iff' : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q < q₀) ∧ (p < p₀)) ∨ ((q₀ < q) ∧ (p₀ < p)) := by
  rw [ζ_pos_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁]
  rw [← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  rw [← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq]
  rw [← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp]
  rw [← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_pos_iff_of_lt₀ (hp₀p₁' : p₀ < p₁) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    (q₀ < q) := by
  rw [ζ_pos_iff' ht hp₀ hq₀ hp₁ hq₁ (ne_of_lt hp₀p₁') hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ (ne_of_lt hp₀p₁') hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_pos_iff_of_lt₁ (hp₀p₁' : p₀ < p₁) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    (q < q₁) := by
  rw [← exp_gt_exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_pos_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_neg_iff_aux₀ : (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔
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

lemma ζ_neg_iff : (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔
    q₁ < q₀ ∧ p₀ < p₁ ∨ q₀ < q₁ ∧ p₁ < p₀ := by
  rw [ζ_neg_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁]
  rw [inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
      inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_neg_iff' : (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔
    ((q < q₀) ∧ (p₀ < p)) ∨ ((q₀ < q) ∧ (p < p₀)) := by
  rw [ζ_neg_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁]
  rw [← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  rw [← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq]
  rw [← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp]
  rw [← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_neg_iff_of_lt₀ (hp₀p₁' : p₀ < p₁) : (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔ q < q₀ := by
  rw [ζ_neg_iff' ht hp₀ hq₀ hp₁ hq₁ (ne_of_lt hp₀p₁') hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ (ne_of_lt hp₀p₁') hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_neg_iff_of_lt₁ (hp₀p₁' : p₀ < p₁) : (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'



-- TODO: check where this is used, replace by ζ_pos_iff'
-- lemma ζ_pos_iff₁ (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ ≠ ⊤) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
--     ((q < q₁) ∧ (p < p₁)) ∨ ((q₁ < q) ∧ (p₁ < p)) := by
--   rw [ζ_symm]
--   have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
--   rw [ζ_pos_iff₀ one_sub_mem] <;> try assumption
--   · exact Ne.symm hp₀p₁
--   · exact Ne.symm hq₀q₁
--   · exact switch_exponents ht hp
--   · exact switch_exponents ht hq

lemma ζ_neg_iff_aux (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) :
    (p₀.toReal * (q₀.toReal - q.toReal) / (q₀.toReal * (p₀.toReal - p.toReal)) < 0) ↔
    ((q.toReal < q₀.toReal) ∧ (p₀.toReal < p.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p.toReal < p₀.toReal)) := by
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  -- field_simp
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma ζ_neg_toReal_iff₀ (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) : (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q.toReal < q₀.toReal) ∧ (p₀.toReal < p.toReal)) ∨ ((q₀.toReal < q.toReal) ∧ (p.toReal < p₀.toReal)) := by
  rw [ζ_equality_4 ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_neg_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_neg_toReal_iff₁ (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ ≠ ⊤) : (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q.toReal < q₁.toReal) ∧ (p₁.toReal < p.toReal)) ∨ ((q₁.toReal < q.toReal) ∧ (p.toReal < p₁.toReal)) := by
  rw [ζ_equality_5 ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_neg_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_neg_iff₀ (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) : (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q < q₀) ∧ (p₀ < p)) ∨ ((q₀ < q) ∧ (p < p₀)) := by
  rw [ζ_neg_toReal_iff₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  rw [preservation_inequality ht hq₀q₁ hq hq₀']
  rw [preservation_inequality ht hp₀p₁ hp hp₀']
  rw [preservation_inequality' ht hq₀q₁ hq hq₀']
  rw [preservation_inequality' ht hp₀p₁ hp hp₀']

-- lemma ζ_neg_iff₁ (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ ≠ ⊤) : (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
--     ((q < q₁) ∧ (p₁ < p)) ∨ ((q₁ < q) ∧ (p < p₁)) := by
--   rw [ζ_symm]
--   have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
--   rw [ζ_neg_iff₀ one_sub_mem] <;> try assumption
--   · exact Ne.symm hp₀p₁
--   · exact Ne.symm hq₀q₁
--   · exact switch_exponents ht hp
--   · exact switch_exponents ht hq

lemma ζ_ne_zero : (@ζ p₀ q₀ p₁ q₁ t ≠ 0) := by
  unfold ζ
  refine div_ne_zero ?_ ?_
  · apply mul_ne_zero
    · apply ne_of_gt
      exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
    · refine sub_ne_zero_of_ne (Ne.symm ?_)
      intro h
      apply hq₀q₁
      rw [← inv_inv q₀, ← inv_inv q₁]
      rw [← coe_inv_exponent hq₀, ← coe_inv_exponent hq₁]
      exact congrArg Inv.inv (congrArg ENNReal.ofReal h)
  · apply mul_ne_zero
    · apply ne_of_gt
      exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
    · refine sub_ne_zero_of_ne (Ne.symm ?_)
      intro h
      apply hp₀p₁
      rw [← inv_inv p₀, ← inv_inv p₁]
      rw [← coe_inv_exponent hp₀, ← coe_inv_exponent hp₁]
      exact congrArg Inv.inv (congrArg ENNReal.ofReal h)

lemma ζ_le_zero_iff_of_lt₀ (hp₀p₁' : p₀ < p₁): (@ζ p₀ q₀ p₁ q₁ t ≤ 0) ↔ q < q₀ := by
  constructor
  · intro h
    rcases (Decidable.lt_or_eq_of_le h) with ζ_lt_0 | ζ_eq_0
    · exact (ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mp ζ_lt_0
    · exact False.elim <| (ζ_ne_zero ht hp₀ hq₀ hp₁ hq₁ (ne_of_lt hp₀p₁') hq₀q₁) ζ_eq_0
  · exact fun h ↦ le_of_lt ((ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mpr h)

lemma ζ_le_zero_iff_of_lt₁ (hp₀p₁' : p₀ < p₁) : (@ζ p₀ q₀ p₁ q₁ t) ≤ 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_le_zero_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma eq_exponents₀ (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal / p₀.toReal + p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
    (q.toReal - q₀.toReal)) = (1 - t) * p₀⁻¹.toReal * q.toReal := by
  rw [div_eq_inv_mul]
  rw [mul_div_assoc, mul_assoc, toReal_inv, ← mul_add, mul_comm_div, ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) = q.toReal * ((1 - t) * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
      calc
      _ = q₀.toReal * q₁⁻¹.toReal - q₀.toReal * q₀⁻¹.toReal +
          q₁⁻¹.toReal * q.toReal - q₁⁻¹.toReal *  q₀.toReal := by
        ring
      _ = q₁⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal := by
        rw [toReal_inv, toReal_inv, toReal_inv, mul_inv_cancel, inv_mul_cancel]
        · ring
        · exact ne_of_gt (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq)
        · exact ne_of_gt (toReal_pos (ne_of_gt hq₀) hq₀')
      _ = q.toReal * (q₁⁻¹.toReal - q⁻¹.toReal) := by ring
      _ = _ := by
        rw [preservation_interpolation ht hq₀ hq₁ hq]
        congr
        ring
    rw [this]
    rw [mul_div_assoc, mul_div_cancel_right₀]
    ring
    exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₁ (hq₀' : q₀ ≠ ⊤) :
    (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) = - t * p₁⁻¹.toReal * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : (p₁⁻¹.toReal * q₀⁻¹.toReal) * (q.toReal - q₀.toReal) = - t * p₁⁻¹.toReal * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
    calc
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - q₀⁻¹.toReal * q₀.toReal) := by ring
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - 1) := by
      rw [toReal_inv, toReal_inv, inv_mul_cancel]
      apply ne_of_gt (exp_toReal_pos hq₀ hq₀')
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal) := by
      rw [toReal_inv, toReal_inv, toReal_inv, inv_mul_cancel]
      exact ne_of_gt <| interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq
    _ = p₁⁻¹.toReal * q.toReal * (q₀⁻¹.toReal - q⁻¹.toReal) := by ring
    _ = _ := by
      rw [preservation_interpolation ht hq₀ hq₁ hq]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma test (a : ℝ) : - (a)⁻¹ = (-a)⁻¹ := by apply?

lemma eq_exponents₂ :
    (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) =
    - (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₀⁻¹.toReal - q₁⁻¹.toReal)) := calc
  _ = - (p₁⁻¹.toReal * q₀⁻¹.toReal * (-(q₁⁻¹.toReal - q₀⁻¹.toReal)⁻¹)) := by
    rw [div_eq_mul_inv]; ring
  _ = _ := by congr; rw [neg_inv, neg_sub]

lemma eq_exponents₃ (hq₁' : q₁ ≠ ⊤):
    (-(p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₁.toReal) + q₁.toReal / p₁.toReal)
    = t * p₁⁻¹.toReal * q.toReal := by
  rw [eq_exponents₂, neg_neg, add_comm]
  rw [eq_exponents₀ (Ioo.one_sub_mem ht) hq₁ hq₀ (Ne.symm hq₀q₁) (switch_exponents ht hq) hq₁']
  ring

lemma eq_exponents₄ (hq₁' : q₁ ≠ ⊤) :
    p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) =
    (1 - t) * p₀⁻¹.toReal * q.toReal := by
  rw [← neg_neg (a := p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal))]
  rw [← eq_exponents₂, neg_mul]
  rw [eq_exponents₁ (Ioo.one_sub_mem ht) hq₁ hq₀ (Ne.symm hq₀q₁) (switch_exponents ht hq) hq₁']
  ring

end sigma_ENNReal



end




noncomputable section

open Real Set

structure ScaledPowerFunction where
  σ : ℝ
  d : ℝ
  hd : d > 0
  hσ : (σ > 0) ∨ (σ < 0)

structure ToneCouple where
  ton : ℝ → ℝ
  inv : ℝ → ℝ
  mon : Bool
  ton_is_ton : if mon then StrictMonoOn ton (Ioi 0) else StrictAntiOn ton (Ioi 0)
  ran_ton : ∀ t ∈ Ioi (0 : ℝ), ton t ∈ Ioi 0
  ran_inv : ∀ t ∈ Ioi (0 : ℝ), inv t ∈ Ioi 0
  inv_pf : if mon
      then ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ s < inv t) ∧ (t < ton s ↔ inv t < s)
      else ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ inv t < s) ∧ (t < ton s ↔ s < inv t)

instance spf_to_tc (spf : ScaledPowerFunction) : ToneCouple where
  ton := fun s : ℝ ↦ (s / spf.d) ^ spf.σ
  inv := fun t : ℝ ↦ spf.d * t ^ spf.σ⁻¹
  mon := if (spf.σ > 0) then true else false
  ran_ton := fun t ht ↦ rpow_pos_of_pos (div_pos ht spf.hd) _
  ran_inv := fun t ht ↦ Real.mul_pos spf.hd (rpow_pos_of_pos ht spf.σ⁻¹)
  ton_is_ton := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte]
      intro s (hs : s > 0) t (ht : t > 0) hst
      refine (rpow_lt_rpow_iff ?_ ?_ sgn_σ).mpr ?_
      · apply le_of_lt (div_pos hs spf.hd)
      · apply le_of_lt (div_pos ht spf.hd)
      · exact div_lt_div_of_pos_right hst spf.hd
    · simp only [↓reduceIte]
      intro s (hs : s > 0) t (ht : t > 0) hst
      rcases spf.hσ with σ_pos | σ_neg
      · exact False.elim (sgn_σ σ_pos)
      · simp only
        refine (Real.rpow_lt_rpow_iff_of_neg (div_pos ht spf.hd)
            (div_pos hs spf.hd) σ_neg).mpr (div_lt_div_of_pos_right hst spf.hd)
  inv_pf := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte, mem_Ioi]
      intro s hs t ht
      constructor
      · rw [← Real.lt_rpow_inv_iff_of_pos
            (div_nonneg (le_of_lt hs) (le_of_lt spf.hd)) (le_of_lt ht) sgn_σ ]
        rw [← _root_.mul_lt_mul_left spf.hd]
        rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
      · rw [← Real.rpow_inv_lt_iff_of_pos (le_of_lt ht)
            (div_nonneg (le_of_lt hs) (le_of_lt spf.hd)) sgn_σ ]
        rw [← _root_.mul_lt_mul_left spf.hd]
        rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
    · simp only [↓reduceIte, mem_Ioi]
      intro s hs t ht
      rcases spf.hσ with σ_pos | σ_neg
      · contradiction
      · constructor
        · rw [← Real.rpow_inv_lt_iff_of_neg ht (div_pos hs spf.hd) σ_neg]
          rw [← _root_.mul_lt_mul_left spf.hd]
          rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
        · rw [← Real.lt_rpow_inv_iff_of_neg (div_pos hs spf.hd) ht σ_neg]
          rw [← _root_.mul_lt_mul_left spf.hd]
          rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]

end

noncomputable section

open Real Set

variable {p₀ q₀ p₁ q₁ p q t : ℝ} (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
  (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
  (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)

/-- A particular choice of scaled power function needed in the real interpolation theorem
    when `q₀` and `q₁` are not equal to infinity -/
instance spfI : ScaledPowerFunction where
  σ := @σ p₀ q₀ p₁ q₁ t
  d := 1
  hd := zero_lt_one
  hσ := lt_or_gt_of_ne <| Ne.symm <| σ_ne_zero hp₀ hq₀ hp₁ hq₁ ht hp₀p₁ hq₀q₁ hp hq

-- (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :



end

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'}
  [NormedAddCommGroup E] [NormedSpace ℝ E] -- [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] -- [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] -- [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] -- [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)
  {f : α → E₁} {t : ℝ} -- {s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}


namespace MeasureTheory

/-- ## Some tools for measure theory computations -/

-- TODO: change lhs and rhs?
-- TODO: rewrite the condition in filter form?
lemma lintegral_double_restrict_set {A B: Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := setLIntegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]

/-- A collection of small lemmas to help with integral manipulations -/

lemma measure_preserving_shift {a : ℝ} :
    MeasurePreserving (fun x ↦ a + x) volume volume := by
  exact measurePreserving_add_left volume a

lemma measureable_embedding_shift {a : ℝ} :
    MeasurableEmbedding (fun x ↦ a + x) := by
  exact measurableEmbedding_addLeft a

lemma measure_preserving_scaling {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun x ↦ a * x) volume ((ENNReal.ofReal |a⁻¹|) • volume) := by
  refine { measurable := ?measurable, map_eq := ?map_eq }
  · exact measurable_const_mul a
  · exact Real.map_volume_mul_left ha

lemma lintegral_shift (f : ℝ → ENNReal) {a : ℝ} :
    ∫⁻ x : ℝ, (f (x + a)) = ∫⁻ x : ℝ, f x :=
  by exact lintegral_add_right_eq_self f a

lemma lintegral_shift' (f : ℝ → ENNReal) {a : ℝ} {s : Set ℝ}:
    ∫⁻ (x : ℝ) in (fun z : ℝ ↦ z + a)⁻¹' s, f (x + a) = ∫⁻ (x : ℝ) in s, f x := by
  rw [MeasurePreserving.setLIntegral_comp_preimage_emb
      (measurePreserving_add_right volume a) (measurableEmbedding_addRight a)]

lemma lintegral_add_right_Ioi (f : ℝ → ENNReal) {a b : ℝ} :
    ∫⁻ (x : ℝ) in Ioi (b - a), f (x + a) = ∫⁻ (x : ℝ) in Ioi b, f x := by
  nth_rewrite 2 [← lintegral_shift' (a := a)]
  simp

lemma lintegral_scale_constant (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0):
    ∫⁻ x : ℝ, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x := by
  rw [← @lintegral_smul_measure]
  rw [MeasurePreserving.lintegral_comp_emb]
  · exact measure_preserving_scaling h
  · exact measurableEmbedding_mulLeft₀ h

lemma lintegral_scale_constant_preimage (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0)
    {s : Set ℝ}:
    ∫⁻ x : ℝ in (fun z : ℝ ↦ a * z)⁻¹' s, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in s, f x := by
  rw [← @lintegral_smul_measure]
  -- TODO: note that the function below has been renamed recently
  rw [MeasurePreserving.setLIntegral_comp_preimage_emb (measure_preserving_scaling h)
      (measurableEmbedding_mulLeft₀ h)]
  rw [@Measure.restrict_smul]

lemma lintegral_scale_constant_halfspace (f: ℝ → ENNReal) {a : ℝ} (h : 0 < a) :
    ∫⁻ x : ℝ in Ioi 0, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [← lintegral_scale_constant_preimage f (Ne.symm (ne_of_lt h))]
  have h₀ : (fun z ↦ a * z) ⁻¹' Ioi 0 = Ioi 0 := by
    unfold preimage
    ext x
    simp
    constructor
    · intro h₁
      exact (pos_iff_pos_of_mul_pos h₁).mp h
    · intro h₁
      exact Real.mul_pos h h₁
  rw [h₀]

lemma lintegral_scale_constant_halfspace' {f: ℝ → ENNReal} {a : ℝ} (h : 0 < a) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ in Ioi 0, f (a*x) = ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [lintegral_scale_constant_halfspace f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a),
      @abs_inv, mul_inv_cancel (abs_ne_zero.mpr (Ne.symm (ne_of_lt h)))]
  simp

lemma lintegral_scale_constant' {f: ℝ → ENNReal} {a : ℝ} (h : a ≠ 0):
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a), @abs_inv,
      mul_inv_cancel (abs_ne_zero.mpr h)]
  simp

-- local convenience function
lemma lintegral_rw_aux {g : ℝ → ℝ≥0∞} {f₁ f₂ : ℝ → ℝ≥0∞} {A : Set ℝ}
    (heq : f₁ =ᶠ[ae (volume.restrict A)] f₂) :
  (∫⁻ s in A, g s * f₁ s) =
  (∫⁻ s in A, g s * f₂ s) := by
  refine (lintegral_rw₂ ?_ ?_ HMul.hMul)
  · exact Filter.EventuallyEq.refl (ae (volume.restrict A)) g
  · exact heq

lemma power_aux {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ (p + q)) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal s ^ p * ENNReal.ofReal s ^ q ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  rw [ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs]
  rw [← ofReal_mul (by positivity)]
  rw [← Real.rpow_add hs]

lemma power_aux_2 {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal (s ^ (p + q))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p) * ENNReal.ofReal (s ^ q) ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  rw [← ofReal_mul (by positivity)]
  rw [← Real.rpow_add hs]

lemma ofReal_rpow_of_pos_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  exact ofReal_rpow_of_pos hs

lemma extract_constant_double_integral_rpow {f : ℝ → ℝ → ℝ≥0∞} {q : ℝ} (hq : q ≥ 0) {a : ℝ≥0∞} (ha : a ≠ ⊤):
    ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, a * f s t)^q =
    (a ^ q) * ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, f s t)^q := by
  rw [← lintegral_const_mul']; swap; refine rpow_ne_top_of_nonneg hq ha
  apply congr
  · rfl
  · ext s
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hq]
    congr
    rw [lintegral_const_mul' a (f s) ha]

lemma ofReal_rpow_rpow_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  exact ofReal_rpow_of_pos hs

lemma lintegral_rpow_of_gt {β γ : ℝ} (hβ : β > 0) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / (γ + 1)) := by
  have hγ2 : γ + 1 > 0 := by linarith
  rw [setLIntegral_congr Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le (le_of_lt hβ)]
    rw [integral_rpow]
    · rw [Real.zero_rpow (ne_of_gt hγ2), sub_zero]
    · exact Or.inl hγ
  · apply (@intervalIntegral.intervalIntegrable_rpow' 0 β γ ?_).1
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt hs.1) γ

/-- ## The truncation of a function -/

-- TODO: could use easier definition of truncation

def trunc' (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

def trunc'' (f : α → E) (t : ℝ) :=
  {x | ¬ ‖f x‖ ≤ t}.indicator (fun x ↦ if 0 < t then (t * (max t ‖f x‖)⁻¹) • f x else 0)

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else
    if 0 < t then (t * ‖f x‖⁻¹) • f x else 0

def trnc (j : Bool) (f : α → E) (t : ℝ)  : α → E :=
  match j with
  | false => f - trunc f t
  | true => trunc f t

lemma trunc_buildup : trunc f t = trunc' f t + trunc'' f t := by
  ext x
  unfold trunc trunc' trunc''
  simp
  split <;> rename_i h₀
  · simp
    intro h
    have _ : ¬ t < ‖f x‖ := by exact not_lt.mpr h₀
    contradiction
  · have h₁ : max t ‖f x‖ = ‖f x‖ := by
      apply max_eq_right_of_lt
      exact lt_of_not_ge h₀
    unfold indicator
    simp
    split
    · rewrite [h₁]
      split <;> rename_i h₂
      · rfl
      · have _ : ‖f x‖ ≤ t := by exact le_of_not_lt h₂
        contradiction
    · exact Eq.symm (ite_self 0)

/-- ### Measurability properties of truncations -/

lemma stronglyMeasurable_inv (hf : StronglyMeasurable f) (ht : 0 < t):
    StronglyMeasurable (fun y ↦ (max t ‖f y‖)⁻¹):= by
  apply Continuous.comp_stronglyMeasurable (g := fun z ↦ (max t ‖z‖)⁻¹) (hf := hf)
  · apply Continuous.inv₀
    · apply Continuous.max
      · exact continuous_const
      · exact continuous_norm
    · intro z
      exact Ne.symm (ne_of_lt (lt_max_of_lt_left ht))

lemma aestronglyMeasurable_trunc' (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc' f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc' g t)
  constructor
  · apply MeasureTheory.StronglyMeasurable.indicator (s := {x | ‖g x‖ ≤ t})
    · exact wg1
    · apply StronglyMeasurable.measurableSet_le
      apply StronglyMeasurable.norm
      · exact wg1
      · exact stronglyMeasurable_const
  apply measure_mono_null ?_ wg2
  intro x
  contrapose
  simp
  intro h₂
  unfold trunc'
  rewrite [h₂]
  rfl

lemma aestronglyMeasurable_trunc'' (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc'' f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc'' g t)
  constructor
  · apply MeasureTheory.StronglyMeasurable.indicator
    · split <;> rename_i h₀
      · apply StronglyMeasurable.smul
        · apply StronglyMeasurable.mul
          · exact stronglyMeasurable_const
          · apply stronglyMeasurable_inv wg1 h₀
        · exact wg1
      · exact stronglyMeasurable_const
    · have h₂ : {x | ¬ ‖g x‖ ≤ t} = { x | t < ‖g x‖ } := by
        ext x
        exact not_le
      rewrite [h₂]
      apply StronglyMeasurable.measurableSet_lt
      · exact stronglyMeasurable_const
      · apply StronglyMeasurable.norm
        exact wg1

  apply measure_mono_null ?_ wg2
  intro x
  contrapose
  simp
  intro h₂
  unfold trunc''
  unfold indicator
  simp
  rewrite [h₂]
  rfl

lemma aestronglyMeasurable_trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := by
  rewrite [trunc_buildup]
  apply AEStronglyMeasurable.add
  · exact aestronglyMeasurable_trunc' hf
  · exact aestronglyMeasurable_trunc'' hf

lemma aestronglyMeasurable_trunc_compl (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (f - trunc f t) μ :=
  AEStronglyMeasurable.sub hf (aestronglyMeasurable_trunc hf)

/-- The norm of the truncation is monotone in the truncation parameter -/
lemma norm_trunc_mono :
  Monotone (fun s ↦ snorm (trunc f s) p μ) := sorry

/-- The norm of the complement of the truncation is antitone in the truncation parameter -/
lemma norm_trunc_compl_anti :
  Antitone (fun s ↦ snorm (f - trunc f s) p μ) := sorry

/-- The norm of the truncation is meaurable in the truncation parameter -/
@[measurability]
lemma norm_trunc_measurable :
    Measurable (fun s ↦ snorm (trunc f s) p μ) :=
  Monotone.measurable norm_trunc_mono

/-- The norm of the complement of the truncation is measurable in the truncation parameter -/
@[measurability]
lemma norm_trunc_compl_measurable :
    Measurable (fun s ↦ snorm (f - trunc f s) p μ) :=
  Antitone.measurable norm_trunc_compl_anti

/-- ## Distribution functions of truncations -/

lemma distribution_shift_trunc (t : ℝ) (s : ℝ≥0∞) :
    distribution (f - (trunc f t)) s μ = distribution f (s + t.toNNReal) μ := by
  -- TODO: clean up
  unfold distribution trunc
  split <;> rename_i h₀
  · have h₁ :
        {x | s < ↑‖(f - fun x ↦ if ‖f x‖ ≤ t then f x else (t * ‖f x‖⁻¹) • f x) x‖₊}
        = {x | (t.toNNReal + s) < ↑‖f x‖₊} := by
      ext x
      simp
      split <;> rename_i h₂
      · simp
        calc
        ‖f x‖₊ ≤ ofNNReal t.toNNReal := by
          refine ENNReal.coe_le_coe.mpr (le_toNNReal_of_coe_le h₂)
        _      ≤ t.toNNReal + s := le_self_add
      · rcases (eq_or_ne s ⊤) with s_eq_top | s_ne_top
        · constructor
          · intro h
            have h₃ : ofNNReal ↑‖f x - (t * ‖f x‖⁻¹) • f x‖₊ < ⊤ := by
              exact coe_lt_top
            have h₄ : s < ⊤ := gt_trans h₃ h
            have _ : ¬ (s < ⊤) := by exact not_lt_top.mpr s_eq_top
            contradiction
          · intro h
            have h₅ : s < ⊤ := by exact gt_trans coe_lt_top (lt_of_le_of_lt le_add_self h)
            have _ : ¬ (s < ⊤) := by exact not_lt_top.mpr s_eq_top
            contradiction
        · rewrite [Iff.symm (toNNReal_lt_toNNReal s_ne_top coe_ne_top)]
          have h_sum_ne_top : ofNNReal t.toNNReal + s ≠ ⊤ :=
            add_ne_top.mpr (ite_ne_left_iff.mp (id (Ne.symm s_ne_top)))
          rewrite [Iff.symm (toNNReal_lt_toNNReal h_sum_ne_top coe_ne_top)]
          change (s.toNNReal.toReal < ‖f x - (t * ‖f x‖⁻¹) • f x‖ ↔
              (↑t.toNNReal + s).toNNReal.toReal < ‖f x‖)
          nth_rewrite 1 [← MulAction.one_smul (α := ℝ) (f x)]
          rewrite [← (sub_smul), norm_smul]
          have h₄ : ‖f x‖⁻¹ < t⁻¹ := inv_lt_inv_of_lt h₀ (lt_of_not_ge h₂)
          have h₅ : t * ‖f x‖⁻¹ < t * t⁻¹ := (_root_.mul_lt_mul_left h₀).mpr h₄
          rewrite [((mul_inv_eq_one₀ (Ne.symm (ne_of_lt h₀))).mpr rfl)] at h₅
          have h₆ : 1 - t * ‖f x‖⁻¹ > 0 := sub_pos.mpr h₅
          rewrite [Real.norm_of_nonneg (le_of_lt h₆)]
          have h₁₁ : (1 - t * ‖f x‖⁻¹)*‖f x‖ = ‖f x‖ - t * (‖f x‖*‖f x‖⁻¹) := by linarith
          have h₁₂ : ‖f x‖*‖f x‖⁻¹ = 1 := by
            apply mul_inv_cancel
            linarith
          rewrite [h₁₂] at h₁₁
          rewrite [h₁₁]
          simp
          rewrite [toNNReal_add coe_ne_top s_ne_top]
          simp
          rewrite [max_eq_left_of_lt h₀]
          constructor
          · intro h
            linarith
          · intro h
            linarith
    rewrite [h₁]
    rw [add_comm]
  · have h₂ : (fun x ↦ if ‖f x‖ ≤ t then f x else 0) = (fun x ↦ 0) := by
      ext x
      split
      · have _ : ‖f x‖ ≥ 0 := norm_nonneg (f x)
        have h₃ : ‖f x‖ = 0 := by linarith
        exact norm_eq_zero.mp h₃
      · rfl
    rw [h₂]
    simp
    rw [Real.toNNReal_of_nonpos (le_of_not_lt h₀)]
    simp

lemma distribution_trunc (t : ℝ) (s : ℝ≥0∞):
    distribution (trunc f t) s μ =
    if s < ENNReal.ofReal t then distribution f s μ else 0 := by
  have simp_norm : ∀ x, t > 0 → ¬ ‖f x‖ ≤  t → ‖(t * ‖f x‖⁻¹) • f x‖.toNNReal = t.toNNReal := by
    intro x t_pos ne_norm_le_t
    have norm_pos := (lt_trans t_pos (not_le.mp ne_norm_le_t))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (le_of_lt t_pos) (le_of_lt (inv_pos_of_pos norm_pos))),
        mul_assoc, mul_comm ‖f x‖⁻¹, mul_inv_cancel (ne_of_gt norm_pos), mul_one]
  split <;> rename_i h₀
  · apply congrArg μ
    ext x
    simp
    unfold trunc
    rw [← norm_toNNReal, ← norm_toNNReal]
    split <;> rename_i h₁
    · rfl
    · split <;> rename_i h₂
      · have coe_t_lt_norm : ENNReal.ofReal t < ENNReal.ofReal ‖f x‖ :=
          (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₂)).mpr (not_le.mp h₁)
        rw [simp_norm x h₂ h₁]
        exact { mp := fun _ ↦ lt_trans h₀ coe_t_lt_norm, mpr := fun _ ↦ h₀ }
      · rw [norm_zero, Real.toNNReal_zero, ENNReal.coe_zero]
        exact
          { mp := fun h ↦ False.elim (not_lt_zero h),
            mpr := False.elim
              (not_lt_zero (lt_of_lt_of_le h₀ (ofReal_le_of_le_toReal (not_lt.mp h₂)))) }
  · unfold distribution trunc
    refine measure_mono_null ?_ (OuterMeasureClass.measure_empty μ)
    intro x
    simp
    rw [← norm_toNNReal]
    split <;> rename_i h₁
    · exact le_trans (ofReal_le_ofReal h₁) (not_lt.mp h₀)
    · split <;> rename_i h₂
      · rw [simp_norm x h₂ h₁]
        exact not_lt.mp h₀
      · rw [norm_zero, Real.toNNReal_zero, ENNReal.coe_zero]
        exact zero_le s

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (MeasureTheory.trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

/-- ## Interpolation properties for weak L-p spaces -/

lemma power_estimate {a b t γ : ℝ} (hγ : γ > 0) (htγ : γ ≤ t) (hab : a ≤ b) :
    (t / γ) ^ a ≤ (t / γ) ^ b := by
  gcongr
  exact (one_le_div hγ).mpr htγ

lemma power_estimate' {a b t γ : ℝ} (ht : t > 0) (htγ : t ≤ γ) (hab: a ≤ b) :
    (t / γ) ^ b ≤ (t / γ) ^ a := by
  have γ_pos : γ > 0 := lt_of_lt_of_le ht htγ
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ hab
  · exact div_pos ht γ_pos
  · exact div_le_one_of_le htγ (le_of_lt γ_pos)

lemma rpow_le_rpow_of_exponent_le_base_le {a b t γ : ℝ} (ht : t > 0) (htγ : t ≤ γ) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ b) ≤ ENNReal.ofReal (t ^ a) * ENNReal.ofReal (γ ^ (b - a)) := by
  rw [mul_comm]
  have γ_pos : 0 < γ := lt_of_lt_of_le ht htγ
  rw [Real.rpow_sub γ_pos]
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (γ ^ (-b) )) ?_ ?_).mp ?_
  · apply ne_of_gt
    refine ofReal_pos.mpr ?_
    exact Real.rpow_pos_of_pos γ_pos (-b)
  · exact coe_ne_top
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, add_left_neg,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul]; swap; positivity
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    apply ofReal_le_ofReal
    exact power_estimate' ht htγ hab

-- TODO: there is a lot of overlap between above proof and below
lemma rpow_le_rpow_of_exponent_le_base_ge {a b t γ : ℝ} (hγ : γ > 0) (htγ : γ ≤ t) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ a) ≤ ENNReal.ofReal (t ^ b) * ENNReal.ofReal (γ ^ (a - b)) := by
  rw [mul_comm]
  have t_pos : 0 < t := by exact gt_of_ge_of_gt htγ hγ
  rw [Real.rpow_sub hγ]
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (γ ^ (-a) )) ?_ ?_).mp ?_
  · apply ne_of_gt
    refine ofReal_pos.mpr ?_
    exact Real.rpow_pos_of_pos hγ (-a)
  · exact coe_ne_top
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, add_left_neg,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul]; swap; positivity
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    apply ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_le ((one_le_div hγ).mpr htγ) hab

lemma ℒp_interpolate_higher {p q : ℝ≥0∞} (hp : p > 0)
    (hq : q ∈ Ioo p ⊤) {f : α → E₁} (hf : AEMeasurable f μ) (hM : snormEssSup f μ ≠ ⊤) :
    snorm f q μ ^ q.toReal ≤ (q / p) * snormEssSup f μ ^ (q.toReal - p.toReal) *
    snorm f p μ ^ p.toReal := by
  have p_lt_q : p < q := hq.1
  have hp_ne_top := (LT.lt.ne_top p_lt_q)
  have q_lt_top := hq.2
  have coe_q : ENNReal.ofReal (q.toReal) = q := by
    refine ofReal_toReal_eq_iff.mpr (LT.lt.ne_top q_lt_top)
  have coe_p : ENNReal.ofReal (p.toReal) = p := by
    refine ofReal_toReal_eq_iff.mpr hp_ne_top
  have q_pos : 0 < q := lt_trans hp hq.1
  have q'pos : 0 < q.toReal:= by
    apply toReal_pos_iff.mpr; exact ⟨q_pos, q_lt_top⟩
  have q'inv_pos : 0 < q.toReal⁻¹ := inv_pos_of_pos q'pos
  nth_rw 1 [← coe_q]
  rw [snorm_pow_eq_distribution' hf q'pos]
  · rw [ENNReal.rpow_inv_rpow (ne_of_gt (exp_toReal_pos q_pos (LT.lt.ne_top q_lt_top)))]
    let M := (snormEssSup f μ).toReal
    have coe_M : ENNReal.ofReal M = snormEssSup f μ := ofReal_toReal_eq_iff.mpr hM
    rw [lintegral_double_restrict_set (B := Ioo (0 : ℝ) M) measurableSet_Ioi
              measurableSet_Ioo]
    · rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
      calc
      _ ≤ ENNReal.ofReal q.toReal *
          ∫⁻ (t : ℝ) in Ioo 0 M, distribution f (ENNReal.ofReal t) μ * (ENNReal.ofReal (t ^ (p.toReal - 1)) * ENNReal.ofReal (M ^ ((q.toReal - 1) - (p.toReal - 1)))) := by
        apply mul_le_mul_left'
        apply setLIntegral_mono' measurableSet_Ioo
        intro t ⟨ht₁, ht₂⟩
        apply mul_le_mul_left'
        apply rpow_le_rpow_of_exponent_le_base_le ht₁ (le_of_lt ht₂)
        refine tsub_le_tsub_right ?_ 1
        refine toReal_mono' ?_ ?_
        · exact (le_of_lt p_lt_q)
        · intro q_eq_top
          have q_ne_top : q ≠ ⊤ := LT.lt.ne_top q_lt_top
          contradiction
      _ ≤ ENNReal.ofReal q.toReal * ENNReal.ofReal (M ^ ((q.toReal - 1) - (p.toReal - 1))) *
          (∫⁻ (t : ℝ) in Ioi 0, distribution f (ENNReal.ofReal t) μ * ENNReal.ofReal (t ^ (p.toReal - 1))) := by
        simp_rw [← mul_assoc]
        rw [lintegral_mul_const']; swap; exact coe_ne_top
        nth_rw 2 [mul_comm]
        rw [← mul_assoc]
        gcongr
        apply lintegral_mono_set
        intro t ht
        exact ht.1
      _ ≤ ENNReal.ofReal q.toReal * ENNReal.ofReal (M ^ ((q.toReal - 1) - (p.toReal - 1))) * ((ENNReal.ofReal p.toReal)⁻¹ * snorm f (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
        rw [← one_mul (a := ∫⁻ (t : ℝ) in Ioi 0, _)]
        rw [← ENNReal.inv_mul_cancel (a := ENNReal.ofReal p.toReal)]
        · rw [mul_assoc _ (ENNReal.ofReal p.toReal)]
          rw [← ENNReal.rpow_inv_rpow (y := p.toReal) (x := ENNReal.ofReal p.toReal *
          ∫⁻ (t : ℝ) in Ioi 0, distribution f (ENNReal.ofReal t) μ * ENNReal.ofReal (t ^ (p.toReal - 1))) (ne_of_gt (exp_toReal_pos hp hp_ne_top))]
          rw [← snorm_pow_eq_distribution' hf]
          exact exp_toReal_pos hp hp_ne_top
        · exact ne_of_gt <| ofReal_pos.mpr (exp_toReal_pos hp hp_ne_top)
        · exact coe_ne_top
      _ = _ := by
        rw [coe_q, coe_p, div_eq_mul_inv, ← coe_M, sub_sub_sub_cancel_right]
        rw [← ofReal_rpow_of_nonneg toReal_nonneg]
        · ring
        · apply sub_nonneg_of_le
          refine toReal_mono ?_ ?_
          · exact LT.lt.ne_top q_lt_top
          · exact le_of_lt hq.1
    · apply ae_of_all
      intro t ht; simp at ht
      have := ht.2 ht.1
      have : distribution f (ENNReal.ofReal t) μ ≤ distribution f (ENNReal.ofReal M) μ := by
        apply distribution_mono_right'
        apply ofReal_le_ofReal (by linarith)
      have : distribution f (ENNReal.ofReal M) μ = 0 := by
        rw [coe_M]; exact meas_snormEssSup_lt
      calc
      _ ≤ distribution f (ENNReal.ofReal M) μ * ENNReal.ofReal (t ^ (q.toReal - 1)) := by
        exact mul_le_mul_right' (distribution_mono_right' (ofReal_le_ofReal (by linarith))) _
      _ = 0 * ENNReal.ofReal (t ^ (q.toReal - 1)) := by rw[coe_M, distribution_snormEssSup]
      _ = _ := by exact zero_mul _


-- TODO : case p = ⊤
-- TODO : rhs can be simplified
lemma ℒp_interpolate_lower {p q : ℝ≥0∞} (hp : p > 0) (hp_ne_top : p ≠ ⊤)
    (hq : q ∈ Ioo 0 p) {f : α → E₁} {γ : ℝ}
    (hγ : γ > 0) (hf : AEMeasurable f μ) :
    snorm f q μ ^ q.toReal ≤ distribution f 0 μ * ENNReal.ofReal (γ ^ q.toReal) +
      ENNReal.ofReal q.toReal * ENNReal.ofReal (γ ^ (q.toReal - p.toReal)) *
      ((ENNReal.ofReal p.toReal)⁻¹ * snorm f (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
  have q_pos := hq.1
  have q_lt_p := hq.2
  have q_ne_top : q ≠ ⊤ := LT.lt.ne_top q_lt_p
  have coe_q : ENNReal.ofReal q.toReal = q := by
    refine ofReal_toReal ?h
    exact LT.lt.ne_top q_lt_p
  nth_rw 1 [← coe_q]
  rw [snorm_pow_eq_distribution']
  · rw [ENNReal.rpow_inv_rpow (ne_of_gt (exp_toReal_pos q_pos q_ne_top))]
    rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hγ)]
    calc
    ENNReal.ofReal q.toReal *
    ∫⁻ (t : ℝ) in Ioc 0 γ ∪ Ioi γ, distribution f (ENNReal.ofReal t) μ *
    ENNReal.ofReal (t ^ (q.toReal - 1))
      ≤ ENNReal.ofReal q.toReal *
        ((∫⁻ (t : ℝ) in Ioc 0 γ, distribution f (ENNReal.ofReal t) μ *
        ENNReal.ofReal (t ^ (q.toReal - 1))) +
        (∫⁻ (t : ℝ) in Ioi γ, distribution f (ENNReal.ofReal t) μ *
        ENNReal.ofReal (t ^ (q.toReal - 1)))) := by
      gcongr
      exact lintegral_union_le _ (Ioc (0 : ℝ) (γ : ℝ)) (Ioi (γ : ℝ))
    _ ≤ ENNReal.ofReal q.toReal *
        ((∫⁻ (t : ℝ) in Ioc 0 γ, distribution f 0 μ *
        ENNReal.ofReal (t ^ (q.toReal - 1))) +
        (∫⁻ (t : ℝ) in Ioi γ, distribution f (ENNReal.ofReal t) μ * (
        ENNReal.ofReal (t ^ (p.toReal - 1)) *
        ENNReal.ofReal (γ ^ ((q.toReal - 1) - (p.toReal - 1)))))) := by
      apply mul_le_mul_left'
      apply add_le_add
      · apply setLIntegral_mono' measurableSet_Ioc
        intro s ⟨hs1, hs2⟩
        apply mul_le_mul_right'
        apply distribution_mono_right
        exact zero_le (ENNReal.ofReal s)
      · apply setLIntegral_mono' measurableSet_Ioi
        intro s (hs : γ < s)
        gcongr
        apply rpow_le_rpow_of_exponent_le_base_ge hγ (le_of_lt hs)
        apply tsub_le_tsub_right
        exact toReal_mono hp_ne_top (le_of_lt q_lt_p)
    _ = ENNReal.ofReal q.toReal * distribution f 0 μ *
        (∫⁻ (t : ℝ) in Ioc 0 γ, ENNReal.ofReal (t ^ (q.toReal - 1))) +
        ENNReal.ofReal q.toReal *
        ENNReal.ofReal (γ ^ ((q.toReal - 1) - (p.toReal - 1))) *
        (∫⁻ (t : ℝ) in Ioi γ, distribution f (ENNReal.ofReal t) μ *
        ENNReal.ofReal (t ^ (p.toReal - 1))) := by
      rw [mul_add, lintegral_const_mul]
      · simp_rw [← mul_assoc]
        rw [lintegral_mul_const']; swap; exact coe_ne_top
        nth_rw 4 [mul_comm]
        rw [← mul_assoc]
      · exact Measurable.coe_nnreal_ennreal
            (Measurable.real_toNNReal (Measurable.pow_const measurable_id' (q.toReal - 1)))
    _ ≤ ENNReal.ofReal q.toReal * distribution f 0 μ * ENNReal.ofReal (γ ^ q.toReal / q.toReal) +
        ENNReal.ofReal q.toReal * ENNReal.ofReal (γ ^ (q.toReal - p.toReal)) *
        ∫⁻ (t : ℝ) in Ioi 0, distribution f (ENNReal.ofReal t) μ *
        ENNReal.ofReal (t ^ (p.toReal - 1)) := by
      rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
      rw [lintegral_rpow_of_gt] <;> try positivity
      · rw [sub_add_cancel, sub_sub_sub_cancel_right]
        gcongr
        apply lintegral_mono_set
        intro s (hs : s > γ)
        exact lt_trans hγ hs
      · rw [← zero_add (-1)]
        exact sub_lt_sub_right (exp_toReal_pos hq.1 (ofReal_toReal_eq_iff.mp coe_q)) 1
    _ = ENNReal.ofReal q.toReal * distribution f 0 μ * ENNReal.ofReal (γ ^ q.toReal / q.toReal) +
        ENNReal.ofReal q.toReal * ENNReal.ofReal (γ ^ (q.toReal - p.toReal)) *
        ((ENNReal.ofReal p.toReal)⁻¹ * snorm f (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
      rw [← one_mul (a := ∫⁻ (t : ℝ) in Ioi 0, _)]
      rw [← ENNReal.inv_mul_cancel (a := ENNReal.ofReal p.toReal)]
      · rw [mul_assoc _ (ENNReal.ofReal p.toReal)]
        rw [← ENNReal.rpow_inv_rpow (y := p.toReal) (x := (ENNReal.ofReal p.toReal) *
            ∫⁻ (t : ℝ) in Ioi 0, distribution f (ENNReal.ofReal t) μ *
            ENNReal.ofReal (t ^ (p.toReal - 1))) (ne_of_gt (exp_toReal_pos hp hp_ne_top))]
        rw [← snorm_pow_eq_distribution' hf (exp_toReal_pos hp hp_ne_top)]
      · exact ne_of_gt <| ofReal_pos.mpr (exp_toReal_pos hp hp_ne_top)
      · exact coe_ne_top
    _ = distribution f 0 μ * ENNReal.ofReal (γ ^ q.toReal) +
        ENNReal.ofReal q.toReal * ENNReal.ofReal (γ ^ (q.toReal - p.toReal)) *
        ((ENNReal.ofReal p.toReal)⁻¹ * snorm f (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
      rw [mul_comm (ENNReal.ofReal q.toReal)]
      rw [mul_assoc, ← ofReal_mul] <;> try positivity
      rw [mul_div_cancel₀]
      apply ne_of_gt
      exact exp_toReal_pos hq.1 (ofReal_toReal_eq_iff.mp coe_q)
  · exact hf
  · exact exp_toReal_pos hq.1 (ofReal_toReal_eq_iff.mp coe_q)

lemma distribution_le_integral_p {p : ℝ≥0∞} (hp : p > 0) (hp_ne_top : p ≠ ⊤) {t : ℝ} (ht : t > 0)
  (hf : AEMeasurable f μ):
    distribution f (ENNReal.ofReal t) μ ≤ ENNReal.ofReal (t ^ (-p.toReal)) *
    snorm f p μ ^ p.toReal := by
  have p_ne_0 : p ≠ 0 := Ne.symm (ne_of_lt hp)
  have p_toReal_ne_0 : p.toReal ≠ 0 := by
    apply ne_of_gt
    exact exp_toReal_pos hp hp_ne_top
  have set_incl :
    {x | ENNReal.ofReal t < ↑‖f x‖₊} ⊆ {x | ENNReal.ofReal (t ^ p.toReal) ≤ ↑‖f x‖₊ ^ p.toReal} := by
    intro x
    rw [← ofReal_rpow_of_pos ht]
    simp only [mem_setOf_eq]
    intro h
    refine (ENNReal.rpow_le_rpow_iff (exp_toReal_pos hp hp_ne_top)).mpr (le_of_lt h)
  unfold distribution
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (t ^ (p.toReal) )) ?_ ?_).mp ?_
  · apply ne_of_gt (ofReal_pos.mpr (Real.rpow_pos_of_pos ht (p.toReal)))
  · exact coe_ne_top
  · unfold snorm snorm'
    split_ifs with h
    · exact False.elim (p_ne_0 h)
    · rw [one_div]
      rw [ENNReal.rpow_inv_rpow p_toReal_ne_0]
      rw [← mul_assoc]
      rw [← ofReal_mul (by positivity)]
      rw [← Real.rpow_add ht]
      simp only [add_right_neg, Real.rpow_zero, ofReal_one, one_mul]
      calc
      _ ≤ ENNReal.ofReal (t ^ p.toReal) * μ {x | ENNReal.ofReal (t ^ p.toReal) ≤ ↑‖f x‖₊ ^ p.toReal} := by
        gcongr
      _ ≤ _ := by
        apply mul_meas_ge_le_lintegral₀ (AEMeasurable.pow_const (AEMeasurable.ennnorm hf) _)

-- TODO: check which assumption is really needed on q
lemma weakℒp_interpolate_lower {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ico 1 p) {f : α → E₁}
    (hf : MemWℒp f p μ) (hμf : μ (Function.support f) < ⊤) :
    Memℒp f q μ := by
  let q' := q.toReal
  have coe_q : ENNReal.ofReal (q') = q := ofReal_toReal_eq_iff.mpr (LT.lt.ne_top hq.2)
  have one_le_q' : 1 ≤ q' := one_le_ofReal.mp (le_of_le_of_eq hq.1 (Eq.symm coe_q))
  have q'min_1 : 0 ≤ q' - 1 := by linarith
  have q'pos : q' > 0 := by linarith
  have obs_distr : distribution f 0 μ < ⊤ := by
    refine lt_of_eq_of_lt ?_ hμf; unfold distribution; apply congr_arg; unfold Function.support
    simp
  refine ⟨hf.1, ?_⟩
  rw [← coe_q]
  rw [snorm_pow_eq_distribution' (AEStronglyMeasurable.aemeasurable hf.1) q'pos]
  · refine (rpow_lt_top_iff_of_pos ?hy).mpr ?_
    · exact inv_pos_of_pos (lt_of_lt_of_le Real.zero_lt_one one_le_q')
    · refine mul_lt_top coe_ne_top ?_
      refine (ne_of_lt ?_)
      have est := hf.2
      unfold wnorm at est
      split_ifs at est with is_ptop
      · let M := (snormEssSup f μ).toReal
        have coe_M : ENNReal.ofReal M = (snormEssSup f μ) :=
            ofReal_toReal_eq_iff.mpr (ne_of_lt est)
        rw [lintegral_double_restrict_set (B := Ioo (0 : ℝ) (snormEssSup f μ).toReal)
            measurableSet_Ioi measurableSet_Ioo]
        · rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
          calc
          _ ≤ ∫⁻ (_ : ℝ) in Ioo 0 M,
              distribution f 0 μ * .ofReal (M ^ (q' - 1)) := by
            apply setLIntegral_mono' measurableSet_Ioo
            intro x hx
            apply mul_le_mul'
            · exact distribution_mono_right (zero_le _)
            · exact ofReal_le_ofReal <|
                  Real.rpow_le_rpow (le_of_lt hx.1) (le_of_lt hx.2) (by linarith)
          _ = distribution f 0 μ * .ofReal (M ^ (q' - 1)) * volume (Ioo 0 M) :=
            setLIntegral_const (Ioo 0 M) (distribution f 0 μ * ENNReal.ofReal (M ^ (q' - 1)))
          _ = distribution f 0 μ * .ofReal (M ^ (q' - 1)) * .ofReal M := by
            rw [@Real.volume_Ioo]; simp
          _ < _ := mul_lt_top (mul_ne_top (LT.lt.ne_top obs_distr) coe_ne_top) coe_ne_top
        · apply ae_of_all
          intro t ht; simp at ht
          have := ht.2 ht.1
          have : distribution f (ENNReal.ofReal t) μ ≤ distribution f (.ofReal M) μ := by
            apply distribution_mono_right'
            apply ofReal_le_ofReal (by linarith)
          have : distribution f (.ofReal M) μ = 0 := by
            rw [coe_M]; exact meas_snormEssSup_lt
          calc
          _ ≤ distribution f (.ofReal M) μ * ENNReal.ofReal (t ^ (q' - 1)) := by
            exact mul_le_mul_right' (distribution_mono_right' (ofReal_le_ofReal (by linarith))) _
          _ = 0 * ENNReal.ofReal (t ^ (q' - 1)) := by rw[coe_M, distribution_snormEssSup]
          _ = _ := by exact zero_mul _
      · let M := (wnorm' f p.toReal μ).toReal
        have coe_M : ENNReal.ofReal M = (wnorm' f p.toReal μ) :=
            ofReal_toReal_eq_iff.mpr (ne_of_lt est)
        let p' := p.toReal
        have coe_p : ENNReal.ofReal p' = p := by
          exact ofReal_toReal_eq_iff.mpr is_ptop
        have p_pos : p > 0 := lt_of_lt_of_le zero_lt_one hp
        have p'pos : p' > 0 := toReal_pos_iff.mpr ⟨p_pos, Ne.lt_top is_ptop⟩
        have one_le_p' : 1 ≤ p' := by refine one_le_ofReal.mp ?_; rw [coe_p]; exact hp
        have q'lt_p': q' < p' := toReal_strict_mono is_ptop hq.2
        have obs : ∀ t : ℝ,
            (.ofReal t) * distribution f (.ofReal t) μ ^ p'⁻¹ ≤ (ENNReal.ofReal M) := by
          intro t
          have coe_t : (.ofReal t) = (ofNNReal t.toNNReal) := rfl
          rw [coe_t, coe_M]
          exact le_iSup (fun t : ℝ≥0 ↦ ↑t * distribution f (↑t) μ ^ p'⁻¹) t.toNNReal
        have : ∀ t ∈ Ioi (0 : ℝ), distribution f (.ofReal t) μ ^ p'⁻¹ ≤
            (.ofReal t)⁻¹ * (ENNReal.ofReal M) := by
          intro t ht
          refine (ENNReal.mul_le_iff_le_inv ?hr₀ ?hr₁).mp (obs t)
          · exact ne_of_gt (ofReal_pos.mpr ht)
          · exact coe_ne_top
        have : ∀ t ∈ Ioi (0 : ℝ), distribution f (.ofReal t) μ ≤
            ((.ofReal t)⁻¹ * (ENNReal.ofReal M)) ^ p' := by
          intro t ht
          refine (ENNReal.rpow_one_div_le_iff ?hz).mp ?_
          · exact p'pos
          · rw [one_div]
            exact this t ht
        calc
        _ = ∫⁻ t : ℝ in Ioc 0 1 ∪ Ioi 1, distribution f (.ofReal t) μ *
            ENNReal.ofReal (t ^ (q' - 1)) := by
          rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt Real.zero_lt_one)]
        _ ≤ _ := lintegral_union_le _ (Ioc (0 : ℝ) (1 : ℝ)) (Ioi (1 : ℝ))
        _ < ⊤ := by
          refine add_lt_top.mpr ⟨?_, ?_⟩
          · calc
            _ ≤ _ := by
              apply setLIntegral_mono' measurableSet_Ioc
              intro t ht
              apply mul_le_mul' (distribution_mono_right (zero_le (.ofReal t)))
              apply ofReal_le_ofReal
              apply Real.rpow_le_rpow (le_of_lt ht.1) ht.2 q'min_1
            _ = distribution f 0 μ * ENNReal.ofReal (1 ^ (q' - 1)) * volume (Ioc (0 : ℝ) 1) :=
              setLIntegral_const (Ioc 0 1) (distribution f 0 μ * ENNReal.ofReal (1 ^ (q' - 1)))
            _ = distribution f 0 μ * ENNReal.ofReal (1 ^ (q' - 1)) := by
              rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
            _ < ⊤ := by
              apply mul_lt_top (ne_of_lt obs_distr) coe_ne_top
          · calc
            _ ≤ ∫⁻ t : ℝ in Ioi 1,
                ((ENNReal.ofReal t)⁻¹ * ENNReal.ofReal M) ^ p' * ENNReal.ofReal (t ^ (q' - 1))
                := by
              apply setLIntegral_mono' measurableSet_Ioi
              intro t ht
              apply mul_le_mul'
              · refine this t (lt_trans Real.zero_lt_one ht)
              · exact Preorder.le_refl (ENNReal.ofReal (t ^ (q' - 1)))
            _ = ∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal M ^ p' * ‖t ^ (-p' + q' - 1)‖₊ := by
              apply lintegral_congr_ae
              filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
              intro t ht
              have t_pos : t > 0 := lt_trans Real.zero_lt_one ht
              have h₀ : 0 ≤ t ^ (-p') := Real.rpow_nonneg (le_of_lt t_pos) (-p')
              rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt p'pos),
                  mul_comm _ (ENNReal.ofReal M ^ p')]
              rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, neg_one_mul,
                  ENNReal.ofReal_rpow_of_pos t_pos, mul_assoc, ← ofReal_mul h₀,
                  ← Real.rpow_add t_pos, add_sub]
              have tpp : t ^ (-p' + q' - 1) > 0 := Real.rpow_pos_of_pos t_pos (-p' + q' - 1)
              nth_rewrite 1 [← abs_of_pos tpp, ← Real.norm_eq_abs, ← norm_toNNReal]; rfl
            _ = ENNReal.ofReal M ^ p' * ∫⁻ t : ℝ in Ioi 1, ‖t ^ (-p' + q' - 1)‖₊ := by
              rw [← lintegral_const_mul']
              refine rpow_ne_top_of_nonneg (le_of_lt p'pos) coe_ne_top
            _ < ⊤ := by
              refine mul_lt_top ?_ ?_
              · exact LT.lt.ne_top (rpow_lt_top_of_nonneg
                    (le_of_lt (lt_of_lt_of_le Real.zero_lt_one one_le_p')) coe_ne_top)
              · have hpq : (-p' + q' - 1) < -1 := by linarith
                exact LT.lt.ne_top (integrableOn_Ioi_rpow_of_lt hpq Real.zero_lt_one).2

-- TODO: the proof below has quite some duplication with the proof above
lemma weakℒp_interpolate_higher {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ioi p) {f : α → E₁}
    (hf : MemWℒp f p μ) (hfinf : snormEssSup f μ < ⊤) :
    Memℒp f q μ := by
  refine ⟨hf.1, ?_⟩
  rcases (eq_top_or_lt_top q) with q_eq_top | q_ne_top
  · rw [q_eq_top]
    simp; exact hfinf
  · let q' := q.toReal
    have coe_q : ENNReal.ofReal (q') = q := ofReal_toReal_eq_iff.mpr (LT.lt.ne_top q_ne_top)
    have p_lt_q : p < q := hq
    have p_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have q_pos : 0 < q := lt_trans p_pos p_lt_q
    have q'pos : 0 < q':= by
      apply toReal_pos_iff.mpr; exact ⟨q_pos, q_ne_top⟩
    have q'inv_pos : 0 < q'⁻¹ := inv_pos_of_pos q'pos
    rw [← coe_q]
    rw [snorm_pow_eq_distribution' (AEStronglyMeasurable.aemeasurable hf.1) q'pos]
    · apply rpow_lt_top_of_nonneg
      · exact le_of_lt q'inv_pos
      · refine ne_of_lt ?_
        have est := hf.2
        unfold wnorm at est
        let M := (snormEssSup f μ).toReal
        have M_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
        have coe_M : ENNReal.ofReal M = (snormEssSup f μ) :=
          ofReal_toReal_eq_iff.mpr (ne_of_lt hfinf)
        split_ifs at est with is_ptop
        · rw [is_ptop] at p_lt_q
          simp only [not_top_lt] at p_lt_q
        · rw [lintegral_double_restrict_set (B := Ioo (0 : ℝ) (M + 1)) measurableSet_Ioi
              measurableSet_Ioo]
          · rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
            let L := (wnorm' f p.toReal μ).toReal
            have L_nonneg : 0 ≤ L := toReal_nonneg
            have coe_L : ENNReal.ofReal L = (wnorm' f p.toReal μ) :=
                ofReal_toReal_eq_iff.mpr (ne_of_lt est)
            let p' := p.toReal
            have p'pos : p' > 0 := toReal_pos_iff.mpr ⟨p_pos, Ne.lt_top is_ptop⟩
            have q'lt_p': p' < q' := by
              refine toReal_strict_mono (LT.lt.ne_top q_ne_top) p_lt_q
            calc
            _ ≤ ENNReal.ofReal (q' * L ^ p') * ∫⁻ (t : ℝ) in Ioo 0 (M + 1),
                ‖t ^ (q' - p' - 1)‖₊ := by
              rw [ofReal_mul (le_of_lt q'pos)]
              rw [mul_assoc (ENNReal.ofReal q')]
              nth_rewrite 2 [← lintegral_const_mul']; swap; exact coe_ne_top
              apply mul_le_mul'
              · exact Preorder.le_refl (ENNReal.ofReal q')
              · apply setLIntegral_mono' measurableSet_Ioo
                intro t ht
                have t_pos := ht.1
                have : q' - 1 = p' + (q'- p' - 1) := by linarith
                rw [this, Real.rpow_add t_pos,
                    ofReal_mul (le_of_lt (Real.rpow_pos_of_pos t_pos p')), ← mul_assoc]
                apply mul_le_mul'
                · rw [← ENNReal.ofReal_rpow_of_nonneg L_nonneg (le_of_lt p'pos)]
                  rw [coe_L]
                  unfold wnorm'
                  have coe_t : (.ofReal t) = (ofNNReal t.toNNReal) := rfl
                  have tp_pos : 0 < t ^ p' := Real.rpow_pos_of_pos t_pos p'
                  refine (ENNReal.rpow_one_div_le_iff p'pos).mp ?_
                  rw [mul_comm, one_div,
                      ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (inv_pos_of_pos p'pos)),
                      ENNReal.ofReal_rpow_of_nonneg (le_of_lt tp_pos)
                        (le_of_lt (inv_pos_of_pos p'pos)),
                      Real.rpow_rpow_inv (le_of_lt t_pos) (ne_of_gt p'pos), coe_t]
                  refine le_iSup (fun t : ℝ≥0 ↦ ↑t * distribution f (↑t) μ ^ p'⁻¹) t.toNNReal
                · have tpp : t ^ (q' - p' - 1) > 0 := Real.rpow_pos_of_pos t_pos (q' - p' - 1)
                  rw [← norm_toNNReal, Real.norm_eq_abs, abs_of_pos tpp]
                  apply Preorder.le_refl
            _ < ⊤ := by
              apply mul_lt_top coe_ne_top
              have zero_lt_Mp1 : 0 < M + 1 := by linarith
              have hqp2 : -1 < q' - p' - 1 := by linarith
              exact LT.lt.ne_top
                  ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_Mp1).mpr hqp2).2
          · -- TODO do something with this code duplication from the other proof
            apply ae_of_all
            intro t ht; simp at ht
            have := ht.2 ht.1
            have : distribution f (ENNReal.ofReal t) μ ≤ distribution f (ENNReal.ofReal M) μ := by
              apply distribution_mono_right'
              apply ofReal_le_ofReal (by linarith)
            have : distribution f (ENNReal.ofReal M) μ = 0 := by
              rw [coe_M]; exact meas_snormEssSup_lt
            calc
            _ ≤ distribution f (ENNReal.ofReal M) μ * ENNReal.ofReal (t ^ (q' - 1)) := by
              exact mul_le_mul_right' (distribution_mono_right' (ofReal_le_ofReal (by linarith))) _
            _ = 0 * ENNReal.ofReal (t ^ (q' - 1)) := by rw[coe_M, distribution_snormEssSup]
            _ = _ := by exact zero_mul _

/-- ### Applications of interpolation properties to truncations -/

lemma computation_smul_norms {t : ℝ} {f : α → E} (x : α) (hfx : ‖f x‖ > 0) :
    ‖(t * ‖f x‖⁻¹) • f x‖ = |t| := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hfx), mul_assoc,
      inv_mul_cancel (ne_of_gt hfx), mul_one]

lemma trunc_bdd {f : α → E₁} {a : ℝ} (x : α) : ‖trunc f a x‖ ≤ |a| := by
  unfold trunc
  split_ifs with h
  · refine le_trans h (le_abs_self a)
  · simp at h
    rw [computation_smul_norms]; linarith
  · simp

/-- A small lemma that is helpful for rewriting -/
lemma coe_coe_eq_ofReal (a : ℝ) : ofNNReal a.toNNReal = ENNReal.ofReal a := by rfl

lemma trunc_snormEssSup_le {f : α → E₁} {a : ℝ} : snormEssSup (trunc f a) μ ≤
    ENNReal.ofReal |a| := by
  apply essSup_le_of_ae_le
  apply ae_of_all
  intro x
  simp only [← norm_toNNReal, coe_coe_eq_ofReal]
  exact  ofReal_le_ofReal <| trunc_bdd x

lemma trunc_le_func {f : α → E₁} {a : ℝ} {x : α} : ‖trunc f a x‖ ≤ ‖f x‖ := by
  unfold trunc
  split_ifs with h
  · exact Preorder.le_refl ‖f x‖
  · rw [computation_smul_norms]
    · rw [abs_of_pos (by positivity)]
      exact le_of_not_ge h
    · linarith
  · simp only [norm_zero, norm_nonneg]

lemma trunc_compl_le_func {f : α → E₁} {a : ℝ} {x : α} : ‖(f - trunc f a) x‖ ≤ ‖f x‖ := by
  unfold trunc
  simp only [Pi.sub_apply]
  split_ifs with h₁ h₂
  · simp only [sub_self, norm_zero, norm_nonneg]
  · have : ((1 : ℝ) • f x) = f x := by exact MulAction.one_smul (f x)
    nth_rw 1 [← this]
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_pos]
    · refine mul_le_of_le_one_left ?_ ?_
      · exact norm_nonneg (f x)
      · refine sub_le_self 1 ?_
        positivity
    · refine sub_pos.mpr ?_
      rw [← div_eq_mul_inv]
      refine (div_lt_one ?_).mpr ?_
      · refine lt_trans h₂ (lt_of_not_ge h₁)
      · exact lt_of_not_ge h₁
  · simp only [sub_zero, le_refl]

lemma trunc_preserves_Lp {p : ℝ≥0∞} {a : ℝ} (hf : Memℒp f p μ) :
    Memℒp (trunc f a) p μ := by
  refine ⟨aestronglyMeasurable_trunc hf.1, ?_⟩
  refine lt_of_le_of_lt ?_ hf.2
  apply snorm_mono_ae
  apply ae_of_all
  intro x
  unfold trunc
  split_ifs with is_fx_le_a is_a_pos
  · exact le_refl _
  · have fx_t_0 : ‖f x‖ > 0 := by linarith
    rw [computation_smul_norms]; swap; exact fx_t_0
    rw [abs_of_pos is_a_pos]; simp at is_fx_le_a; linarith
  · simp

lemma snorm_trunc_compl_le {p : ℝ≥0∞} {a : ℝ} : snorm (f - trunc f a) p μ ≤
    snorm f p μ := by
  apply snorm_mono
  intro x
  apply trunc_compl_le_func

lemma trunc_compl_preserves_Lp {p : ℝ≥0∞} {a : ℝ} (hf : Memℒp f p μ) :
    Memℒp (f - trunc f a) p μ := by
  have truncLp : Memℒp (trunc f a) p μ := trunc_preserves_Lp hf
  apply Memℒp.sub hf truncLp

lemma trunc_Lp_MemLq_higher {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q > p) {f : α → E₁}
    (hf : Memℒp f p μ) (a : ℝ) : Memℒp (trunc f a) q μ := by
  have : MemWℒp f p μ := by
    apply Memℒp.memWℒp hp hf
  apply weakℒp_interpolate_higher hp hq
  · apply Memℒp.memWℒp hp
    apply trunc_preserves_Lp hf
  · have coe_a_lt_top : ENNReal.ofReal |a| < ⊤ := coe_lt_top
    refine lt_of_le_of_lt ?_ coe_a_lt_top
    apply trunc_snormEssSup_le

lemma distribution_finite_for_finite_snorm {f : α → E₁} {p : ℝ} (hp : 0 < p)
    (hf : AEMeasurable f μ) (f_fin : snorm' f  p μ < ⊤) {t : ℝ} (ht : t > 0) :
    distribution f (.ofReal t) μ < ⊤ := by
  unfold snorm' at f_fin
  have obs : ∫⁻ (a : α), ↑‖f a‖₊ ^ p ∂μ < ⊤ := by
    exact lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hp f_fin
  rw [lintegral_norm_pow_eq_distribution' hf hp] at obs
  have p_ne_0 : ENNReal.ofReal p ≠ 0 := (ne_of_gt (ofReal_pos.mpr hp))
  have : ∫⁻ (t : ℝ) in Ioi 0,
      distribution f (ENNReal.ofReal t) μ * ENNReal.ofReal (t ^ (p - 1)) < ⊤ := by
    contrapose obs
    simp
    simp at obs
    rw [obs]
    exact mul_top p_ne_0
  have : volume {t : ℝ | t ∈ Ioi 0 ∧ distribution f (ENNReal.ofReal t) μ *
      ENNReal.ofReal (t ^ (p - 1)) = ⊤} = 0 := by
    apply measure_eq_top_of_setLintegral_ne_top
    · -- TODO: extract as lemma
      apply Measurable.aemeasurable
      apply Measurable.mul
      · apply distribution_measurable_from_real
      · refine Measurable.ennreal_ofReal ?_
        exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) (p - 1)
    · exact LT.lt.ne_top this
  contrapose this
  have ttop : (distribution f (ENNReal.ofReal t) μ = ⊤) := by
    exact not_lt_top.mp this
  apply ne_of_gt
  calc
  0 < ENNReal.ofReal t := ofReal_pos.mpr ht
  _ = ENNReal.ofReal (t - 0) := by rw [sub_zero]
  _ = volume (Ioo 0 t) := by exact Eq.symm Real.volume_Ioo
  _ ≤ _ := by
    apply measure_mono
    intro s hs
    refine ⟨hs.1, ?_⟩
    have dbtop : distribution f (ENNReal.ofReal s) μ = ⊤ := by
      apply eq_top_iff.mpr
      refine le_of_eq_of_le (Eq.symm ttop) ?_
      apply distribution_mono_right
      apply ofReal_le_ofReal
      exact (le_of_lt hs.2)
    rw [dbtop]
    apply top_mul
    apply ne_of_gt
    refine ofReal_pos.mpr ?_
    exact Real.rpow_pos_of_pos hs.1 (p - 1)


lemma trunc_compl_Lp_Lq_lower {p q : ℝ≥0∞} (hp : p ∈ Ico 1 ⊤) (hq : q ∈ Ico 1 p) {f : α → E₁}
    (hf : Memℒp f p μ) {a : ℝ} (ha : a > 0) : Memℒp (f - trunc f a) q μ := by
  apply weakℒp_interpolate_lower hp.1 hq
  · apply Memℒp.memWℒp hp.1
    apply trunc_compl_preserves_Lp hf
  · unfold Function.support
    have key : distribution (f - trunc f a) 0 μ < ⊤ := by
      rw [distribution_shift_trunc]
      rw [coe_coe_eq_ofReal]
      rw [← ofReal_zero]
      rw [← ofReal_add]
      · have p_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp.1
        let p' := p.toReal
        have coe_p : ENNReal.ofReal p' = p := by
          refine ofReal_toReal_eq_iff.mpr ?_
          apply LT.lt.ne_top
          exact hp.2
        have p'pos : 0 < p' := by
          apply toReal_pos_iff.mpr
          exact ⟨p_pos, hp.2⟩
        apply distribution_finite_for_finite_snorm p'pos
        · exact (AEStronglyMeasurable.aemeasurable hf.1)
        · have est := hf.2
          unfold snorm at est
          split_ifs at est with is_p_0 is_p_top
          · exact False.elim <| ne_of_gt p_pos is_p_0
          · exact False.elim <| ofReal_toReal_eq_iff.mp coe_p is_p_top
          · exact est
        · linarith
      · exact Preorder.le_refl 0
      · exact (le_of_lt ha)
    refine lt_of_eq_of_lt ?_ key; apply congr_arg; ext x; simp

lemma trunc_compl_Lp_Lq_est {p q : ℝ≥0∞} (hp : p ∈ Ioo 0 ⊤) (hq : q ∈ Ioo 0 p) {f : α → E₁}
    (hf : AEMeasurable f μ) {a : ℝ} (ha : a > 0) :
    snorm (f - trunc f a) q μ ^ q.toReal ≤
    (1 + q / p) * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
    snorm f p μ ^ p.toReal := by
  have q_pos := hq.1
  have q_lt_p := hq.2
  have p_pos := hp.1
  have p_lt_top := hp.2
  have p_ne_top : p ≠ ⊤ := LT.lt.ne_top p_lt_top
  have q_ne_top : q ≠ ⊤ := LT.lt.ne_top q_lt_p
  have p_ne_0 : p ≠ 0 := by exact Ne.symm (ne_of_lt p_pos)
  have q_ne_0 : q ≠ 0 := by exact Ne.symm (ne_of_lt q_pos)
  have coe_q : ENNReal.ofReal q.toReal = q := by exact ofReal_toReal_eq_iff.mpr q_ne_top
  have coe_p : ENNReal.ofReal p.toReal = p := by exact ofReal_toReal_eq_iff.mpr p_ne_top
  calc
  _ ≤ distribution (f - trunc f a) 0 μ * ENNReal.ofReal (a ^ q.toReal) +
      ENNReal.ofReal q.toReal * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
      ((ENNReal.ofReal p.toReal)⁻¹ * snorm (f - trunc f a) (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
    apply ℒp_interpolate_lower p_pos p_ne_top hq ha
    sorry
  _ = distribution f (ENNReal.ofReal a) μ * ENNReal.ofReal (a ^ q.toReal) +
      ENNReal.ofReal q.toReal * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
      ((ENNReal.ofReal p.toReal)⁻¹ * snorm (f - trunc f a) (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
    rw [distribution_shift_trunc]
    rw [zero_add]
    rw [coe_coe_eq_ofReal]
  _ ≤ ENNReal.ofReal (a ^ (-p.toReal)) *
      snorm f p μ ^ p.toReal * ENNReal.ofReal (a ^ q.toReal) +
      ENNReal.ofReal q.toReal * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
      ((ENNReal.ofReal p.toReal)⁻¹ * snorm f (ENNReal.ofReal p.toReal) μ ^ p.toReal) := by
    gcongr
    · apply distribution_le_integral_p <;> assumption
    · apply snorm_trunc_compl_le
  _ = ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
      snorm f p μ ^ p.toReal * (1 + q / p) := by
    rw [mul_comm, ← mul_assoc, ← ofReal_mul (by positivity), ← Real.rpow_add ha]
    nth_rw 3 [mul_comm]
    rw [mul_assoc, mul_add, ← mul_assoc (ENNReal.ofReal q.toReal), coe_q, coe_p]
    rw [mul_comm (q * p⁻¹), ← mul_assoc, mul_one, ← div_eq_mul_inv]
    rfl
  _ = _ := by
    rw [mul_comm, ← mul_assoc]

lemma trunc_Lp_Lq_est {p q : ℝ≥0∞} (hp : p > 0) (hq : q ∈ Ioo p ⊤) {f : α → E₁}
    (hf : AEMeasurable f μ) {a : ℝ} (ha : a > 0) : -- (hM : snormEssSup f μ ≠ ⊤)
    snorm (trunc f a) q μ ^ q.toReal ≤ (q / p) * (ENNReal.ofReal (a ^ (q.toReal - p.toReal))) * snorm f p μ ^ p.toReal := by
  have q_le_p_toReal : 0 ≤ q.toReal - p.toReal := by
    refine sub_nonneg_of_le ?_
    refine toReal_mono ?_ ?_
    · exact LT.lt.ne_top hq.2
    · exact le_of_lt hq.1
  have : snormEssSup (trunc f a) μ ≤ ENNReal.ofReal a := by
    calc
    _ ≤ ENNReal.ofReal |a| := by
      apply trunc_snormEssSup_le (f := f) (μ := μ)
    _ = ENNReal.ofReal a := by rw [abs_of_pos ha]
  have hM : snormEssSup (trunc f a) μ ≠ ⊤ := by
    apply LT.lt.ne_top (b := ⊤)
    apply lt_of_le_of_lt this
    exact coe_lt_top
  have p_lt_q := hq.1
  calc
  _ ≤ (q / p) * (snormEssSup (trunc f a) μ) ^ (q.toReal - p.toReal) * snorm (trunc f a) p μ ^ p.toReal := by
    apply ℒp_interpolate_higher hp hq _ hM
    sorry
  _ ≤ _ := by
    rw [← ofReal_rpow_of_nonneg] <;> try positivity
    gcongr
    apply snorm_mono
    exact fun x ↦ trunc_le_func

/-- Estimate the strong norm of the complement of the truncation by an integral involving
  the distribution function-/
lemma estimate_snorm_trunc_compl_ {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (hf : AEStronglyMeasurable f μ) {a : ℝ}
    (ha : a ≥ 0) :
  snorm (f - trunc f a) (ENNReal.ofReal p₀) μ =
  (∫⁻ s : ℝ in Ioi (a : ℝ), ENNReal.ofReal p₀ * ENNReal.ofReal ((s - a) ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
  rewrite [← lintegral_add_right_Ioi (a := a), sub_self]
  simp only [add_sub_cancel_right]
  rw [snorm_pow_eq_distribution']
  rw [← lintegral_const_mul']
  refine congrFun (congrArg ?_ ?_) p₀⁻¹
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro t ht
    rw [distribution_shift_trunc]
    rw [mul_comm _ (ENNReal.ofReal (t ^ (p₀ - 1))), ← mul_assoc]
    congr
    · rw [ofReal_add]
      · rw [coe_coe_eq_ofReal]
      · exact (le_of_lt ht)
      · exact ha
  · exact coe_ne_top
  · apply AEStronglyMeasurable.aemeasurable
    apply aestronglyMeasurable_trunc_compl hf
  · linarith

lemma estimate_snorm_trunc_compl {p₀ : ℝ} {a : ℝ}
    (hp₀ : 1 ≤ p₀) (hf : AEStronglyMeasurable f μ) (ha : 0 ≤ a) :
    snorm (f - trunc f a) (ENNReal.ofReal p₀) μ ≤
    (∫⁻ s : ℝ in Ioi a, ENNReal.ofReal p₀ * ENNReal.ofReal (s ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
  rw [estimate_snorm_trunc_compl_ hp₀ hf ha]
  refine (ENNReal.rpow_one_div_le_iff (inv_pos_of_pos (by linarith))).mp ?_
  simp
  rw [ENNReal.rpow_inv_rpow (by linarith)]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t (t_gt_a : a < t)
  -- rw [mem_Ioi] at t_gt_a
  refine mul_le_mul_three (le_of_eq rfl) ?_ (le_of_eq rfl)
  -- rw [ofReal_rpow_of_pos (lt_of_le_of_lt ha t_gt_a)]
  apply ofReal_le_ofReal_iff'.mpr; left; apply Real.rpow_le_rpow <;> linarith

-- TODO: weaken to AEMeasurable
lemma estimate_snorm_trunc_compl_interp {p q : ℝ≥0∞} (hp : p ∈ Ioo 0 ⊤) (hq : q ∈ Ico 1 p) {f : α → E₁}
    (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : a > 0) :
    snorm (f - trunc f a) q μ ^ q.toReal ≤
    (q / p) * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
    snorm f p μ ^ p.toReal := by
  have q_lt_p := hq.2
  have coe_p : ENNReal.ofReal p.toReal = p := ofReal_toReal (LT.lt.ne_top hp.2)
  have coe_q : ENNReal.ofReal q.toReal = q := ofReal_toReal (LT.lt.ne_top q_lt_p)
  calc
  _ ≤ ((∫⁻ s : ℝ in Ioi a, q * ENNReal.ofReal (s ^ (q.toReal - 1)) *
      distribution f (ENNReal.ofReal s) μ) ^ (q.toReal⁻¹)) ^ q.toReal := by
    gcongr
    nth_rw 1 [← coe_q]; nth_rw 2 [← coe_q]
    apply estimate_snorm_trunc_compl
    · exact one_le_toReal hq.1 (Ne.lt_top (LT.lt.ne_top q_lt_p))
    · exact hf
    · exact (le_of_lt ha)
  _ = ∫⁻ s : ℝ in Ioi a, q * ENNReal.ofReal (s ^ (q.toReal - 1)) *
      distribution f (ENNReal.ofReal s) μ := by
    rw [ENNReal.rpow_inv_rpow]
    exact exp_toReal_ne_zero_of_Ico hq
  _ ≤ ∫⁻ s : ℝ in Ioi a, q * (ENNReal.ofReal (s ^ (p.toReal - 1)) * ENNReal.ofReal (a ^ ((q.toReal - 1) - (p.toReal - 1)))) *
      distribution f (ENNReal.ofReal s) μ := by
    apply setLIntegral_mono_ae' measurableSet_Ioi
    apply ae_of_all
    intro s hs
    gcongr
    apply rpow_le_rpow_of_exponent_le_base_ge
    · exact ha
    · exact (le_of_lt hs)
    · refine tsub_le_tsub_right ?_ 1
      apply toReal_mono
      · exact ne_top_of_Ioo hp
      · exact le_of_lt q_lt_p
  _ = (q * ∫⁻ s : ℝ in Ioi a, (distribution f (ENNReal.ofReal s) μ * ENNReal.ofReal (s ^ (p.toReal - 1))) ) * ENNReal.ofReal (a ^ (q.toReal - p.toReal))
       := by
    rw [← lintegral_const_mul']; swap; exact ne_top_of_Ico hq
    rw [← lintegral_mul_const']; swap; exact coe_ne_top
    simp_rw [sub_sub_sub_cancel_right]; apply congr_arg; ext x; ring
  _ = (q / p) * ((ENNReal.ofReal p.toReal * ∫⁻ s : ℝ in Ioi a, (distribution f (ENNReal.ofReal s) μ * ENNReal.ofReal (s ^ (p.toReal - 1))) ) ^ (p.toReal⁻¹)) ^ p.toReal * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) := by
    rw [ENNReal.rpow_inv_rpow (toReal_ne_zero_of_Ioo hp)]
    rw [← mul_assoc (q / p)]
    congr
    rw [coe_p]
    rw [ENNReal.div_mul_cancel]
    · exact ne_of_gt hp.1
    · exact LT.lt.ne_top hp.2
  _ ≤ (q / p) * ((ENNReal.ofReal p.toReal * ∫⁻ s : ℝ in Ioi 0, (distribution f (ENNReal.ofReal s) μ * ENNReal.ofReal (s ^ (p.toReal - 1))) ) ^ (p.toReal⁻¹)) ^ p.toReal * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) := by
    gcongr
    apply lintegral_mono_set
    refine Ioi_subset_Ioi (le_of_lt ha)
  _ = (q / p) * (snorm f p μ) ^ p.toReal * ENNReal.ofReal (a ^ (q.toReal - p.toReal)) := by
    nth_rw 8 [← coe_p]
    congr
    apply Eq.symm
    apply snorm_pow_eq_distribution'
    · exact AEStronglyMeasurable.aemeasurable hf
    · exact toReal_pos_of_Ioo hp
  _ = _ := by ring

/-- ## Weaktype estimates applied to truncations -/

lemma weaktype_estimate {C₀ : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q < ⊤)
  {f : α → E₁} (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p q μ ν C₀) {t : ℝ} (ht : t > 0) :
    distribution (T f) (ENNReal.ofReal t) ν ≤ C₀ ^ q.toReal *
        snorm f p μ ^ q.toReal * ENNReal.ofReal (t ^ (-q.toReal)) := by
  have wt_est := (h₀T f hf).2 -- the weaktype estimate
  have q_pos : q.toReal > 0 := by
    refine toReal_pos ?_ ?_
    · apply (ne_of_gt)
      apply (lt_of_lt_of_le zero_lt_one hq)
    · exact LT.lt.ne_top hq'
  have tq_pos : ENNReal.ofReal t ^ q.toReal > 0 := coe_pow_pos ht
  have tq_ne_top : (ENNReal.ofReal t) ^ q.toReal ≠ ⊤ := by
    apply coe_pow_ne_top'
    exact one_le_toReal hq hq'
  -- have hq₁ : q.toReal = q := by exact toReal_ofReal q_nonneg
  have : q ≠ ⊤ := by exact LT.lt.ne_top hq'
  unfold wnorm wnorm' at wt_est; simp [this] at wt_est
  have wt_est_t := wt_est t.toNNReal -- this is the weaktype estimate applied to t
  rw [← ENNReal.mul_le_mul_right (c := (ENNReal.ofReal t) ^ q.toReal) _ tq_ne_top,
      ofReal_rpow_of_pos, mul_assoc _ _ (ENNReal.ofReal (t ^ q.toReal)), ← ofReal_mul',
      ← Real.rpow_add, neg_add_self, Real.rpow_zero, ofReal_one, mul_one, mul_comm,
      ← ENNReal.mul_rpow_of_nonneg] <;> try positivity
  refine (ENNReal.rpow_one_div_le_iff q_pos).mp ?_
  rw [ENNReal.mul_rpow_of_nonneg, one_div, ENNReal.ofReal_rpow_of_pos,
      Real.rpow_rpow_inv] <;> try positivity
  rwa [← coe_coe_eq_ofReal]
  -- apply wt_est_t
  -- exact wt_est_t

-- lemma weaktype_estimate_top_top {C₀ : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞} {hp : p = ⊤} {hq : q = ⊤}
--     {f : α → E₁} (hf : Memℒp f p μ)
--     (h₀T : HasWeakType T p q μ ν C₀) {t : ℝ} (ht : t > 0) :
--     distribution (T f) (ENNReal.ofReal t) ν = 0 := by
--   have wt_est := (h₀T f hf).2
--   unfold wnorm snorm at wt_est
--   simp [hq, hp] at wt_est
--   unfold distribution




-- TODO: this may need to be generalized to the cases where the exponents equal ⊤
lemma weaktype_estimate_trunc_compl {C₀ : ℝ≥0} {p p₀: ℝ≥0∞} (hp : 1 ≤ p) (hp' : p < ⊤) (hp₀ : 1 ≤ p₀) {q₀ : ℝ≥0∞}
  (hq₀ : 1 ≤ q₀) (hq₀' : q₀ < ⊤) (hp₀p : p₀ < p)
  {f : α → E₁} (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) {t : ℝ} (ht : t > 0) {a : ℝ} (ha : a > 0) :
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν ≤ C₀ ^ q₀.toReal *
        snorm (f - trunc f a) p₀ μ ^ q₀.toReal * (ENNReal.ofReal (t ^ (-q₀.toReal))) := by
  apply weaktype_estimate hq₀ hq₀'
  · apply trunc_compl_Lp_Lq_lower (p := p)
    · exact ⟨hp, hp'⟩
    · exact ⟨hp₀, hp₀p⟩
    · exact hf
    · exact ha
  · exact h₀T
  · exact ht

lemma weaktype_estimate_trunc {C₁ : ℝ≥0} {p p₁ q₁: ℝ≥0∞} (hp : 1 ≤ p)
  (hq₁ : 1 ≤ q₁) (hq₁' : q₁ < ⊤) (hp₁p : p < p₁)
  {f : α → E₁} (hf : Memℒp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : t > 0) {a : ℝ} :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν ≤ C₁ ^ q₁.toReal *
        snorm (trunc f a) p₁ μ ^ q₁.toReal * ENNReal.ofReal (t ^ (-q₁.toReal)) := by
  apply weaktype_estimate hq₁ hq₁'
  · apply trunc_Lp_MemLq_higher (p := p)
    · exact hp
    · exact hp₁p
    · exact hf
  · exact h₁T
  · exact ht

lemma weaktype_estimate_trunc_top_top {a : ℝ} {C₁ : ℝ≥0} (hC₁ : C₁ > 0) {p p₁ q₁ : ℝ≥0∞} (hp : 1 ≤ p)
    (hp₁ : p₁ = ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : Memℒp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : t > 0) (ha : a = t / C₁) :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  rw [ha]
  have obs : Memℒp (trunc f (t / C₁)) p₁ μ := by
    apply trunc_Lp_MemLq_higher hp hp₁p hf
  have wt_est := (h₁T (trunc f (t / C₁)) obs).2
  unfold wnorm snorm at wt_est
  simp [hq₁, hp₁] at wt_est
  apply nonpos_iff_eq_zero.mp
  have ineq : snormEssSup (T (trunc f (t / C₁))) ν ≤ ENNReal.ofReal t := calc
    _ ≤ C₁ * snormEssSup (trunc f (t / C₁)) μ := by
      apply wt_est
    _ ≤ C₁ * ENNReal.ofReal |t / C₁| := by
      gcongr
      apply trunc_snormEssSup_le
    _ ≤ _ := by
      let C := C₁.toReal
      have coe_C : C.toNNReal = C₁ := Real.toNNReal_coe
      have coe_C' : C.toNNReal.toReal = C := by exact congrArg toReal coe_C
      rw [← coe_C, coe_coe_eq_ofReal, ← ENNReal.ofReal_mul, abs_of_pos, coe_C', mul_div_cancel₀]
      · exact Ne.symm (ne_of_lt hC₁)
      · exact div_pos ht (lt_of_lt_of_eq hC₁ (Eq.symm coe_C'))
      · exact zero_le_coe
  calc
  _ ≤ distribution (T (trunc f (t / C₁))) (snormEssSup (T (trunc f (t / C₁))) ν) ν := by
    gcongr
  _ = 0 := by
    apply distribution_snormEssSup


-- TODO: move this up
-- TODO: check which ones are actually used
lemma eq_of_rpow_eq (a b: ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) (h : a ^ c = b ^ c) : a = b := by
  rw [← ENNReal.rpow_rpow_inv hc a, ← ENNReal.rpow_rpow_inv hc b]
  exact congrFun (congrArg HPow.hPow h) c⁻¹

lemma le_of_rpow_le {a b: ℝ≥0∞} {c : ℝ} (hc : c > 0) (h : a ^ c ≤ b ^ c) : a ≤ b := by
  rw [← ENNReal.rpow_rpow_inv (ne_of_gt hc) a, ← ENNReal.rpow_rpow_inv (ne_of_gt hc) b]
  refine (ENNReal.rpow_le_rpow_iff ?_).mpr h
  exact inv_pos_of_pos hc

lemma weaktype_estimate_trunc_compl_top {C₀ : ℝ≥0} (hC₀ : C₀ > 0) {p p₀ q₀ : ℝ≥0∞}
    (hp₀ : 1 ≤ p₀) (hq₀ : q₀ = ⊤) (hp₀p : p₀ < p) (hp : p ≠ ⊤) {f : α → E₁} (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) {t : ℝ} (ht : t > 0) {a : ℝ} {d : ℝ} -- (hd : d > 0)
    (ha : a = (t / d) ^
    (p₀.toReal / (p₀.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₀) ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal).toReal ^ p₀.toReal⁻¹) :
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  have p₀ne_top : p₀ ≠ ⊤ := LT.lt.ne_top hp₀p
  rcases (eq_zero_or_pos (snormEssSup f μ)) with snorm_zero | snorm_pos
  · have f_ae_0 : f =ᵐ[μ] 0 := by
      exact snormEssSup_eq_zero_iff.mp snorm_zero
    have tr_c_le_f : (fun x : α ↦ ‖(f - trunc f a) x‖) ≤ᵐ[μ] (fun x : α ↦ ‖f x‖) := by
      apply ae_of_all
      intro x
      exact trunc_compl_le_func
    have f_ae_le : (fun x : α ↦ ‖f x‖) ≤ᵐ[μ] 0 := by
      refine Filter.EventuallyEq.le ?_
      apply measure_mono_null
      · exact fun x a ↦ ne_zero_of_norm_ne_zero a
      · exact f_ae_0
    have tr_c_le_0 : (fun x : α ↦ ‖(f - trunc f a) x‖) ≤ᵐ[μ] 0 :=
      Filter.EventuallyLE.trans tr_c_le_f f_ae_le
    have tr_c_ge_0 : 0 ≤ᵐ[μ] (fun x : α ↦ ‖(f - trunc f a) x‖) := by
      apply ae_of_all
      intro x
      simp only [Pi.zero_apply, Pi.sub_apply, norm_nonneg]
    have tr_c_eq_0' : (fun x : α ↦ ‖(f - trunc f a) x‖) =ᵐ[μ] 0 := by
      apply Filter.EventuallyLE.antisymm
      · exact tr_c_le_0
      · exact tr_c_ge_0
    have tr_c_eq_0 : (f - trunc f a) =ᵐ[μ] 0 := by
      apply measure_mono_null _ tr_c_eq_0'
      simp only [Pi.sub_apply, Pi.zero_apply, norm_eq_zero, compl_subset_compl, setOf_subset_setOf,
        imp_self, implies_true]
    have snorm_p₀_0 : snorm (f - trunc f a) p₀ μ = 0 := by
      calc
      _ = snorm 0 p₀ μ := by
        apply snorm_congr_ae
        exact tr_c_eq_0
      _ = _ := by exact MeasureTheory.snorm_zero
    have obs : Memℒp (f - trunc f a) p₀ μ := by
      refine ⟨?_, ?_⟩
      · exact aestronglyMeasurable_trunc_compl hf.1
      · exact Trans.trans snorm_p₀_0 zero_lt_top
    have wt_est := (h₀T (f - trunc f a) obs).2
    unfold wnorm at wt_est
    split_ifs at wt_est
    rw [snorm_p₀_0, mul_zero] at wt_est
    -- have snorm_T_tr_c_0 : snormEssSup (T (f - trunc f a)) ν = 0 := nonpos_iff_eq_zero.mp wt_est
    apply nonpos_iff_eq_zero.mp
    calc
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν
      ≤ distribution (T (f - trunc f a)) (snormEssSup (T (f - trunc f a)) ν) ν := by
      apply distribution_mono_right
      refine le_trans wt_est (zero_le (ENNReal.ofReal t))
    _ = 0 := by
      apply meas_snormEssSup_lt
  · have p₀pos : p₀ > 0 := lt_of_lt_of_le zero_lt_one hp₀
    have p_pos : p > 0 := lt_trans p₀pos hp₀p
    have snorm_p_pos : snorm f p μ ≠ 0 := by
      intro snorm_0
      apply Ne.symm (ne_of_lt snorm_pos)
      apply snormEssSup_eq_zero_iff.mpr
      exact (snorm_eq_zero_iff hf.1 (ne_of_gt p_pos)).mp snorm_0
    have term_pos : (ENNReal.ofNNReal C₀) ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal > 0 := by
      apply ENNReal.mul_pos
      · refine mul_ne_zero ?_ ?_
        · apply ne_of_gt
          refine rpow_pos_of_nonneg ?_ ?_
          · positivity
          · positivity
        · apply ne_of_gt
          rw [div_eq_mul_inv]
          apply ENNReal.mul_pos (Ne.symm (ne_of_lt p₀pos)) (ENNReal.inv_ne_zero.mpr hp)
      · apply ne_of_gt
        refine rpow_pos_of_nonneg ?_ ?_
        · positivity
        · positivity
    have term_ne_top : (ENNReal.ofNNReal C₀) ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal ≠ ⊤ := by
      apply mul_ne_top
      · apply mul_ne_top
        · refine rpow_ne_top' ?_ ?_
          · apply ENNReal.coe_ne_zero.mpr
            apply ne_of_gt hC₀
          · exact coe_ne_top
        · rw [div_eq_mul_inv]
          apply mul_ne_top p₀ne_top (inv_ne_top.mpr (Ne.symm (ne_of_lt p_pos)))
      · exact rpow_ne_top' snorm_p_pos (Memℒp.snorm_ne_top hf)
    have d_pos : d > 0 := by
      rw [hdeq]
      apply Real.rpow_pos_of_pos
      rw [← zero_toReal]
      exact toReal_strict_mono term_ne_top term_pos
    have a_pos : a > 0 := by rw [ha]; positivity
    have obs : Memℒp (f - trunc f a) p₀ μ := by
      apply trunc_compl_Lp_Lq_lower (p := p)
      · refine ⟨?_, ?_⟩
        · apply le_of_lt
          apply lt_of_le_of_lt hp₀ hp₀p
        · exact Ne.lt_top' (Ne.symm hp)
      · exact ⟨hp₀, hp₀p⟩
      · exact hf
      · exact a_pos
    have wt_est := (h₀T (f - trunc f a) obs).2
    unfold wnorm at wt_est
    split_ifs at wt_est
    have snorm_est : snormEssSup (T (f - trunc f a)) ν ≤ ENNReal.ofReal t := by
      apply le_of_rpow_le (exp_toReal_pos' hp₀ (Ne.lt_top' (Ne.symm p₀ne_top)))
      calc
      _ ≤ (↑C₀ * snorm (f - trunc f a) p₀ μ) ^ p₀.toReal := by gcongr
      _ ≤ (↑C₀) ^ p₀.toReal * ((p₀ / p) * ENNReal.ofReal (a ^ (p₀.toReal - p.toReal)) *
          snorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ toReal_nonneg]
        gcongr
        apply estimate_snorm_trunc_compl_interp
        · exact ⟨p_pos, Ne.lt_top' (Ne.symm hp)⟩
        · exact ⟨hp₀, hp₀p⟩
        · apply hf.1
        · exact a_pos
      _ = (↑C₀) ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal *
          (ENNReal.ofReal (d ^ p₀.toReal))⁻¹ * ENNReal.ofReal (t ^ p₀.toReal) := by
        rw [ha]
        rw [← Real.rpow_mul, div_mul_cancel₀]
        · rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          nth_rw 2 [div_eq_mul_inv]
          ring
        · apply ne_of_lt
          apply sub_neg.mpr
          apply toReal_strict_mono hp hp₀p
        · positivity
      _ = _ := by
        rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        congr
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top]
        rw [ENNReal.mul_inv_cancel (by positivity) term_ne_top]
        refine toReal_ne_zero.mpr ⟨?_, ?_⟩
        · exact Ne.symm (ne_of_lt p₀pos)
        · exact p₀ne_top
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ distribution (T (f - trunc f a)) (snormEssSup (T (f - trunc f a)) ν) ν := by
      gcongr
    _ = _ := meas_snormEssSup_lt

lemma weaktype_estimate_trunc_top {C₁ : ℝ≥0} (hC₁ : C₁ > 0) {p p₁ q₁ : ℝ≥0∞} (hp : 1 ≤ p)
    (hp₁ : p₁ < ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : Memℒp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : t > 0) {a : ℝ} {d : ℝ} -- (hd : d > 0)
    (ha : a = (t / d) ^
      (p₁.toReal / (p₁.toReal - p.toReal)))
      (hdeq : d = ((ENNReal.ofNNReal C₁) ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal).toReal ^ p₁.toReal⁻¹) :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  have obs : Memℒp (trunc f a) p₁ μ := trunc_Lp_MemLq_higher hp hp₁p hf _
  have wt_est := (h₁T (trunc f a) obs).2
  have p_pos : p > 0 := lt_of_lt_of_le zero_lt_one hp
  unfold wnorm at wt_est
  have one_le_p₁ : 1 ≤ p₁ := le_of_lt (lt_of_le_of_lt hp hp₁p)
  have p₁ne_zero: p₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_p₁)
  have p₁_pos : p₁ > 0 := pos_of_gt hp₁p
  have p₁ne_top : p₁ ≠ ⊤ := LT.lt.ne_top hp₁
  -- simp only [mul_ite, mul_zero] at wt_est
  split_ifs at wt_est
  let p₁' := p₁.toReal
  have : p₁.toReal ≠ 0 := ne_of_gt <| exp_toReal_pos' one_le_p₁ hp₁
  have coe_p₁ : ENNReal.ofReal p₁' = p₁ := ofReal_toReal_eq_iff.mpr p₁ne_top
  have : snormEssSup (T (trunc f a)) ν ^ p₁.toReal ≤ (↑C₁ * snorm (trunc f a) p₁ μ) ^ p₁.toReal := by
    gcongr
  have snorm_est : snormEssSup (T (trunc f a)) ν ≤ ENNReal.ofReal t := by
    apply le_of_rpow_le (exp_toReal_pos' one_le_p₁ hp₁)
    refine le_trans this ?_
    rcases (eq_zero_or_pos (snormEssSup f μ)) with snorm_zero | snorm_pos
    · gcongr
      calc
      _ ≤ (ENNReal.ofNNReal C₁) * snorm f p₁ μ := by
        gcongr
        apply snorm_mono
        exact fun x ↦ trunc_le_func
      _ ≤ _ := by
        have : snorm f p₁ μ = 0 := Trans.trans (snorm_congr_ae
            (snormEssSup_eq_zero_iff.mp snorm_zero)) MeasureTheory.snorm_zero
        simp only [this, mul_zero, zero_le]
    · have snorm_p_pos : snorm f p μ ≠ 0 := by
        intro snorm_0
        apply Ne.symm (ne_of_lt snorm_pos)
        apply snormEssSup_eq_zero_iff.mpr
        exact (snorm_eq_zero_iff hf.1 (ne_of_gt p_pos)).mp snorm_0
      have term_pos : (ENNReal.ofNNReal C₁) ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal > 0 := by
        apply ENNReal.mul_pos
        · refine mul_ne_zero ?_ ?_
          · apply ne_of_gt
            refine rpow_pos_of_nonneg ?_ ?_
            · positivity
            · positivity
          · refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
            · positivity
            · exact LT.lt.ne_top hp₁p
        · apply ne_of_gt
          refine rpow_pos_of_nonneg ?_ ?_
          · positivity
          · positivity
      have term_ne_top : (ENNReal.ofNNReal C₁) ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal ≠ ⊤ := by
        apply mul_ne_top
        · apply mul_ne_top
          · refine rpow_ne_top' ?_ ?_
            · apply ENNReal.coe_ne_zero.mpr
              apply ne_of_gt hC₁
            · exact coe_ne_top
          · rw [div_eq_mul_inv]
            apply mul_ne_top p₁ne_top (inv_ne_top.mpr (Ne.symm (ne_of_lt p_pos)))
        · exact rpow_ne_top' snorm_p_pos (Memℒp.snorm_ne_top hf)
      have d_pos : d > 0 := by
        rw [hdeq]
        apply Real.rpow_pos_of_pos
        rw [← zero_toReal]
        exact toReal_strict_mono term_ne_top term_pos
      calc
      _ ≤ ↑C₁ ^ p₁.toReal *
          ((p₁ / p) * (ENNReal.ofReal (a ^ (p₁.toReal - p.toReal))) * snorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        gcongr
        · apply trunc_Lp_Lq_est
          · exact (lt_of_lt_of_le zero_lt_one hp)
          · exact ⟨hp₁p, hp₁⟩
          · apply AEStronglyMeasurable.aemeasurable hf.1
          · rw [ha]; positivity
        · exact toReal_nonneg
      _ = ↑C₁ ^ p₁.toReal *
          (p₁ / p) * snorm f p μ ^ p.toReal * (ENNReal.ofReal (d ^ p₁.toReal))⁻¹ *
          ENNReal.ofReal (t ^ p₁.toReal) := by
        rw [ha]
        rw [← Real.rpow_mul, div_mul_cancel₀]
        · rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          nth_rw 2 [div_eq_mul_inv]
          ring
        · apply ne_of_gt (sub_pos.mpr (toReal_strict_mono p₁ne_top hp₁p))
        · positivity
      _ = _ := by
        rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        congr
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top]
        rw [ENNReal.mul_inv_cancel (by positivity) term_ne_top]
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T (trunc f a)) (snormEssSup (T (trunc f a)) ν) ν := by
    gcongr
  _ = _ := meas_snormEssSup_lt

end MeasureTheory

end

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] -- [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] -- [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] -- [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  -- (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)
  {f : α → E₁} {t : ℝ} -- {s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}
namespace MeasureTheory

-- /-- # The real interpolation theorem

-- ## Definitions-/

def Subadditive (T : (α → E₁) → α' → E₂) : Prop :=
  ∃ A > 0, ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

-- TODO: put `A` in ℝ≥0∞?
def Subadditive' (T : (α → E₁) → α' → E₂) (A : ℝ) : Prop :=
  ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

def Sublinear (T : (α → E₁) → α' → E₂) : Prop :=
  Subadditive T ∧ ∀ (f : α → E₁) (c : ℝ), T (c • f) = c • T f

/-- Proposition that expresses that the map `T` map between function spaces preserves
    AE strong measurability on L^p. -/
def PreservesAEStrongMeasurability (T : (α → E₁) → α' → E₂) (p : ℝ≥0∞) : Prop :=
    ∀ ⦃f : α → E₁⦄, Memℒp f p μ → AEStronglyMeasurable (T f) ν

def d := ENNReal.toReal
    ((C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^
      (p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    ((C₁ ^ p₁.toReal) * (p₁ / p) * snorm f p μ ^ p.toReal) ^
      (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)))

lemma d_pos_aux₀ {C : ℝ≥0} {p' : ℝ≥0∞} (hp' : p' > 0) (hC : C > 0) (hp : p ∈ Ioo 0 ⊤)
    (hF : snorm f p μ ∈ Ioo 0 ⊤) :
    0 < C ^ p₀.toReal * (p' / p) * snorm f p μ ^ p.toReal := by
  apply ENNReal.mul_pos
  · apply ne_of_gt
    apply ENNReal.mul_pos
    · apply ne_of_gt
      apply ENNReal.rpow_pos
      · exact ENNReal.coe_pos.mpr hC
      · exact coe_ne_top
    · apply ne_of_gt
      apply ENNReal.div_pos
      · exact ne_of_gt hp'
      · exact ne_top_of_Ioo hp
  · apply ne_of_gt <| ENNReal.rpow_pos (pos_of_Ioo hF) (ne_top_of_Ioo hF)

lemma d_ne_top_aux₀ {C : ℝ≥0} {p' : ℝ≥0∞} (hp'ne_top : p' ≠ ⊤)
    (hC : C > 0) (hp : p ∈ Ioo 0 ⊤)
    (hF : snorm f p μ ∈ Ioo 0 ⊤) :
    C ^ p₀.toReal * (p' / p) * snorm f p μ ^ p.toReal ≠ ⊤ := by
  apply mul_ne_top
  · apply mul_ne_top
    · apply rpow_ne_top'
      · exact ne_of_gt (ENNReal.coe_pos.mpr hC)
      · exact coe_ne_top
    · apply ne_of_lt
      apply div_lt_top
      · exact hp'ne_top
      · exact ne_zero_of_Ioo hp
  · exact rpow_ne_top' (ne_zero_of_Ioo hF) (ne_top_of_Ioo hF)

lemma d_ne_zero_aux₀ {C : ℝ≥0} {p' : ℝ≥0∞} {b : ℝ} (hp' : p' > 0) (hC : C > 0) (hp : p ∈ Ioo 0 ⊤)
    (hF : snorm f p μ ∈ Ioo 0 ⊤) (hp'top : p' = ⊤ → b = 0) :
    (C ^ p₀.toReal * (p' / p) * snorm f p μ ^ p.toReal) ^ b ≠ 0 := by
  rcases (eq_or_ne p' ⊤) with p'eq_top | p'ne_top
  · rw [hp'top p'eq_top]; simp
  · apply ne_of_gt
    apply ENNReal.rpow_pos
    · exact d_pos_aux₀ hp' hC hp hF
    · exact d_ne_top_aux₀ p'ne_top hC hp hF

lemma d_ne_top_aux₁ {C : ℝ≥0} {b : ℝ} {p' : ℝ≥0∞} (hp'top : p' = ⊤ → b = 0)
    (hp' : p' > 0) (hC : C > 0) (hp : p ∈ Ioo 0 ⊤)
    (hF : snorm f p μ ∈ Ioo 0 ⊤) :
    (C ^ p₀.toReal * (p' / p) * snorm f p μ ^ p.toReal) ^ b ≠ ⊤ := by
  rcases (eq_or_ne p' ⊤) with p'eq_top | p'ne_top
  · rw [hp'top p'eq_top]; simp
  · apply rpow_ne_top'
    · exact ne_of_gt <| d_pos_aux₀ hp' hC hp hF
    · exact d_ne_top_aux₀ p'ne_top hC hp hF

-- If the `p`-norm of `f` is positive and finite, then `d` is positive
lemma d_pos (hC₀ : C₀ > 0) (hC₁ : C₁ > 0) (hF : snorm f p μ ∈ Ioo 0 ⊤)
  (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp : p ∈ Ioo 0 ⊤): @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f > 0 := by
  unfold d
  apply toReal_pos
  · refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
    · apply d_ne_zero_aux₀ <;> try assumption
      intro h; rw [h]; simp
    · apply d_ne_top_aux₁ <;> try assumption
      intro h; rw [h]; simp
  · apply ne_of_lt
    apply div_lt_top
    · apply d_ne_top_aux₁ <;> try assumption
      intro h; rw [h]; simp
    · apply d_ne_zero_aux₀ <;> try assumption
      intro h; rw [h]; simp





  --     apply mul_ne_zero
  --     · apply ne_of_gt
  --       apply ENNReal.rpow_pos
  --       · exact ENNReal.coe_pos.mpr hC₀
  --       · exact coe_ne_top
  --     · apply ne_of_gt
  --       rcases (eq_or_ne p₀ ⊤) with p₀eq_top | p₀ne_top
  --       · rw [p₀eq_top]
  --         simp
  --       · apply ENNReal.rpow_pos
  --         · apply ENNReal.mul_pos
  --           · refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
  --             · exact Ne.symm (ne_of_lt hp₀)
  --             · exact ne_top_of_Ioo hp
  --           · exact snorm_rpow_ne_zero
  --         · apply mul_ne_top
  --           · apply ne_of_lt
  --             apply div_lt_top
  --             · exact p₀ne_top
  --             · exact ne_zero_of_Ioo hp
  --           · exact snorm_rpow_ne_top
  --   · apply mul_ne_top
  --     · apply rpow_ne_top'
  --       · exact ne_of_gt (ENNReal.coe_pos.mpr hC₁)
  --       · exact coe_ne_top
  --     · rcases (eq_or_ne p₁ ⊤) with p₁eq_top | p₁ne_top
  --       · rw [p₁eq_top]
  --         simp
  --       · apply rpow_ne_top'
  --         · apply mul_ne_zero
  --           · apply ne_of_gt
  --             apply ENNReal.div_pos
  --             · exact ne_of_gt hp₁
  --             · exact ne_top_of_Ioo hp
  --           · exact snorm_rpow_ne_zero
  --         · apply mul_ne_top
  --           · rw [ENNReal.div_eq_inv_mul]
  --             apply mul_ne_top
  --             · refine inv_ne_top.mpr (by exact ne_zero_of_Ioo hp)
  --             · exact p₁ne_top
  --           · exact snorm_rpow_ne_top
  -- · apply ne_of_lt
  --   apply div_lt_top
  --   · apply mul_ne_top
  --     · apply rpow_ne_top'
  --       · exact ne_of_gt (ENNReal.coe_pos.mpr hC₀)
  --       · exact coe_ne_top
  --     · rcases (eq_or_ne p₀ ⊤) with p₀eq_top | p₀ne_top
  --       · rw [p₀eq_top]
  --         simp
  --       · apply rpow_ne_top'
  --         · apply mul_ne_zero
  --           · refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
  --             · exact ne_of_gt hp₀
  --             · exact ne_top_of_Ioo hp
  --           · exact snorm_rpow_ne_zero
  --         · apply mul_ne_top
  --           · apply ne_of_lt
  --             apply div_lt_top
  --             · exact p₀ne_top
  --             · exact ne_zero_of_Ioo hp
  --           · exact snorm_rpow_ne_top
  --   · apply mul_ne_zero
  --     · apply ne_of_gt
  --       apply ENNReal.rpow_pos
  --       · exact ENNReal.coe_pos.mpr hC₁
  --       · exact coe_ne_top
  --     · apply ne_of_gt
  --       rcases (eq_or_ne p₁ ⊤) with p₁eq_top | p₁ne_top
  --       · rw [p₁eq_top]
  --         simp
  --       · apply ENNReal.rpow_pos
  --         · apply ENNReal.mul_pos
  --           · apply ne_of_gt
  --             apply ENNReal.div_pos
  --             · apply ne_of_gt hp₁
  --             · exact ne_top_of_Ioo hp
  --           · apply ne_of_gt
  --             apply ENNReal.rpow_pos
  --             · exact pos_of_Ioo hF
  --             · exact ne_top_of_Ioo hF
  --         · apply mul_ne_top
  --           · apply ne_of_lt
  --             apply ENNReal.div_lt_top
  --             · exact p₁ne_top
  --             · exact ne_zero_of_Ioo hp
  --           · exact snorm_rpow_ne_top

/-- The particular choice of scaled power function that works in the proof of the
    real interpolation theorem. -/
def spf_ch (ht : t ∈ Ioo 0 1) (hq₀q₁ : q₀ ≠ q₁) (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀)
    (hp₁ : 1 ≤ p₁) (hq₁ : 1 ≤ q₁) (hp₀p₁ : p₀ ≠ p₁) (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : snorm f p μ ∈ Ioo 0 ⊤)
    (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹) :
    ScaledPowerFunction where
  σ := @ζ p₀ q₀ p₁ q₁ t
  d := @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f
  hσ := by
    apply lt_or_gt_of_ne
    apply Ne.symm
    apply ζ_ne_zero ht (lt_of_lt_of_le zero_lt_one hp₀) (lt_of_lt_of_le zero_lt_one hq₀)
        (lt_of_lt_of_le zero_lt_one hp₁) (lt_of_lt_of_le zero_lt_one hq₁) hp₀p₁ hq₀q₁
  hd := by
    apply d_pos hC₀ hC₁ hF (lt_of_lt_of_le zero_lt_one hp₀) (lt_of_lt_of_le zero_lt_one hp₁)
    refine ⟨?_, ?_⟩
    · exact ENNReal_preservation_positivity' (lt_of_lt_of_le zero_lt_one hp₀)
          (lt_of_lt_of_le zero_lt_one hp₁) hp
    · exact interp_exp_lt_top hp₀p₁ ht hp

lemma estimate_distribution_subadditive {f : α → E₁} {t : ℝ}
    (ht : t > 0) {a : ℝ} {A : ℝ} (hA : A > 0) (h : Subadditive' T A) :
    distribution (T f) (ENNReal.ofReal ((2 : ℝ) * t)) ν ≤
    distribution (T (trunc f a)) (ENNReal.ofReal (t / A)) ν +
    distribution (T (f - trunc f a)) (ENNReal.ofReal (t / A)) ν := by
  rw [ofReal_div_of_pos hA, ← Real.ennnorm_eq_ofReal (le_of_lt hA)]
  rw [← distribution_smul_left (ne_of_gt hA), ← distribution_smul_left (ne_of_gt hA)]
  have : ENNReal.ofReal (2 * t) = ENNReal.ofReal t + ENNReal.ofReal t := by
    rw [← ofReal_add, two_mul] <;> try positivity
  rewrite [this]
  apply distribution_add_le'
  apply ae_of_all
  intro x
  rw [@Pi.smul_apply, @Pi.smul_apply, norm_smul, norm_smul, ← mul_add]
  simp [abs_of_pos hA]
  nth_rewrite 1 [← add_sub_cancel (trunc f a) f]
  apply h

lemma estimate_distribution_subadditive' {f : α → E₁} {t : ℝ}
    (ht : t > 0) (a : ℝ) {A : ℝ} (hA : A > 0) (h : Subadditive' T A) :
    distribution (T f) (ENNReal.ofReal (2 * A * t)) ν ≤
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν +
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν := by
  rw [mul_assoc]
  nth_rewrite 2 [← one_mul t]
  nth_rewrite 3 [← one_mul t]
  rw [← inv_mul_cancel (ne_of_gt hA)]
  rw [mul_rotate]
  rw [← div_eq_mul_inv]
  apply estimate_distribution_subadditive
  · exact Real.mul_pos hA ht
  · exact hA
  · exact h

lemma _rewrite_norm_func {q : ℝ} {g : α' → E} (hq : 1 ≤ q) {A : ℝ} (hA : A > 0)
    (hg : AEMeasurable g ν):
    ∫⁻ x, ‖g x‖₊ ^q ∂ν =
    ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s in Ioi (0 : ℝ),
    distribution g ((ENNReal.ofReal (2 * A * s)))  ν * (ENNReal.ofReal (s^(q - 1))) := by
  rewrite [lintegral_norm_pow_eq_distribution' hg (by linarith)]
  nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := (2*A)) (by linarith)]
  rw [← lintegral_const_mul']; swap; exact coe_ne_top
  rw [← lintegral_const_mul']; swap; exact coe_ne_top
  rw [← lintegral_const_mul']; swap; exact coe_ne_top
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro t (zero_lt_t : 0 < t)
  rw [Real.mul_rpow, ofReal_mul' (q := t ^ (q - 1)), ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← mul_assoc] <;> try positivity
  refine congrFun (congrArg ?_ ?_) ?_
  rw [ofReal_mul' (q := t), mul_assoc _ _ (ENNReal.ofReal ((2 * A) ^ (q - 1))),
      mul_comm _ (ENNReal.ofReal ((2 * A) ^ (q - 1))), ← mul_assoc] <;> try positivity
  refine congrFun (congrArg ?_ ?_) ?_
  rw [abs_of_nonneg, ← ofReal_mul, ← ofReal_mul] <;> try positivity
  apply congr_arg
  rw [mul_assoc]
  nth_rewrite 1 [← Real.rpow_one (2 * A), ← Real.rpow_add (by linarith), add_sub_cancel,
      mul_comm]; rfl

-- TODO: rename

lemma _estimate_norm_rpow_range_operator {q : ℝ} {f : α → E₁} (hq : 1 ≤ q) (tc : ToneCouple) {A : ℝ} (hA : A > 0)
    (ht : Subadditive' T A) (hTf : AEMeasurable (T f) ν) :
  ∫⁻ x : α', ‖T f x‖₊ ^ q ∂ν ≤
  ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) +
  distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) := by
  rw [_rewrite_norm_func hq hA hTf]
  apply mul_le_mul'
  · exact le_refl _
  · apply setLIntegral_mono' measurableSet_Ioi
    intro s s_pos
    rw [← add_mul]
    apply mul_le_mul'
    · apply estimate_distribution_subadditive' s_pos (tc.ton s) hA ht
    · exact le_refl _

-- lemma estimate_norm_rpow_range_operator {C₁ : ℝ} {p p₁: ℝ} (hp : 1 ≤ p) {q₁ : ℝ} (hq₁ : 1 ≤ q₁)
--     (hp₁p : p < p₁) {q : ℝ} {C₀ : ℝ} {p₀: ℝ} (hp₀ : 1 ≤ p₀) {q₀ : ℝ} (hq₀ : 1 ≤ q₀) (hp₀p : p₀ < p) {f : α → E₁} (tc : ToneCouple)
--     (hf : Memℒp f (ENNReal.ofReal p) μ)
--     (hT₁ : HasWeakType T (ENNReal.ofReal p₁) (ENNReal.ofReal q₁) μ ν C₁.toNNReal) (hT₀ : HasWeakType T (ENNReal.ofReal p₀) (ENNReal.ofReal q₀) μ ν C₀.toNNReal):
--     ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) +
--     distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) ≤
--     ENNReal.ofReal C₁ ^ q₁ * (∫⁻ s in Ioi (0 : ℝ),
--         snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ ^ q₁ * ENNReal.ofReal (s ^ (q - q₁ - 1))) +
--     ENNReal.ofReal C₀ ^ q₀ * ∫⁻ s in Ioi (0 : ℝ),
--         snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ^ q₀ * ENNReal.ofReal (s ^ (q - q₀ - 1)) := by
--   have : ∀ q' : ℝ, -q' + (q - 1) = q - q' - 1 := by intro q'; group
--   rw [← this, ← this]
--   -- TODO: is there a way to use lintegral_rw₂ conveniently?
--   rw [lintegral_rw_aux power_aux_2, lintegral_rw_aux power_aux_2]
--   rw [← lintegral_const_mul']; swap; exact coe_pow_ne_top' (hq₁)
--   rw [← lintegral_const_mul']; swap; exact coe_pow_ne_top' (hq₀)
--   simp_rw [← mul_assoc]
--   rw [← lintegral_add_left']
--   · apply setLIntegral_mono' measurableSet_Ioi
--     intro s (s_pos : s > 0)
--     gcongr
--     · apply weaktype_estimate_trunc hp <;> try assumption
--     · apply weaktype_estimate_trunc_compl <;> try assumption
--       · exact tc.ran_ton s s_pos
--   -- TODO: split off the measurability lemmas
--   · apply AEMeasurable.mul
--     · apply AEMeasurable.mul
--       · apply AEMeasurable.const_mul
--         · apply AEMeasurable.pow_const
--           · change AEMeasurable ((fun t : ℝ ↦ snorm (trunc f t) (ENNReal.ofReal p₁) μ) ∘ (tc.ton)) (volume.restrict (Ioi 0))
--             have tone := tc.ton_is_ton
--             split_ifs at tone
--             · apply aemeasurable_restrict_of_monotoneOn measurableSet_Ioi
--               exact Monotone.comp_monotoneOn norm_trunc_mono (StrictMonoOn.monotoneOn tone)
--             · apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
--               exact Monotone.comp_antitoneOn norm_trunc_mono (StrictAntiOn.antitoneOn tone)
--       · apply AEMeasurable.coe_nnreal_ennreal
--         · apply AEMeasurable.real_toNNReal
--           · apply AEMeasurable.pow_const
--             apply aemeasurable_id'
--     · apply AEMeasurable.coe_nnreal_ennreal
--       · apply AEMeasurable.real_toNNReal
--         · apply AEMeasurable.pow_const
--           · apply aemeasurable_id'

lemma estimate_norm_rpow_range_operator' (hp : 1 ≤ p) (hp' : p < ⊤) (hq₁ : 1 ≤ q₁)
    (hp₁p : p < p₁) (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀)
    (hp₀p : p₀ < p) (tc : ToneCouple)
    (hq₀' : q₀ < ⊤ ∨ ∀ s ∈ Ioi (0 : ℝ), distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν = 0)
    (hq₁' : q₁ < ⊤ ∨ ∀ s ∈ Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν = 0)
    (hf : Memℒp f p μ)
    (hT₁ : HasWeakType T p₁ q₁ μ ν C₁) (hT₀ : HasWeakType T p₀ q₀ μ ν C₀) :
    ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q.toReal - 1)) +
    distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q.toReal - 1)) ≤
    (if (q₁ < ⊤) then 1 else 0) * (C₁ ^ q₁.toReal * (∫⁻ s in Ioi (0 : ℝ),
        snorm (trunc f (tc.ton s)) p₁ μ ^ q₁.toReal * ENNReal.ofReal (s ^ (q.toReal - q₁.toReal - 1)))) +
    (if (q₀ < ⊤) then 1 else 0) * (C₀ ^ q₀.toReal * ∫⁻ s in Ioi (0 : ℝ),
        snorm (f - trunc f (tc.ton s)) (p₀) μ ^ q₀.toReal * ENNReal.ofReal (s ^ (q.toReal - q₀.toReal - 1))) := by
  have : ∀ q' q : ℝ, -q' + (q - 1) = q - q' - 1 := by intro q' q; group
  rw [← this, ← this]
  -- TODO: is there a way to use lintegral_rw₂ conveniently?
  rw [lintegral_rw_aux power_aux_2, lintegral_rw_aux power_aux_2]
  nth_rw 2 [← lintegral_const_mul']; swap; refine rpow_ne_top_of_nonneg toReal_nonneg coe_ne_top
  nth_rw 1 [← lintegral_const_mul']; swap; refine rpow_ne_top_of_nonneg toReal_nonneg coe_ne_top
  simp_rw [← mul_assoc]
  split_ifs with is_q₁top is_q₀top
  · rw [one_mul, one_mul, ← lintegral_add_left']
    · apply setLIntegral_mono' measurableSet_Ioi
      intro s (s_pos : s > 0)
      gcongr
      · apply weaktype_estimate_trunc hp hq₁ <;> assumption
      · apply weaktype_estimate_trunc_compl hp _ hp₀ <;> try assumption
        exact tc.ran_ton s s_pos
  -- TODO: split off the measurability lemmas
    · apply AEMeasurable.mul
      · apply AEMeasurable.mul
        · apply AEMeasurable.const_mul
          · apply AEMeasurable.pow_const
            · change AEMeasurable ((fun t : ℝ ↦ snorm (trunc f t) p₁ μ) ∘ (tc.ton)) (volume.restrict (Ioi 0))
              have tone := tc.ton_is_ton
              split_ifs at tone
              · apply aemeasurable_restrict_of_monotoneOn measurableSet_Ioi
                exact Monotone.comp_monotoneOn norm_trunc_mono (StrictMonoOn.monotoneOn tone)
              · apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
                exact Monotone.comp_antitoneOn norm_trunc_mono (StrictAntiOn.antitoneOn tone)
        · apply AEMeasurable.coe_nnreal_ennreal
          · apply AEMeasurable.real_toNNReal
            · apply AEMeasurable.pow_const
              apply aemeasurable_id'
      · apply AEMeasurable.coe_nnreal_ennreal
        · apply AEMeasurable.real_toNNReal
          · apply AEMeasurable.pow_const
            · apply aemeasurable_id'
  · rw [one_mul, zero_mul, add_zero]
    apply setLIntegral_mono' measurableSet_Ioi
    intro s (s_pos : s > 0)
    simp only [is_q₀top, mem_Ioi, false_or] at hq₀'
    rw [hq₀' s s_pos, zero_mul, add_zero]
    gcongr
    apply weaktype_estimate_trunc hp <;> try assumption
  · rw [one_mul, zero_mul, zero_add]
    apply setLIntegral_mono' measurableSet_Ioi
    intro s (s_pos : s > 0)
    simp only [is_q₁top, mem_Ioi, false_or] at hq₁'
    rw [hq₁' s s_pos, zero_mul, zero_add]
    gcongr
    apply weaktype_estimate_trunc_compl hp _ hp₀ <;> try assumption
    exact tc.ran_ton s s_pos
  · simp only [zero_mul, add_zero, nonpos_iff_eq_zero]
    have : ∫⁻ (_ : ℝ) in Ioi 0, 0 = 0 := by exact lintegral_zero
    rw [← this]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro s (s_pos)
    have is_q₀top : ¬ q₀ < ⊤ := by assumption
    simp only [is_q₀top, mem_Ioi, false_or] at hq₀'
    simp only [is_q₁top, mem_Ioi, false_or] at hq₁'
    rw [hq₀' s s_pos, hq₁' s s_pos, zero_mul, add_zero]

def res (j : Bool) (β : ℝ) : Set ℝ := if j then Ioo (0 : ℝ) β else Ioi β

lemma measurableSet_res {j : Bool} {β : ℝ} : MeasurableSet (res j β) := by
  unfold res
  split
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi

lemma res_subset_Ioi {j : Bool} {β : ℝ} (hβ : β > 0) : res j β ⊆ Ioi 0 := by
  unfold res
  split
  · exact Ioo_subset_Ioi_self
  · unfold Ioi
    simp
    intro s hs
    linarith

instance decidableMemRes {j : Bool} {β : ℝ} : Decidable (t ∈ res j β) := by
  exact Classical.propDecidable (t ∈ res j β)

def φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} (s t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
  distribution f (ENNReal.ofReal t) μ *
  if t ∈ res j (tc.ton s) then 1 else 0

lemma switch_arguments_φ' {j : Bool} {tc : ToneCouple} {s t : ℝ} (hs : s ∈ Ioi 0)
    (ht : t ∈ Ioi 0) :
    (if t ∈ res j (tc.ton s) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1 else
    @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0) =
    if s ∈ res (xor j tc.mon) (tc.inv t) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1 else
    @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 := by
  -- Written out because otherwise it got quite slow
  unfold res Ioo Ioi
  have h₀ := tc.inv_pf
  split at h₀ <;> rename_i mon
  · have h₀₁ := (h₀ s hs t ht).1
    have h₀₂ := (h₀ s hs t ht).2
    split <;> rename_i hj
    · rw [mon, hj]
      simp only [mem_setOf_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i hc1
      · split <;> rename_i hc2
        · exact Eq.refl (OfNat.ofNat 1)
        · exact False.elim (hc2 (h₀₂.mp hc1.2))
      · split <;> rename_i hc2
        · exact False.elim (hc1 (And.intro ht (h₀₂.mpr hc2)))
        · exact Eq.refl (OfNat.ofNat 0)
    · rw [mon, eq_false_of_ne_true hj]
      simp only [mem_setOf_eq, Bool.bne_true, Bool.not_false, ↓reduceIte]
      split <;> rename_i hc1
      · split <;> rename_i hc2
        · exact Eq.refl (OfNat.ofNat 1)
        · exact False.elim (hc2 (And.intro hs (h₀₁.mp hc1)))
      · split <;> rename_i hc2
        · exact False.elim (hc1 (h₀₁.mpr hc2.2))
        · exact Eq.refl (OfNat.ofNat 0)
  · have h₀₁ := (h₀ s hs t ht).1
    have h₀₂ := (h₀ s hs t ht).2
    split <;> rename_i hj
    · rw [eq_false_of_ne_true mon, hj]
      simp only [mem_setOf_eq, Bool.bne_false, ↓reduceIte]
      · split <;> rename_i hc1
        · split <;> rename_i hc2
          · exact Eq.refl (OfNat.ofNat 1)
          · exact False.elim (hc2 (And.intro hs (h₀₂.mp hc1.2)))
        · split <;> rename_i hc2
          · exact False.elim (hc1 (And.intro ht (h₀₂.mpr hc2.2)))
          · exact Eq.refl (OfNat.ofNat 0)
    · rw [eq_false_of_ne_true mon, eq_false_of_ne_true hj]
      simp only [mem_setOf_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      · split <;> rename_i hc1
        · split <;> rename_i hc2
          · exact Eq.refl (OfNat.ofNat 1)
          · exact False.elim (hc2 (h₀₁.mp hc1))
        · split <;> rename_i hc2
          · exact False.elim (hc1 (h₀₁.mpr hc2))
          · exact Eq.refl (OfNat.ofNat 0)

lemma switch_arguments_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} (s t : ℝ) (hs : s ∈ Ioi 0)
    (ht : t ∈ Ioi 0) :
    @φ _ _ _ μ _ f j p' q' q tc s t
    = ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
      distribution f (ENNReal.ofReal t) μ *
      if s ∈ res (xor j tc.mon) (tc.inv t) then 1 else 0
     := by
  unfold φ
  rw [switch_arguments_φ' hs ht]

-- TODO: generalize tc.inv?
lemma value_integral_φ' {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0):
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t),
    (ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
        distribution f (ENNReal.ofReal t) μ) ^
      (q' / p')
    := by
  rw [lintegral_double_restrict_set (B := res (xor j tc.mon) (tc.inv t))]
  · rw [inter_eq_right.mpr (res_subset_Ioi (tc.ran_inv t ht))]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_res]
    intro s hs
    have h₁ : s ∈ Ioi 0 := res_subset_Ioi (tc.ran_inv t ht) hs
    rw [switch_arguments_φ _ _ h₁ ht]
    split
    · rw [mul_one]
    · contradiction
  · exact measurableSet_Ioi
  · exact measurableSet_res
  · filter_upwards
    intro s hs
    have h₁ : s ∈ Ioi 0 := by exact mem_of_mem_diff hs
    rw [switch_arguments_φ _ _ h₁ ht]
    split <;> rename_i hs1
    · exact False.elim (hs.2 hs1)
    . rw [mul_zero]
      rw [zero_rpow_of_pos]
      exact div_pos hq' hp'

lemma estimate_trunc_comp_integral {f : α → E₁} (hf : AEStronglyMeasurable f μ) {q p₀ q₀ : ℝ}
    {tc : ToneCouple} (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀) :
    ∫⁻ (s : ℝ) in (Ioi 0),
    (snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ) ^ q₀ * ENNReal.ofReal (s ^ (q - q₀ - 1)) ≤
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₀) * (@φ _ _ _ μ _ f false p₀ q₀ q tc s t )) ^ (q₀ / p₀) := by
  apply setLIntegral_mono' measurableSet_Ioi
  intro s (hs : s > 0)
  refine Preorder.le_trans ?_
      (ENNReal.ofReal (s ^ (q - q₀ - 1)) *
      ((∫⁻ (s : ℝ) in (res false (tc.ton s)),
        ENNReal.ofReal p₀ * ENNReal.ofReal (s ^ (p₀ - 1)) * distribution f (ENNReal.ofReal s) μ) ^
      p₀⁻¹) ^ q₀) ?_ ?_ ?_
  · rw [mul_comm]
    apply mul_le_mul_left'
    have hq₀ : q₀ ≥ 0 := by linarith
    have h₀ : snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ≤
        (∫⁻ s : ℝ in res false (tc.ton s), ENNReal.ofReal p₀ * ENNReal.ofReal (s ^ (p₀ - 1)) *
        distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹)  := by
      apply estimate_snorm_trunc_compl hp₀ hf
      apply le_of_lt
      apply tc.ran_ton s hs
    apply ENNReal.rpow_le_rpow
    · exact h₀
    · exact hq₀
  · have hq₀ : q₀ ≠ 0 := by linarith
    -- have hp₀inv : p₀⁻¹ ≠ 0 := by
    --   refine inv_ne_zero ?_
    --   linarith
    -- have hp₀ : (ENNReal.ofReal p₀).toReal = p₀ := by
    --   refine toReal_ofReal ?_
    --   linarith
    have h₁ : p₀⁻¹ * q₀ ≠ 0 := by positivity
    have h₂ : p₀⁻¹ * q₀ ≥ 0 := by positivity
    -- rw [hp₀]
    rw [← ENNReal.rpow_mul, div_eq_inv_mul]
    rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal (s ^ (q - q₀ - 1)))]
    rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
    rw [← mul_rpow_of_nonneg (hz := h₂)]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
    rw [← lintegral_const_mul']; swap; exact coe_ne_top
    refine ENNReal.rpow_le_rpow ?_ h₂
    unfold φ
    have h₃ : Ioi (0 : ℝ) ∩ res false (tc.ton s) = res false (tc.ton s) := by
      refine inter_eq_self_of_subset_right ?_
      refine res_subset_Ioi ?_
      apply tc.ran_ton s hs
    nth_rewrite 2 [lintegral_double_restrict_set (B := res false (tc.ton s)) _ measurableSet_res]
    · rw [h₃]
      apply setLIntegral_mono_ae' (measurableSet_Ioi)
      apply ae_of_all
      intro t ht; simp at (ht : t > tc.ton s)
      have := tc.ran_ton s hs
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₀)]
      split <;> rename_i t_res
      · rw [← Real.rpow_mul (by positivity), mul_one, ← mul_assoc, ← mul_assoc]
        apply mul_le_mul_right'
        rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← ENNReal.ofReal_rpow_of_pos hs,
            ← ENNReal.ofReal_rpow_of_pos (lt_trans this ht)]
        · apply mul_le_mul_right'
          apply mul_le_mul_left'
          apply le_of_eq
          rw [@mul_inv, inv_inv p₀, ← mul_assoc, ← div_eq_mul_inv]
      · unfold res at t_res
        simp at t_res
        contrapose t_res; simp; exact ht
    · apply ae_of_all
      simp
      intro t ht ht2 ht3
      contrapose! ht3; exact ht2
    · exact measurableSet_Ioi

lemma estimate_trunc' (p₁ : ℝ) (A : ℝ):
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution (trunc f A) (ENNReal.ofReal t) μ =
          ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution f (ENNReal.ofReal ↑t) μ := by
  rw [lintegral_double_restrict_set (B := Ioo 0 A) _ measurableSet_Ioo]
  rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo]; intro t ht; rw [distribution_trunc]
    split <;> rename_i h₀
    · rfl
    · exact False.elim (h₀ ((ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht.1)).mpr ht.2))
  · apply ae_of_all; intro t ht; rw [distribution_trunc]
    split <;> rename_i ht2
    · exact False.elim (ht.2 ⟨ht.1, (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht.1)).mp ht2⟩)
    · rw [mul_zero]
  · exact measurableSet_Ioi

lemma estimate_trunc {p₁ : ℝ} (hp₁ : p₁ > 0) (A : ℝ) (hf : AEStronglyMeasurable f μ):
    snorm (trunc f A) (.ofReal p₁) μ =
    (∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
            distribution f (ENNReal.ofReal t) μ) ^ p₁⁻¹ := by
  rw [snorm_pow_eq_distribution', ← estimate_trunc', ← lintegral_const_mul']
  refine congrFun (congrArg ?_ ?_) ?_
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro t ht
  rw [mul_comm _ (ENNReal.ofReal (t ^ (p₁ - 1))), ← mul_assoc]
  · congr; exact Eq.symm (ofReal_rpow_of_pos ht)
  · exact coe_ne_top
  · apply AEStronglyMeasurable.aemeasurable (aestronglyMeasurable_trunc hf)
  · exact hp₁

-- TODO: Combine this function with estimate_trunc_compl_integral'
-- TODO the assumption of AEStronglyMeasurable can probably be weakened to measurable
lemma eq_trunc_integral' {f : α → E₁} (hf : AEStronglyMeasurable f μ)
    (q p₁ q₁ : ℝ) (tc : ToneCouple) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0):
    ∫⁻ (s : ℝ) in Ioi 0,
    (snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ) ^ q₁ * ENNReal.ofReal (s ^ (q - q₁ - 1)) =
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁) * (@φ _ _ _ μ _ f true p₁ q₁ q tc s t )) ^ (q₁ / p₁)
    := by
  apply setLIntegral_congr_fun measurableSet_Ioi
  apply ae_of_all
  intro s hs
  rw [estimate_trunc hp₁ _ hf]
  have hq₀ : q₁ ≠ 0 := by positivity
  -- have hp₀inv : p₁⁻¹ ≠ 0 := by positivity
  -- have hp₀ : (ENNReal.ofReal p₁).toReal = p₁ := toReal_ofReal (le_of_lt hp₁)
  have h₁ : p₁⁻¹ * q₁ ≠ 0 := by positivity
  have h₂ : p₁⁻¹ * q₁ ≥ 0 := by positivity
  -- rw [hp₀]
  rw [mul_comm]
  rw [← ENNReal.ofReal_rpow_of_pos hs, ← ENNReal.rpow_mul, div_eq_inv_mul]
  rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₁ - 1))]
  rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
  rw [← mul_rpow_of_nonneg (hz := h₂)]
  have h₃ : (ENNReal.ofReal s ^ (q - q₁ - q₁ / q₁)) ^ (p₁⁻¹ * q₁)⁻¹ ≠ ⊤ := by
    refine rpow_ne_top_of_nonneg ?_ ?_
    · positivity
    · apply rpow_ne_top'
      · apply ne_of_gt (ofReal_pos.mpr hs)
      · exact coe_ne_top
  rw [← lintegral_const_mul' (hr := h₃)]
  refine congrFun (congrArg HPow.hPow ?_) (p₁⁻¹ * q₁)
  unfold φ
  nth_rewrite 2 [lintegral_double_restrict_set (B := res true (tc.ton s)) _ measurableSet_res]
  · have h₃ : Ioi (0 : ℝ) ∩ (res true (tc.ton s)) = res true (tc.ton s) := by
      refine inter_eq_self_of_subset_right ?_
      refine res_subset_Ioi ?_
      exact tc.ran_ton s hs
    rw [h₃]
    apply setLIntegral_congr_fun (measurableSet_Ioo)
    apply ae_of_all
    intro t ht; simp at ht
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₁)]
    split
    · rw [mul_one, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      apply congrArg
      rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₁, ← mul_assoc]
      rfl
    · tauto
  · apply ae_of_all
    simp
    intro t ht1 ht2 ht3
    contradiction
  · exact measurableSet_Ioi

/-- Extract expressions for the lower Lebesgue integral of power functions -/

lemma lintegral_rpow_of_gt_abs {β γ : ℝ} (hβ : β > 0) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  have hγ2 : γ + 1 > 0 := by linarith
  rw [abs_of_nonneg (le_of_lt hγ2)]
  exact lintegral_rpow_of_gt hβ hγ

-- TODO: treat symmetrically to Ioo case?
lemma lintegral_Ioi_rpow_of_lt_abs {β σ : ℝ} (hβ : β > 0) (hσ : σ < -1):
    ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / |σ + 1|) := by
  have hσ2 : σ + 1 < 0 := by linarith
  rw [abs_of_neg hσ2]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt hσ hβ]
    rw [div_neg, neg_div]
  · apply integrableOn_Ioi_rpow_of_lt hσ hβ
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt (lt_trans hβ hs)) σ

-- TODO : check if the tc.inv parameter can be generalized
lemma lintegral_rpow_abs {j : Bool} {tc : ToneCouple} {γ : ℝ} {t : ℝ}
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) (ht : t > 0) :
  ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t), ENNReal.ofReal s ^ γ =
    ENNReal.ofReal ((tc.inv t) ^ (γ + 1) / |γ + 1|) := by
  rw [← lintegral_congr_ae (Filter.mp_mem (self_mem_ae_restrict measurableSet_res)
      (Filter.univ_mem'
      (fun s hs ↦ Eq.symm (ofReal_rpow_of_pos (res_subset_Ioi (tc.ran_inv t ht) hs)))))]
  unfold res
  split at hγ <;> rename_i xor_split
  · rw [xor_split]
    simp
    rw [lintegral_rpow_of_gt_abs (tc.ran_inv t ht) hγ]
  · rw [eq_false_of_ne_true xor_split]
    simp
    rw [lintegral_Ioi_rpow_of_lt_abs (tc.ran_inv t ht) hγ]

/-- Compute the integrals obtained after switching the arguments -/

lemma value_integral_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0)
    (hγ : if xor j tc.mon = true then q - q' - 1 > -1 else q - q' - 1 < -1) :
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') =
    ENNReal.ofReal (tc.inv t ^ (q - q') / |q - q'|) * ENNReal.ofReal t ^ ((p' - 1) * (q' / p')) *
    distribution f (ENNReal.ofReal t) μ ^ (q' / p')
    := by
  have h₁ : ((q - q' - 1) * p' / q') * (q' / p') = q - q' - 1 := calc
    _ = (p'⁻¹ * p') * (q'⁻¹ * q') * (q - q' - 1) := by ring
    _ = _ := by
      simp (discharger := positivity) only [inv_mul_cancel, mul_one, one_mul]
  rw [value_integral_φ' ht hq' hp']
  rw [funext fun f ↦ mul_rpow_of_nonneg _ _ (by positivity)]
  rw [lintegral_mul_const _ (Measurable.pow_const (Measurable.mul_const
      (Measurable.pow_const measurable_ofReal _) _) _)]
  rw [funext fun f ↦ mul_rpow_of_nonneg _ _ (by positivity)]
  rw [lintegral_mul_const _ (Measurable.pow_const (Measurable.pow_const measurable_ofReal _) _)]
  rw [← ENNReal.rpow_mul, ← funext fun _ ↦ ENNReal.rpow_mul _ _ _]
  rw [h₁]
  rw [lintegral_rpow_abs _ ht]
  · rw [sub_add_cancel]
  · exact hγ

lemma value_integral_φ'' {j : Bool} {p' q' q : ℝ} {spf : ScaledPowerFunction} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0)
    (hσ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p') =
    ENNReal.ofReal (spf.d ^ (q - q')) * ENNReal.ofReal |q - q'|⁻¹ *
    ENNReal.ofReal t ^ ((p' - 1) * (q' / p') + spf.σ⁻¹ * (q - q')) *
    distribution f (ENNReal.ofReal t) μ ^ (q' / p') := by
  rewrite [value_integral_φ ht hq' hp' hσ]
  unfold ToneCouple.inv spf_to_tc
  simp only
  have := spf.hd
  rw [div_eq_mul_inv, ofReal_mul', Real.mul_rpow (le_of_lt spf.hd),
      ← Real.rpow_mul (le_of_lt ht), ofReal_mul, ← mul_comm _ (ENNReal.ofReal _),
        mul_comm _ (ENNReal.ofReal t ^ ((p' - 1) * (q' / p'))), ← mul_assoc, ← mul_assoc,
        ← ofReal_rpow_of_pos ht, ← ENNReal.rpow_add _ _ (by positivity), mul_assoc _ _ (ENNReal.ofReal |q - q'|⁻¹),
        mul_comm _ ((ENNReal.ofReal (spf.d ^ (q - q')) * ENNReal.ofReal |q - q'|⁻¹))] <;>
          try positivity
  · exact coe_ne_top

lemma value_integral_φ''' {j : Bool} {p' q' q : ℝ} {spf : ScaledPowerFunction}
    (hq' : q' > 0) (hp' : p' > 0) (hp : p' + spf.σ⁻¹ * (q - q') * (p' / q') > 0)
    (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1)
    (hf : AEMeasurable f μ) :
    ∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p')) ^ (p' / q') =
    ENNReal.ofReal (spf.d ^ (q - q')) ^ (p' / q') * ENNReal.ofReal |q - q'|⁻¹ ^ (p' / q') *
    (ENNReal.ofReal (p' + spf.σ⁻¹ * (q - q') * (p' / q') ))⁻¹ *
    snorm f (ENNReal.ofReal (p' + spf.σ⁻¹ * (q - q') * (p' / q'))) μ ^
    (p' + spf.σ⁻¹ * (q - q') * (p' / q'))
    := by
  have hp2 : p' + spf.σ⁻¹ * (q - q') * (p' / q') > 0 := by linarith
  nth_rewrite 3 [← Real.coe_toNNReal (p' + spf.σ⁻¹ * (q - q') * (p' / q')) (le_of_lt hp2)]
  rw [snorm_pow_eq_distribution' hf hp]
  rw [Real.coe_toNNReal (p' + spf.σ⁻¹ * (q - q') * (p' / q')) (le_of_lt hp2)]
  have h₀ : p' - 1 + spf.σ⁻¹ * (q - q') * (p' / q') =
      p' + spf.σ⁻¹ * (q - q') * (p' / q') - 1 := by linarith
  rw [← h₀]
  rw [← lintegral_const_mul', ENNReal.rpow_inv_rpow, ← lintegral_const_mul']
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro t ht
    rw [value_integral_φ'' ht hq' hp' hγ]
    have hpq : p'/q' ≥ 0 := by positivity
    have hpq2 : q' / p' * (p' / q') = 1 := calc
      _ = (q' * q'⁻¹) * (p' * p'⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel, mul_inv_cancel, mul_one] <;> positivity
    rw [mul_rpow_of_nonneg _ _ hpq, mul_rpow_of_nonneg _ _ hpq,
        mul_rpow_of_nonneg _ _ hpq, ← ENNReal.rpow_mul, add_mul, ← ENNReal.rpow_mul,
        mul_assoc (p' - 1), hpq2, mul_one, ENNReal.rpow_one]
    repeat rw [mul_assoc]
    rw [← mul_assoc (ENNReal.ofReal (p' + spf.σ⁻¹ * ((q - q') * (p' / q'))))⁻¹,
        ENNReal.inv_mul_cancel, one_mul, mul_comm (distribution _ _ _), ofReal_rpow_of_pos ht]
    · rw [← mul_assoc]; positivity
    · exact coe_ne_top
  · refine mul_ne_top (mul_ne_top ?_ ?_) ?_
    · apply coe_pow_ne_top (by positivity)
    · apply coe_pow_ne_top (by positivity)
    · exact inv_ne_top.mpr (by positivity)
  · positivity
  · exact coe_ne_top

lemma value_integral_summary {j : Bool} {spf : ScaledPowerFunction} {p' q' : ℝ≥0∞}
  (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (ht : t ∈ Ioo 0 1)
  (hp₀p₁ : p₀ < p₁)
  (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
  (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹)
  (hspf : p'.toReal + (spf.σ⁻¹) * (q.toReal - q'.toReal) * (p'.toReal / q'.toReal) = p.toReal)
  (hp' : p' = match j with | ⊥ => p₀ | ⊤ => p₁)
  (hq' : q' = match j with | ⊥ => q₀ | ⊤ => q₁) (hp'ne_top : p' ≠ ⊤)
  (hq'ne_top : q' ≠ ⊤)
  (hq₀q₁ : if xor j (spf_to_tc spf).mon then q' < q else q < q')
  (hq₀q₁' : q₀ ≠ q₁)
  (hf : AEMeasurable f μ):
  ∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p'.toReal q'.toReal q.toReal (spf_to_tc spf) s t ^
      (q'.toReal / p'.toReal)) ^ (p'.toReal / q'.toReal) =
    ENNReal.ofReal (spf.d ^ (q.toReal - q'.toReal)) ^ (p'.toReal / q'.toReal) *
    ENNReal.ofReal |q.toReal - q'.toReal|⁻¹ ^ (p'.toReal / q'.toReal) *
    p⁻¹ *
    snorm f p μ ^ (p.toReal)
    := by
  have coe_p : ENNReal.ofReal p.toReal = p := by
    refine ofReal_toReal_eq_iff.mpr ?_
    apply interp_exp_ne_top (ne_of_lt hp₀p₁) ht hp
  nth_rw 1 [← coe_p]; nth_rw 2 [← coe_p]
  rw [← hspf]
  rcases j with bot | top
  · simp only at hp'; simp only at hq'; rw [hp', hq']
    apply value_integral_φ'''
    · refine toReal_pos ?_ ?_
      · exact Ne.symm (ne_of_lt hq₀)
      · rw [← hq']; exact hq'ne_top
    · refine toReal_pos ?_ ?_
      · exact Ne.symm (ne_of_lt hp₀)
      · exact LT.lt.ne_top hp₀p₁
    · rw [hp', hq'] at hspf
      rw [hspf]
      apply ENNReal_preservation_positivity_real hp₀ hp₁ (ne_of_lt hp₀p₁) ht hp
    · split_ifs with mon
      · suffices (q₀.toReal < q.toReal) by linarith
        split_ifs at hq₀q₁
        rw [hq'] at hq₀q₁
        refine toReal_strict_mono ?_ hq₀q₁
        apply interp_exp_ne_top hq₀q₁' ht hq
      · suffices (q.toReal < q₀.toReal) by linarith
        split_ifs at hq₀q₁
        refine toReal_strict_mono ?_ ?_
        · rw [← hq']; exact hq'ne_top
        · rw [← hq']; exact hq₀q₁
    · exact hf
  · simp only at hp'; simp only at hq'; rw [hp', hq']
    apply value_integral_φ''' (q' := q₁.toReal) (p' := p₁.toReal)
    · refine toReal_pos ?_ ?_
      · exact Ne.symm (ne_of_lt hq₁)
      · rw [← hq']; exact hq'ne_top
    · refine toReal_pos ?_ ?_
      · apply (ne_of_gt hp₁)
      · rw [← hp']
        apply hp'ne_top
    · rw [hp', hq'] at hspf
      rw [hspf]
      apply ENNReal_preservation_positivity_real hp₀ hp₁ (ne_of_lt hp₀p₁) ht hp
    · split_ifs with mon
      · suffices (q₁.toReal < q.toReal) by linarith
        split_ifs at hq₀q₁
        refine toReal_strict_mono ?_ ?_
        · exact interp_exp_ne_top hq₀q₁' ht hq
        · rw [← hq']; exact hq₀q₁
      · suffices (q.toReal < q₁.toReal) by linarith
        split_ifs at hq₀q₁
        · rw [hq'] at hq₀q₁
          refine toReal_strict_mono ?_ hq₀q₁
          rw [← hq']; exact hq'ne_top
    · exact hf

/-- Minkowksi's inequality applied in this special case. -/

-- TODO: add conditions
lemma minkowski_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in Ioi 0, (∫⁻ t : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t )^ (q' / p') ≤
    (∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p')) ^ (p' / q') ) ^ (q' / p') := sorry

-- TODO : rename
lemma computation_0 {A : ℝ} {C : ℝ≥0} {q p' q' : ℝ≥0∞} {d : ℝ}
  (p'gt_0 : p' > 0) (q'gt_0 : q' > 0) (p'lt_top : p' < ⊤) (q'lt_top : q' < ⊤) :
    (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C ^ q'.toReal *
      (ENNReal.ofReal p'.toReal ^ (q'.toReal / p'.toReal) *
      (ENNReal.ofReal (d ^ (q.toReal - q'.toReal)) ^ (p'.toReal / q'.toReal) *
      ENNReal.ofReal |q.toReal - q'.toReal|⁻¹ ^ (p'.toReal / q'.toReal) *
      p⁻¹ * snorm f p μ ^ p.toReal) ^ (q'.toReal / p'.toReal)))) =
    (C ^ p'.toReal * (p' / p) * snorm f p μ ^ p.toReal) ^ (q'.toReal / p'.toReal) *
    ENNReal.ofReal (d ^ (q.toReal - q'.toReal)) *
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * ENNReal.ofReal |q.toReal - q'.toReal|⁻¹ := by
  have exp_pos : q'.toReal / p'.toReal ≥ 0 := by positivity
  repeat rw [ENNReal.div_eq_inv_mul]
  repeat rw [ENNReal.mul_rpow_of_nonneg _ _ exp_pos]
  repeat rw [← ENNReal.rpow_mul]
  have : p'.toReal * (q'.toReal / p'.toReal) = q'.toReal := by
    exact mul_div_cancel₀ q'.toReal <| toReal_ne_zero.mpr ⟨ne_of_gt p'gt_0, ne_of_lt p'lt_top⟩
  rw [this]
  have : p'.toReal / q'.toReal * (q'.toReal / p'.toReal) = 1 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
    _ = (q'.toReal⁻¹ * q'.toReal) * (p'.toReal⁻¹ * p'.toReal) := by ring
    _ = 1 := by
      rw [inv_mul_cancel, inv_mul_cancel, mul_one]
      · exact toReal_ne_zero.mpr ⟨ne_of_gt p'gt_0, ne_of_lt p'lt_top⟩
      · exact toReal_ne_zero.mpr ⟨ne_of_gt q'gt_0, ne_of_lt q'lt_top⟩
  rw [this]
  rw [ENNReal.rpow_one, ENNReal.rpow_one]
  have coe_p' : ENNReal.ofReal p'.toReal = p' := ofReal_toReal_eq_iff.mpr (LT.lt.ne_top p'lt_top)
  rewrite [coe_p']
  ring

-- TODO: to what extent is `p₁ ≤ q₁` necessary?
lemma combine_estimates' {A : ℝ} (hA : A > 0)
  {spf : ScaledPowerFunction} (hp₀ : p₀ ∈ Icc 1 q₀) (hq₀ : 1 ≤ q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
  (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
  (hq : q⁻¹ = (1 - (ENNReal.ofReal t)) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹) (hf : Memℒp f p μ) (hT : Subadditive' T A)
  (hpσ₀ : q₀ < ⊤ → p₀.toReal + spf.σ⁻¹ * (q.toReal - q₀.toReal) * (p₀.toReal / q₀.toReal) = p.toReal)
  (hpσ₁ : q₁ < ⊤ → p₁.toReal + spf.σ⁻¹ * (q.toReal - q₁.toReal) * (p₁.toReal / q₁.toReal) = p.toReal)
  (h_cases_q₀top : q₀ < ⊤ ∨ ∀ s ∈ Ioi 0, distribution (T (f - trunc f ((spf_to_tc spf).ton s))) (ENNReal.ofReal s) ν = 0)
  (h_cases_q₁top : q₁ < ⊤ ∨ ∀ s ∈ Ioi 0, distribution (T (trunc f ((spf_to_tc spf).ton s))) (ENNReal.ofReal s) ν = 0)
  (hq_select₀ : if (spf_to_tc spf).mon = true then q₀ < q else q < q₀)
  (hq_select₁ : if (spf_to_tc spf).mon = false then q₁ < q else q < q₁)
  (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
  (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
  (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ)) :
    ∫⁻ x , ‖T f x‖₊ ^ q.toReal ∂ν ≤
    (if (q₁ < ⊤) then 1 else 0) *
    ((C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
    ENNReal.ofReal (spf.d ^ (q.toReal - q₁.toReal)) *
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹) +
    (if (q₀ < ⊤) then 1 else 0) *
    ((C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
    ENNReal.ofReal (spf.d ^ (q.toReal - q₀.toReal)) *
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
  have one_le_p₀ := hp₀.1
  have one_le_p1 := hp₁.1
  have p₀pos : p₀ > 0 := lt_of_lt_of_le zero_lt_one hp₀.1
  have q₀pos : q₀ > 0 := lt_of_lt_of_le zero_lt_one hq₀
  have p₁pos : p₁ > 0 := lt_of_lt_of_le zero_lt_one hp₁.1
  have q₁pos : q₁ > 0 := lt_of_lt_of_le zero_lt_one hq₁
  let tc := spf_to_tc spf
  have := spf.hd
  calc
  ∫⁻ x , ‖T f x‖₊ ^ q.toReal ∂ν
    ≤ ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * ∫⁻ s in Ioi (0 : ℝ),
      distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q.toReal - 1)) +
      distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q.toReal - 1)) := by
    apply _estimate_norm_rpow_range_operator
    · apply one_le_toReal
      · exact one_le_interp hq₀ hq₁ hq₀q₁ ht hq
      · exact Ne.lt_top (interp_exp_ne_top hq₀q₁ ht hq)
    · exact hA
    · exact hT
    · exact AEStronglyMeasurable.aemeasurable (h₂T hf)
  _ ≤ ENNReal.ofReal ((2 * A)^q.toReal * q.toReal) *
      ((if (q₁ < ⊤) then 1 else 0) * (C₁ ^ q₁.toReal * (∫⁻ s in Ioi (0 : ℝ),
        snorm (trunc f (tc.ton s)) p₁ μ ^ q₁.toReal * ENNReal.ofReal (s ^ (q.toReal - q₁.toReal - 1)))) +
      (if (q₀ < ⊤) then 1 else 0) * (C₀ ^ q₀.toReal * ∫⁻ s in Ioi (0 : ℝ),
        snorm (f - trunc f (tc.ton s)) p₀ μ ^ q₀.toReal * ENNReal.ofReal (s ^ (q.toReal - q₀.toReal - 1)))) := by
    gcongr
    have one_le_p : 1 ≤ p := one_le_interp hp₀.1 hp₁.1 (ne_of_lt hp₀p₁) ht hp
    apply estimate_norm_rpow_range_operator' one_le_p <;> try assumption
    · exact Ne.lt_top (interp_exp_ne_top (ne_of_lt hp₀p₁) ht hp)
    · refine (interp_exp_between (lt_of_lt_of_le zero_lt_one hp₀.1) (lt_of_lt_of_le zero_lt_one hp₁.1) hp₀p₁ ht hp).2
    · refine (interp_exp_between (lt_of_lt_of_le zero_lt_one hp₀.1) (lt_of_lt_of_le zero_lt_one hp₁.1) hp₀p₁ ht hp).1
  _ ≤ (if (q₁ < ⊤) then 1 else 0) * (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C₁ ^ q₁.toReal * ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁.toReal) * (@φ _ _ _ μ _ f true p₁.toReal q₁.toReal q.toReal tc s t )) ^ (q₁.toReal / p₁.toReal)))
    +
    (if (q₀ < ⊤) then 1 else 0) * (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C₀ ^ q₀.toReal * ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₀.toReal) * (@φ _ _ _ μ _ f false p₀.toReal q₀.toReal q.toReal tc s t )) ^ (q₀.toReal / p₀.toReal))) := by
    rw [mul_add]
    repeat rw [← mul_assoc]
    rw [mul_comm _ (if q₁ < ⊤ then 1 else 0)]
    rw [mul_comm _ (if q₀ < ⊤ then 1 else 0)]
    repeat rw [mul_assoc]
    have eq_p₀ : ENNReal.ofReal (p₀.toReal) = p₀ := ofReal_toReal (LT.lt.ne_top hp₀p₁)
    nth_rw 1 [← eq_p₀]
    split_ifs with is_q₁top is_q₀top
    · have eq_p₁ : ENNReal.ofReal (p₁.toReal) = p₁ := by
        refine ofReal_toReal (ne_of_lt (lt_of_le_of_lt hp₁.2 is_q₁top))
      nth_rw 1 [← eq_p₁]
      rw [eq_trunc_integral' hf.1]
      · apply add_le_add_left
        apply mul_le_mul_left'
        apply mul_le_mul_left'
        apply mul_le_mul_left'
        apply estimate_trunc_comp_integral hf.1
        · apply one_le_toReal
          · exact hp₀.1
          · exact Ne.lt_top (ofReal_toReal_eq_iff.mp eq_p₀)
        · apply one_le_toReal
          · exact hq₀
          · exact is_q₀top
      · exact exp_toReal_pos' one_le_p1 (lt_of_le_of_lt hp₁.2 is_q₁top)
      · exact exp_toReal_pos' hq₁ is_q₁top
    · have eq_p₁ : ENNReal.ofReal (p₁.toReal) = p₁ := ofReal_toReal
          (LT.lt.ne_top (lt_of_le_of_lt hp₁.2 is_q₁top))
      nth_rw 1 [← eq_p₁]
      rw [eq_trunc_integral' hf.1]
      · apply add_le_add_left
        · repeat rw [zero_mul]
      · exact exp_toReal_pos' one_le_p1 (lt_of_le_of_lt hp₁.2 is_q₁top)
      · exact exp_toReal_pos' hq₁ is_q₁top
    · repeat rw [zero_mul]
      apply add_le_add_left
      apply mul_le_mul_left'
      apply mul_le_mul_left'
      apply mul_le_mul_left'
      apply estimate_trunc_comp_integral hf.1
      · apply one_le_toReal hp₀.1 (Ne.lt_top (ofReal_toReal_eq_iff.mp eq_p₀))
      · apply one_le_toReal hq₀ (by assumption)
    · repeat rw [zero_mul]
  _ ≤ (if (q₁ < ⊤) then 1 else 0) * (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C₁ ^ q₁.toReal * (ENNReal.ofReal p₁.toReal ^ (q₁.toReal / p₁.toReal) * (∫⁻ t : ℝ in Ioi 0,
      (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f ⊤ p₁.toReal q₁.toReal q.toReal tc s t ^(q₁.toReal / p₁.toReal)) ^ (p₁.toReal / q₁.toReal) ) ^ (q₁.toReal / p₁.toReal))))
      +
      (if (q₀ < ⊤) then 1 else 0) * (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C₀ ^ q₀.toReal * (ENNReal.ofReal p₀.toReal ^ (q₀.toReal / p₀.toReal) * (∫⁻ t : ℝ in Ioi 0,
      (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f ⊥ p₀.toReal q₀.toReal q.toReal tc s t ^ (q₀.toReal / p₀.toReal)) ^ (p₀.toReal / q₀.toReal) ) ^ (q₀.toReal / p₀.toReal)))) := by
    rw [extract_constant_double_integral_rpow (by positivity)]; swap; exact coe_ne_top
    rw [extract_constant_double_integral_rpow (by positivity)]; swap; exact coe_ne_top
    split_ifs with is_p₁top is_p₀top
    · gcongr
      · apply minkowski_φ
      · apply minkowski_φ
    · rw [zero_mul, add_zero, zero_mul, add_zero]
      gcongr
      apply minkowski_φ
    · rw [zero_mul, zero_add, zero_mul, zero_add]
      gcongr
      apply minkowski_φ
    · simp
  _ = (if (q₁ < ⊤) then 1 else 0) * (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C₁ ^ q₁.toReal *
      (ENNReal.ofReal p₁.toReal ^ (q₁.toReal / p₁.toReal) *
      (ENNReal.ofReal (spf.d ^ (q.toReal - q₁.toReal)) ^ (p₁.toReal / q₁.toReal) *
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ ^ (p₁.toReal / q₁.toReal) *
      p⁻¹ * snorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal)))) +
      (if (q₀ < ⊤) then 1 else 0) * (ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * (C₀ ^ q₀.toReal *
      (ENNReal.ofReal p₀.toReal ^ (q₀.toReal / p₀.toReal) *
      (ENNReal.ofReal (spf.d ^ (q.toReal - q₀.toReal)) ^ (p₀.toReal / q₀.toReal) *
      ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ ^ (p₀.toReal / q₀.toReal) *
      p⁻¹ * snorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal)))) := by
    split_ifs with is_q₁top is_q₀top
    · rw [value_integral_summary (q' := q₁) (p' := p₁) (p := p) p₀pos q₀pos p₁pos q₁pos ht] <;> try assumption
      rw [value_integral_summary (q' := q₀) (p' := p₀) (p := p) p₀pos q₀pos p₁pos q₁pos ht] <;> try assumption
      · exact hpσ₀ is_q₀top
      · simp only
      · simp only
      · exact LT.lt.ne_top hp₀p₁
      · exact LT.lt.ne_top is_q₀top
      · simpa
      · exact AEStronglyMeasurable.aemeasurable hf.1
      · exact hpσ₁ is_q₁top
      · simp only
      · simp only
      · exact LT.lt.ne_top (lt_of_le_of_lt hp₁.2 is_q₁top)
      · apply ne_of_lt is_q₁top
      · simpa
      · exact AEStronglyMeasurable.aemeasurable hf.1
    · simp only [top_eq_true, one_mul, bot_eq_false, zero_mul, add_zero, toReal_nonneg]
      rw [value_integral_summary (q' := q₁) (p' := p₁) p₀pos q₀pos p₁pos q₁pos] <;> try assumption
      · exact hpσ₁ is_q₁top
      · simp only
      · simp only
      · exact LT.lt.ne_top (lt_of_le_of_lt hp₁.2 is_q₁top)
      · exact LT.lt.ne_top is_q₁top
      · simpa
      · exact AEStronglyMeasurable.aemeasurable hf.1
    · simp only [top_eq_true, zero_mul, bot_eq_false, one_mul, zero_add]
      rw [value_integral_summary (q' := q₀) (p' := p₀) p₀pos q₀pos p₁pos q₁pos] <;> try assumption
      · apply hpσ₀; assumption
      · simp only
      · simp only
      · apply LT.lt.ne_top; assumption
      · apply LT.lt.ne_top; assumption
      · simpa
      · exact AEStronglyMeasurable.aemeasurable hf.1
    · simp only [top_eq_true, zero_mul, bot_eq_false, add_zero]
  _ = _ := by
    split_ifs with is_q₁top is_q₀top
    · repeat rw [one_mul]
      rw [computation_0, computation_0] <;> try first | positivity | assumption
      · exact lt_of_le_of_lt hp₀.2 is_q₀top
      · exact lt_of_le_of_lt hp₁.2 is_q₁top
    · simp only [one_mul, zero_mul, add_zero]
      rw [computation_0] <;> try first | positivity | assumption
      exact lt_of_le_of_lt hp₁.2 is_q₁top
    · simp only [one_mul, zero_mul, add_zero]
      rw [computation_0] <;> try first | positivity | assumption
      have q₀lt_top : q₀ < ⊤ := by assumption
      exact lt_of_le_of_lt hp₀.2 q₀lt_top
    · simp only [zero_mul, add_zero]

lemma simplify_factor₀ {spf : ScaledPowerFunction} (hq₀' : q₀ < ⊤)
    (hp₀ : p₀ ∈ Icc 1 q₀) (hq₀ : 1 ≤ q₀) (hp₁ : p₁ ∈ Icc 1 q₁)
    (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
    (hq : q⁻¹ = (1 - (ENNReal.ofReal t)) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹)
    (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : snorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ (ne_of_lt hp₀p₁) hC₀ hC₁ hF hp) :
    (C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
    ENNReal.ofReal (spf.d ^ (q.toReal - q₀.toReal)) =
    (C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ ((1 - t) * p₀⁻¹.toReal * q.toReal) *
    (C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (t * p₁⁻¹.toReal * q.toReal) := by
  have hp' : p ∈ Ioo 0 ⊤ := ⟨interpolated_pos' (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp,
              interp_exp_lt_top (ne_of_lt hp₀p₁) ht hp⟩ -- TODO: make this a separate lemma
  rw [hspf]
  unfold spf_ch d
  dsimp only
  rw [← ofReal_rpow_of_pos]
  · rw [ofReal_toReal]
    · nth_rw 3 [div_eq_mul_inv]
      rw [ENNReal.mul_rpow_of_ne_zero _ _ (q.toReal - q₀.toReal)]
      · rw [← ENNReal.rpow_neg, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        repeat rw [← mul_assoc]
        rw [← ENNReal.rpow_add]
        · rw [eq_exponents₀ ht (pos_rb_of_Icc_1_inh hp₀) (pos_rb_of_Icc_1_inh hp₁) hq₀q₁ hq (ne_of_lt hq₀')]
          rw [neg_mul]
          rw [eq_exponents₁ ht (pos_rb_of_Icc_1_inh hp₀) (pos_rb_of_Icc_1_inh hp₁) hq₀q₁ hq (ne_of_lt hq₀')]
          congr
          ring
        · apply ne_of_gt <| d_pos_aux₀ (pos_of_Icc_1 hp₀) hC₀ hp' hF
        · exact d_ne_top_aux₀ (LT.lt.ne_top hp₀p₁) hC₀ hp' hF
      · refine d_ne_zero_aux₀ (pos_of_Icc_1 hp₀) hC₀ hp' hF ?_
        intro h; rw [h]; simp
      · apply ENNReal.inv_ne_zero.mpr
        refine d_ne_top_aux₁ ?_ (pos_of_Icc_1 hp₁) hC₁ hp' hF
        intro h; rw [h]; simp
    · apply ne_of_lt
      apply div_lt_top
      · refine d_ne_top_aux₁ ?_ (pos_of_Icc_1 hp₀) hC₀ hp' hF
        intro h; rw [h]; simp
      · refine d_ne_zero_aux₀ (pos_of_Icc_1 hp₁) hC₁ hp' hF ?_
        intro h; rw [h]; simp
  · apply d_pos hC₀ hC₁ hF (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp'

lemma simplify_factor₁ {spf : ScaledPowerFunction} (hq₁' : q₁ < ⊤)
    (hp₀ : p₀ ∈ Icc 1 q₀) (hq₀ : 1 ≤ q₀) (hp₁ : p₁ ∈ Icc 1 q₁)
    (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
    (hq : q⁻¹ = (1 - (ENNReal.ofReal t)) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹)
    (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : snorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ (ne_of_lt hp₀p₁) hC₀ hC₁ hF hp) :
    (C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
    ENNReal.ofReal (spf.d ^ (q.toReal - q₁.toReal)) =
    (C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ ((1 - t) * p₀⁻¹.toReal * q.toReal) *
    (C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (t * p₁⁻¹.toReal * q.toReal) := by
  have hp' : p ∈ Ioo 0 ⊤ := ⟨interpolated_pos' (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp,
              interp_exp_lt_top (ne_of_lt hp₀p₁) ht hp⟩ -- TODO: make this a separate lemma
  rw [hspf]
  unfold spf_ch d
  dsimp only
  rw [← ofReal_rpow_of_pos]
  · rw [ofReal_toReal]
    · nth_rw 3 [div_eq_mul_inv]
      rw [ENNReal.mul_rpow_of_ne_zero _ _ (q.toReal - q₁.toReal)]
      · rw [← ENNReal.rpow_neg, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        repeat rw [← mul_assoc]
        rw [mul_comm, ← mul_assoc]
        rcases (ne_or_eq p₁ ⊤) with p₁ne_top | p₁eq_top
        · rw [← ENNReal.rpow_add]
          · rw [eq_exponents₃ ht (pos_rb_of_Icc_1_inh hp₀) (pos_rb_of_Icc_1_inh hp₁) hq₀q₁ hq (ne_of_lt hq₁')]
            rw [eq_exponents₄ ht (pos_rb_of_Icc_1_inh hp₀) (pos_rb_of_Icc_1_inh hp₁) hq₀q₁ hq (ne_of_lt hq₁')]
            rw [mul_comm]
          · exact ne_of_gt <| d_pos_aux₀ (pos_of_Icc_1 hp₁) hC₁ hp' hF
          · exact d_ne_top_aux₀ p₁ne_top hC₁ hp' hF
        · rw [p₁eq_top]
          simp
          rw [eq_exponents₄ ht (pos_rb_of_Icc_1_inh hp₀) (pos_rb_of_Icc_1_inh hp₁) hq₀q₁ hq (ne_of_lt hq₁')]
      · refine d_ne_zero_aux₀ (pos_of_Icc_1 hp₀) hC₀ hp' hF ?_
        intro h; rw [h]; simp
      · apply ENNReal.inv_ne_zero.mpr
        refine d_ne_top_aux₁ ?_ (pos_of_Icc_1 hp₁) hC₁ hp' hF
        intro h; rw [h]; simp
    · apply ne_of_lt
      apply div_lt_top
      · refine d_ne_top_aux₁ ?_ (pos_of_Icc_1 hp₀) hC₀ hp' hF
        intro h; rw [h]; simp
      · refine d_ne_zero_aux₀ (pos_of_Icc_1 hp₁) hC₁ hp' hF ?_
        intro h; rw [h]; simp
  · apply d_pos hC₀ hC₁ hF (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp'

lemma combine_estimates'' {A : ℝ} (hA : A > 0)
    {spf : ScaledPowerFunction}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hq₀ : 1 ≤ q₀) (hp₁ : p₁ ∈ Icc 1 q₁)
    (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
    (hq : q⁻¹ = (1 - (ENNReal.ofReal t)) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹) (hf : Memℒp f p μ) (hT : Subadditive' T A)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ))
    (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : snorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ (ne_of_lt hp₀p₁) hC₀ hC₁ hF hp):
    ∫⁻ x , ‖T f x‖₊ ^ q.toReal ∂ν ≤
    (if (q₁ < ⊤) then 1 else 0) *
    ((C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
    ENNReal.ofReal (spf.d ^ (q.toReal - q₁.toReal)) *
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹) +
    (if (q₀ < ⊤) then 1 else 0) *
    ((C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
    ENNReal.ofReal (spf.d ^ (q.toReal - q₀.toReal)) *
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
  have p₀pos : p₀ > 0 := by exact pos_of_Icc_1 hp₀
  have p₁pos : p₁ > 0 := by exact pos_of_Icc_1 hp₁
  have q₀pos : q₀ > 0 := by exact pos_rb_of_Icc_1_inh hp₀
  have q₁pos : q₁ > 0 := by exact pos_rb_of_Icc_1_inh hp₁
  have p₀ne_p₁ : p₀ ≠ p₁ := by exact ne_of_lt hp₀p₁
  apply combine_estimates' <;> try assumption
  · intro q₀lt_top
    rw [hspf]
    apply ζ_equality_6 ht (pos_of_Icc_1 hp₀) (pos_rb_of_Icc_1_inh hp₀)
        (pos_of_Icc_1 hp₁) (pos_rb_of_Icc_1_inh hp₁) (ne_of_lt hp₀p₁) (hq₀q₁)
        hp hq (ne_of_lt (lt_of_le_of_lt hp₀.2 q₀lt_top)) (ne_of_lt q₀lt_top)
  · intro q₁lt_top
    rw [hspf]
    sorry
  · rcases (ne_or_eq q₀ ⊤) with q₀ne_top | q₀eq_top
    · exact Or.inl (Ne.lt_top q₀ne_top)
    · right
      intro s (hs : s > 0)
      #check weaktype_estimate_trunc_compl_top
      apply weaktype_estimate_trunc_compl_top (p₀ := p₀) (p := p) (d := spf.d) hC₀ hp₀.1 q₀eq_top
      · unfold spf_to_tc
        simp only
        rw [hspf]
        unfold spf_ch
        simp only
        unfold ζ
        sorry
      · rw [hspf]
        unfold spf_ch
        dsimp only
        unfold d
        sorry
      · exact (interp_exp_between (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp₀p₁ ht hp).1
      · exact interp_exp_ne_top (ne_of_lt hp₀p₁) ht hp
      · exact hf
      · exact h₀T
      · exact hs
  · rcases (ne_or_eq q₁ ⊤) with q₁ne_top | q₁eq_top
    · exact Or.inl (Ne.lt_top q₁ne_top)
    · right
      intro s (hs : s > 0)
      rcases (ne_or_eq p₁ ⊤) with p₁ne_top | p₁eq_top
      · apply weaktype_estimate_trunc_top (p₁ := p₁) (p := p) (d := spf.d) hC₁
        · sorry
        · sorry
        · exact one_le_interp hp₀.1 hp₁.1 (ne_of_lt hp₀p₁) ht hp
        · exact Ne.lt_top p₁ne_top
        · exact q₁eq_top
        · exact (interp_exp_between (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp₀p₁ ht hp).2
        · exact hf
        · exact h₁T
        · exact hs
      · apply weaktype_estimate_trunc_top_top (p₁ := p₁) (p := p) hC₁
        · exact one_le_interp hp₀.1 hp₁.1 (ne_of_lt hp₀p₁) ht hp
        · exact p₁eq_top
        · exact q₁eq_top
        · exact (interp_exp_between (pos_of_Icc_1 hp₀) (pos_of_Icc_1 hp₁) hp₀p₁ ht hp).2
        · exact hf
        · exact h₁T
        · exact hs
        · unfold spf_to_tc
          simp only
          rw [hspf]
          unfold spf_ch
          simp only
          sorry
  · unfold spf_to_tc
    rw [hspf]
    simp only
    unfold spf_ch
    simp only
    split_ifs with is_σ_pos eq
    · exact (ζ_pos_iff_of_lt₀ ht (pos_of_Icc_1 hp₀) (pos_rb_of_Icc_1_inh hp₀) (pos_of_Icc_1 hp₁)
        (pos_rb_of_Icc_1_inh hp₁) hq₀q₁ hp hq hp₀p₁).mp is_σ_pos
    · exact absurd (Eq.refl true) eq
    · tauto
    · exact (ζ_le_zero_iff_of_lt₀ ht p₀pos q₀pos p₁pos q₁pos hq₀q₁ hp hq hp₀p₁).mp
          (le_of_not_lt is_σ_pos)
  · unfold spf_to_tc
    rw [hspf]
    simp only
    unfold spf_ch
    simp only
    split_ifs with is_σ_pos eq
    · exact False.elim eq
    · exact (ζ_pos_iff_of_lt₁ ht p₀pos q₀pos p₁pos q₁pos hq₀q₁ hp hq hp₀p₁).mp is_σ_pos
    · exact (ζ_le_zero_iff_of_lt₁ ht p₀pos q₀pos p₁pos q₁pos hq₀q₁ hp hq hp₀p₁).mp
          (le_of_not_lt is_σ_pos)
    · tauto

lemma combine_estimates''' {A : ℝ} (hA : A > 0)
    {spf : ScaledPowerFunction}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hq₀ : 1 ≤ q₀) (hp₁ : p₁ ∈ Icc 1 q₁)
    (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
    (hq : q⁻¹ = (1 - (ENNReal.ofReal t)) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹) (hf : Memℒp f p μ) (hT : Subadditive' T A)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ))
    (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : snorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ (ne_of_lt hp₀p₁) hC₀ hC₁ hF hp):
    ∫⁻ x , ‖T f x‖₊ ^ q.toReal ∂ν ≤
    (C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ ((1 - t) * p₀⁻¹.toReal * q.toReal) *
    (C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (t * p₁⁻¹.toReal * q.toReal) *
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ((if (q₁ < ⊤) then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if (q₀ < ⊤) then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
  calc
  _ ≤ _ := by
    apply combine_estimates'' (hT := hT) <;> try assumption
  _ = _ := by
    split_ifs
    · rw [simplify_factor₀ (ht := ht) (C₀ := C₀) (p₁ := p₁) (C₁ := C₁)] <;> try assumption
      rw [simplify_factor₁ (ht := ht) (C₁ := C₁) (p₀ := p₀) (C₀ := C₀)] <;> try assumption
      ring
    · simp only [one_mul, zero_mul, add_zero]
      rw [simplify_factor₁ (ht := ht) (C₀ := C₀) (p₁ := p₁) (C₁ := C₁)] <;> try assumption
    · simp only [one_mul, zero_mul, add_zero]
      rw [simplify_factor₀ (ht := ht) (C₀ := C₀) (p₁ := p₁) (C₁ := C₁)] <;> try assumption
      ring
    · simp only [zero_mul, add_zero, mul_zero]

lemma combine_estimates'''' {A : ℝ} (hA : A > 0)
    {spf : ScaledPowerFunction}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hq₀ : 1 ≤ q₀) (hp₁ : p₁ ∈ Icc 1 q₁)
    (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - (ENNReal.ofReal t)) * p₀⁻¹ + (ENNReal.ofReal t) * p₁⁻¹)
    (hq : q⁻¹ = (1 - (ENNReal.ofReal t)) * q₀⁻¹ + (ENNReal.ofReal t) * q₁⁻¹) (hf : Memℒp f p μ) (hT : Subadditive' T A)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ))
    (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : snorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ (ne_of_lt hp₀p₁) hC₀ hC₁ hF hp) :
    snorm (T f) q ν ≤
    C₀ ^ (1 - t) * (p₀ / p) ^ ((1- t) * p₀⁻¹.toReal) *
    C₁ ^ t * (p₁ / p) ^ (t * p₁⁻¹.toReal) *
    snorm f p μ *
    ENNReal.ofReal (2 * A) * q ^ q⁻¹.toReal *
    (((if (q₁ < ⊤) then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if (q₀ < ⊤) then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal := by
  have q_ne_zero : q ≠ 0 :=
    ne_of_gt <| interpolated_pos' (pos_rb_of_Icc_1_inh hp₀) (pos_rb_of_Icc_1_inh hp₁) hq
  have q_ne_top : q ≠ ⊤ := interp_exp_ne_top hq₀q₁ ht hq
  have q'pos : q.toReal > 0 := toReal_pos q_ne_zero q_ne_top
  refine le_of_rpow_le q'pos ?_
  calc
  _ = ∫⁻ x , ‖T f x‖₊ ^ q.toReal ∂ν := by
    unfold snorm snorm'
    split_ifs <;> [contradiction; rw [one_div, ENNReal.rpow_inv_rpow (ne_of_gt q'pos)]]
  _ ≤ _ := by apply combine_estimates''' (hT := hT) <;> try assumption
  _ = ((↑C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ ((1 - t) * p₀⁻¹.toReal) *
            (↑C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (t * p₁⁻¹.toReal) *
          ENNReal.ofReal (2 * A) *
        q ^ q⁻¹.toReal *
      ((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
          (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) ^
        q⁻¹.toReal) ^
    q.toReal := by
    repeat rw [toReal_inv]
    repeat rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt q'pos)]
    repeat rw [ENNReal.rpow_inv_rpow (ne_of_gt q'pos)]
    rw [ofReal_mul' (le_of_lt q'pos)]
    rw [ofReal_toReal_eq_iff.mpr q_ne_top]
    repeat rw [← ENNReal.rpow_mul]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (le_of_lt q'pos)]
    repeat rw [← mul_assoc]
  _ = _ := by
    repeat rw [← mul_assoc]
    have : (↑C₀ ^ p₀.toReal * (p₀ / p) * snorm f p μ ^ p.toReal) ^ ((1 - t) * p₀⁻¹.toReal) *
            (↑C₁ ^ p₁.toReal * (p₁ / p) * snorm f p μ ^ p.toReal) ^ (t * p₁⁻¹.toReal) =
            C₀ ^ (1 - t) * (p₀ / p) ^ ((1- t) * p₀⁻¹.toReal) *
            C₁ ^ t * (p₁ / p) ^ (t * p₁⁻¹.toReal) *
            snorm f p μ := by
      rw [mul_rpow_of_nonneg]
    congr
























-- For Minkowski's inequality: first prove statement dual statement about the norm
#exit


lemma rpow_add_of_pos (a : ℝ≥0∞) (c d : ℝ) (hc : c > 0) (hd : d > 0):
    a ^ (c + d) = a ^ c * a ^ d := by
  have hcd : c + d  > 0 := by linarith
  rcases (eq_or_ne a 0) with a_eq_zero | a_ne_zero
  · rw [a_eq_zero]
    rw [zero_rpow_of_pos hcd, zero_rpow_of_pos hc, zero_rpow_of_pos hd, mul_zero]
  · rcases (eq_or_ne a ⊤) with a_eq_top | a_ne_top
    · rw [a_eq_top]
      rw [top_rpow_of_pos hcd, top_rpow_of_pos hc, top_rpow_of_pos hd, top_mul_top]
    · rw [ENNReal.rpow_add c d a_ne_zero a_ne_top]

lemma exists_monotone_integrable {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∃ g : ℕ → α → ℝ≥0∞, Monotone g ∧ ∀ n : ℕ, ∫⁻ x, g n x ∂μ < ⊤ ∧
    ⨆ n : ℕ, g n = f := by
  sorry

lemma representationLp {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : Measurable f) {p q : ℝ} (hp : p > 1) (hq : q ≥ 1)
    (hpq : 1 / p + 1 / q = 1):
    ∫⁻ x : α, (f x) ^ p ∂μ =
    ⨆ g ∈ {g' : α → ℝ≥0∞ | ∫⁻ x : α, (g x) ^ q ∂μ ≤ 1},
    ∫⁻ x : α, (f x) * g x ∂μ := by
  let A := spanningSets μ
  have A_mon := monotone_spanningSets μ
  let g := fun n : ℕ ↦ (A n).indicator (fun x ↦ min (f x) n)
  have g_mon : Monotone g := by
    intro m n hmn x; unfold_let g; unfold indicator; simp only
    split <;> rename_i hx1
    · split <;> rename_i hx2
      · refine min_le_min_left (f x) (Nat.cast_le.mpr hmn)
      · exact (False.elim (hx2 (A_mon hmn hx1)))
    · exact zero_le _
  have f_mul : ∀ n : ℕ, (g n) ^ p ≤ f * (g n) ^ (p - 1) := by
    intro n x; unfold_let g; unfold indicator; simp; split <;> rename_i hx1
    · refine le_trans (b := (min (f x) ↑n) * min (f x) ↑n ^ (p - 1)) ?_ ?_
      · nth_rewrite 1 [← add_sub_cancel 1 p]
        rw [rpow_add_of_pos, ENNReal.rpow_one]; exact Real.zero_lt_one; linarith
      · exact mul_le_mul_right' (min_le_left (f x) ↑n) (min (f x) ↑n ^ (p - 1))
    · rw [zero_rpow_of_pos]; exact zero_le _; linarith
  have g_sup : ∀ x : α, ⨆ n : ℕ, g n x = f x := by
    intro x; refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?h₁ ?h₂
    · intro n; unfold_let g; unfold indicator; simp only
      split; exact min_le_left (f x) ↑n; exact zero_le (f x)
    · intro w hw
      rcases (exists_exists_eq_and.mp
          (Eq.mpr (id (congrArg (fun _a ↦ x ∈ _a) (MeasureTheory.iUnion_spanningSets μ))) True.intro)) with ⟨m, wm⟩
      rcases exists_nat_gt (w.toReal + (f x).toReal) with ⟨n, wn⟩
      use n + m
      unfold_let g; unfold indicator; simp only
      split <;> rename_i hx
      · rcases (eq_top_or_lt_top (f x)) with fx_eq_top | fx_lt_top
        · simp only [Nat.cast_add, lt_min_iff]; simp [fx_eq_top] at wn
          exact ⟨hw, lt_of_lt_of_le (b := (n : ℝ≥0∞))
              ((toNNReal_lt_toNNReal (LT.lt.ne_top hw) coe_ne_top).mp wn) le_self_add⟩
        · rw [min_eq_left]; exact hw
          rw [Nat.cast_add]
          refine le_trans (le_of_lt ?_) (le_self_add (a := (n : ℝ≥0∞)) (c := m))
          rw [← (ofReal_toReal_eq_iff.mpr (LT.lt.ne_top fx_lt_top))]
          exact (ofReal_lt_iff_lt_toReal toReal_nonneg coe_ne_top).mpr
              (lt_of_add_lt_of_nonneg_right wn (toReal_nonneg))
      · refine False.elim (hx (A_mon le_add_self wm))
  sorry

/-- Marcinkiewicz real interpolation theorem, for the case of equal domain: p₀ = p₁. -/
lemma exists_hasStrongType_real_interpolation' {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (hp₀₁ : p₀ = p₁) :
    ∃ C > 0, HasStrongType T p q μ ν C := by
  let Cfinal : ℝ≥0 := C₀
  exists Cfinal
  constructor
  · sorry
  · have p_eq_p₀ : p = p₀ := by sorry
    intros f f_mem
    rewrite [p_eq_p₀] at f_mem
    have h₀T_ap := (h₀T f f_mem).2
    rewrite [hp₀₁] at f_mem
    have h₁T_ap := (h₁T f f_mem).2
    constructor
    · exact (h₁T f f_mem).1
    · unfold wnorm at h₀T_ap
      split at h₀T_ap
      · have q_eq_top : q = ⊤ := sorry
        rewrite [← p_eq_p₀] at h₀T_ap
        unfold snorm
        split
        · apply zero_le
        · exact h₀T_ap
      · sorry

/-- Marcinkiewicz real interpolation theorem, for the case p₀ ≠ p₁ and all exponents
    are less than ∞.
    TODO: So far the assymption that p₀ ≠ p₁ is not added -/
lemma exists_hasStrongType_real_interpolation'' {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hq₀ : q₀ < ∞) (hq₁ : q₁ < ∞) :
    ∃ C > 0, HasStrongType T p q μ ν C := sorry

/-- Marcinkiewicz real interpolation theorem. -
-- feel free to assume that T also respect a.e.-equality if needed. -/
/- For the proof, see
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.4, theorem 6.28.
You want to use `trunc f A` when the book uses `h_A`.
Minkowski's inequality is `ENNReal.lintegral_Lp_add_le` -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) :
    ∃ C > 0, HasStrongType T p q μ ν C := by
  exists ?_
  constructor
  · sorry
  · unfold HasStrongType
    intros f fMem
    constructor
    · exact h₂T f fMem
    · let A := (3 : ℝ).toNNReal
      have h₀ : ∫⁻ x, ‖trunc f A x‖₊ ^ p.toReal ∂μ =
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
          distribution (trunc f A) (ENNReal.ofReal t) μ := by
        apply lintegral_norm_pow_eq_distribution
        sorry
      -- #check distribution_trunc
      -- have h₁ := distribution_trunc (f := f) (s := ENNReal.ofReal t) (t := A.toReal) (μ := μ)
      -- rewrite [h₁] at h₀
      -- have h₁ : ∫⁻ t in Ioo 0 A, ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ =
      --     ∫⁻ x : ℝ, (Ioo 0 A).indicator (fun t : ℝ ↦ ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ) := by
      sorry
      -- have h₂ : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
      --     distribution (trunc f A) (ENNReal.ofReal t) μ =
      --     ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ := by
      --   rewrite [← lintegral_indicator (hs := measurableSet_Ioi)]
      --   rewrite [← lintegral_indicator (hs := measurableSet_Ioo)]
      --   apply congr_arg
      --   ext t
      --   unfold indicator
      --   simp
      --   rewrite [distribution_trunc]
      --   simp
      --   split <;> rename_i h₃
      --   · split <;> rename_i h₄
      --     · split <;> rename_i h₅
      --       · rfl
      --       · simp at h₅
      --         have h₆ := h₅ h₃
      --         have _ : t < ↑A := by
      --           rewrite [← ofReal_coe_nnreal] at h₄
      --           refine (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₃)).mp h₄
      --         linarith
      --     · split <;> rename_i h₅
      --       · have _ : A.toReal ≤ t := by
      --           simp at h₄
      --           rewrite [← ofReal_coe_nnreal] at h₄
      --           exact (ofReal_le_ofReal_iff (le_of_lt h₃)).mp h₄
      --         linarith
      --       · rfl
      --   · split <;> rename_i h₄
      --     · linarith
      --     · rfl
      -- unfold HasWeakType at h₀T
      -- unfold wnorm at h₀T
      -- unfold wnorm' at h₀T
      -- -- have h₃ : ∫⁻ x, ‖T f (x)‖₊ ^q.toReal ∂ν  =
      --     2^q.toReal * q * ∫⁻ s in Ioi (0 : ℝ),
      --     ENNReal.ofReal s^(q.toReal - 1) * distribution (T f) ((ENNReal.ofReal 2)*(ENNReal.ofReal s)) ν := by
      --   have one_le_q : (1 : ℝ) ≤ q.toReal := sorry
      --   rewrite [lintegral_norm_pow_eq_distribution one_le_q]
      --   · have two_gt_0 : (2 : ℝ) > 0 := by linarith
      --     nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := 2) two_gt_0]
      --     have h₄ : ENNReal.ofReal |2| ≠ ⊤ := coe_ne_top
      --     have h₅ : (2 ^ q.toReal) * q ≠ ⊤ := sorry
      --     rewrite [← lintegral_const_mul' (hr := h₄)]
      --     rewrite [← lintegral_const_mul' (hr := h₅)]
      --     apply set_lintegral_congr_fun (measurableSet_Ioi)
      --     apply ae_of_all
      --     simp
      --     intros t t_gt_0
      --     rw [ofReal_mul' (le_of_lt t_gt_0)]
      --     have h₈ : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
      --       exact ofReal_eq_ofNat.mpr rfl
      --     rw [h₈]
      --     rw [← mul_assoc]
      --     rw [← mul_assoc]
      --     -- TODO: rename!!!
      --     apply test_9
      --     sorry

/- State and prove Remark 1.2.7 -/

end MeasureTheory
