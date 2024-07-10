import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Carleson.ToMathlib.MeasureReal

/-
* This file can import all ToMathlib files.
* If adding more than a few result, please put them in a more appropriate file in ToMathlib.
-/

open Function Set
open scoped ENNReal
attribute [gcongr] Metric.ball_subset_ball

lemma IsTop.isMax_iff {α} [PartialOrder α] {i j : α} (h : IsTop i) : IsMax j ↔ j = i := by
  simp_rw [le_antisymm_iff, h j, true_and]
  refine ⟨(· (h j)), swap (fun _ ↦ h · |>.trans ·)⟩


theorem Int.floor_le_iff (c : ℝ) (z : ℤ) : ⌊c⌋ ≤ z ↔ c < z + 1 := by
  rw_mod_cast [← Int.floor_le_sub_one_iff, add_sub_cancel_right]

theorem Int.le_ceil_iff (c : ℝ) (z : ℤ) : z ≤ ⌈c⌉ ↔ z - 1 < c := by
  rw_mod_cast [← Int.add_one_le_ceil_iff, sub_add_cancel]

theorem Int.Icc_of_eq_sub_1 {a b : ℤ} (h : a = b - 1) : Finset.Icc a b = {a, b} := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · rw [h, Finset.mem_Icc] at ht
    by_cases hta : t = b - 1
    · rw [hta, ← h]; exact Finset.mem_insert_self a {b}
    · suffices b = t from this ▸ Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 rfl))
      exact le_antisymm (sub_add_cancel b 1 ▸ (ne_eq t (b - 1) ▸ hta).symm.lt_of_le ht.1) ht.2
  · have hab : a ≤ b := h ▸ sub_le_self b one_pos.le
    rcases Finset.mem_insert.1 ht with rfl | hb
    · exact Finset.mem_Icc.2 ⟨le_refl t, hab⟩
    · rw [Finset.mem_singleton.1 hb]; exact Finset.mem_Icc.2 ⟨hab, le_refl b⟩

lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
  if hfin : s.Finite then
    have hfin' : Finite s := by exact hfin
    rw [tsum_def]
    simp only [ENNReal.summable, ↓reduceDIte]
    have hsup: support (fun (_ : s) ↦ (1 : ℝ≥0∞)) = Set.univ := by
      ext i
      simp only [mem_support, ne_eq, one_ne_zero, not_false_eq_true, mem_univ]
    have hsupfin: (Set.univ : Set s).Finite := by exact finite_univ
    rw [← hsup] at hsupfin
    rw [if_pos hsupfin]
    rw [hfin.encard_eq_coe_toFinset_card]
    simp only [ENat.toENNReal_coe]
    rw [Finset.card_eq_sum_ones]
    rw [finsum_eq_sum (fun (_ : s) ↦ (1 :ℝ≥0∞)) hsupfin]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_inj]
    apply Finset.card_bij (fun a _ => a.val)
    · intro a
      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
        Subtype.coe_prop, imp_self]
    · intro a _ a' _ heq
      ext
      exact heq
    · intro a ha
      use ⟨a,by
        simp only [Finite.mem_toFinset] at ha
        exact ha⟩
      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
        exists_const]
  else
  have : Infinite s := by exact infinite_coe_iff.mpr hfin
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)]
  rw [Set.encard_eq_top_iff.mpr hfin]
  simp only [ENat.toENNReal_top]


lemma ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ℝ≥0∞) :
    ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
  nth_rw 1 [← one_mul c]
  rw [ENNReal.tsum_mul_right,tsum_one_eq']

theorem PseudoMetricSpace.dist_eq_of_dist_zero {X : Type*} [PseudoMetricSpace X] (x : X) {y y' : X}
    (hyy' : dist y y' = 0) : dist x y = dist x y' :=
  dist_comm y x ▸ dist_comm y' x ▸ sub_eq_zero.1 (abs_nonpos_iff.1 (hyy' ▸ abs_dist_sub_le y y' x))

/-! ## `ENNReal` manipulation lemmas -/

lemma ENNReal.sum_geometric_two_pow_toNNReal {k : ℕ} (hk : k > 0) :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-k * n : ℤ) = (1 / (1 - 1 / 2 ^ k) : ℝ).toNNReal := by
  conv_lhs =>
    enter [1, n]
    rw [← rpow_intCast, show (-k * n : ℤ) = (-k * n : ℝ) by simp, rpow_mul, rpow_natCast]
  rw [tsum_geometric, show (2 : ℝ≥0∞) = (2 : ℝ).toNNReal by simp,
    coe_rpow_of_ne_zero (by simp), ← Real.toNNReal_rpow_of_nonneg zero_le_two,
    ← coe_one, ← Real.toNNReal_one, ← coe_sub, NNReal.sub_def,
    Real.toNNReal_one, NNReal.coe_one, Real.coe_toNNReal', max_eq_left (by positivity),
    Real.rpow_neg zero_le_two, Real.rpow_natCast, one_div]
  have : ((1 : ℝ) - (2 ^ k)⁻¹).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add, not_le, inv_lt_one_iff]
    right; exact one_lt_pow (R := ℝ) _root_.one_lt_two hk.ne'
  rw [← coe_inv this, coe_inj, Real.toNNReal_inv, one_div]

lemma ENNReal.sum_geometric_two_pow_neg_one : ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-n : ℤ) = 2 := by
  conv_lhs => enter [1, n]; rw [← one_mul (n : ℤ), ← neg_mul, ← Nat.cast_one]
  rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one]; norm_num

lemma ENNReal.sum_geometric_two_pow_neg_two :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-2 * n : ℤ) = ((4 : ℝ) / 3).toNNReal := by
  conv_lhs => enter [1, n, 2]; rw [← Nat.cast_two]
  rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_two]; norm_num
