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
