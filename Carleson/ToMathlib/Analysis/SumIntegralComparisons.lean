import Mathlib.Analysis.SumIntegralComparisons
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.ToMathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory Set

open scoped ENNReal



variable {x₀ : ℝ} {a b : ℕ} {f g : ℝ → ℝ}

lemma sum_le_integral_of_le
    (hab : a ≤ b) (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) (i + 1 : ℕ), f i ≤ g x)
    (hg : IntegrableOn g (Set.Ico a b)) :
    ∑ i ∈ Finset.Ico a b, f i ≤ ∫ x in a..b, g x := by
  have A i (hi : i ∈ Finset.Ico a b) : IntervalIntegrable g volume i (i + 1 : ℕ) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    apply hg.mono _ le_rfl
    rintro x ⟨hx, h'x⟩
    simp only [Finset.mem_Ico, mem_Ico] at hi ⊢
    exact ⟨le_trans (mod_cast hi.1) hx, h'x.trans_le (mod_cast hi.2)⟩
  calc
  ∑ i ∈ Finset.Ico a b, f i
  _ = ∑ i ∈ Finset.Ico a b, (∫ x in (i : ℝ)..(i + 1 : ℕ), f i) := by simp
  _ ≤ ∑ i ∈ Finset.Ico a b, (∫ x in (i : ℝ)..(i + 1 : ℕ), g x) := by
    apply Finset.sum_le_sum (fun i hi ↦ ?_)
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by simp) (by simp) (A _ hi) (fun x hx ↦ ?_)
    exact h _ (by simpa using hi) _ (Ioo_subset_Ico_self hx)
  _ = ∫ x in a..b, g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun i ↦ i) hab]
    intro i hi
    exact A _ (by simpa using hi)

lemma sum_mul_le_integral_of_monotone_antitone
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f a) (gpos : 0 ≤ g (b - 1)) :
    ∑ i ∈ Finset.Ico a b, f i * g i ≤ ∫ x in a..b, f x * g (x - 1) := by
  apply sum_le_integral_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico] at hx hi
    have I0 : (i : ℝ) ≤ b - 1 := by
      simp only [le_sub_iff_add_le]
      norm_cast
      omega
    have I1 : (i : ℝ) ∈ Icc (a - 1 : ℝ) (b - 1) := by
      simp only [mem_Icc, tsub_le_iff_right]
      exact ⟨by norm_cast; omega, I0⟩
    have I2 : x ∈ Icc (a : ℝ) b := by
      refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
      norm_cast
      omega
    apply mul_le_mul
    · apply hf
      · simp only [mem_Icc, Nat.cast_le]
        exact ⟨hi.1, hi.2.le⟩
      · exact I2
      · exact hx.1
    · apply hg
      · simp only [mem_Icc, tsub_le_iff_right, sub_add_cancel]
        refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
        norm_cast
        omega
      · exact I1
      · simpa [sub_le_iff_le_add] using hx.2.le
    · apply gpos.trans
      apply hg I1 (by simp [hab]) I0
    · apply fpos.trans
      apply hf (by simp [hab]) I2
      exact le_trans (mod_cast hi.1) hx.1
  · rw [IntegrableOn, ← memℒp_one_iff_integrable]
    apply Memℒp.mono_measure (μ := volume.restrict (Icc (a : ℝ) b))
    · apply Measure.restrict_mono_set
      exact Ico_subset_Icc_self
    apply Memℒp.memℒp_of_exponent_le_of_measure_support_ne_top (s := univ)
      _ (by simp) (by simp) le_top
    apply Memℒp.mul_of_top_left
    · apply AntitoneOn.memℒp_isCompact isCompact_Icc
      intro x hx y hy hxy
      apply hg
      · simpa using hx
      · simpa using hy
      · simpa using hxy
    · exact hf.memℒp_isCompact isCompact_Icc
