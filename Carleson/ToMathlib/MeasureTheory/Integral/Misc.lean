import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.MeasureTheory.Function.SimpleFunc
import Carleson.ToMathlib.MeasureTheory.Measure.NNReal

open NNReal ENNReal MeasureTheory

-- This is Theorem 4.19 in https://doi.org/10.1007/978-3-319-30034-4
theorem lintegral_antitone_mul_le {f g k : ℝ≥0 → ℝ≥0∞} (hf : AEMeasurable f) (hg : AEMeasurable g)
  (h : ∀ {t}, ∫⁻ s in Set.Iio t, f s ≤ ∫⁻ s in Set.Iio t, g s) (hk : Antitone k) :
    ∫⁻ s, k s * f s ≤ ∫⁻ s, k s * g s := by
  revert k
  apply Antitone.ennreal_induction'
  · apply SimpleFunc.antitone_induction
    · intro c b
      simp_rw [SimpleFunc.restrict_apply _ measurableSet_Iio, ← Set.indicator_mul_left]
      simp only [SimpleFunc.coe_const, Function.const_apply, measurableSet_Iio, lintegral_indicator]
      rw [lintegral_const_mul'' _ hf.restrict, lintegral_const_mul'' _ hg.restrict]
      gcongr 1
      exact h
    · intro c b
      simp_rw [SimpleFunc.restrict_apply _ measurableSet_Iic, ← Set.indicator_mul_left]
      simp only [SimpleFunc.coe_const, Function.const_apply, measurableSet_Iic, lintegral_indicator]
      rw [lintegral_const_mul'' _ hf.restrict, lintegral_const_mul'' _ hg.restrict]
      gcongr 1
      convert (@h b) using 2
      · exact Measure.restrict_congr_set Iio_ae_eq_Iic.symm
      · exact Measure.restrict_congr_set Iio_ae_eq_Iic.symm
    · intro c
      simp only [SimpleFunc.coe_const, Function.const_apply]
      rw [lintegral_const_mul'' _ hf, lintegral_const_mul'' _ hg]
      gcongr 1
      have hf' : f = ⨆ (i : ℕ), (Set.Iic (i : ℝ≥0)).indicator f := by
        rw [Set.iSup_indicator bot_eq_zero monotone_const, iSup_const]
        · convert (Set.indicator_univ f).symm
          apply iUnion_Iic_of_not_bddAbove_range
          rw [not_bddAbove_iff]
          intro x
          use (Nat.ceil (x.toReal + 1))
          simp only [Set.mem_range, Nat.cast_inj, exists_eq, true_and]
          apply (Nat.le_ceil (x + 1)).trans_lt'
          simp
        intro n m hnm
        simpa
      have hg' : g = ⨆ (i : ℕ), (Set.Iic (i : ℝ≥0)).indicator g := by
        rw [Set.iSup_indicator bot_eq_zero monotone_const, iSup_const]
        · convert (Set.indicator_univ g).symm
          apply iUnion_Iic_of_not_bddAbove_range
          rw [not_bddAbove_iff]
          intro x
          use (Nat.ceil (x.toReal + 1))
          simp only [Set.mem_range, Nat.cast_inj, exists_eq, true_and]
          apply (Nat.le_ceil (x + 1)).trans_lt'
          simp
        intro n m hnm
        simpa
      rw [hf', hg']
      simp only [iSup_apply, ge_iff_le]
      rw [lintegral_iSup', lintegral_iSup']
      · gcongr 1 with n
        simp only [measurableSet_Iic, lintegral_indicator]
        convert (@h n) using 2
        · exact Measure.restrict_congr_set Iio_ae_eq_Iic.symm
        · exact Measure.restrict_congr_set Iio_ae_eq_Iic.symm
      · intro n
        apply AEMeasurable.indicator hg measurableSet_Iic
      · filter_upwards []
        intro x n m hmn
        simp only
        gcongr
      · intro n
        apply AEMeasurable.indicator hf measurableSet_Iic
      · filter_upwards []
        intro x n m hmn
        simp only
        gcongr
    · intro k c t measurable_t hks hk ht
      simp only [SimpleFunc.coe_add, Pi.add_apply]
      simp_rw [add_mul]
      rw [lintegral_add_left' ((SimpleFunc.aemeasurable _).mul hf),
          lintegral_add_left' ((SimpleFunc.aemeasurable _).mul hg)]
      gcongr
  · intro fs monotone_fs hfs
    simp only
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup', lintegral_iSup']
    · gcongr 1 with n
      exact hfs n
    · fun_prop
    · filter_upwards []
      intro x
      apply Monotone.mul_const _ (by simp)
      intro n m hmn
      apply monotone_fs hmn
    · fun_prop
    · filter_upwards []
      intro x
      apply Monotone.mul_const _ (by simp)
      intro n m hmn
      apply monotone_fs hmn
