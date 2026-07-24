/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.NoAtomsBasics
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace ENNReal

namespace NoAtoms'

--TODO: should we use `Nonempty α` or rather `Inhabited α` ?
lemma of_metric {α : Type*} [ne : Nonempty α] [PseudoMetricSpace α] [ProperSpace α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
  (hμ : ∀ r, μ (Metric.closedBall ne.some r) = μ (Metric.ball ne.some r)) :
    NoAtoms' μ := by
  rw [no_atoms_iff]
  intro s meas_s hs
  let c := ne.some
  set f := fun r ↦ μ ((Metric.ball c r) ∩ s)
  have hf : Monotone f := by
    intro a b hab
    apply measure_mono
    apply inter_subset_inter_left
    apply Metric.ball_subset_ball hab
  have cont_left : ∀ x ∈ Ici 0, ⨆ b ∈ Iio x, f b = f x := by
    intro x hx
    rw [← iSup_subtype'', ← Monotone.measure_iUnion]
    · rw [← iUnion_inter]
      congr with y
      simp only [iUnion_coe_set, mem_Iio, mem_iUnion, Metric.mem_ball, exists_prop]
      constructor
      · grind
      · intro h
        exact exists_between' h
    · intro a b hab
      simp only [subset_inter_iff, inter_subset_right, and_true]
      apply inter_subset_left.trans
      apply Metric.ball_subset_ball
      simpa
  have cont_right : ∀ x ∈ Ici 0, ⨅ b ∈ Ioi x, f b = f x := by
    intro x hx
    rw [← iInf_subtype'', ← Monotone.measure_iInter]
    · rw [← iInter_inter]
      apply measure_congr
      apply ae_eq_set_inter _ (by rfl)
      have : ⋂ (i : Ioi x), Metric.ball c i = Metric.closedBall c x := by
        ext y
        simp only [iInter_coe_set, mem_Ioi, mem_iInter, Metric.mem_ball, Metric.mem_closedBall]
        exact forall_gt_iff_le
      rw [this]
      symm
      exact ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall (by rw [hμ])
        measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
    · intro a b hab
      exact inter_subset_inter_left _ (Metric.ball_subset_ball (by simpa))
    · measurability
    · rcases exists_gt x with ⟨r, hr⟩
      use ⟨r, hr⟩, measure_inter_ne_top_of_left_ne_top measure_ball_ne_top
  have iSup_f : ⨆ r, f r = μ s := by
    rw [← Monotone.measure_iUnion]
    · rw [← iUnion_inter]
      congr
      rw [iUnion_eq_univ_iff.mpr, univ_inter]
      simp only [Metric.mem_ball]
      intro x
      exact exists_gt _
    · intro a b hab
      exact inter_subset_inter_left _ (Metric.ball_subset_ball hab)
  have : Ico (f 0) (μ s) ⊆ f '' (Ici 0) := by
    have ha : (0 : ℝ) ∈ Ici 0 := by simp
    have hl : atTop (α := ℝ) ≤ 𝓟 (Ici 0) := le_principal_iff.mpr (Ici_mem_atTop 0)
    apply IsPreconnected.intermediate_value_Ico isPreconnected_Ici ha hl
    · rw [ContinuousOn]
      intro x hx
      rw [continuousWithinAt_iff_continuous_left_right, Ici_inter_Ici, max_eq_right hx,
        Ici_inter_Iic]
      constructor
      · apply ContinuousWithinAt.mono _ Icc_subset_Iic_self
        rw [← continuousWithinAt_Iio_iff_Iic, hf.continuousWithinAt_Iio_iff_leftLim_eq,
          hf.leftLim_eq_sSup, sSup_eq_iSup, iSup_image]
        apply cont_left _ hx
      · rw [← continuousWithinAt_Ioi_iff_Ici, hf.continuousWithinAt_Ioi_iff_rightLim_eq,
          hf.rightLim_eq_sInf, sInf_eq_iInf, iInf_image]
        apply cont_right _ hx
    rw [← iSup_f]
    exact tendsto_atTop_iSup hf
  unfold f at this
  simp only [Metric.ball_zero, empty_inter, measure_empty] at this
  rcases exists_between hs with ⟨μt, hμt, hμts⟩
  have : ∃ r ≥ 0, f r = μt := by
    apply this
    aesop
  rcases this with ⟨r, _, hr⟩
  rw [← hr] at hμt hμts
  use Metric.ball c r ∩ s, inter_subset_right, measurableSet_ball.inter meas_s

instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] [Nontrivial E] : NoAtoms' μ := by
  apply of_metric
  apply addHaar_closedBall_eq_addHaar_ball

--TODO: Prove more general result, possibly using this :
--https://math.stackexchange.com/questions/3881683/does-mu-x-0-imply-non-atomic-for-radon-measure
--#check MeasureTheory.Measure.IsAddHaarMeasure.noAtoms
--#check MeasureTheory.Measure.prod.instNoAtoms_snd

instance : NoAtoms' (volume : Measure unitInterval) := subtype measurableSet_Icc

end NoAtoms'

end MeasureTheory
