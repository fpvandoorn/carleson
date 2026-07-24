/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.NoAtoms
public import Carleson.ToMathlib.MeasureTheory.Integral.Layercake
public import Carleson.ToMathlib.NoAtomsProd
public import Carleson.ToMathlib.NoAtomsBasics
public import Mathlib.MeasureTheory.Constructions.UnitInterval

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace ENNReal

--variable {α : Type*} {m0 : MeasurableSpace α}

namespace NoAtoms'

#check IsPreconnected.intermediate_value₂_eventually₂

#check IsPreconnected.intermediate_value_Iic

#check Monotone.continuousAt_iff_leftLim_eq_rightLim

#check IntegrableOn.continuousOn_Iic_primitive_Iic

#check Metric.iUnion_inter_closedBall_nat

lemma of_metric {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] {μ : Measure α} :
    NoAtoms' (@volume ℝ _) := by
  rw [no_atoms_iff]
  intro s meas_s hs
  /-
  wlog s_ne_top : volume s ≠ ⊤
  · sorry
  -/
  set f := fun r ↦ volume ((Metric.ball 0 r) ∩ s)
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
      simp only [iUnion_coe_set, mem_Iio, mem_iUnion, Metric.mem_ball, dist_zero_right,
        Real.norm_eq_abs, exists_prop]
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
      have : ⋂ (i : Ioi x), Metric.ball (0 : ℝ) i = Metric.closedBall 0 x := by
        ext y
        simp only [iInter_coe_set, mem_Ioi, mem_iInter, Metric.mem_ball, dist_zero_right,
          Real.norm_eq_abs, Metric.mem_closedBall]
        exact forall_gt_iff_le
      rw [this]
      sorry --TODO: add assumption for this
    · intro a b hab
      apply inter_subset_inter_left
      exact Metric.ball_subset_ball (by simpa)
    · measurability
    · sorry --TODO: assumption for this
  have iSup_f : ⨆ r, f r = volume s := by
    rw [← Monotone.measure_iUnion]
    · rw [← iUnion_inter]
      congr
      rw [iUnion_eq_univ_iff.mpr, univ_inter]
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      intro x
      exact exists_gt |x|
    · intro a b hab
      apply inter_subset_inter_left
      exact Metric.ball_subset_ball hab
  have : Ico (f 0) (volume s) ⊆ f '' (Ici 0) := by
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
  use Metric.ball 0 r ∩ s, inter_subset_right, measurableSet_ball.inter meas_s

instance : NoAtoms' (@volume ℝ _) := by
  sorry

end NoAtoms'

end MeasureTheory
