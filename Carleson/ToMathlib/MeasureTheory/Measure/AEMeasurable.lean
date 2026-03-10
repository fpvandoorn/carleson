import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.Order.Interval.Set.Disjoint
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

-- Upstreaming status: useful and ready to go
namespace MeasureTheory

-- TODO: generalize this to other measures and density functions?
lemma aeMeasurable_withDensity_inv {f : NNReal → ENNReal} (hf : AEMeasurable f) :
    AEMeasurable f (volume.withDensity (fun t ↦ t⁻¹)) := by
  have : AEMeasurable f (volume.withDensity (fun t ↦ ENNReal.ofNNReal t⁻¹)) := by
    rw [aemeasurable_withDensity_ennreal_iff measurable_inv]
    fun_prop
  convert this using 1
  rw [withDensity_eq_iff_of_sigmaFinite]
  · rw [Filter.eventuallyEq_iff_exists_mem]
    use {x | x ≠ 0}
    constructor
    · rw [mem_ae_iff]
      simp only [ne_eq, Set.compl_ne_eq_singleton]
      apply measure_singleton
    · intro x hx
      simp only [ne_eq, Set.mem_setOf_eq] at *
      exact (ENNReal.coe_inv hx).symm
  · fun_prop
  · fun_prop

-- analogous to `aemeasurable_Ioi_of_forall_Ioc` in mathlib
open MeasureTheory MeasureTheory.Measure Filter Set Function ENNReal in
theorem aemeasurable_Ici_of_forall_Icc {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {β : Type*}
  {mβ : MeasurableSpace β} [LinearOrder α] [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α → β}
  (g_meas : ∀ t ≥ x, AEMeasurable g (μ.restrict (Set.Icc x t))) : AEMeasurable g (μ.restrict (Set.Ici x)) := by
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (atTop : Filter α)
  have Ici_eq_iUnion : Ici x = ⋃ n : ℕ, Icc x (u n) := by
    rw [iUnion_Icc_eq_Ici_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_atTop y)).exists
  rw [Ici_eq_iUnion, aemeasurable_iUnion_iff]
  intro n
  rcases le_or_gt x (u n) with h | h
  · exact g_meas (u n) h
  · rw [Icc_eq_empty (not_le.mpr h), Measure.restrict_empty]
    exact aemeasurable_zero_measure

open MeasureTheory MeasureTheory.Measure Filter Set Function ENNReal in
theorem aemeasurable_Ici_of_forall_Icc' {α : Type*} {m0 : MeasurableSpace α} [MeasurableSingletonClass α]
  {μ : Measure α} {β : Type*}
  {mβ : MeasurableSpace β} [LinearOrder α] [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α → β}
  (g_meas : ∀ t > x, AEMeasurable g (μ.restrict (Set.Icc x t))) : AEMeasurable g (μ.restrict (Set.Ici x)) := by
  apply aemeasurable_Ici_of_forall_Icc
  intro t ht
  rcases ht.lt_or_eq with h | h
  · exact g_meas t h
  rw [h, Icc_self, Measure.restrict_singleton]
  apply aemeasurable_dirac.smul_measure

@[fun_prop, measurability]
lemma AEMeasurable.withDensity {α β : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  {mβ : MeasurableSpace β} {f : α → β} {d : α → ENNReal} (hf : AEMeasurable f μ) :
    AEMeasurable f (μ.withDensity d) := hf.mono' (withDensity_absolutelyContinuous μ d)

@[fun_prop, measurability]
lemma AEStronglyMeasurable.withDensity {α β : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace β] {f : α → β} {d : α → ENNReal} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable f (μ.withDensity d) := hf.mono_ac (withDensity_absolutelyContinuous μ d)

end MeasureTheory
