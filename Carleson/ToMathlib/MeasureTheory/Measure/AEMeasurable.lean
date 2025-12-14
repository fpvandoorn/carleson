import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral


namespace MeasureTheory

--TODO: generalize this?
lemma aeMeasurable_withDensity_inv {f : NNReal → ENNReal} (hf : AEMeasurable f) :
    AEMeasurable f (volume.withDensity (fun t ↦ t⁻¹)) := by
  have : AEMeasurable f (volume.withDensity (fun t ↦ ENNReal.ofNNReal t⁻¹)) := by
    rw [aemeasurable_withDensity_ennreal_iff measurable_inv]
    apply AEMeasurable.mul _ hf
    exact measurable_inv.aemeasurable.coe_nnreal_ennreal
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
      exact Eq.symm (ENNReal.coe_inv hx)
  · apply Measurable.aemeasurable
    measurability
  · exact measurable_inv.aemeasurable.coe_nnreal_ennreal

end MeasureTheory
