import Mathlib.MeasureTheory.Integral.IntegrableOn

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

-- Upstreaming note: Hypotheses and variables have been matched to corresponding Mathlib file

variable {α β ε ε' E F : Type*} [MeasurableSpace α]

section NormedAddCommGroup

variable [NormedAddCommGroup E] {f g : α → ε'} {s t : Set α} {μ ν : Measure α}
variable [TopologicalSpace ε'] [ENormedAddMonoid ε']

theorem integrableOn_of_integrableOn_inter_support [PseudoMetrizableSpace ε'] {f : α → ε'}
  (hs : MeasurableSet s) (hf : IntegrableOn f (s ∩ support f) μ) :
    IntegrableOn f s μ := by
  apply IntegrableOn.of_forall_diff_eq_zero hf hs
  simp

end NormedAddCommGroup
