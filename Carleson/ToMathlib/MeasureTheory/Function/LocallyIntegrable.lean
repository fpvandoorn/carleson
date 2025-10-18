import Mathlib.MeasureTheory.Function.LocallyIntegrable


theorem MeasureTheory.LocallyIntegrable.norm {X : Type*} {E : Type*} [MeasurableSpace X]
  [TopologicalSpace X] [NormedAddCommGroup E] {f : X → E} {μ : Measure X}
  (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x ↦ ‖f x‖) μ := fun x ↦ (hf x).norm
