import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.ToMathlib.MeasureTheory.Integral.IntegrableOn

namespace MeasureTheory

theorem LocallyIntegrable.norm {X : Type*} {E : Type*} [MeasurableSpace X]
  [TopologicalSpace X] [NormedAddCommGroup E] {f : X → E} {μ : Measure X}
  (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x ↦ ‖f x‖) μ := fun x ↦ (hf x).norm


variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ : Measure X} {s : Set X}

theorem LocallyIntegrable.congr'_enorm {f : X → ε} {g : X → ε'} (hf : LocallyIntegrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : LocallyIntegrable g μ :=
  fun x ↦ (hf x).congr'_enorm hg h

theorem locallyIntegrable_congr'_enorm {f : X → ε} {g : X → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    LocallyIntegrable f μ ↔ LocallyIntegrable g μ :=
  ⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf <| Filter.EventuallyEq.symm h⟩

theorem LocallyIntegrable.congr {f g : X → ε} (hf : LocallyIntegrable f μ) (h : f =ᵐ[μ] g) :
  LocallyIntegrable g μ := fun x ↦ (hf x).congr h


theorem locallyIntegrable_congr {f g : X → ε} (h : f =ᵐ[μ] g) : LocallyIntegrable f μ ↔ LocallyIntegrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

end MeasureTheory
