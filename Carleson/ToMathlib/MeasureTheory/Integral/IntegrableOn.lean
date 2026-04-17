import Mathlib.MeasureTheory.Integral.IntegrableOn

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

-- Upstreaming note: Hypotheses and variables have been matched to corresponding Mathlib file
-- `IntegrableAtFilter.congr` already in mathlib.
-- `integrableOn_of_integrableOn_inter_support` already in mathlib as
-- `MeasureTheory.IntegrableOn.of_inter_support`.

variable {α β ε ε' E F : Type*} [MeasurableSpace α]

namespace MeasureTheory

protected theorem IntegrableAtFilter.congr'_enorm {μ : Measure α} [TopologicalSpace ε]
  [TopologicalSpace ε'] [ContinuousENorm ε] [ContinuousENorm ε']
  {l : Filter α} {f : α → ε} {g : α → ε'}
  (hf : IntegrableAtFilter f l μ) (hg : AEStronglyMeasurable g μ)
  (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    IntegrableAtFilter g l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.congr'_enorm hg.restrict (ae_restrict_le h)⟩

end MeasureTheory

section NormedAddCommGroup

variable [NormedAddCommGroup E] {f g : α → ε'} {s t : Set α} {μ ν : Measure α}
variable [TopologicalSpace ε'] [ENormedAddMonoid ε']

theorem integrableOn_of_integrableOn_inter_support [PseudoMetrizableSpace ε'] {f : α → ε'}
  (hs : MeasurableSet s) (hf : IntegrableOn f (s ∩ support f) μ) :
    IntegrableOn f s μ := by
  apply IntegrableOn.of_forall_diff_eq_zero hf hs
  simp

end NormedAddCommGroup
