module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

public section

-- Upstreaming status: Hypotheses and variables have been matched to corresponding Mathlib file
-- `IntegrableAtFilter.congr` already in mathlib.

variable {α β ε ε' : Type*} [MeasurableSpace α]

namespace MeasureTheory

protected theorem IntegrableAtFilter.congr'_enorm {μ : Measure α} [TopologicalSpace ε]
  [TopologicalSpace ε'] [ContinuousENorm ε] [ContinuousENorm ε']
  {l : Filter α} {f : α → ε} {g : α → ε'}
  (hf : IntegrableAtFilter f l μ) (hg : AEStronglyMeasurable g μ)
  (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    IntegrableAtFilter g l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.congr'_enorm hg.restrict (ae_restrict_le h)⟩

end MeasureTheory
