import Mathlib.MeasureTheory.Measure.Restrict

open Set MeasureTheory

variable {α ι : Type*}
variable {m0 : MeasurableSpace α}
variable {μ : Measure α}

namespace MeasureTheory

namespace Measure

-- Add after `restrict_iUnion_le`
theorem restrict_biUnion_le {μ : Measure α} {s : ι → Set α} (T : Set ι) [hT : Countable T] :
    μ.restrict (⋃ i ∈ T, s i) ≤ sum fun (i : T) => μ.restrict (s i) :=
  le_iff.2 fun t ht ↦ by simpa [ht, inter_iUnion] using measure_biUnion_le μ hT (t ∩ s ·)

end Measure

end MeasureTheory
