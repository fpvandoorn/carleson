module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving

--Upstreaming status: ready

public section

namespace MeasureTheory

namespace MeasurePreserving

open Set

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μα : Measure α} {μβ : Measure β}

lemma ae_comp
   {f : α → β} {hf : MeasurePreserving f μα μβ} {P : β → Prop}
  (h : ∀ᵐ x ∂μβ, P x) :
    ∀ᵐ x ∂μα, P (f x) := by
  rw [ae_iff] at *
  rw [← preimage_setOf_eq, ← h]
  exact hf.measure_preimage (NullMeasurableSet.of_null h)

end MeasurePreserving

end MeasureTheory
