module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Carleson.ToMathlib.MeasureTheory.Integral.IntegrableOn

public section

-- Upstreaming status: easy and useful; good to go

namespace MeasureTheory

namespace LocallyIntegrable

theorem norm {X : Type*} {E : Type*} [MeasurableSpace X]
  [TopologicalSpace X] [NormedAddCommGroup E] {f : X → E} {μ : Measure X}
  (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x ↦ ‖f x‖) μ := fun x ↦ (hf x).norm

variable {X ε ε' : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  {f g : X → ε} {μ : Measure X}

theorem congr'_enorm {f : X → ε} {g : X → ε'} (hf : LocallyIntegrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : LocallyIntegrable g μ :=
  fun x ↦ (hf x).congr'_enorm hg h

/-
theorem locallyIntegrable_congr'_enorm {f : X → ε} {g : X → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    LocallyIntegrable f μ ↔ LocallyIntegrable g μ :=
  ⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf <| Filter.EventuallyEq.symm h⟩
-/
/-
theorem iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
  (h : ∀ (i : ι), LocallyIntegrableOn f (s i) μ) :
    LocallyIntegrableOn f (⋃ i, s i) μ := by
  unfold LocallyIntegrableOn
  simp only [Set.mem_iUnion, forall_exists_index]
  intro x i hx
  #check IntegrableOn
  --#check IntegrableOn.union
  rw [LocallyFinite.nhdsWithin_iUnion]
  --unfold IntegrableAtFilter
  have := h i _ hx
  apply this.filter_mono
  apply iSup_le
-/

end LocallyIntegrable

end MeasureTheory
