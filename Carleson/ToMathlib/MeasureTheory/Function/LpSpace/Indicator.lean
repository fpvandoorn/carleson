import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology symmDiff

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E]
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

namespace MeasureTheory

-- not actually used in the project, but we want to upstream this and similar lemmas.

/-- A bounded measurable function with compact support is in L^p. -/
theorem _root_.HasCompactSupport.memLp_of_enorm_bound {f : X → E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) (hC : C ≠ ⊤) :
      MemLp f p μ := by
  have : MemLp f ∞ μ :=
    ⟨h2f, eLpNormEssSup_le_of_ae_enorm_bound hfC |>.trans_lt hC.lt_top⟩
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) hf.measure_ne_top le_top
