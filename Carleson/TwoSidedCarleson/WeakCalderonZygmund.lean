import Carleson.Defs
import Carleson.ToMathlib.HardyLittlewood

open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Section 10.2 and Lemma 10.0.3 -/

/-- The constant used in `nontangential_from_simple`. -/
irreducible_def C10_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a)

/-- Lemma 10.2.1. -/
theorem maximal_theorem (ha : 4 ≤ a)
    {f : X → ℂ} (hmf : Measurable f) (hf : IsBounded (range f)) (h2f : volume (support f) < ∞)
    {α : ℝ≥0} (hα : 0 < α):
    α * distribution (globalMaximalFunction volume 1 f) α volume ≤ C10_2_1 a * eLpNorm f 1 := by
  sorry

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3 -/
theorem czoperator_weak_1_1 (ha : 4 ≤ a)
    (hT : ∃ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : IsBounded (range f)) (h2f : volume (support f) < ∞)
    {α : ℝ≥0} (hα : 0 < α) :
    distribution (CZOperator K r f) α volume ≤ C10_0_3 a / α * ∫⁻ y, ‖f y‖ₑ := by
  sorry


end
