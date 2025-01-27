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

/-- Lemma 10.2.1, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and wnorm'`.
-/
theorem maximal_theorem (ha : 4 ≤ a) :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  sorry

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and wnorm'`.
-/
theorem czoperator_weak_1_1 (ha : 4 ≤ a)
    (hT : ∃ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (CZOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
