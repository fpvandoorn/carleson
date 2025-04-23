import Carleson.Defs

open scoped NNReal
open MeasureTheory Set

noncomputable section

/-- The constant used in `linearized_metric_carleson`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C1_0_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ}


/- Theorem 1.0.3 -/
theorem linearized_metric_carleson [CompatibleFunctions ℝ X (defaultA a)]
  [IsCancellative X (defaultτ a)] [IsOneSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (Q : SimpleFunc X (Θ X)) {θ : Θ X}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
    C1_0_3 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  sorry

end
