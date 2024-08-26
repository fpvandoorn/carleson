import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators
open scoped ENNReal
noncomputable section

/-- The constant used in `linearized_metric_carleson`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C1_0_3 (a : ℕ) (q : ℝ) : ℝ := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ q q' : ℝ} {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}


/- Theorem 1.0.3 -/
theorem linearized_metric_carleson [CompatibleFunctions ℝ X (defaultA a)]
  [IsCancellative X (defaultτ a)] [IsOneSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (Q : SimpleFunc X (Θ X)) {θ : Θ X}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : HasBoundedStrongType (LinearizedNontangentialOperator Q θ K · · |>.toReal)
      2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, LinearizedCarlesonOperator Q K f x ≤
    ENNReal.ofReal (C1_0_3 a q) * (volume G) ^ q'⁻¹ * (volume F) ^ q⁻¹ := by
  sorry

end
