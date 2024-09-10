import Carleson.MetricCarleson

open MeasureTheory Set

noncomputable section

/-- The constant used in `two_sided_metric_carleson`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C10_0_1 (a : ℕ) (q : ℝ) : ℝ := (C_K a) ^ 2 * C1_0_2 a q

lemma C10_0_1_pos {a : ℕ} {q : ℝ} (hq : 1 < q) : 0 < C10_0_1 a q := mul_pos (pow_two_pos_of_ne_zero (C_K_pos a).ne.symm) (C1_0_2_pos hq)

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ q q' : ℝ} {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}

/- Theorem 10.0.1 -/
theorem two_sided_metric_carleson [CompatibleFunctions ℝ X (defaultA a)]
  [IsCancellative X (defaultτ a)] [IsTwoSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    ENNReal.ofReal (C10_0_1 a q) * (volume G) ^ q'⁻¹ * (volume F) ^ q⁻¹ := by
  sorry

end
