import Carleson.MetricCarleson
import Carleson.TwoSidedCarleson.NontangentialOperator

open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

/-- The constant used in `two_sided_metric_carleson`.
Has value `2 ^ (452 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- todo: put C_K in NNReal?
def C10_0_1 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := (⟨C_K a, C_K_pos _ |>.le⟩) ^ 2 * C1_0_2 a q

lemma C10_0_1_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C10_0_1 a q :=
  _root_.mul_pos (pow_two_pos_of_ne_zero
    (by simp_rw [ne_eq, ← NNReal.coe_eq_zero, NNReal.coe_mk, C_K_pos _ |>.ne', not_false_eq_true])) (C1_0_2_pos hq)

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Theorem 10.0.1 -/

/- Theorem 10.0.1 -/
theorem two_sided_metric_carleson (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    C10_0_1 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  sorry



end
