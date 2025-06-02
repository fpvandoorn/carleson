import Carleson.MetricCarleson.Main
import Carleson.TwoSidedCarleson.NontangentialOperator

open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

/-- The constant used in `two_sided_metric_carleson`.
Has value `2 ^ (452 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- todo: put C_K in NNReal?
def C10_0_1 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := (C_K a) ^ 2 * C1_0_2 a q

lemma C10_0_1_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C10_0_1 a q :=
  mul_pos (pow_two_pos_of_ne_zero <| by simp_rw [ne_eq, C_K_pos.ne', not_false_eq_true])
    (C1_0_2_pos hq)

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Theorem 10.0.1 -/

/- Theorem 10.0.1 -/
theorem two_sided_metric_carleson (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    C10_0_1 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  -- note: you might need to case on whether `volume F` is `∞` or not.
  sorry

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_restricted_weak_type (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
  (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
      HasRestrictedWeakType (carlesonOperator K) q q' volume volume (C10_0_1 a q) := sorry

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_strong_type (ha : 4 ≤ a) (hq : q ∈ Ioo 1 2) (hqq' : q.HolderConjugate q')
  (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
      HasStrongType (carlesonOperator K) q q' volume volume (C10_0_1 a q) := by
  /- TODO: Fix next line. -/
  --have := (two_sided_metric_carleson_restricted_weak_type ha (mem_Ioc_of_Ioo hq) hqq' hT hmf hf).HasLorentzType
  /- Apply `exists_hasLorentzType_real_interpolation` and `MemLorentz_nested` here,
  or just directly write another version of real interpolation that directly gives strong type.
  -/
  sorry

end
