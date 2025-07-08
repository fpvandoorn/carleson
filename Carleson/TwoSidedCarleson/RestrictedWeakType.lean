import Carleson.ToMathlib.RealInterpolation.LorentzInterpolation
import Carleson.TwoSidedCarleson.MainTheorem

/-! This file contains a reformulation of Theorem 10.0.1.
It is not officially part of the blueprint. -/


open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Reformulations of Theorem 10.0.1 -/

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_restricted_weak_type (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2)
  (hqq' : q.HolderConjugate q')
  (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
      HasRestrictedWeakType (carlesonOperator K) q q' volume volume (C10_0_1 a q) := sorry

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_strong_type (ha : 4 ≤ a) (hq : q ∈ Ioo 1 2)
    (hqq' : q.HolderConjugate q')
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
