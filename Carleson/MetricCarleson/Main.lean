import Carleson.MetricCarleson.Linearized

open MeasureTheory Set
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ : ℝ} {q q' : ℝ≥0} {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}

/- Theorem 1.0.2 -/
theorem metric_carleson [CompatibleFunctions ℝ X (defaultA a)]
  [IsCancellative X (defaultτ a)] [IsOneSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    C1_0_2 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  sorry

end
