module

public import Carleson.BasicDefinitions

/-! # Challenge file for using comparator -/

public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Challenge

-- Carleson's theorem asserting a.e. convergence of the partial Fourier sums for continous functions
open Real in
theorem classical_carleson' {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
  ∀ᵐ x, Filter.Tendsto (partialFourierSum · f x) Filter.atTop (nhds (f x)) := sorry

theorem metric_carleson'
    {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [KernelProofData a K] {f : X → ℂ} [IsCancellative X (defaultτ a)] (hq : q ∈ Ioc 1 2)
    (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (2 ^ a ^ 3)) :
    ∫⁻ x in G, carlesonOperator K f x ≤ C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ :=
  sorry

theorem linearized_metric_carleson'
    {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [KernelProofData a K] {Q : SimpleFunc X (Θ X)} {f : X → ℂ} [IsCancellative X (defaultτ a)]
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (2 ^ a ^ 3)) :
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
      C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ :=
  sorry

end Challenge
