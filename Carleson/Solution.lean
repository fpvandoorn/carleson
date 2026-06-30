module

public import Carleson
public import Carleson.ChallengeDefs

/-! # Solution file for using comparator -/

public noncomputable section

open MeasureTheory Set Challenge
open scoped NNReal

namespace Solution

-- Carleson's theorem asserting a.e. convergence of the partial Fourier sums for continous functions
open Real in
theorem ClassicalCarleson {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
    ∀ᵐ x, Filter.Tendsto (Challenge.partialFourierSum · f x) Filter.atTop (nhds (f x)) :=
  classical_carleson cont_f periodic_f

/-- The constant used in `MetricSpaceCarleson` and `LinearizedMetricCarleson` -/
def C (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (443 * a ^ 3) / (q - 1) ^ 6

theorem metric_carleson
    {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [Challenge.KernelProofData a K] {f : X → ℂ} [Challenge.IsCancellative X (Challenge.defaultτ a)] (hq : q ∈ Ioc 1 2)
    (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : Challenge.HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (2 ^ a ^ 3)) :
    ∫⁻ x in G, carlesonOperator K f x ≤ C a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  sorry -- have aux := _root_.metric_carleson hq hqq' mF mG mf nf hT (a := a)

theorem linearized_metric_carleson
    {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [Challenge.KernelProofData a K] {Q : SimpleFunc X (Θ X)} {f : X → ℂ}
    [Challenge.IsCancellative X (Challenge.defaultτ a)]
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : ∀ θ : Θ X, Challenge.HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (2 ^ a ^ 3)) :
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
      C a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ :=
  sorry

end Solution
