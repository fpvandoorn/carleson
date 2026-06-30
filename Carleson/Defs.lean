module

public import Carleson.BasicDefinitions

@[expose] public section

open MeasureTheory Set Function ENNReal
open scoped NNReal

noncomputable section

/-! # Main statements of the Carleson project

This file contains the statements of the main theorems from the Carleson formalization project:
Theorem 1.0.1 (classical Carleson), Theorem 1.1.1 (metric space Carleson) and Theorem 1.1.2
(linearised metric Carleson). More precisely,

- `ClassicalCarleson`: statement of Carleson's theorem asserting a.e. convergence of the partial
Fourier sums for continous functions (Theorem 1.0.1 in the blueprint).
- `MetricSpaceCarleson`: statement of Theorem 1.1.1 from the blueprint.
- `LinearizedMetricCarleson`: statement of Theorem 1.1.2 from the blueprint.

-/

attribute [instance] KernelProofData.hcz

set_option linter.unusedVariables false

/-- A constant used on the boundedness of `T_Q^θ` and `T_*`. We generally assume
`HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·) 2 2 volume volume (C_Ts a)`
throughout this formalization. -/
def C_Ts (a : ℕ) : ℝ≥0 := 2 ^ a ^ 3

open Real in
/-- Theorem 1.0.1: Carleson's theorem asserting a.e. convergence of the partial Fourier sums for
continous functions.
For the proof, see `classical_carleson` in the file `Carleson.Classical.ClassicalCarleson`. -/
def ClassicalCarleson : Prop :=
  ∀ {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)),
    ∀ᵐ x, Filter.Tendsto (partialFourierSum · f x) Filter.atTop (nhds (f x))

/-- Theorem 1.1.1.
For the proof, see `metric_carleson` in the file `Carleson.MetricCarleson.Main`. -/
def MetricSpaceCarleson : Prop :=
  ∀ {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [KernelProofData a K] {f : X → ℂ} [IsCancellative X (defaultτ a)] (hq : q ∈ Ioc 1 2)
    (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)),
    ∫⁻ x in G, carlesonOperator K f x ≤ C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹

/-- Theorem 1.1.2.
For the proof, see `linearized_metric_carleson` in the file `Carleson.MetricCarleson.Linearized`. -/
def LinearizedMetricCarleson : Prop :=
  ∀ {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [KernelProofData a K] {Q : SimpleFunc X (Θ X)} {f : X → ℂ} [IsCancellative X (defaultτ a)]
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)),
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
      C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹
