module

public import Carleson.BasicDefinitions
public import Carleson.ToMathlib.Annulus
public import Carleson.ToMathlib.MeasureTheory.Measure.IsDoubling
public import Carleson.ToMathlib.WeakType
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.AddCircle

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

-- /-- The main constant in the blueprint, driving all the construction, is `D = 2 ^ (100 * a ^ 2)`.
-- It turns out that the proof is robust, and works for other values of `100`, giving better constants
-- in the end. We will formalize it using a parameter `𝕔` (that we fix equal to `100` to follow
-- the blueprint) and having `D = 2 ^ (𝕔 * a ^ 2)`. We register two lemmas `seven_le_c` and
-- `c_le_100` and will never unfold `𝕔` from this point on. -/
-- irreducible_def 𝕔 : ℕ := 100

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

-- /-- The constant used in `MetricSpaceCarleson` and `LinearizedMetricCarleson`.
-- Has value `2 ^ (443 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- def C1_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ ((3 * 𝕔 + 18 + 5 * (𝕔 / 4)) * a ^ 3) / (q - 1) ^ 6

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
