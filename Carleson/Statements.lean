module

public import Carleson.Defs

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
