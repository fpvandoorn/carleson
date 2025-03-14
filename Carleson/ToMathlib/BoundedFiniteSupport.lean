import Carleson.ToMathlib.BoundedCompactSupport

/-
This file defines BoundedFiniteSupport.
TODO It should be suitably generalized in analogy to `BoundedCompactSupport`.
-/

open MeasureTheory Function ENNReal

noncomputable section

variable {X : Type*} [MeasureSpace X]
variable {f : X → ℂ}

/-- Definition to avoid repeating ourselves.
Blueprint states: *bounded measurable function $g$ on $X$ supported on a set of finite measure*.
Slightly weaker than `BoundedCompactSupport`.
TODO probably want this as a `structure` instead of an explicit conjunction. -/
def BoundedFiniteSupport (f : X → ℂ) : Prop :=
  MemLp f ∞ volume ∧ volume (support f) < ∞

/-
TODO prove suitable lemmas e.g. BFS f implies Measurable f
-/
