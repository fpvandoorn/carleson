import Carleson.ToMathlib.BoundedCompactSupport

/-
This file defines BoundedFiniteSupport.
TODO It should be suitably generalized in analogy to `BoundedCompactSupport`.
-/

open MeasureTheory Function ENNReal

noncomputable section

variable {X E : Type*} [MeasurableSpace X]
variable {f : X → E} [TopologicalSpace E] [ContinuousENorm E] [Zero E] {μ : Measure X}

/-- Definition to avoid repeating ourselves.
Blueprint states: *bounded measurable function $g$ on $X$ supported on a set of finite measure*.
Slightly weaker than `BoundedCompactSupport`.
TODO probably want this as a `structure` instead of an explicit conjunction. -/
@[fun_prop]
structure BoundedFiniteSupport (f : X → E) (μ : Measure X := by volume_tac) : Prop where
  memLp : MemLp f ∞ μ
  measure_support_lt : μ (support f) < ∞
  aestronglyMeasurable : AEStronglyMeasurable f μ

attribute [fun_prop] BoundedFiniteSupport.aestronglyMeasurable

/-
TODO prove suitable lemmas e.g. BFS f implies Measurable f
-/
namespace BoundedFiniteSupport

@[fun_prop]
theorem aemeasurable [MeasurableSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [BorelSpace E]
    (bfs : BoundedFiniteSupport f μ) : AEMeasurable f μ :=
  bfs.aestronglyMeasurable.aemeasurable

@[fun_prop]
theorem aestronglyMeasurable_restrict {s : Set X} (bfs : BoundedFiniteSupport f μ) :
    AEStronglyMeasurable f (μ.restrict s) :=
  bfs.aestronglyMeasurable.restrict

@[fun_prop]
theorem aemeasurable_restrict [MeasurableSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [BorelSpace E] {s : Set X} (bfs : BoundedFiniteSupport f μ) :
    AEMeasurable f (μ.restrict s) :=
  bfs.aemeasurable.restrict

theorem measurable [MeasurableSpace E] (bfs : BoundedFiniteSupport f μ) : Measurable f := by
  sorry -- not true, but we keep it temporarily to not break code
