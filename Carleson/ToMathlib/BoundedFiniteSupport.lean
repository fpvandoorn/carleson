import Carleson.ToMathlib.BoundedCompactSupport

/-
This file defines BoundedFiniteSupport.
TODO It should be suitably generalized in analogy to `BoundedCompactSupport`.
-/

open MeasureTheory Function ENNReal TopologicalSpace

noncomputable section

variable {X E : Type*} [MeasurableSpace X]
variable {f : X → E} [TopologicalSpace E] [ENorm E] [Zero E] {μ : Measure X}

/-- Definition to avoid repeating ourselves.
Blueprint states: *bounded measurable function $g$ on $X$ supported on a set of finite measure*. -/
@[fun_prop]
structure BoundedFiniteSupport (f : X → E) (μ : Measure X := by volume_tac) : Prop where
  memLp : MemLp f ∞ μ
  measure_support_lt : μ (support f) < ∞

/-
TODO prove suitable lemmas e.g. BFS f implies AEMeasurable f
-/
namespace BoundedFiniteSupport

variable (bfs : BoundedFiniteSupport f μ)
section Includebfs
include bfs

@[fun_prop]
theorem aestronglyMeasurable : AEStronglyMeasurable f μ :=
  bfs.memLp.aestronglyMeasurable

@[fun_prop]
theorem aemeasurable [MeasurableSpace E] [PseudoMetrizableSpace E]
    [BorelSpace E] : AEMeasurable f μ :=
  bfs.aestronglyMeasurable.aemeasurable

@[fun_prop]
theorem aestronglyMeasurable_restrict {s : Set X} :
    AEStronglyMeasurable f (μ.restrict s) :=
  bfs.aestronglyMeasurable.restrict

@[fun_prop]
theorem aemeasurable_restrict [MeasurableSpace E] [PseudoMetrizableSpace E]
    [BorelSpace E] {s : Set X} :
    AEMeasurable f (μ.restrict s) :=
  bfs.aemeasurable.restrict

theorem eLpNorm_lt_top :
    eLpNorm f ∞ μ < ∞ :=
  bfs.memLp.eLpNorm_lt_top

end Includebfs
