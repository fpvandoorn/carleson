import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.ENorm

/-
This file defines BoundedFiniteSupport.
-/

open MeasureTheory Function ENNReal TopologicalSpace

noncomputable section

variable {X E : Type*} [MeasurableSpace X] {f : X → E} {μ : Measure X}

variable [TopologicalSpace E] [ENorm E] [Zero E] in
/-- Definition to avoid repeating ourselves.
Blueprint states: *bounded measurable function $g$ on $X$ supported on a set of finite measure*. -/
@[fun_prop]
structure BoundedFiniteSupport (f : X → E) (μ : Measure X := by volume_tac) : Prop where
  memLp_top : MemLp f ∞ μ
  measure_support_lt : μ (support f) < ∞

namespace BoundedFiniteSupport

section Includebfs
variable [TopologicalSpace E] [ENorm E] [Zero E] (bfs : BoundedFiniteSupport f μ)
include bfs

@[fun_prop]
theorem aestronglyMeasurable : AEStronglyMeasurable f μ :=
  bfs.memLp_top.aestronglyMeasurable

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
  bfs.memLp_top.eLpNorm_lt_top

end Includebfs

section  ENormedAddMonoid
variable [TopologicalSpace E] [ENormedAddMonoid E]

/-- Bounded finitely supported functions are in all `Lᵖ` spaces. -/
theorem memLp (hf : BoundedFiniteSupport f μ) (p : ℝ≥0∞) :
    MemLp f p μ :=
  hf.memLp_top.mono_exponent_of_measure_support_ne_top
    (fun _ ↦ notMem_support.mp) hf.measure_support_lt.ne le_top

end ENormedAddMonoid

section NormedAddCommGroup

variable [NormedAddCommGroup E]

/-- Bounded finitely supported functions are integrable. -/
theorem integrable (hf : BoundedFiniteSupport f μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp <| hf.memLp 1

theorem indicator (bfs : BoundedFiniteSupport f μ) {s : Set X} (hs : MeasurableSet s) :
    BoundedFiniteSupport (s.indicator f) μ := by
  constructor
  · exact MemLp.indicator hs bfs.memLp_top
  · rw[Set.support_indicator]
    apply measure_inter_lt_top_of_right_ne_top
    rw [← lt_top_iff_ne_top]
    exact bfs.measure_support_lt

end NormedAddCommGroup

end BoundedFiniteSupport
