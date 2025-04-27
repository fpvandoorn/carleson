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
TODO prove suitable lemmas e.g. BFS f implies Measurable f
-/
namespace BoundedFiniteSupport

@[fun_prop]
lemma aestronglyMeasurable {f : X → E} {μ : Measure X} (hf : BoundedFiniteSupport f μ) :
    AEStronglyMeasurable f μ :=
  hf.memLp.1

@[fun_prop]
theorem aemeasurable [MeasurableSpace E] [PseudoMetrizableSpace E]
    [BorelSpace E]
    (bfs : BoundedFiniteSupport f μ) : AEMeasurable f μ :=
  bfs.aestronglyMeasurable.aemeasurable

@[fun_prop]
theorem aestronglyMeasurable_restrict {s : Set X} (bfs : BoundedFiniteSupport f μ) :
    AEStronglyMeasurable f (μ.restrict s) :=
  bfs.aestronglyMeasurable.restrict

@[fun_prop]
theorem aemeasurable_restrict [MeasurableSpace E] [PseudoMetrizableSpace E]
    [BorelSpace E] {s : Set X} (bfs : BoundedFiniteSupport f μ) :
    AEMeasurable f (μ.restrict s) :=
  bfs.aemeasurable.restrict

theorem measurable [MeasurableSpace E] (bfs : BoundedFiniteSupport f μ) : Measurable f := by
  sorry -- not true, but we keep it temporarily to not break code


theorem indicator {F : Type*} [TopologicalSpace F] [hF : ENormedAddMonoid F] {g : X → F}
  (bgs : BoundedFiniteSupport g μ) {s : Set X} (hs : MeasurableSet s) :
    BoundedFiniteSupport (s.indicator g) μ := by
  constructor
  . exact MemLp.indicator hs bgs.memLp
  . rw[Set.support_indicator]
    apply measure_inter_lt_top_of_right_ne_top
    rw [← lt_top_iff_ne_top]
    exact bgs.measure_support_lt
