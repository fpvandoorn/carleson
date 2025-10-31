import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-
This file defines BoundedFiniteSupport.

Upstreaming status: something like this is useful, but the precise form is not final yet
- decide of this or BoundedCompactSupport is better (see comment there)
  and possibly rewrite Carleson in favour of the one class we prefer
- TODO: can other proofs be golfed using fun_prop now?
-/

open MeasureTheory Function ENNReal TopologicalSpace

noncomputable section

variable {X E : Type*} [MeasurableSpace X] {f g : X → E} {μ : Measure X}

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

@[aesop (rule_sets := [finiteness]) unsafe 80% apply]
theorem eLpNorm_lt_top : eLpNorm f ∞ μ < ∞ := bfs.memLp_top.eLpNorm_lt_top

end Includebfs

section  ENormedAddMonoid
variable [TopologicalSpace E] [ENormedAddMonoid E]

/-- Bounded finitely supported functions are in all `Lᵖ` spaces. -/
theorem memLp (hf : BoundedFiniteSupport f μ) (p : ℝ≥0∞) : MemLp f p μ :=
  hf.memLp_top.mono_exponent_of_measure_support_ne_top
    (fun _ ↦ notMem_support.mp) hf.measure_support_lt.ne le_top

end ENormedAddMonoid

section NormedAddCommGroup

variable [NormedAddCommGroup E]

/-- Bounded finitely supported functions are integrable. -/
@[fun_prop]
theorem integrable (hf : BoundedFiniteSupport f μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp <| hf.memLp 1

@[fun_prop]
theorem indicator (bfs : BoundedFiniteSupport f μ) {s : Set X} (hs : MeasurableSet s) :
    BoundedFiniteSupport (s.indicator f) μ := by
  constructor
  · exact MemLp.indicator hs bfs.memLp_top
  · rw[Set.support_indicator]
    apply measure_inter_lt_top_of_right_ne_top
    rw [← lt_top_iff_ne_top]
    exact bfs.measure_support_lt

@[fun_prop]
protected theorem neg (hf : BoundedFiniteSupport f μ) : BoundedFiniteSupport (-f) μ :=
  ⟨memLp_neg_iff.mpr hf.memLp_top, support_neg f ▸ hf.measure_support_lt⟩

@[fun_prop]
protected theorem add (hf : BoundedFiniteSupport f μ) (hg : BoundedFiniteSupport g μ) :
    BoundedFiniteSupport (f + g) μ :=
  ⟨hf.memLp_top.add hg.memLp_top,
    (measure_mono (support_add f g)).trans_lt <| (measure_union_le (support f) (support g)).trans_lt
      (add_lt_top.mpr ⟨hf.measure_support_lt, hg.measure_support_lt⟩)⟩

@[fun_prop]
protected theorem sub (hf : BoundedFiniteSupport f μ) (hg : BoundedFiniteSupport g μ) :
    BoundedFiniteSupport (f - g) μ :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

end NormedAddCommGroup

end BoundedFiniteSupport
