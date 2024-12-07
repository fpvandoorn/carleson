import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Carleson.ToMathlib.Misc

/-!

EXPERIMENTAL

# Bounded compactly supported functions

The purpose of this file is to provide helper lemmas to streamline proofs that
functions are (essentially) bounded, compactly supported and measurable.

We use essential boundedness in the form of `Memℒp f ⊤`.

Most functions we need to deal with are of this class.
Hopefully this will be a useful way to streamline proofs of `L^p` membership,
in particular integrability.

Todo: make `Mathlib.Tactic.FunProp` work for this

The `sorry`s in this file are supposed to be "easy".

-/

namespace MeasureTheory

open Bornology Function Set HasCompactSupport
open scoped ENNReal

section

-- This setting should be enough for this project, but
-- for mathlib should generalize to vector-valued, and use `MeasurableSpace X`, `Measure μ`
variable {X 𝕜} [MeasureSpace X] [RCLike 𝕜] {f : X → 𝕜}
variable [TopologicalSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
variable [SigmaFinite (volume : Measure X)]

variable (f) in
/-- Bounded compactly supported measurable functions -/
-- There are various alternative definitions one could use here
structure BoundedCompactSupport : Prop where
  memℒp_top : Memℒp f ⊤
  hasCompactSupport : HasCompactSupport f

lemma isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by convert isBounded_iff_forall_norm_le; simp

lemma _root_.Bornology.IsBounded.eLpNorm_top_lt_top (hf : IsBounded (range f)) :
    eLpNorm f ⊤ < ⊤ := by
  obtain ⟨C, hC⟩ := isBounded_range_iff_forall_norm_le.mp hf
  apply eLpNormEssSup_lt_top_of_ae_bound (C := C)
  exact ae_of_all volume hC

-- alternative constructor
theorem BoundedCompactSupport.mk' (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) : BoundedCompactSupport f :=
  ⟨⟨h3f, hf.eLpNorm_top_lt_top⟩, h2f⟩

-- mathlib?
theorem ae_le_of_eLpNorm_top_lt_top (hf : eLpNorm f ⊤ < ⊤) :
    ∀ᵐ x, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤) := by
  have := coe_nnnorm_ae_le_eLpNormEssSup f volume
  filter_upwards [this] with x hx
  have : ENNReal.ofReal ‖f x‖₊ ≠ ⊤ := ENNReal.ofReal_ne_top
  convert (ENNReal.toReal_le_toReal this ?_).mpr ?_
  · simp
  · exact hf.ne_top
  · exact trans ENNReal.ofReal_coe_nnreal hx

namespace BoundedCompactSupport

variable {f : X → 𝕜}
variable {g : X → 𝕜}

variable (hf : BoundedCompactSupport f)
variable (hg : BoundedCompactSupport g)

section Includehf

include hf

omit [IsFiniteMeasureOnCompacts (volume : Measure X)] in
theorem aestronglyMeasurable : AEStronglyMeasurable f := hf.memℒp_top.aestronglyMeasurable

theorem ae_le : ∀ᵐ x, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤) :=
  ae_le_of_eLpNorm_top_lt_top hf.memℒp_top.2

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memℒp (p : ENNReal) : Memℒp f p :=
  memℒp_of_bound hf.hasCompactSupport hf.aestronglyMeasurable _ hf.ae_le

/-- Bounded compactly supported functions are integrable. -/
theorem integrable : Integrable f := memℒp_one_iff_integrable.mp <| memℒp hf 1

-- needed
theorem mul_ess_bdd (hg : eLpNorm g ⊤ < ⊤) : BoundedCompactSupport (f * g) := sorry

theorem ess_bdd_mul (hg : eLpNorm g ⊤ < ⊤) : BoundedCompactSupport (g * f) := by
  rw [mul_comm]; exact mul_ess_bdd hf hg

/-- A bounded compactly supported function times a bounded function is
bounded compactly supported. -/
theorem mul_bdd (hg : IsBounded (range g)) : BoundedCompactSupport (f * g) :=
  hf.mul_ess_bdd hg.eLpNorm_top_lt_top

theorem bdd_mul (hg : IsBounded (range g)) : BoundedCompactSupport (g * f) :=
  hf.ess_bdd_mul hg.eLpNorm_top_lt_top

-- should eventually have version for essentially bounded, but not needed now

#check Integrable.bdd_mul
-- for convenience
theorem integrable_mul (hg : Integrable g) : Integrable (f * g) := sorry

-- needed
theorem conj : BoundedCompactSupport (star f) := sorry

-- needed
theorem norm : BoundedCompactSupport (‖f ·‖) := sorry

theorem const_mul (c : 𝕜) : BoundedCompactSupport (fun x ↦ c * (f x)) := sorry

theorem mul_const (c : 𝕜) : BoundedCompactSupport (fun x ↦ (f x) * c) := sorry

end Includehf

section Includehfhg

include hf hg

theorem mul : BoundedCompactSupport (f * g) := mul_ess_bdd hf hg.memℒp_top.2

-- prove when needed
theorem add : BoundedCompactSupport (f + g) := sorry

end Includehfhg

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem of_norm_le {g : X → ℝ} (hg : BoundedCompactSupport g)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f := sorry

-- needed
-- this is a very common use case, so it deserves its own theorem
theorem of_norm_le_const_mul {g : X → ℝ} {M : ℝ} (hg : BoundedCompactSupport g)
    (hfg : ∀ x, ‖f x‖ ≤ M * g x) : BoundedCompactSupport f := sorry

section Sum

variable {ι : Type*} {s : Finset ι} {F : ι → X → 𝕜}

-- needed
/-- A finite sum of bounded compactly supported functions is bounded compactly supported. -/
theorem _root_.Finset.boundedCompactSupport_sum
    (hF : ∀ i ∈ s, BoundedCompactSupport (F i)) : BoundedCompactSupport (fun x ↦ ∑ i ∈ s, F i x) :=
  sorry

end Sum

section Prod

variable {Y: Type*} [MeasureSpace Y] {g : Y → 𝕜}
variable [TopologicalSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
variable [SigmaFinite (volume : Measure Y)]

-- needed
/-- An elementary tensor of bounded compactly supported functions is
bounded compactly supported. -/
theorem prod_mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (uncurry fun x y ↦ (f x) * (g y)) := sorry

variable {F : X × Y → 𝕜}

-- prove when needed
theorem swap (hF : BoundedCompactSupport F) : BoundedCompactSupport (F ∘ Prod.swap) :=
  sorry

end Prod

end BoundedCompactSupport

end

namespace BoundedCompactSupport


section Metric

variable {X Y 𝕜: Type*} [RCLike 𝕜]
variable [MeasureSpace X] {f : X → 𝕜} [PseudoMetricSpace X] [SigmaFinite (volume : Measure X)]
variable [MeasureSpace Y] {g : Y → 𝕜} [PseudoMetricSpace Y] [SigmaFinite (volume : Measure Y)]

variable (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)

section Prod

variable {F : X × Y → 𝕜}

-- adapt and prove below when needed
-- theorem prod_left_ae (hF : BoundedCompactSupport F) :
--     ∀ᵐ y, BoundedCompactSupport (fun x ↦ F (x, y)) := sorry

-- theorem prod_right_ae (hF : BoundedCompactSupport F) :
--     ∀ᵐ x, BoundedCompactSupport (fun y ↦ F (x, y)) := hF.swap.prod_left_ae

-- theorem integral_prod_left (hF : BoundedCompactSupport F) :
--     BoundedCompactSupport (fun x ↦ ∫ y, F (x, y)) := sorry
-- --   have := hF.integrable.integrable_prod_left

-- theorem integral_prod_right (hF : BoundedCompactSupport F) :
--     BoundedCompactSupport (fun y ↦ ∫ x, F (x, y)) := hF.swap.integral_prod_left

end Prod

section
include hf

theorem isBoundedSupport' : IsBounded (tsupport f) :=
  hf.hasCompactSupport.isBounded

theorem isBoundedSupport : IsBounded (support f) :=
  hf.isBoundedSupport'.subset <| subset_tsupport f

end

end Metric


end BoundedCompactSupport

end MeasureTheory
