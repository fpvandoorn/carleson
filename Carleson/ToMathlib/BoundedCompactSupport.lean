/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Sébastien Gouëzel
-/

import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Prod
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

Most functions we need to deal with are of this class.
This can be a useful way to streamline proofs of `L^p` membership,
in particular integrability.

Todo: make `Mathlib.Tactic.FunProp` work for this

This can be expanded as needed

-/

set_option linter.unusedSectionVars false -- remove for mathlib

namespace MeasureTheory

open Bornology Function Set HasCompactSupport
open scoped ENNReal

section

-- This setting should be enough for this project, but
-- for mathlib should generalize to vector-valued, and use `MeasurableSpace X`, `Measure μ`
variable {X 𝕜} [MeasurableSpace X] [RCLike 𝕜] {f : X → 𝕜} {μ : Measure X}
variable [TopologicalSpace X]
-- variable [T2Space X] -- for mathlib should remove this
-- variable [IsFiniteMeasureOnCompacts μ]
-- variable [SigmaFinite (volume : Measure X)]

/-- Bounded compactly supported measurable functions -/
-- There are various alternative definitions one could use here
-- After all it does seem to be better to use `IsBounded (range f)`
-- Todo: Refactor accordingly
structure BoundedCompactSupport (f : X → 𝕜) : Prop where
  isBounded : IsBounded (range f)
  stronglyMeasurable : StronglyMeasurable f
  hasCompactSupport : HasCompactSupport f

lemma isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by convert isBounded_iff_forall_norm_le; simp

omit [TopologicalSpace X] in
lemma _root_.Bornology.IsBounded.eLpNorm_top_lt_top (hf : IsBounded (range f)) :
    eLpNorm f ⊤ μ < ⊤ := by
  obtain ⟨C, hC⟩ := isBounded_range_iff_forall_norm_le.mp hf
  exact eLpNormEssSup_lt_top_of_ae_bound (C := C) (ae_of_all μ hC)

omit [TopologicalSpace X] in
-- maybe in mathlib, but couldn't find it
theorem ae_le_of_eLpNorm_top_lt_top (hf : eLpNorm f ⊤ μ < ⊤) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤ μ) := by
  have := enorm_ae_le_eLpNormEssSup f μ
  filter_upwards [this] with x hx
  have : ENNReal.ofReal ‖f x‖₊ ≠ ⊤ := ENNReal.ofReal_ne_top
  convert (ENNReal.toReal_le_toReal this ?_).mpr ?_
  · simp
  · exact hf.ne_top
  · exact trans ENNReal.ofReal_coe_nnreal hx

namespace BoundedCompactSupport

protected theorem zero : BoundedCompactSupport (fun (_ : X) ↦ (0 : 𝕜)) where
  isBounded := isBounded_range_iff_forall_norm_le.2 ⟨0, by simp⟩
  stronglyMeasurable := stronglyMeasurable_const
  hasCompactSupport := HasCompactSupport.zero

theorem indicator_of_isBounded_range {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] {f : X → 𝕜} (hf : IsBounded (range f))
    (h'f : StronglyMeasurable f) {s : Set X} (h's : IsBounded s) (hs : MeasurableSet s) :
    BoundedCompactSupport (s.indicator f) where
  stronglyMeasurable := h'f.indicator hs
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf with ⟨C, hC⟩
    apply isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
    simp only [indicator]
    split_ifs
    · exact hC x
    · simp only [norm_zero]
      exact (norm_nonneg _).trans (hC x)
  hasCompactSupport := by
    apply HasCompactSupport.intro (K := closure s)
    · exact Metric.isCompact_of_isClosed_isBounded isClosed_closure h's.closure
    · exact fun x hx ↦ by simp [not_mem_of_not_mem_closure hx]

protected theorem indicator {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] {f : X → 𝕜} (hf : BoundedCompactSupport f) {s : Set X}
    (hs : MeasurableSet s) : BoundedCompactSupport (s.indicator f) := by
  rw [← Set.indicator_eq_self.mpr (subset_tsupport f), Set.indicator_indicator]
  apply indicator_of_isBounded_range hf.isBounded hf.stronglyMeasurable
  · exact hf.hasCompactSupport.isBounded.subset inter_subset_right
  · exact hs.inter (isClosed_tsupport f).measurableSet

variable {f : X → 𝕜} {g : X → 𝕜} (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
section Includehf

include hf

theorem aestronglyMeasurable : AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

theorem memLp_top : MemLp f ⊤ μ :=
  ⟨hf.aestronglyMeasurable, hf.isBounded.eLpNorm_top_lt_top⟩

theorem ae_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤ μ) :=
  ae_le_of_eLpNorm_top_lt_top hf.memLp_top.2

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memLp [IsFiniteMeasureOnCompacts μ] (p : ENNReal) : MemLp f p μ :=
  hf.hasCompactSupport.memLp_of_bound hf.aestronglyMeasurable _ hf.ae_le

/-- Bounded compactly supported functions are integrable. -/
theorem integrable [IsFiniteMeasureOnCompacts μ] : Integrable f μ :=
  memLp_one_iff_integrable.mp <| memLp hf 1

theorem mul_bdd_right (hg : IsBounded (range g)) (h2g : StronglyMeasurable g) :
    BoundedCompactSupport (f * g) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg with ⟨D, hD⟩
    apply isBounded_range_iff_forall_norm_le.2 ⟨C * D, fun x ↦ ?_⟩
    simp only [Pi.mul_apply, norm_mul]
    gcongr
    · exact (norm_nonneg _).trans (hC x)
    · exact hC x
    · exact hD x
  stronglyMeasurable := hf.stronglyMeasurable.mul h2g
  hasCompactSupport := hf.hasCompactSupport.mul_right

theorem mul_bdd_left (hg : IsBounded (range g)) (h2g : StronglyMeasurable g) :
    BoundedCompactSupport (g * f) := by
  rw [mul_comm]; exact mul_bdd_right hf hg h2g

-- doesn't use compact support but is convenient to have here
theorem integrable_mul (hg : Integrable g μ) : Integrable (f * g) μ :=
  Integrable.bdd_mul' hg hf.aestronglyMeasurable hf.ae_le

theorem conj : BoundedCompactSupport (star f) where
  isBounded := by simpa [star, isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := RCLike.continuous_conj.comp_stronglyMeasurable hf.stronglyMeasurable
  hasCompactSupport := by -- mathlib should have a lemma `HasCompactSupport.conj`?
    simp only [star, RCLike.star_def]
    exact (hasCompactSupport_comp_left (by simp)).2 hf.hasCompactSupport

theorem norm : BoundedCompactSupport (‖f ·‖) where
  isBounded := by simpa [isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := hf.stronglyMeasurable.norm
  hasCompactSupport := hf.hasCompactSupport.norm

theorem const_mul (c : 𝕜) : BoundedCompactSupport (fun x ↦ c * (f x)) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨‖c‖ * C, fun x ↦ ?_⟩
    rw [norm_mul]
    gcongr
    exact hC x
  stronglyMeasurable := hf.stronglyMeasurable.const_mul _
  hasCompactSupport := by
    suffices support (fun x ↦ c * (f x)) ⊆ support f from hf.hasCompactSupport.mono this
    exact support_mul_subset_right ..

theorem mul_const (c : 𝕜) : BoundedCompactSupport (fun x ↦ (f x) * c) := by
  simp_rw [mul_comm]; exact hf.const_mul _

end Includehf

section Includehfhg

include hf hg

theorem mul : BoundedCompactSupport (f * g) := mul_bdd_right hf hg.isBounded hg.stronglyMeasurable

protected theorem add : BoundedCompactSupport (f + g) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨D, hD⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨C + D, fun x ↦ (norm_add_le _ _).trans ?_⟩
    gcongr
    exacts [hC x, hD x]
  stronglyMeasurable := hf.stronglyMeasurable.add hg.stronglyMeasurable
  hasCompactSupport := hf.hasCompactSupport.add hg.hasCompactSupport

protected theorem sub : BoundedCompactSupport (f - g) := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul]
  exact hf.add (hg.const_mul (-1))

end Includehfhg

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem mono {g : X → ℝ} (hg : BoundedCompactSupport g) (hf : StronglyMeasurable f)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨C, hC⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
    exact (hfg x).trans ((le_abs_self _).trans (hC x))
  hasCompactSupport := by
    refine hg.hasCompactSupport.mono ?_
    by_contra h
    simp only [support_subset_iff, ne_eq, mem_support, not_forall, Classical.not_imp,
      Decidable.not_not] at h
    obtain ⟨x, hfx, hgx⟩ := h
    specialize hfg x
    rw [hgx] at hfg
    exact hfx <| norm_le_zero_iff.mp hfg
  stronglyMeasurable := hf

theorem of_norm_le_const_mul {g : X → ℝ} {M : ℝ} (hg : BoundedCompactSupport g)
    (hf : StronglyMeasurable f)
    (hfg : ∀ x, ‖f x‖ ≤ M * g x) : BoundedCompactSupport f :=
  BoundedCompactSupport.mono (hg.const_mul M) hf hfg

theorem toComplex {f : X → ℝ} (hf : BoundedCompactSupport f) :
    BoundedCompactSupport (fun x ↦ (f x : ℂ)) :=
  mono (g := (‖f ·‖)) hf.norm
    (Complex.continuous_ofReal.comp_stronglyMeasurable hf.stronglyMeasurable) (by simp)

section Sum

variable {ι : Type*} {s : Finset ι} {F : ι → X → 𝕜}

/-- A finite sum of bounded compactly supported functions is bounded compactly supported. -/
theorem finset_sum
    (hF : ∀ i ∈ s, BoundedCompactSupport (F i)) :
    BoundedCompactSupport (fun x ↦ ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction with
  | empty => simp [BoundedCompactSupport.zero]
  | @insert j s hjs IH =>
    simp_rw [Finset.sum_insert hjs]
    apply BoundedCompactSupport.add
    · exact hF _ (Finset.mem_insert_self j s)
    · exact IH (fun i hi ↦ hF _ (Finset.mem_insert_of_mem hi))

end Sum

section Prod

variable {Y: Type*} [MeasureSpace Y] {g : Y → 𝕜}
variable [TopologicalSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
variable [SigmaFinite (volume : Measure Y)] [R1Space (X × Y)]

/-- An elementary tensor of bounded compactly supported functions is
  bounded compactly supported. -/
theorem prod_mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (uncurry fun x y ↦ (f x) * (g y)) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C₁, hC₁⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨C₂, hC₂⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨C₁ * C₂, fun x ↦ ?_⟩
    rw [uncurry, norm_mul]
    gcongr
    · exact (norm_nonneg _).trans (hC₁ x.1)
    · exact hC₁ x.1
    · exact hC₂ x.2
  stronglyMeasurable := .mul (.fst hf.stronglyMeasurable) (.snd hg.stronglyMeasurable)
  hasCompactSupport := by
    apply HasCompactSupport.intro <| IsCompact.prod hf.hasCompactSupport hg.hasCompactSupport
    intro ⟨x,y⟩ hxy
    simp only [uncurry_apply_pair, mul_eq_zero]
    simp only [mem_prod, not_and] at hxy
    by_cases hx : x ∈ tsupport f
    · exact Or.inr (image_eq_zero_of_nmem_tsupport (hxy hx))
    · exact Or.inl (image_eq_zero_of_nmem_tsupport hx)

variable {F : X × Y → 𝕜}

-- -- prove when needed
-- theorem swap (hF : BoundedCompactSupport F) : BoundedCompactSupport (F ∘ Prod.swap) where
--   isBounded := sorry
--   stronglyMeasurable := sorry
--   hasCompactSupport := sorry

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

-- ---- adapt and prove below when needed
-- theorem prod_left (hF : BoundedCompactSupport F) :
--     ∀ y, BoundedCompactSupport (fun x ↦ F (x, y)) := fun y ↦ {
--   isBounded := by
--     rcases isBounded_range_iff_forall_norm_le.1 hF.isBounded with ⟨C, hC⟩
--     apply isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
--     exact hC (x, y)
--   stronglyMeasurable := hF.stronglyMeasurable.comp_measurable measurable_prod_mk_right
--   hasCompactSupport := sorry
--   -- by
--   --   apply HasCompactSupport.intro
--   --   sorry
-- }


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
