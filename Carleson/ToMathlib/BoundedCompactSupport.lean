/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Sébastien Gouëzel
-/

import Carleson.ToMathlib.BoundedFiniteSupport

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

open Bornology Function Set HasCompactSupport
open scoped ENNReal

namespace MeasureTheory

section

variable {X E} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] {f : X → E}

/-- Bounded compactly supported measurable functions -/
-- There are various alternative definitions one could use here
-- Maybe we only want to say that `f` is a.e.-bounded.
structure BoundedCompactSupport {E} [Bornology E] [Zero E] [TopologicalSpace E]
    (f : X → E) : Prop where
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
    ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  have := enorm_ae_le_eLpNormEssSup f μ
  filter_upwards [this] with x hx
  have : ENNReal.ofReal ‖f x‖₊ ≠ ⊤ := ENNReal.ofReal_ne_top
  convert (ENNReal.toReal_le_toReal this ?_).mpr ?_
  · simp
  · exact hf.ne_top
  · exact trans ENNReal.ofReal_coe_nnreal hx

namespace BoundedCompactSupport

theorem aestronglyMeasurable (hf : BoundedCompactSupport f) : AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

theorem memLp_top (hf : BoundedCompactSupport f) : MemLp f ⊤ μ :=
  ⟨hf.aestronglyMeasurable, hf.isBounded.eLpNorm_top_lt_top⟩

theorem boundedFiniteSupport [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f) :
    BoundedFiniteSupport f μ where
  memLp_top := hf.memLp_top
  measure_support_lt :=
    measure_mono (subset_tsupport _) |>.trans_lt hf.hasCompactSupport.isCompact.measure_lt_top

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memLp [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f) (p : ℝ≥0∞) :
    MemLp f p μ :=
  hf.boundedFiniteSupport.memLp p

/-- Bounded compactly supported functions are integrable. -/
theorem integrable [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f) : Integrable f μ :=
  hf.boundedFiniteSupport.integrable

protected theorem zero : BoundedCompactSupport (fun (_ : X) ↦ (0 : E)) where
  isBounded := isBounded_range_iff_forall_norm_le.2 ⟨0, by simp⟩
  stronglyMeasurable := stronglyMeasurable_const
  hasCompactSupport := HasCompactSupport.zero

theorem indicator_of_isBounded_range {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] {f : X → E} (hf : IsBounded (range f))
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
    [MeasurableSpace X] [BorelSpace X] {f : X → E} (hf : BoundedCompactSupport f) {s : Set X}
    (hs : MeasurableSet s) : BoundedCompactSupport (s.indicator f) := by
  rw [← Set.indicator_eq_self.mpr (subset_tsupport f), Set.indicator_indicator]
  apply indicator_of_isBounded_range hf.isBounded hf.stronglyMeasurable
  · exact hf.hasCompactSupport.isBounded.subset inter_subset_right
  · exact hs.inter (isClosed_tsupport f).measurableSet

theorem ae_le (hf : BoundedCompactSupport f) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal :=
  ae_le_of_eLpNorm_top_lt_top hf.memLp_top.2

theorem norm (hf : BoundedCompactSupport f) : BoundedCompactSupport (‖f ·‖) where
  isBounded := by simpa [isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := hf.stronglyMeasurable.norm
  hasCompactSupport := hf.hasCompactSupport.norm

protected theorem neg (hf : BoundedCompactSupport f) : BoundedCompactSupport (- f) where
  isBounded := by simpa [isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := hf.stronglyMeasurable.neg
  hasCompactSupport := hf.hasCompactSupport.neg'

variable {𝕜 : Type*} [RCLike 𝕜] {g : X → E}

protected theorem add (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (f + g) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨D, hD⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨C + D, fun x ↦ (norm_add_le _ _).trans ?_⟩
    gcongr
    exacts [hC x, hD x]
  stronglyMeasurable := hf.stronglyMeasurable.add hg.stronglyMeasurable
  hasCompactSupport := hf.hasCompactSupport.add hg.hasCompactSupport

protected theorem sub (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

section Mul

variable {f g : X → 𝕜}

theorem mul_bdd_right (hf : BoundedCompactSupport f)
    (hg : IsBounded (range g)) (h2g : StronglyMeasurable g) :
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

theorem mul_bdd_left (hf : BoundedCompactSupport f)
    (hg : IsBounded (range g)) (h2g : StronglyMeasurable g) :
    BoundedCompactSupport (g * f) := by
  rw [mul_comm]; exact mul_bdd_right hf hg h2g

theorem mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (f * g) :=
  mul_bdd_right hf hg.isBounded hg.stronglyMeasurable

-- doesn't use compact support but is convenient to have here
theorem integrable_mul (hf : BoundedCompactSupport f) (hg : Integrable g μ) :
    Integrable (f * g) μ :=
  Integrable.bdd_mul' hg hf.aestronglyMeasurable hf.ae_le

theorem conj (hf : BoundedCompactSupport f) : BoundedCompactSupport (star f) where
  isBounded := by simpa [star, isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := RCLike.continuous_conj.comp_stronglyMeasurable hf.stronglyMeasurable
  hasCompactSupport := by -- mathlib should have a lemma `HasCompactSupport.conj`?
    simp only [star, RCLike.star_def]
    exact (hasCompactSupport_comp_left (by simp)).2 hf.hasCompactSupport

theorem const_mul (hf : BoundedCompactSupport f) (c : 𝕜) :
    BoundedCompactSupport (fun x ↦ c * f x) :=
  hf.mul_bdd_left (isBounded_singleton.subset Set.range_const_subset) stronglyMeasurable_const

theorem mul_const (hf : BoundedCompactSupport f) (c : 𝕜) :
    BoundedCompactSupport (fun x ↦ f x * c) := by
  simp_rw [mul_comm]; exact hf.const_mul _

end Mul

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

variable {ι : Type*} {s : Finset ι} {F : ι → X → E}

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

variable {Y : Type*} [MeasureSpace Y] {f : X → 𝕜} {g : Y → 𝕜}
variable [TopologicalSpace Y]
variable [R1Space (X × Y)]

/-- An elementary tensor of bounded compactly supported functions is
  bounded compactly supported. -/
theorem prod_mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (uncurry fun x y ↦ f x * g y) where
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

variable {F : X × Y → E}

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

variable {X Y E: Type*} [RCLike E]
variable [MeasureSpace X] {f : X → E} [PseudoMetricSpace X]
variable [MeasureSpace Y] {g : Y → E} [PseudoMetricSpace Y] [SigmaFinite (volume : Measure Y)]

variable (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)

section Prod

variable {F : X × Y → E}

-- ---- adapt and prove below when needed
-- theorem prod_left (hF : BoundedCompactSupport F) :
--     ∀ y, BoundedCompactSupport (fun x ↦ F (x, y)) := fun y ↦ {
--   isBounded := by
--     rcases isBounded_range_iff_forall_norm_le.1 hF.isBounded with ⟨C, hC⟩
--     apply isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
--     exact hC (x, y)
--   stronglyMeasurable := hF.stronglyMeasurable.comp_measurable measurable_prodMk_right
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
