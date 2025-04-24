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

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X} {f : X → E}

variable [TopologicalSpace E] [ENorm E] [Zero E] in
/-- Bounded compactly supported measurable functions -/
structure BoundedCompactSupport (f : X → E) (μ : Measure X := by volume_tac) :
    Prop where
  memLp_top : MemLp f ∞ μ
  hasCompactSupport : HasCompactSupport f

namespace BoundedCompactSupport

section General

variable [TopologicalSpace E] [ENorm E] [Zero E]

theorem aestronglyMeasurable (hf : BoundedCompactSupport f μ) : AEStronglyMeasurable f μ :=
  hf.memLp_top.aestronglyMeasurable

theorem boundedFiniteSupport [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f μ) :
    BoundedFiniteSupport f μ where
  memLp_top := hf.memLp_top
  measure_support_lt :=
    measure_mono (subset_tsupport _) |>.trans_lt hf.hasCompactSupport.isCompact.measure_lt_top

end General


section NormedAddCommGroup

variable [NormedAddCommGroup E]

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memLp [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f μ) (p : ℝ≥0∞) :
    MemLp f p μ :=
  hf.boundedFiniteSupport.memLp p

/-- Bounded compactly supported functions are integrable. -/
theorem integrable [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f μ) :
    Integrable f μ :=
  hf.boundedFiniteSupport.integrable

protected theorem zero : BoundedCompactSupport (fun (_ : X) ↦ (0 : E)) μ where
  memLp_top := memLp_top_const 0
  hasCompactSupport := HasCompactSupport.zero

theorem enorm (hf : BoundedCompactSupport f μ) : BoundedCompactSupport (‖f ·‖ₑ) μ where
  memLp_top := hf.memLp_top.enorm
  hasCompactSupport := hasCompactSupport_comp_left enorm_eq_zero |>.mpr hf.hasCompactSupport

protected theorem neg (hf : BoundedCompactSupport f μ) : BoundedCompactSupport (- f) μ where
  memLp_top := hf.memLp_top.neg
  hasCompactSupport := hf.hasCompactSupport.neg'

variable {𝕜 : Type*} [RCLike 𝕜] {g : X → E}

protected theorem add (hf : BoundedCompactSupport f μ) (hg : BoundedCompactSupport g μ) :
    BoundedCompactSupport (f + g) μ where
  memLp_top := hf.memLp_top.add hg.memLp_top
  hasCompactSupport := hf.hasCompactSupport.add hg.hasCompactSupport

protected theorem sub (hf : BoundedCompactSupport f μ) (hg : BoundedCompactSupport g μ) :
    BoundedCompactSupport (f - g) μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

section Mul

variable {f g : X → 𝕜}

theorem mul_bdd_right (hf : BoundedCompactSupport f μ) (hg : MemLp g ∞ μ) :
    BoundedCompactSupport (f * g) μ where
  memLp_top := hg.mul hf.memLp_top
  hasCompactSupport := hf.hasCompactSupport.mul_right

theorem mul_bdd_left (hf : BoundedCompactSupport f μ) (hg : MemLp g ∞ μ) :
    BoundedCompactSupport (g * f) μ := by
  rw [mul_comm]; exact mul_bdd_right hf hg

theorem mul (hf : BoundedCompactSupport f μ) (hg : BoundedCompactSupport g μ) :
    BoundedCompactSupport (f * g) μ :=
  hf.mul_bdd_right hg.memLp_top

-- doesn't use compact support but is convenient to have here
theorem integrable_mul (hf : BoundedCompactSupport f μ) (hg : Integrable g μ) :
    Integrable (f * g) μ := by
  rw [← memLp_one_iff_integrable] at hg ⊢
  exact hg.mul hf.memLp_top

-- todo: extract 3-4 lemmas from this proof
theorem conj (hf : BoundedCompactSupport f μ) : BoundedCompactSupport (star f) μ where
  memLp_top := by
    refine ⟨RCLike.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable, ?_⟩
    simp_rw [star]
    rw [MeasureTheory.eLpNorm_congr_enorm_ae (g := f)]
    · exact hf.memLp_top.eLpNorm_lt_top
    simp
  hasCompactSupport := by
    simp_rw [star]
    exact (hasCompactSupport_comp_left (by simp)).2 hf.hasCompactSupport

theorem const_mul (hf : BoundedCompactSupport f μ) (c : 𝕜) :
    BoundedCompactSupport (fun x ↦ c * f x) μ :=
  hf.mul_bdd_left <| memLp_top_const _

theorem mul_const (hf : BoundedCompactSupport f μ) (c : 𝕜) :
    BoundedCompactSupport (fun x ↦ f x * c) μ :=
  hf.mul_bdd_right <| memLp_top_const _

end Mul

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem mono {g : X → ℝ≥0∞} (hg : BoundedCompactSupport g μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ x, ‖f x‖ₑ ≤ g x) : BoundedCompactSupport f μ where
  memLp_top := ⟨hf, eLpNorm_mono_enorm hfg |>.trans_lt hg.memLp_top.eLpNorm_lt_top⟩
  hasCompactSupport := by
    refine hg.hasCompactSupport.mono ?_
    by_contra h
    simp only [support_subset_iff, ne_eq, mem_support, not_forall, Classical.not_imp,
      Decidable.not_not] at h
    obtain ⟨x, hfx, hgx⟩ := h
    specialize hfg x
    simp_rw [hgx, nonpos_iff_eq_zero, enorm_eq_zero, hfx] at hfg

theorem toComplex {f : X → ℝ} (hf : BoundedCompactSupport f μ) :
    BoundedCompactSupport (fun x ↦ (f x : ℂ)) μ :=
  mono (g := (‖f ·‖ₑ)) hf.enorm
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (by simp [← ofReal_norm])

section Sum

variable {ι : Type*} {s : Finset ι} {F : ι → X → E}

/-- A finite sum of bounded compactly supported functions is bounded compactly supported. -/
theorem finset_sum
    (hF : ∀ i ∈ s, BoundedCompactSupport (F i) μ) :
    BoundedCompactSupport (fun x ↦ ∑ i ∈ s, F i x) μ := by
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

variable {Y : Type*} [MeasureSpace Y] {f : X → 𝕜} {g : Y → 𝕜} {ν : Measure Y}
variable [TopologicalSpace Y]
variable [R1Space (X × Y)]

/-- An elementary tensor of bounded compactly supported functions is
  bounded compactly supported. -/
theorem prod_mul (hf : BoundedCompactSupport f μ) (hg : BoundedCompactSupport g ν) :
    BoundedCompactSupport (uncurry fun x y ↦ f x * g y) (μ.prod ν) where
  memLp_top := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C₁, hC₁⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨C₂, hC₂⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨C₁ * C₂, fun x ↦ ?_⟩
    rw [uncurry, norm_mul]
    gcongr
    · exact (norm_nonneg _).trans (hC₁ x.1)
    · exact hC₁ x.1
    · exact hC₂ x.2
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
-- theorem swap (hF : BoundedCompactSupport f μ) : BoundedCompactSupport (F ∘ Prod.swap) where
--   memLp_top := sorry
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

variable (hf : BoundedCompactSupport f μ) (hg : BoundedCompactSupport g μ)


theorem indicator_of_isBounded_range {f : X → E} (hf : IsBounded (range f))
    (h'f : StronglyMeasurable f) {s : Set X} (h's : IsBounded s) (hs : MeasurableSet s) :
    BoundedCompactSupport (s.indicator f) where
  stronglyMeasurable := h'f.indicator hs
  memLp_top := by
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
    [MeasurableSpace X] [BorelSpace X] {f : X → E} (hf : BoundedCompactSupport f μ) {s : Set X}
    (hs : MeasurableSet s) : BoundedCompactSupport (s.indicator f) := by
  rw [← Set.indicator_eq_self.mpr (subset_tsupport f), Set.indicator_indicator]
  apply indicator_of_isBounded_range hf.isBounded hf.stronglyMeasurable
  · exact hf.hasCompactSupport.isBounded.subset inter_subset_right
  · exact hs.inter (isClosed_tsupport f).measurableSet


section Prod

variable {F : X × Y → E}

-- ---- adapt and prove below when needed
-- theorem prod_left (hF : BoundedCompactSupport f μ) :
--     ∀ y, BoundedCompactSupport (fun x ↦ F (x, y)) := fun y ↦ {
--   memLp_top := by
--     rcases isBounded_range_iff_forall_norm_le.1 hF.isBounded with ⟨C, hC⟩
--     apply isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
--     exact hC (x, y)
--   stronglyMeasurable := hF.stronglyMeasurable.comp_measurable measurable_prodMk_right
--   hasCompactSupport := sorry
--   -- by
--   --   apply HasCompactSupport.intro
--   --   sorry
-- }


-- theorem prod_right_ae (hF : BoundedCompactSupport f μ) :
--     ∀ᵐ x, BoundedCompactSupport (fun y ↦ F (x, y)) := hF.swap.prod_left_ae

-- theorem integral_prod_left (hF : BoundedCompactSupport f μ) :
--     BoundedCompactSupport (fun x ↦ ∫ y, F (x, y)) := sorry
-- --   have := hF.integrable.integrable_prod_left

-- theorem integral_prod_right (hF : BoundedCompactSupport f μ) :
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


end NormedAddCommGroup

end BoundedCompactSupport

end MeasureTheory
