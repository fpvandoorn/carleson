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

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ ν : Measure X} {f : X → E}

-- move near the MeasurePreserving/mono_measure analogues
variable {α : Type*} {m0 : MeasurableSpace α} {μ ν : Measure α}
  {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} in
theorem eLpNorm_mono_ac (hμν : ν ≪ μ) : eLpNorm f ∞ ν ≤ eLpNorm f ∞ μ := by
  simp_rw [eLpNorm_exponent_top, MeasureTheory.eLpNormEssSup_mono_measure _ hμν]

variable {α : Type*} {m0 : MeasurableSpace α} {μ ν : Measure α}
  {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} in
theorem MemLp.mono_ac (hf : MemLp f ∞ μ) (hμν : ν ≪ μ) :
    MemLp f ∞ ν :=
⟨hf.1.mono_ac hμν, eLpNorm_mono_ac hμν |>.trans_lt hf.2⟩

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → ε} {ν : Measure β} in
theorem MemLp.comp_quasiMeasurePreserving
    (hg : MemLp g ∞ ν) (hf : Measure.QuasiMeasurePreserving f μ ν) : MemLp (g ∘ f) ∞ μ :=
  .comp_of_map (hg.mono_ac hf.absolutelyContinuous) hf.aemeasurable

-- maybe don't upstream
variable {α : Type*} {m0 : MeasurableSpace α} {μ ν : Measure α}
  {E : Type*} [NormedAddCommGroup E] {f : α → E} in
theorem MemLp.ae_norm_le (hf : MemLp f ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := f)] with x hx
  simp_rw [← toReal_enorm]
  apply ENNReal.toReal_mono hf.2.ne
  simp [hx]

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

section ContinuousENorm

variable [TopologicalSpace E] [ContinuousENorm E] [Zero E]

theorem mono_ac (hf : BoundedCompactSupport f μ) (h : ν ≪ μ) :
    BoundedCompactSupport f ν where
  memLp_top := hf.memLp_top.mono_ac h
  hasCompactSupport := hf.hasCompactSupport

theorem mono_measure (hf : BoundedCompactSupport f μ) (h : ν ≤ μ) : BoundedCompactSupport f ν :=
  hf.mono_ac h.absolutelyContinuous

theorem restrict {s : Set X} (hf : BoundedCompactSupport f μ) :
    BoundedCompactSupport f (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self


end ContinuousENorm


section  ENormedAddCommMonoid
variable [TopologicalSpace E] [ENormedAddCommMonoid E]

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memLp [IsFiniteMeasureOnCompacts μ] (hf : BoundedCompactSupport f μ) (p : ℝ≥0∞) :
    MemLp f p μ :=
  hf.boundedFiniteSupport.memLp p

end ENormedAddCommMonoid

section NormedAddCommGroup

variable [NormedAddCommGroup E]

-- todo: prove more results for ENorm-classes (awaiting-mathlib)

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

-- preferably use `enorm`
theorem norm (hf : BoundedCompactSupport f μ) : BoundedCompactSupport (‖f ·‖) μ where
  memLp_top := hf.memLp_top.norm
  hasCompactSupport := hasCompactSupport_comp_left norm_eq_zero |>.mpr hf.hasCompactSupport

theorem comp_left_norm {F} [MeasurableSpace E] [NormedAddCommGroup F] {g : E → F}
    (hf : BoundedCompactSupport f μ) (hg : g 0 = 0)
    (hg1 : Continuous g)
    (hg2 : (∀ (a : E), ‖g a‖ = ‖a‖)) :
    BoundedCompactSupport (g ∘ f) μ := by
  refine ⟨?_, hf.hasCompactSupport.comp_left hg⟩
  rw [← memLp_norm_iff]
  · simp_rw [Function.comp_apply, hg2, memLp_norm_iff hf.aestronglyMeasurable, hf.memLp_top]
  exact hg1.comp_aestronglyMeasurable hf.aestronglyMeasurable

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

-- use `mono` preferably
theorem mono_norm {g : X → ℝ} (hg : BoundedCompactSupport g μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f μ where
  memLp_top := ⟨hf, eLpNorm_mono_real hfg |>.trans_lt hg.memLp_top.eLpNorm_lt_top⟩
  hasCompactSupport := by
    refine hg.hasCompactSupport.mono ?_
    by_contra h
    simp only [support_subset_iff, ne_eq, mem_support, not_forall, Classical.not_imp,
      Decidable.not_not] at h
    obtain ⟨x, hfx, hgx⟩ := h
    specialize hfg x
    simp_rw [hgx, norm_le_zero_iff, hfx] at hfg

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
    -- todo: maybe separate out as lemmas
    have h2f : MemLp (fun z : X × Y ↦ f z.1) ∞ (μ.prod ν) :=
      hf.memLp_top.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2g : MemLp (fun z : X × Y ↦ g z.2) ∞ (μ.prod ν) :=
      hg.memLp_top.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    -- todo: reorder arguments of `mul`
    exact h2g.mul (r := ∞) h2f
  hasCompactSupport := by
    -- todo: separate out as lemmas
    apply HasCompactSupport.intro <| hf.hasCompactSupport.prod hg.hasCompactSupport
    intro ⟨x,y⟩ hxy
    simp only [uncurry_apply_pair, mul_eq_zero]
    simp only [mem_prod, not_and] at hxy
    by_cases hx : x ∈ tsupport f
    · exact Or.inr (image_eq_zero_of_nmem_tsupport (hxy hx))
    · exact Or.inl (image_eq_zero_of_nmem_tsupport hx)

variable [R1Space X] in
theorem indicator_of_isCompact_closure {f : X → E} (hf : MemLp f ∞ μ)
    {s : Set X} (h's : IsCompact (closure s)) (hs : MeasurableSet s) :
    BoundedCompactSupport (s.indicator f) μ where
  memLp_top := hf.indicator hs
  hasCompactSupport := by
    apply HasCompactSupport.intro h's
    exact fun x hx ↦ by simp [not_mem_of_not_mem_closure hx]

protected theorem indicator {f : X → E} (hf : BoundedCompactSupport f μ) {s : Set X}
    (hs : MeasurableSet s) : BoundedCompactSupport (s.indicator f) μ where
  memLp_top := hf.memLp_top.indicator hs
  hasCompactSupport := hf.hasCompactSupport.mono (by simp)

variable {F : X × Y → E}

-- -- prove when needed
-- theorem swap (hF : BoundedCompactSupport f μ) : BoundedCompactSupport (F ∘ Prod.swap) where
--   memLp_top := sorry
--   stronglyMeasurable := sorry
--   hasCompactSupport := sorry

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

end NormedAddCommGroup


end BoundedCompactSupport

end

section Metric
namespace BoundedCompactSupport

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] {μ : Measure X}
  [TopologicalSpace E] [ENorm E] [Zero E]
  {f : X → E}

theorem isBoundedTSupport (hf : BoundedCompactSupport f μ) : IsBounded (tsupport f) :=
  hf.hasCompactSupport.isBounded

theorem isBoundedSupport (hf : BoundedCompactSupport f μ) : IsBounded (support f) :=
  hf.isBoundedTSupport.subset <| subset_tsupport f


end BoundedCompactSupport

end Metric

end MeasureTheory

section

open Bornology ENNReal MeasureTheory Set

variable {X 𝕜 E F : Type*} [MeasurableSpace X] [MetricSpace X]
variable [NormedAddCommGroup E]
variable {Y W : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
variable [MeasurableSpace W] [TopologicalSpace W] {μ : Measure W}
variable {f : X → 𝕜} {ν : Measure X} [RCLike 𝕜]

lemma BoundedCompactSupport.mul_bdd_right'' (hf : BoundedCompactSupport f ν) {e : W → X}
    {g : W → 𝕜} (he : Continuous e) (he1 : Measure.QuasiMeasurePreserving e μ ν)
    (hg : AEStronglyMeasurable g μ)
    (hg1 : ∀ K : Set X, IsCompact K -> IsCompact (e ⁻¹' K ∩ tsupport g))
    (hg2 : ∀ (A : Set X) (_hA : IsBounded A), IsBounded (g '' (e ⁻¹' A))) :
    BoundedCompactSupport (fun x ↦ f (e x) * g x) μ where
  memLp_top := by
    have := hf.memLp_top.ae_norm_le
    set B := (eLpNorm f ⊤ ν).toReal
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (hg2 (tsupport f) hf.hasCompactSupport.isBounded)
    apply memLp_top_of_bound (C := max 0 B * max 0 C)
    · exact (hf.mono_ac he1.absolutelyContinuous |>.aestronglyMeasurable.comp_measurable
        he1.measurable).mul hg
    filter_upwards [he1.ae this] with z hB
    rw [norm_mul]
    by_cases hz : z ∈ e ⁻¹' tsupport f
    · gcongr
      · exact hB.trans (le_max_right ..)
      refine hC _ ?_ |>.trans (le_max_right ..)
      exact mem_image_of_mem g hz
    · simp only [image_eq_zero_of_nmem_tsupport hz, norm_zero, zero_mul,
        mul_nonneg (le_max_left 0 B) (le_max_left 0 C)]
  hasCompactSupport := by
    refine IsCompact.of_isClosed_subset (hg1 _ hf.hasCompactSupport)
      (isClosed_tsupport fun x ↦ f (e x) * g x) ?_
    apply subset_inter ?_ tsupport_mul_subset_right
    apply subset_trans (tsupport_mul_subset_left)
    rw [tsupport, ((isClosed_tsupport f).preimage he ).closure_subset_iff]
    exact fun _ hx ↦ subset_closure hx

lemma BoundedCompactSupport.mul_bdd_left' (hf : BoundedCompactSupport f ν) {e : W → X} {g : W → 𝕜}
    (he : Continuous e) (he1 : Measure.QuasiMeasurePreserving e μ ν)
    (hg : AEStronglyMeasurable g μ)
    (hg1 : ∀ K : Set X, IsCompact K -> IsCompact (e ⁻¹' K ∩ tsupport g))
    (hg2 : ∀ (A : Set X) (_hA : IsBounded A), IsBounded (g '' (e ⁻¹' A))) :
    BoundedCompactSupport (fun x ↦ g x * f (e x)) μ:= by
  simp_rw [mul_comm]; exact mul_bdd_right'' hf he he1 hg hg1 hg2

end
