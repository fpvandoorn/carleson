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
variable {X 𝕜} [MeasureSpace X] [RCLike 𝕜] {f : X → 𝕜}
variable [TopologicalSpace X]
-- variable [T2Space X] -- for mathlib should remove this
variable [IsFiniteMeasureOnCompacts (volume : Measure X)]
-- variable [SigmaFinite (volume : Measure X)]

variable (f) in
/-- Bounded compactly supported measurable functions -/
-- There are various alternative definitions one could use here
-- After all it does seem to be better to use `IsBounded (range f)`
-- (and `AEStronglyMeasurable f`)
-- Todo: Refactor accordingly
structure BoundedCompactSupport : Prop where
  memℒp_top : Memℒp f ⊤ -- comment this out and uncomment the next two lines
  -- isBounded : IsBounded (range f)
  -- aestronglyMeasurable : AEStronglyMeasurable f
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

-- maybe in mathlib, but couldn't find it
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

theorem aestronglyMeasurable : AEStronglyMeasurable f := hf.memℒp_top.aestronglyMeasurable

theorem ae_le : ∀ᵐ x, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤) :=
  ae_le_of_eLpNorm_top_lt_top hf.memℒp_top.2

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memℒp (p : ENNReal) : Memℒp f p :=
  hf.hasCompactSupport.memℒp_of_bound hf.aestronglyMeasurable _ hf.ae_le

/-- Bounded compactly supported functions are integrable. -/
theorem integrable : Integrable f := memℒp_one_iff_integrable.mp <| memℒp hf 1

theorem mul_ess_bdd_right (hg : eLpNorm g ⊤ < ⊤) (h2g : AEStronglyMeasurable g) :
    BoundedCompactSupport (f * g) where
  memℒp_top := by
    suffices ∀ᵐ x, ‖(f * g) x‖ ≤ (eLpNorm f ⊤).toReal * (eLpNorm g ⊤).toReal from
      memℒp_top_of_bound (hf.aestronglyMeasurable.mul h2g) _ this
    filter_upwards [hf.ae_le, ae_le_of_eLpNorm_top_lt_top hg] with _ _ _
    refine trans (norm_mul_le ..) ?_
    gcongr
  hasCompactSupport := hf.hasCompactSupport.mul_right

theorem mul_ess_bdd_left (hg : eLpNorm g ⊤ < ⊤) (h2g : AEStronglyMeasurable g) :
    BoundedCompactSupport (g * f) := by
  rw [mul_comm]; exact mul_ess_bdd_right hf hg h2g

/-- A bounded compactly supported function times a bounded function is
bounded compactly supported. -/
theorem mul_bdd_right (hg : IsBounded (range g)) (h2g : AEStronglyMeasurable g) :
    BoundedCompactSupport (f * g) :=
  hf.mul_ess_bdd_right hg.eLpNorm_top_lt_top h2g

theorem mul_bdd_left (hg : IsBounded (range g))  (h2g : AEStronglyMeasurable g) :
    BoundedCompactSupport (g * f) :=
  hf.mul_ess_bdd_left hg.eLpNorm_top_lt_top h2g

-- doesn't use compact support but is convenient to have here
theorem integrable_mul (hg : Integrable g) : Integrable (f * g) :=
  Integrable.bdd_mul' hg hf.aestronglyMeasurable hf.ae_le

theorem conj : BoundedCompactSupport (star f) where
  memℒp_top := by -- mathlib should have a lemma `Memℒp.conj`?
    suffices ∀ᵐ x, ‖(star f) x‖ ≤ (eLpNorm f ⊤).toReal by
      refine memℒp_top_of_bound ?_ _ this
      exact RCLike.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable
    filter_upwards [hf.ae_le] with x hx
    exact trans (RCLike.norm_conj _) hx
  hasCompactSupport := by -- mathlib should have a lemma `HasCompactSupport.conj`?
    suffices support (star f) = support f by
      rw [hasCompactSupport_def, this]; exact hf.hasCompactSupport
    apply support_eq_iff.mpr
    simp only [mem_support, ne_eq, Pi.star_apply, RCLike.star_def, map_eq_zero, imp_self,
      implies_true, Decidable.not_not, and_self]

theorem norm : BoundedCompactSupport (‖f ·‖) := ⟨hf.memℒp_top.norm, hf.hasCompactSupport.norm⟩

theorem const_mul (c : 𝕜) : BoundedCompactSupport (fun x ↦ c * (f x)) where
  memℒp_top := hf.memℒp_top.const_mul ..
  hasCompactSupport := by
    suffices support (fun x ↦ c * (f x)) ⊆ support f from
      hf.hasCompactSupport.mono this
    exact support_mul_subset_right ..

theorem mul_const (c : 𝕜) : BoundedCompactSupport (fun x ↦ (f x) * c) := by
  simp_rw [mul_comm]; exact hf.const_mul _

end Includehf

section Includehfhg

include hf hg

theorem mul : BoundedCompactSupport (f * g) := mul_ess_bdd_right hf hg.memℒp_top.2 hg.memℒp_top.1

------ prove when needed
-- theorem add : BoundedCompactSupport (f + g) := sorry

end Includehfhg

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem mono {g : X → ℝ} (hg : BoundedCompactSupport g)
    (hf : AEStronglyMeasurable f)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f where
  memℒp_top := by
    refine hg.memℒp_top.mono hf ?_
    apply ae_of_all
    intro x
    refine trans (hfg x) ?_
    exact Real.le_norm_self (g x)
  hasCompactSupport := by
    refine hg.hasCompactSupport.mono ?_
    by_contra h
    simp only [support_subset_iff, ne_eq, mem_support, not_forall, Classical.not_imp,
      Decidable.not_not] at h
    obtain ⟨x, hfx, hgx⟩ := h
    specialize hfg x
    rw [hgx] at hfg
    exact hfx <| norm_le_zero_iff.mp hfg

theorem of_norm_le_const_mul [T2Space X] {g : X → ℝ} {M : ℝ} (hg : BoundedCompactSupport g)
    (hf : AEStronglyMeasurable f)
    (hfg : ∀ x, ‖f x‖ ≤ M * g x) : BoundedCompactSupport f :=
  BoundedCompactSupport.mono (hg.const_mul M) hf hfg

section Sum

variable {ι : Type*} {s : Finset ι} {F : ι → X → 𝕜}

/-- A finite sum of bounded compactly supported functions is bounded compactly supported. -/
theorem finset_sum
    (hF : ∀ i ∈ s, BoundedCompactSupport (F i)) :
    BoundedCompactSupport (fun x ↦ ∑ i ∈ s, F i x) where
  memℒp_top := memℒp_finset_sum s <| fun i hi ↦ (hF i hi).memℒp_top
  hasCompactSupport := by -- `HasCompactSupport.finset_sum` or so should be in mathlib?
    haveI : DecidableEq ι := Classical.decEq _
    revert hF
    refine Finset.induction_on s ?_ ?_
    · simp only [implies_true, Finset.sum_empty, hasCompactSupport_def,
        support_zero, closure_empty, isCompact_empty]
    · intro i s his ih hf
      simp only [his, Finset.sum_insert, not_false_iff]
      refine HasCompactSupport.add ?_ ?_
      · exact hf i (s.mem_insert_self i) |>.hasCompactSupport
      · exact ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)

end Sum

section Prod

variable {Y: Type*} [MeasureSpace Y] {g : Y → 𝕜}
variable [TopologicalSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
variable [SigmaFinite (volume : Measure Y)]

---- currently not used
-- /-- An elementary tensor of bounded compactly supported functions is
-- bounded compactly supported. -/
-- theorem prod_mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
--     BoundedCompactSupport (uncurry fun x y ↦ (f x) * (g y)) where
--   memℒp_top := by
--     have hm : AEStronglyMeasurable (uncurry fun x y ↦ (f x) * (g y)) := by
--       exact .mul (.fst hf.aestronglyMeasurable) (.snd hg.aestronglyMeasurable)
--     letI C := (eLpNorm f ⊤).toReal * (eLpNorm g ⊤).toReal
--     suffices ∀ᵐ z, ‖(uncurry fun x y ↦ (f x) * (g y)) z‖ ≤ C from memℒp_top_of_bound hm _ this
--     sorry
    -- have h₀ : ∀ᵐ x, ∀ᵐ y, ‖(uncurry fun x y ↦ (f x) * (g y)) (x, y)‖ ≤ C := by
    --   filter_upwards [hf.ae_le] with x hx
    --   filter_upwards [hg.ae_le] with y hy
    --   simp; simp only [C]
    --   gcongr
    -- let s := { z | ‖(uncurry fun x y ↦ (f x) * (g y)) z‖ ≤ C  }
    -- have := Measure.ae_prod_mem_iff_ae_ae_mem (s := s) (μ := (volume : Measure X))
    --         (ν := (volume : Measure Y)) ?_ |>.mpr h₀
    -- exact this
    -- have := hm.norm
  -- hasCompactSupport := sorry

variable {F : X × Y → 𝕜}

-- -- prove when needed
-- theorem swap (hF : BoundedCompactSupport F) : BoundedCompactSupport (F ∘ Prod.swap) :=
--   sorry

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

---- adapt and prove below when needed
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
