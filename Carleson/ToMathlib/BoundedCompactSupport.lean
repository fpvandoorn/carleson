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

# Bounded compactly supported measurable functions

The purpose of this file is to provide helper lemmas to streamline proofs that
functions are bounded compactly supported and measurable.
Most functions we need to deal with are of this class.
Hopefully this will be a useful way to streamline proofs of `L^p` membership,
in particular integrability.

Todo: make `Mathlib.Tactic.FunProp` work for this

The `sorry`s in this file are supposed to be "easy".

-/

namespace MeasureTheory

open Bornology Function Set HasCompactSupport
open scoped ENNReal

-- Can generalize to vector-valued, but for this project scalar-valued should be enough
variable {X 𝕜} [MeasureSpace X] [RCLike 𝕜] {f : X → 𝕜}
variable [TopologicalSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]

variable (f) in
/-- Bounded compactly supported measurable functions -/
-- There are various alternative definitions one could use here
-- For now I used the formulations that were already used throughout `ForestOperator`
structure BoundedCompactSupport : Prop where
  bounded : IsBounded (range f)  -- could use a version of essential boundedness instead,
                                 -- e.g. `∃ M, ∀ᵐ x ∂μ, ‖f x‖ ≤ M`
  compact_support : HasCompactSupport f -- could use bounded support instead
  measurable : AEStronglyMeasurable f -- could use `Measurable` instead

-- Why is there no `IsEssBounded` predicate in mathlib?

-- /-- If `f` has bounded range, then it is bounded ae. -/
-- -- not currently used, but maybe in the future
-- lemma ae_bounded_of_isBounded_range [Nonempty X]
--     (μ : Measure X) (hf : IsBounded (range f)) : ∃ M, ∀ᵐ x ∂μ, ‖f x‖ ≤ M := by
--   obtain ⟨M, hM⟩ := Metric.isBounded_range_iff.mp hf
--   let x₀ : X := Classical.choice (by infer_instance)
--   use M+‖f x₀‖
--   apply ae_of_all
--   intro x
--   calc
--     _ = ‖f x - f x₀ + f x₀‖ := by group
--     _ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_add_le ..
--     _ ≤ _ := by gcongr; sorry -- fix broke after copy to this context: exact hM x x₀

-- in mathlib?
lemma isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by convert isBounded_iff_forall_norm_le; simp

namespace BoundedCompactSupport

variable {f : X → 𝕜}
variable {g : X → 𝕜}

variable (hf : BoundedCompactSupport f)
variable (hg : BoundedCompactSupport g)

section Includehf

include hf

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memℒp (p : ENNReal) : Memℒp f p := hf.2.memℒp_of_isBounded hf.1 hf.3

/-- Bounded compactly supported functions are integrable. -/
theorem integrable : Integrable f := memℒp_one_iff_integrable.mp <| memℒp hf 1

/-- A bounded compactly supported function times a bounded function is
bounded compactly supported. -/
theorem mul_bdd (hg : IsBounded (range g)) : BoundedCompactSupport (f * g) := sorry

theorem bdd_mul (hg : IsBounded (range g)) : BoundedCompactSupport (g * f) := by
  rw [mul_comm]; exact mul_bdd hf hg

#check Integrable.bdd_mul
-- for convenience
theorem integrable_mul (hg : Integrable g) : Integrable (f * g) := sorry

theorem conj : BoundedCompactSupport (star f) := sorry

theorem norm : BoundedCompactSupport (‖f ·‖) := sorry

theorem const_mul (c : 𝕜) : BoundedCompactSupport (fun x ↦ c * (f x)) := sorry

theorem mul_const (c : 𝕜) : BoundedCompactSupport (fun x ↦ (f x) * c) := sorry

end Includehf

section Includehfhg

include hf hg

theorem mul : BoundedCompactSupport (f * g) := mul_bdd hf hg.bounded

theorem add : BoundedCompactSupport (f + g) := sorry

end Includehfhg

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem of_norm_le {g : X → ℝ} (hg : BoundedCompactSupport g)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f := sorry

-- this is a very common use case, so it deserves its own theorem
theorem of_norm_le_const_mul {g : X → ℝ} {M : ℝ} (hg : BoundedCompactSupport g)
    (hfg : ∀ x, ‖f x‖ ≤ M * g x) : BoundedCompactSupport f := sorry

section Sum

variable {ι : Type*} {s : Finset ι} {F : ι → X → 𝕜}

/-- A finite sum of bounded compactly supported functions is bounded compactly supported. -/
theorem _root_.Finset.boundedCompactSupport_sum
    (hF : ∀ i ∈ s, BoundedCompactSupport (F i)) : BoundedCompactSupport (fun x ↦ ∑ i ∈ s, F i x) :=
  sorry

end Sum

section Prod

variable {Y: Type*} [MeasureSpace Y] {g : Y → 𝕜}
variable [TopologicalSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]

/-- An elementary tensor of bounded compactly supported functions is
bounded compactly supported. -/
theorem prod_mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (uncurry fun x y ↦ (f x) * (g y)) := sorry

end Prod

end BoundedCompactSupport

end MeasureTheory
