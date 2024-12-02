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

-- EXPERIMENTAL

# Bounded compactly supported measurable functions

Bounded compactly supported measurable functions are a very convenient class of functions:
it is contained in all `Lᵖ` spaces (in particular they are `Integrable`)
and it is closed under many common operations

Often it is enough to reason with bounded compactly supported functions (as done in the blueprint).
Here we provide helper lemmas mostly meant to streamline integrability proofs.

-/

namespace MeasureTheory

open Bornology Function Set HasCompactSupport
open scoped ENNReal

-- can generalize to vector-valued, but for this project scalar-valued should be enough
variable {X 𝕜} [MeasureSpace X] [RCLike 𝕜] {f : X → 𝕜}
variable [TopologicalSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]

variable (f) in
structure BoundedCompactSupport : Prop where
  bounded : IsBounded (range f)
  compact_support : HasCompactSupport f
  measurable : AEStronglyMeasurable f

namespace BoundedCompactSupport

variable {f : X → 𝕜}
variable {g : X → 𝕜}

variable (hf : BoundedCompactSupport f)
variable (hg : BoundedCompactSupport g)

section Includehf
/-! Results depending on `f` being bounded compactly supported. -/

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

end Includehf

section Includehfhg
/-! Results depending on `f` and `g` being bounded compactly supported. -/

include hf hg

theorem mul : BoundedCompactSupport (f * g) := mul_bdd hf hg.bounded

theorem add : BoundedCompactSupport (f + g) := sorry

theorem const_mul (c : 𝕜) : BoundedCompactSupport (fun x ↦ c * (f x)) := sorry

theorem mul_const (c : 𝕜) : BoundedCompactSupport (fun x ↦ (f x) * c) := sorry

end Includehfhg

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem of_norm_le {g : X → ℝ} (hg : BoundedCompactSupport g)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f := sorry

section Prod

variable {Y: Type*} [MeasureSpace Y] {g : Y → 𝕜}
variable [TopologicalSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]

/-- An elementary tensor of bounded compactly supported functions is
bounded compactly supported. -/
theorem prod_mul (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    BoundedCompactSupport (uncurry fun x y ↦ (f x) * (g y)) := sorry

end Prod

-- section PotentialDanger?

-- instance [BoundedCompactSupport f] [BoundedCompactSupport g] :
--     BoundedCompactSupport (f + g) := sorry

-- instance [hf : BoundedCompactSupport f] [hg : BoundedCompactSupport g]  :
--     BoundedCompactSupport (f * g) := mul_bdd hf hg.bounded

-- -- generalize to other types than `𝕜`
-- instance [BoundedCompactSupport f] (c : 𝕜) :
--     BoundedCompactSupport (c • f) := sorry

-- variable [BoundedCompactSupport f]
-- #synth BoundedCompactSupport ((5:𝕜)•f+f*f)

-- example : Integrable ((5:𝕜)•f+f*f) := BoundedCompactSupport.integrable (by infer_instance)

-- -- would be nice if this could work:
-- --variable {hg : IsBounded (range g)}
-- --#synth BoundedCompactSupport (f*g)

-- -- one could make `IsBounded` a typeclass too, and measurable and HasCompactSupport, ..
-- namespace Experimental

-- variable (f) in
-- class IsBounded : Prop where
--   intro : Bornology.IsBounded (range f)

-- instance [BoundedCompactSupport f] [IsBounded g] :
--     BoundedCompactSupport (f * g) := sorry

-- -- now this works
-- variable [IsBounded g]
-- #synth BoundedCompactSupport (f*g)

-- end Experimental

-- -- instance for fiberwise integral

-- end PotentialDanger?

end BoundedCompactSupport

end MeasureTheory
