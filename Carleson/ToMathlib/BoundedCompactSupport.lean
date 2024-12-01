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

This makes it reasonable to bundle these three properties and prove basic properties.

-/

-- File has `sorry`s but all sorrys are easy

namespace MeasureTheory

open Bornology Set HasCompactSupport

variable {X 𝕜: Type*} [MeasureSpace X] [RCLike 𝕜] {f : X → 𝕜}
variable [TopologicalSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]

variable (f) in
-- carefully make this a typeclass?
class BoundedCompactSupport : Prop where
  bounded : IsBounded (range f)
  compact_support : HasCompactSupport f
  measurable : AEStronglyMeasurable f

namespace BoundedCompactSupport

variable {f : X → 𝕜}
variable {g : X → 𝕜}

-- parameter `hf` explicit
theorem integrable (hf : BoundedCompactSupport f) : Integrable f := by
  exact memℒp_one_iff_integrable.mp <| hf.2.memℒp_of_isBounded hf.1 hf.3

theorem mul_bdd
    (hf : BoundedCompactSupport f) (hg : IsBounded (range g)) :
    BoundedCompactSupport (f * g) := sorry

theorem integrable_mul
    (hf : BoundedCompactSupport f) (hg : Integrable g) : Integrable (f * g) := by
  sorry -- doesn't need `hf.compact_support`

section PotentialDanger?

instance [BoundedCompactSupport f] [BoundedCompactSupport g] :
    BoundedCompactSupport (f + g) := sorry

instance [hf : BoundedCompactSupport f] [hg : BoundedCompactSupport g]  :
    BoundedCompactSupport (f * g) := mul_bdd hf hg.bounded

-- generalize to other types than `𝕜`
instance [BoundedCompactSupport f] (c : 𝕜) :
    BoundedCompactSupport (c • f) := sorry

variable [BoundedCompactSupport f]
#synth BoundedCompactSupport ((5:𝕜)•f+f*f)

example : Integrable ((5:𝕜)•f+f*f) := BoundedCompactSupport.integrable (by infer_instance)

-- would be nice if this could work:
--variable {hg : IsBounded (range g)}
--#synth BoundedCompactSupport (f*g)

-- one could make `IsBounded` a typeclass too, and measurable and HasCompactSupport, ..
namespace Experimental

variable (f) in
class IsBounded : Prop where
  intro : Bornology.IsBounded (range f)

instance [BoundedCompactSupport f] [IsBounded g] :
    BoundedCompactSupport (f * g) := sorry

-- now this works
variable [IsBounded g]
#synth BoundedCompactSupport (f*g)

end Experimental

-- instance for fiberwise integral

end PotentialDanger?

end BoundedCompactSupport

end MeasureTheory
