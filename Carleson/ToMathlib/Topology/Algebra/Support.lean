import Mathlib.Topology.Algebra.Support

section DivisionMonoid

variable {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
variable {f f' : α → β}

/- PR after HasCompactMulSupport.inv' -/

@[to_additive]
theorem HasCompactMulSupport.div (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f / f') := hf.comp₂_left hf' (div_one 1)

end DivisionMonoid
