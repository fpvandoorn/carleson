import Mathlib.Analysis.Normed.Group.Basic

open scoped ENNReal

section ENormedMonoid

variable {ι E : Type*} [TopologicalSpace E]

theorem enorm_multiset_sum_le [ENormedAddCommMonoid E] (m : Multiset E) :
    ‖m.sum‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.le_sum_of_subadditive enorm enorm_zero enorm_add_le

@[to_additive existing]
theorem enorm_multiset_prod_le [ENormedCommMonoid E] (m : Multiset E) :
    ‖m.prod‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum := by
  rw [← Multiplicative.ofAdd_le, ofAdd_multiset_prod, Multiset.map_map]
  refine Multiset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ enorm) ?_ (fun x y => ?_) _
  · simp [enorm_one', ofAdd_zero]
  · exact enorm_mul_le' x y

end ENormedMonoid
