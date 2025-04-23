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

@[bound]
theorem enorm_sum_le [ENormedAddCommMonoid E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.le_sum_of_subadditive enorm enorm_zero enorm_add_le f

@[to_additive existing]
theorem enorm_prod_le [ENormedCommMonoid E] (s : Finset ι) (f : ι → E) :
    ‖∏ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ := by
  rw [← Multiplicative.ofAdd_le, ofAdd_sum]
  refine Finset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ enorm) ?_ (fun x y => ?_) _ _
  · simp [enorm_one', ofAdd_zero]
  · exact enorm_mul_le' x y

@[to_additive]
theorem enorm_prod_le_of_le [ENormedCommMonoid E] (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0∞}
      (h : ∀ b ∈ s, ‖f b‖ₑ ≤ n b) :
    ‖∏ b ∈ s, f b‖ₑ ≤ ∑ b ∈ s, n b :=
  (enorm_prod_le s f).trans <| Finset.sum_le_sum h

end ENormedMonoid
