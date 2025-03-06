import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Order.CompletePartialOrder

/-! ## `ENNReal` manipulation lemmas -/

open Function Set
open scoped NNReal

variable {α ι : Type*} {s : Set ι} {t : Finset α}

namespace ENNReal

lemma coe_biSup {f : ι → ℝ≥0} (hf : BddAbove (range f)) :
    ⨆ x ∈ s, f x = ⨆ x ∈ s, (f x : ℝ≥0∞) := by
  simp_rw [bddAbove_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hf
  rw [ENNReal.coe_iSup]
  · congr with x; rw [ENNReal.coe_iSup]
    apply Bornology.IsBounded.bddAbove
    simp_rw [Metric.isBounded_iff, mem_range, exists_prop, and_imp, forall_apply_eq_imp_iff,
      dist_self, forall_self_imp]
    use 0; simp
  · simp_rw [bddAbove_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    obtain ⟨K, hK⟩ := hf; use K; intro c
    exact ciSup_le' fun _ ↦ hK c

-- unused
lemma biSup_add_biSup {f g : ι → ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, f i + g j ≤ f k + g k) :
    (⨆ i ∈ s, f i) + ⨆ i ∈ s, g i = ⨆ i ∈ s, f i + g i := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  · refine le_antisymm ?_ (iSup₂_le fun a ma => add_le_add (le_biSup _ ma) (le_biSup _ ma))
    refine biSup_add_biSup_le hs hs fun i hi j hj => ?_
    obtain ⟨k, mk, hk⟩ := h i hi j hj
    exact hk.trans <| le_iSup₂_of_le k mk fun a za ↦ ⟨a, za, le_rfl⟩

-- unused
lemma finsetSum_biSup {f : α → ι → ℝ≥0∞}
    (hf : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ t, ⨆ i ∈ s, f a i = ⨆ i ∈ s, ∑ a ∈ t, f a i := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    exact biSup_add_biSup fun i hi j hj ↦ (hf i hi j hj).imp fun k hk ↦
      ⟨hk.1, add_le_add (hk.2 a).1 (Finset.sum_le_sum fun i a ↦ (hk.2 _).2)⟩

lemma biSup_add_le_add_biSup {f g : ι → ℝ≥0∞} :
    ⨆ i ∈ s, f i + g i ≤ (⨆ i ∈ s, f i) + ⨆ i ∈ s, g i :=
  iSup₂_le fun _ ma => add_le_add (le_biSup _ ma) (le_biSup _ ma)

lemma biSup_finsetSum_le_finsetSum_biSup {f : α → ι → ℝ≥0∞} :
    ⨆ i ∈ s, ∑ a ∈ t, f a i ≤ ∑ a ∈ t, ⨆ i ∈ s, f a i := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp only [Finset.sum_cons]
    exact biSup_add_le_add_biSup.trans (add_le_add_left ihs _)

variable {E : Type*} [SeminormedAddCommGroup E]

lemma edist_sum_le_sum_edist {f g : α → E} : edist (∑ i ∈ t, f i) (∑ i ∈ t, g i) ≤
    ∑ i ∈ t, edist (f i) (g i) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp only [Finset.sum_cons]
    exact (edist_add_add_le _ _ _ _).trans (add_le_add_left ihs _)

/-- The reverse triangle inequality for `enorm`. -/
lemma enorm_enorm_sub_enorm_le {x y : E} : ‖‖x‖ₑ - ‖y‖ₑ‖ₑ ≤ ‖x - y‖ₑ := by
  rw [enorm_eq_self, tsub_le_iff_right]; nth_rw 1 [← sub_add_cancel x y]
  exact enorm_add_le (x - y) y

variable (s) in
lemma exists_biSup_eq_enorm (f : ι → E) : ∃ x ∈ s, ⨆ z ∈ s, ‖f z‖ₑ = ‖f x‖ₑ := by
  sorry

variable (s) in
lemma exists_biInf_eq_enorm (f : ι → E) : ∃ x ∈ s, ⨅ z ∈ s, ‖f z‖ₑ = ‖f x‖ₑ := by
  sorry

end ENNReal

/-- Transfer an inequality over `ℝ` to one of `ENorm`s over `ℝ≥0∞`. -/
lemma Real.enorm_le_enorm {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) : ‖x‖ₑ ≤ ‖y‖ₑ := by
  rw [Real.enorm_of_nonneg hx, Real.enorm_of_nonneg (hx.trans hy)]
  exact ENNReal.ofReal_le_ofReal hy
