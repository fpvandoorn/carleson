/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Joachim Breitner
-/
import Carleson.ToMathlib.Height

/-!
# Minimal and maximal layers of a set

This file defines `Set.minLayer` and `Set.maxLayer` as the sets obtained from iterated application
of `minimals`/`maximals` on a set, excluding earlier layers.

## Main declarations

* `Set.minLayer` (`Set.maxLayer`): The `n`th minimal (maximal) layer of the given set `A`.
* `Set.pairwiseDisjoint_minLayer` (`Set.pairwiseDisjoint_maxLayer`),
  `Set.isAntichain_minLayer` (`Set.isAntichain_maxLayer`):
  minimal (maximal) layers are pairwise disjoint antichains.
* `Set.iUnion_minLayer_iff_bounded_series`: if the length of `LTSeries` in `A` is bounded,
  `A` equals the union of its `minLayer`s up to `n`.
-/

namespace Set

variable {α : Type*} [PartialOrder α]

/-- The `n`th minimal layer of `A`. -/
def minLayer (A : Set α) (n : ℕ) : Set α :=
  {a | Minimal (· ∈ A \ ⋃ (k < n), A.minLayer k) a}

/-- The `n`th maximal layer of `A`. -/
def maxLayer (A : Set α) (n : ℕ) : Set α :=
  A.minLayer (α := αᵒᵈ) n

/-- The elements above `A`'s `n` minimal layers. -/
def layersAbove (A : Set α) (n : ℕ) : Set α :=
  A \ ⋃ (k ≤ n), A.minLayer k

/-- The elements below `A`'s `n` maximal layers. -/
def layersBelow (A : Set α) (n : ℕ) : Set α :=
  A \ ⋃ (k ≤ n), A.maxLayer k

variable {A : Set α} {m n : ℕ} {a : α}

lemma maxLayer_def : A.maxLayer n = {a | Maximal (· ∈ A \ ⋃ (k < n), A.maxLayer k) a} := by
  rw [maxLayer, minLayer]; rfl

lemma minLayer_subset : A.minLayer n ⊆ A :=
  calc
    _ ⊆ A \ ⋃ (k < n), A.minLayer k := by
      rw [minLayer]; refine fun _ h ↦ ?_; rw [mem_setOf] at h; exact h.prop
    _ ⊆ A := diff_subset

lemma maxLayer_subset : A.maxLayer n ⊆ A := minLayer_subset

lemma layersAbove_subset : A.layersAbove n ⊆ A := diff_subset

lemma layersBelow_subset : A.layersBelow n ⊆ A := diff_subset

lemma minLayer_zero : A.minLayer 0 = {a | Minimal (· ∈ A) a} := by rw [minLayer]; simp

lemma maxLayer_zero : A.maxLayer 0 = {a | Maximal (· ∈ A) a} := by rw [maxLayer_def]; simp

lemma disjoint_minLayer_of_ne (h : m ≠ n) : Disjoint (A.minLayer m) (A.minLayer n) := by
  wlog hl : m < n generalizing m n; · exact (this h.symm (by omega)).symm
  rw [disjoint_right]; intro p hp
  rw [minLayer] at hp; replace hp := hp.1.2; contrapose! hp
  exact mem_iUnion₂_of_mem hl hp

lemma disjoint_maxLayer_of_ne (h : m ≠ n) : Disjoint (A.maxLayer m) (A.maxLayer n) :=
  disjoint_minLayer_of_ne h

lemma pairwiseDisjoint_minLayer : univ.PairwiseDisjoint A.minLayer := fun _ _ _ _ ↦
  disjoint_minLayer_of_ne

lemma pairwiseDisjoint_maxLayer : univ.PairwiseDisjoint A.maxLayer := fun _ _ _ _ ↦
  disjoint_minLayer_of_ne

lemma isAntichain_minLayer : IsAntichain (· ≤ ·) (A.minLayer n) := by
  rw [minLayer]; apply setOf_minimal_antichain

lemma isAntichain_maxLayer : IsAntichain (· ≤ ·) (A.maxLayer n) := by
  rw [maxLayer_def]; apply setOf_maximal_antichain

lemma exists_le_in_minLayer_of_le (ha : a ∈ A.minLayer n) (hm : m ≤ n) :
    ∃ c ∈ A.minLayer m, c ≤ a := by
  induction n, hm using Nat.le_induction generalizing a with
  | base => use a
  | succ n _ ih =>
    have nma : a ∉ A.minLayer n :=
      disjoint_right.mp (disjoint_minLayer_of_ne (by omega)) ha
    rw [minLayer, mem_setOf, minimal_iff] at ha nma
    have al : a ∈ A \ ⋃ (l < n), A.minLayer l := by
      refine (diff_subset_diff_right (biUnion_subset_biUnion_left fun k hk ↦ ?_)) ha.1
      rw [mem_def, Nat.le_eq] at hk ⊢; omega
    simp_rw [al, true_and] at nma; push_neg at nma; obtain ⟨a', ha', la⟩ := nma
    have ma' : a' ∈ A.minLayer n := by
      by_contra h
      have a'l : a' ∈ A \ ⋃ (l < n + 1), A.minLayer l := by
        have : ∀ l, l < n + 1 ↔ l < n ∨ l = n := by omega
        simp_rw [this, iUnion_or, iUnion_union_distrib]
        simp only [iUnion_iUnion_eq_left, mem_diff, mem_union, mem_iUnion, exists_prop, not_or,
          not_exists, not_and] at ha' ⊢
        tauto
      exact absurd (ha.2 a'l la.1) (ne_eq _ _ ▸ la.2)
    obtain ⟨c, mc, lc⟩ := ih ma'; use c, mc, lc.trans la.1

lemma exists_le_in_maxLayer_of_le (ha : a ∈ A.maxLayer n) (hm : m ≤ n) :
    ∃ c ∈ A.maxLayer m, a ≤ c := exists_le_in_minLayer_of_le (α := αᵒᵈ) ha hm

/-- `A.minLayer n` comprises exactly `A`'s elements of height `n`. -/
lemma minLayer_eq_setOf_height : A.minLayer n = {x | ∃ hx : x ∈ A, height (⟨x, hx⟩ : A) = n} := by
  induction n using Nat.strongRec with
  | ind n ih =>
    ext x
    simp only [mem_setOf_eq]
    wlog hxs : x ∈ A
    · simp only [hxs, IsEmpty.exists_iff, iff_false]
      contrapose! hxs; exact minLayer_subset hxs
    simp only [hxs, exists_true_left]
    rw [minLayer]
    simp_rw [← mem_minimal_le_height_iff_height]
    simp (config := {contextual := true}) only [ih]; clear ih
    have : Minimal (n ≤ height ·) (⟨x, hxs⟩ : A) ↔
        Minimal (· ∈ {y | n ≤ height y}) (⟨x, hxs⟩ : A) := Eq.to_iff rfl
    rw [this, subtype_mk_minimal_iff, mem_setOf]
    congr! 2 with y
    wlog hys : y ∈ A
    · simp [hys]
    simp only [mem_diff, hys, mem_iUnion, exists_prop, not_exists, not_and, true_and, mem_setOf_eq,
      exists_and_left, exists_true_left]
    cases height (⟨y, hys⟩ : A)
    · simp
    · simp only [Nat.cast_inj, Nat.cast_le]
      exact ⟨fun h ↦ by contrapose! h; simp [h], fun h m hm ↦ by omega⟩

/-- `A` equals the union of its `minLayer`s up to `n` iff
all `LTSeries` in `A` have length at most `n`. -/
lemma iUnion_minLayer_iff_bounded_series :
    ⋃ (k ≤ n), A.minLayer k = A ↔ ∀ p : LTSeries A, p.length ≤ n := by
  refine ⟨fun h p ↦ ?_, fun hlength ↦ ?_⟩
  · have hx : p.last.1 ∈ ⋃ (k ≤ n), A.minLayer k := h.symm ▸ p.last.2
    simp only [minLayer_eq_setOf_height, mem_iUnion, mem_setOf_eq, Subtype.coe_eta,
      Subtype.coe_prop, exists_const, exists_prop] at hx
    obtain ⟨i, hix, hi⟩ := hx
    have hh := height_last_ge_length p
    rw [hi, Nat.cast_le] at hh
    exact hh.trans hix
  · ext x
    simp only [minLayer_eq_setOf_height, mem_iUnion, mem_setOf_eq, exists_prop]
    wlog hxs : x ∈ A; · simp [hxs]
    simp only [hxs, exists_true_left, iff_true]
    suffices height (⟨x, hxs⟩ : A) ≤ n by
      revert this
      cases height (⟨x, hxs⟩ : A) <;> simp
    exact iSup_le fun _ ↦ by simp [hlength]

open Classical

variable [Fintype α]

lemma exists_le_in_layersAbove_of_le (ha : a ∈ A.layersAbove n) (hm : m ≤ n) :
    ∃ c ∈ A.minLayer m, c ≤ a := by
  have ma : a ∈ A \ ⋃ (l' < n), A.minLayer l' := by
    refine mem_of_mem_of_subset ha (diff_subset_diff_right ?_)
    refine biUnion_subset_biUnion_left fun k hk ↦ ?_
    rw [mem_def, Nat.le_eq] at hk ⊢; omega
  let C : Finset α :=
    (A.toFinset \ (Finset.range n).biUnion fun l ↦ (A.minLayer l).toFinset).filter (· ≤ a)
  have Cn : C.Nonempty := by
    use a
    simp_rw [C, Finset.mem_filter, le_rfl, and_true, Finset.mem_sdiff,
      Finset.mem_biUnion, Finset.mem_range, not_exists, not_and, mem_toFinset]
    simp_rw [mem_diff, mem_iUnion, exists_prop, not_exists, not_and] at ma
    exact ma
  obtain ⟨a', ma', mina'⟩ := C.exists_minimal Cn
  simp_rw [C, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, not_exists,
    not_and, mem_toFinset] at ma' mina'
  conv at mina' => enter [x]; rw [and_imp]
  have ma'₁ : a' ∈ A.minLayer n := by
    rw [minLayer, mem_setOf, minimal_iff]
    simp_rw [mem_diff, mem_iUnion, exists_prop, not_exists, not_and]
    exact ⟨ma'.1, fun y hy ly ↦ (eq_of_le_of_not_lt ly (mina' y hy (ly.trans ma'.2))).symm⟩
  obtain ⟨c, mc, lc⟩ := exists_le_in_minLayer_of_le ma'₁ hm
  use c, mc, lc.trans ma'.2

lemma exists_le_in_layersBelow_of_le (ha : a ∈ A.layersBelow n) (hm : m ≤ n) :
    ∃ c ∈ A.maxLayer m, a ≤ c := exists_le_in_layersAbove_of_le (α := αᵒᵈ) ha hm

end Set
