/-
Copyright (c) 2024 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Mathlib.Order.RelSeries
import Mathlib.Order.WithBot
import Mathlib.Order.Height
import Mathlib.Order.Minimal
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Pairwise.Basic

/-!
This module contains a definition for the height of an element in a partial order
with assorted API.

This could replace the `height` definition in mathlib. I think it is preferrable,
due to the simpler construction and more precise type (the height cannot be -∞, even
though the `krullDim` could).

Some results found here:

* An element of finite height n has a LTSeries ending in it of length n
* For an element of finite height n there exists a series of length n ending in it
* A series of length n ends in an element of height at least n
* The element at position i of a series has height at least i
* Every series of length n ending in the element has at position i an element of height i
* The elements of height n are the minimal elements among those of height ≥n.
  This lemma proves the recursive equation in the blueprint.

It also defines `Set.with_height`, the subset of a set `s` of elements with given height in that
set. Some results

* the sets are disjoint antichains
* a recursive equation in terms of `minimals`
* if the length of ascending sequences in `s` is bounded, `s` is the union of these sets

-/

lemma ENat.iSup_eq_coe_iff' {α : Type*} [Nonempty α] (f : α → ℕ∞) (n : ℕ) :
    (⨆ x, f x = n) ↔ (∃ x, f x = n) ∧ (∀ y, f y ≤ n) := by
  sorry

lemma ENat.iSup_eq_coe_iff {α : Type*} [Nonempty α] (f : α → ℕ) (n : Nat) :
    (⨆ x, (f x : ℕ∞) = n) ↔ (∃ x, f x = n) ∧ (∀ y, f y ≤ n) := by
  simp [ENat.iSup_eq_coe_iff']

@[simp]
lemma ENat.not_lt_zero (n : ℕ∞) : ¬ n < 0 := by
  cases n <;> simp

@[simp]
lemma ENat.coe_lt_top (n : ℕ) : (n : ℕ∞) < ⊤ := by
  exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

theorem ENat.lt_add_one_iff (n m : ℕ∞) (hm : n ≠ ⊤) : m < n + 1 ↔ m ≤ n := by
  cases n <;> cases m <;> try contradiction
  · norm_num
  · norm_cast; omega

lemma ENat.isup_add (ι : Type*) [Nonempty ι] (f : ι → ℕ∞) (n : ℕ∞) :
    (⨆ x, f x) + n = (⨆ x, f x + n) := by
  cases n; simp; next n =>
  apply le_antisymm
  · apply le_iSup_iff.mpr
    intro m hm
    cases m; simp; next m =>
    have hnm : n ≤ m := by
      specialize hm Classical.ofNonempty
      revert hm
      cases f Classical.ofNonempty
      · simp
      · intro h; norm_cast at *; omega
    suffices (⨆ x, f x) ≤ ↑(m - n) by
      revert this
      generalize (⨆ x, f x) = k
      cases k
      · intro h; exfalso
        simp only [top_le_iff, coe_ne_top] at h
      · norm_cast; omega
    apply iSup_le
    intro i
    specialize hm i
    revert hm
    cases f i <;> intro hm
    · exfalso; simp at hm
    · norm_cast at *; omega
  · apply iSup_le
    intro i
    gcongr
    exact le_iSup f i


variable {α : Type*}

lemma RelSeries.eraseLast_last_rel_last {r : Rel α α} (p : RelSeries r) (h : p.length > 0) :
    r p.eraseLast.last p.last := by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert p.step ⟨p.length -1, by omega⟩
  simp; omega

def RelSeries.take {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r :=
  { length := i
    toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by omega⟩
    step := fun ⟨j, h⟩ => p.step ⟨j, by omega⟩
  }

@[simps]
def RelSeries.drop {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r :=
  { length := p.length - i
    toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by omega⟩
    step := fun ⟨j, h⟩ => by -- TODO: not pretty
      cases i with | _ i hi =>
      have := p.step ⟨j+i, by simp_all; omega⟩
      convert this
      simp; omega
  }

@[simp]
lemma RelSeries.head_drop {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.drop i).head = p.toFun i := by simp [drop, head]

@[simp]
lemma RelSeries.last_drop {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.drop i).last = p.last := by simp [drop, last, Fin.last]; congr; omega

def RelSeries.replaceLast {r : Rel α α} (trans : Transitive r) (p : RelSeries r) (x : α)
    (h : r p.last x) : RelSeries r :=
  if hlen : p.length = 0
  then singleton r x
  else p.eraseLast.snoc x (by
    apply trans
    · apply p.step ⟨p.length - 1, by omega⟩
    · convert h
      simp only [Fin.succ_mk, Nat.succ_eq_add_one, last, Fin.last]
      congr; omega)

@[simp]
lemma RelSeries.last_singleton {r : Rel α α} (x : α) : (singleton r x).last = x :=
  by simp [singleton, last]

def LTSeries.replaceLast [Preorder α] (p : LTSeries α) (x : α) (h : p.last ≤ x) :
    LTSeries α :=
  if hlen : p.length = 0
  then RelSeries.singleton _ x
  else p.eraseLast.snoc x (by
    apply lt_of_lt_of_le
    · apply p.step ⟨p.length - 1, by omega⟩
    · convert h
      simp only [Fin.succ_mk, Nat.succ_eq_add_one, RelSeries.last, Fin.last]
      congr; omega)

@[simp]
lemma LTSeries.last_replaceLast [Preorder α] (p : LTSeries α) (x : α) (h : p.last ≤ x) :
    (p.replaceLast x h).last = x := by
  unfold replaceLast; split <;> simp

@[simp]
lemma LTSeries.length_replaceLast [Preorder α] (p : LTSeries α) (x : α) (h : p.last ≤ x) :
    (p.replaceLast x h).length = p.length := by
  unfold replaceLast; split <;> (simp;omega)

lemma LTSeries.head_le_last [Preorder α] (p : LTSeries α) : p.head ≤ p.last := by
  sorry

lemma LTSeries.int_head_add_len_le_last (p : LTSeries ℤ) : p.head + p.length ≤ p.last := by
  sorry

variable [Preorder α]

noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : {p : LTSeries α // p.last = a}), p.1.length

instance (a : α) : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩

lemma exists_series_of_finite_height (a : α) {n : ℕ} (h : height a = n) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n := by
  unfold height at h
  rw [ENat.iSup_eq_coe_iff'] at h
  obtain ⟨⟨⟨p, hlast⟩, hlen⟩, _hmax⟩ := h
  simp only [Nat.cast_inj] at hlen
  exact ⟨p, hlast, hlen⟩

lemma height_last_ge_length (p : LTSeries α) : p.length ≤ height p.last :=
  le_iSup (α := ℕ∞) (ι := {p' : LTSeries α // p'.last = p.last}) (f := fun p' =>↑p'.1.length) ⟨p, rfl⟩

lemma height_ge_index (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  height_last_ge_length (p.take i)

@[simp]
theorem ENat.iSup_eq_zero {ι : Type*} (s : ι → ℕ∞) : iSup s = 0 ↔ ∀ i, s i = 0 := iSup_eq_bot

lemma height_mono : Monotone (α := α) height := by
  intro x y hxy
  apply sSup_le_sSup
  rw [Set.range_subset_range_iff_exists_comp]
  use fun ⟨p, h⟩ => ⟨p.replaceLast y (h ▸ hxy), by simp⟩
  ext ⟨p, hp⟩
  simp


-- only true for finite height
lemma height_strictMono (x y : α) (hxy : x < y) (hfin : height y < ⊤) :
    height x < height y := by
  obtain ⟨n, hfin : height y = n⟩ := Option.ne_none_iff_exists'.mp (LT.lt.ne_top hfin)
  suffices height x + 1 ≤ height y by
    revert hfin this
    cases height y <;> cases height x <;> simp_all;  norm_cast;  omega
  unfold height
  rw [ENat.isup_add]
  apply sSup_le_sSup
  rw [Set.range_subset_range_iff_exists_comp]
  use fun ⟨p, h⟩ => ⟨p.snoc y (h ▸ hxy), by simp⟩
  ext ⟨p, _hp⟩
  simp


lemma height_le_iff (x : α) (n : ℕ) :
    height x ≤ n ↔ (∀ y, y < x → height y < n) := by
  constructor
  · intro h y hyx
    refine lt_of_lt_of_le ?_ h
    apply height_strictMono y x hyx
    apply lt_of_le_of_lt h
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · intro h
    unfold height
    apply iSup_le
    intro ⟨p, hp⟩
    simp only
    cases hlen : p.length
    case zero => simp
    case succ m =>
      specialize h p.eraseLast.last (by rw [←hp]; apply RelSeries.eraseLast_last_rel_last _ (by omega))
      have h' := height_last_ge_length p.eraseLast
      have := lt_of_le_of_lt h' h
      simp at *
      norm_cast at *
      omega

lemma height_eq_zero_iff (x : α) : height x = 0 ↔ (∀ y, ¬(y < x)) := by
  simpa using height_le_iff x 0

lemma height_eq_index_of_length_eq_last_height (p : LTSeries α) (h : p.length = height p.last) :
    ∀ (i : Fin (p.length + 1)), i = height (p i) := by
  suffices ∀ i, height (p i) ≤ i by
    apply_rules [le_antisymm, height_ge_index]
  intro i
  apply iSup_le
  intro ⟨p', hp'⟩
  simp only [Nat.cast_le, ge_iff_le]
  have hp'' := height_last_ge_length <| p'.smash (p.drop i) (by simpa)
  simp [← h] at hp''; clear h
  norm_cast at hp''
  omega

lemma lt_height_iff (x : α) (n : ℕ) (hfin : height x < ⊤):
    n < height x ↔ (∃ y, y < x ∧ height y = n) := by
  constructor
  · intro h
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp (LT.lt.ne_top hfin)
    rw [hx] at h; norm_num at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_finite_height x hx
    use p ⟨n, by omega⟩
    constructor
    · rw [←hp]
      apply LTSeries.strictMono
      simp [Fin.last]; omega
    · symm
      exact height_eq_index_of_length_eq_last_height p (by simp [hlen, hp, hx]) ⟨n, by omega⟩
  · intro ⟨y, hyx, hy⟩
    exact hy ▸ height_strictMono y x hyx hfin

lemma height_eq_succ_iff (x : α) (n : ℕ)  :
    height x = n + 1 ↔ height x < ⊤ ∧ (∃ y < x, height y = n) ∧ (∀ y, y < x → height y ≤ n) := by
  wlog hfin : height x < ⊤
  · simp_all
    exact ne_of_beq_false rfl
  simp only [hfin, true_and]
  trans (n < height x ∧ height x ≤ n + 1)
  · rw [le_antisymm_iff, and_comm]
    simp [hfin, ENat.lt_add_one_iff, ENat.add_one_le_iff]
  · congr! 1
    · exact lt_height_iff x n hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_iff x (n+1)

lemma height_eq_iff (x : α) (n : ℕ) :
    height x = n ↔ height x < ⊤ ∧ (n = 0 ∨ ∃ y < x, height y = n - 1) ∧ (∀ y, y < x → height y < n) := by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp_all [height_eq_zero_iff x]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_succ_iff x n]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp ; norm_cast; omega


-- This is from mathlib, but has too strict requirements, PartialOrder is too strong, Preorder suffices
theorem mem_minimals_iff_forall_lt_not_mem'' {x : α} {s : Set α} :
    x ∈ minimals (· ≤ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, y < x → y ∉ s :=
  mem_minimals_iff_forall_lt_not_mem' (· < ·)

lemma mem_minimal_univ_iff_height_eq_zero (a : α) :
    a ∈ minimals (·≤·) Set.univ ↔ height a = 0 := by
  simp [mem_minimals_iff_forall_lt_not_mem'', height_eq_zero_iff]

lemma mem_minimal_le_height_iff_height (a : α) (n : ℕ) :
    a ∈ minimals (·≤·) { y | n ≤ height y } ↔ height a = n := by
  wlog hfin : height a < ⊤
  · simp only [not_lt, top_le_iff] at hfin
    -- have ha' : n < height a := by simp [hfin]
    simp only [mem_minimals_iff_forall_lt_not_mem'', Set.mem_setOf_eq, hfin, le_top, not_le,
      true_and, ENat.top_ne_coe, iff_false, not_forall, Classical.not_imp, not_lt]

    sorry
  have hfin : height a < ⊤ := by sorry
  simp only [mem_minimals_iff_forall_lt_not_mem'', Set.mem_setOf_eq, not_le]
  simp only [height_eq_iff, hfin, true_and, and_congr_left_iff]
  intro _
  cases n
  case zero => simp
  case succ _ =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    simp only [ne_eq, ENat.coe_ne_top, not_false_eq_true, ENat.add_one_le_iff]
    simp only [lt_height_iff, hfin]
    rfl

def Set.with_height (s : Set α) (n : ℕ) : Set α :=
  minimals (·≤·) (s \ ⋃ (n' < n), Set.with_height s n')

-- Q: Should this be the definition and the other a lemma? Does it matter?
-- Q: What's a good name?

/-- `Set.mem_with_height s n` contains those elements of `s` that have height `n` in `s` -/
lemma Set.mem_with_height_iff (s : Set α) (n : Nat) (x : α) :
    x ∈ s.with_height n ↔ ∃ (hx : x ∈ s), height (⟨x, hx⟩ : s) = n := by
-- induction n using Set.with_height.induct -- TODO: investigate this induction theorem bug?
  wlog hxs : x ∈ s
  · sorry
  simp only [hxs, exists_true_left]
  rw [Set.with_height]
  simp_rw [← mem_minimal_le_height_iff_height]
  simp [mem_minimals_iff_forall_lt_not_mem'', hxs]
  sorry

/- Variant of Set.mem_with_height_iff' expressed on the subtype of `s`  -/
lemma Set.mem_with_height_iff' (s : Set α) (n : Nat) (x : s) :
    x.val ∈ s.with_height n ↔ height x = n := by
  cases x; simp only [mem_with_height_iff, exists_true_left, *]

lemma Set.Disjoint_with_height (s : Set α) {n n'} (h : n ≠ n') :
    Disjoint (s.with_height n) (s.with_height n') := by
  wlog hl : n < n'
  · exact (this s h.symm (by omega)).symm
  rw [disjoint_right]; intro p hp hp'
  rw [Set.mem_with_height_iff] at hp hp'
  aesop

lemma Set.PairwiseDisjoint_with_height (s : Set α) : univ.PairwiseDisjoint s.with_height :=
    fun _ _ _ _ => Disjoint_with_height s

lemma Set.with_height_subset (s : Set α) (n : ℕ) : s.with_height n ⊆ s := by
  intro x
  rw [Set.mem_with_height_iff]
  tauto

/-
If all increasing series have lenght bounded by `n`, then `s` is the union of its elements with
height `≤ n`.

The precondition could also be expressed as `(hkrull : krullDim α < n)`.
-/
lemma Set.iUnion_with_height_of_bounded_series {s : Set α} {n : ℕ}
    (hlength : (p : LTSeries s) → p.length ≤ n) :
    (⋃ (l ≤ n), s.with_height l) = s := by
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro ⟨l, hln, hx⟩
    apply Set.with_height_subset _ _ hx
  · intro hx
    simp_rw [Set.mem_with_height_iff' s _ ⟨x, hx⟩]
    cases hh : height (⟨x, hx⟩ : s)
    next =>
      exfalso
      sorry -- if height is ⊤, then arbitrary long sequences exist
    next l =>
      use l
      obtain ⟨p, hlast, hp⟩ := exists_series_of_finite_height _  hh
      specialize hlength p
      constructor; omega; rfl

lemma Set.IsAntichain_with_height {α} [PartialOrder α] (s : Set α) (n : ℕ) :
    IsAntichain (·≤·) (s.with_height n) := by
  rw [with_height]
  apply minimals_antichain

lemma Set.exists_series_of_mem_with_height {s : Set α} {a : α} {n : ℕ} (h : a ∈ s.with_height n) :
  ∃ p : LTSeries s, p.last = a ∧ p.length = n := by
  rw [mem_with_height_iff] at h
  obtain ⟨p, hlast, hp⟩ := exists_series_of_finite_height _  h.2
  use p
  simp_all

/-- The dual of `Set.with_height`.  -/
def Set.with_coheight (s : Set α) (n : ℕ) : Set α :=
  maximals (·≤·) (s \ ⋃ (n' < n), Set.with_coheight s n')

-- TODO: Copy the API

lemma Set.IsAntichain_with_coheight {α} [PartialOrder α] (s : Set α) (n : ℕ) :
    IsAntichain (·≤·) (s.with_coheight n) := by
  rw [with_coheight]
  apply maximals_antichain
