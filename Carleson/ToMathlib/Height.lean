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
theorem ENat.iSup_eq_zero {ι : Type*} (s : ι → ℕ∞) : iSup s = 0 ↔ ∀ i, s i = 0 := iSup_eq_bot


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

lemma RelSeries.eraseLast_last_rel_last {r : Rel α α} (p : RelSeries r) (h : 0 < p.length) :
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
    step := fun ⟨j, h⟩ => by
      convert p.step ⟨j+i.1, by omega⟩
      simp only [Nat.succ_eq_add_one, Fin.succ_mk]; omega }

@[simp]
lemma RelSeries.head_drop {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.drop i).head = p.toFun i := by simp [drop, head]

@[simp]
lemma RelSeries.last_drop {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.drop i).last = p.last := by simp [drop, last, Fin.last]; congr; omega

@[simp]
lemma RelSeries.last_singleton {r : Rel α α} (x : α) : (singleton r x).last = x :=
  by simp [singleton, last]

/--
Replaces the last element in a series. Essentially `p.eraseLast.snoc x`, but also works when
`p` is a singleton.
-/
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

lemma LTSeries.head_le_last [Preorder α] (p : LTSeries α) : p.head ≤ p.last :=
  LTSeries.monotone p (Fin.zero_le (Fin.last p.length))

lemma LTSeries.int_head_add_le_toFun (p : LTSeries ℤ) (i : Fin (p.length + 1)) : p.head + i ≤ p i := by
  have ⟨i, hi⟩ := i
  simp only
  induction i with
  | zero => simp [RelSeries.head]
  | succ i ih =>
    suffices p.head + i < p.toFun ⟨i + 1, hi⟩ by
      apply Int.le_of_lt_add_one
      simpa [← add_assoc]
    exact lt_of_le_of_lt (ih (by omega)) (p.step ⟨i, by omega⟩)

lemma LTSeries.int_head_add_len_le_last (p : LTSeries ℤ) : p.head + p.length ≤ p.last := by
  apply LTSeries.int_head_add_le_toFun

variable [Preorder α]

noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : {p : LTSeries α // p.last = a}), p.1.length

instance (a : α) : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩


lemma height_last_ge_length (p : LTSeries α) : p.length ≤ height p.last :=
  le_iSup (α := ℕ∞) (ι := {p' : LTSeries α // p'.last = p.last}) (f := fun p' =>↑p'.1.length) ⟨p, rfl⟩

lemma height_ge_index (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  height_last_ge_length (p.take i)

lemma height_eq_index_of_length_eq_last_height (p : LTSeries α) (h : p.length = height p.last) :
    ∀ (i : Fin (p.length + 1)), i = height (p i) := by
  suffices ∀ i, height (p i) ≤ i by
    apply_rules [le_antisymm, height_ge_index]
  intro i
  apply iSup_le
  intro ⟨p', hp'⟩
  simp only [Nat.cast_le]
  have hp'' := height_last_ge_length <| p'.smash (p.drop i) (by simpa)
  simp [← h] at hp''; clear h
  norm_cast at hp''
  omega


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
  suffices height x + 1 ≤ height y by
    obtain ⟨n, hfin : height y = n⟩ := Option.ne_none_iff_exists'.mp (LT.lt.ne_top hfin)
    revert hfin this
    cases height y <;> cases height x <;> simp_all;  norm_cast;  omega
  unfold height
  rw [ENat.isup_add]
  apply sSup_le_sSup
  rw [Set.range_subset_range_iff_exists_comp]
  use fun ⟨p, h⟩ => ⟨p.snoc y (h ▸ hxy), by simp⟩
  ext ⟨p, _hp⟩
  simp

/-- There exist a series ending in a element for any lenght up to the element’s height.  -/
lemma exists_series_of_le_height (a : α) {n : ℕ} (h : n ≤ height a) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n := by
  cases ha : height a with
  | top =>
    clear h
    rw [height, ENat.iSup_coe_eq_top, bddAbove_def] at ha
    push_neg at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by omega⟩) (by simp) (by simp; omega)
  | coe m =>
    rw [ha, Nat.cast_le] at h
    rw [height, ENat.iSup_eq_coe_iff'] at ha
    obtain ⟨⟨⟨p, hlast⟩, hlen⟩, _hmax⟩ := ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by omega⟩
    constructor
    · simp [hlast]
    . simp [hlen]; omega

/-- For an element of finite height there exists a series ending in that element of that height. -/
lemma exists_series_of_height_eq_coe (a : α) {n : ℕ} (h : height a = n) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n :=
  exists_series_of_le_height a (le_of_eq h.symm)

/--
The height of an elemnet is infinite if there exist series of arbitrary length ending in that
element.
-/
lemma height_eq_top_iff (x : α) :
    height x = ⊤ ↔ (∀ n, ∃ p : LTSeries α, p.last = x ∧ p.length = n) := by
  constructor
  · intro h n
    apply exists_series_of_le_height x (n := n)
    simp [h]
  · intro h
    rw [height, ENat.iSup_coe_eq_top, bddAbove_def]
    push_neg
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n+1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

/-- Another characterization of height, based on the supremum of the heights of elements below -/
lemma height_eq_isup_lt_height (x : α) :
    height x = ⨆ (y : α) (_  : y < x), height y + 1 := by
  unfold height
  simp_rw [ENat.isup_add]
  apply le_antisymm
  · apply iSup_le; intro ⟨p, hp⟩
    simp only
    cases hlen : p.length; simp; next n =>
    apply le_iSup_of_le p.eraseLast.last
    apply le_iSup_of_le (by rw [← hp]; apply RelSeries.eraseLast_last_rel_last _ (by omega))
    apply le_iSup_of_le ⟨p.eraseLast, rfl⟩
    simp [hlen]
  · apply iSup_le; intro y
    apply iSup_le; intro hyx
    apply iSup_le; intro ⟨p, hp⟩
    apply le_iSup_of_le ⟨p.snoc x (hp ▸ hyx), by simp⟩
    simp


lemma height_le_coe_iff (x : α) (n : ℕ) :
    height x ≤ n ↔ (∀ y, y < x → height y < n) := by
  conv_lhs => rw [height_eq_isup_lt_height]
  simp only [iSup_le_iff]
  congr! 2 with y _
  cases height y; simp; norm_cast

lemma height_eq_zero_iff (x : α) : height x = 0 ↔ (∀ y, ¬(y < x)) := by
  simpa using height_le_coe_iff x 0

lemma coe_lt_height_iff (x : α) (n : ℕ) (hfin : height x < ⊤):
    n < height x ↔ (∃ y, y < x ∧ height y = n) := by
  constructor
  · intro h
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp (LT.lt.ne_top hfin)
    rw [hx] at h; norm_num at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by omega⟩
    constructor
    · rw [←hp]
      apply LTSeries.strictMono
      simp [Fin.last]; omega
    · symm
      exact height_eq_index_of_length_eq_last_height p (by simp [hlen, hp, hx]) ⟨n, by omega⟩
  · intro ⟨y, hyx, hy⟩
    exact hy ▸ height_strictMono y x hyx hfin


lemma height_eq_coe_add_one_iff (x : α) (n : ℕ)  :
    height x = n + 1 ↔ height x < ⊤ ∧ (∃ y < x, height y = n) ∧ (∀ y, y < x → height y ≤ n) := by
  wlog hfin : height x < ⊤
  · simp_all
    exact ne_of_beq_false rfl
  simp only [hfin, true_and]
  trans (n < height x ∧ height x ≤ n + 1)
  · rw [le_antisymm_iff, and_comm]
    simp [hfin, ENat.lt_add_one_iff, ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff x n hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff x (n+1)

lemma height_eq_coe_iff (x : α) (n : ℕ) :
    height x = n ↔ height x < ⊤ ∧ (n = 0 ∨ ∃ y < x, height y = n - 1) ∧ (∀ y, y < x → height y < n) := by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp_all [height_eq_zero_iff x]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff x n]
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
  by_cases hfin : height a < ⊤
  · simp only [mem_minimals_iff_forall_lt_not_mem'', Set.mem_setOf_eq, not_le]
    simp only [height_eq_coe_iff, hfin, true_and, and_congr_left_iff]
    intro _
    cases n
    case pos.zero => simp
    case pos.succ _ =>
      simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
      simp only [ne_eq, ENat.coe_ne_top, not_false_eq_true, ENat.add_one_le_iff]
      simp only [coe_lt_height_iff, hfin]
      rfl
  · suffices ∃ x, ∃ (_ : x < a), ↑n ≤ height x by
      simp only [not_lt, top_le_iff] at hfin
      simpa only [mem_minimals_iff_forall_lt_not_mem'', Set.mem_setOf_eq, hfin, le_top, not_le,
        true_and, ENat.top_ne_coe, iff_false, not_forall, Classical.not_imp, not_lt]
    simp only [not_lt, top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n+1)
    use p.eraseLast.last, RelSeries.eraseLast_last_rel_last _ (by omega)
    simpa [hp] using height_last_ge_length p.eraseLast

-- Q: Should this be the definition and the other a lemma? Does it matter?
-- Q: What's a good name?
def Set.with_height (s : Set α) (n : ℕ) : Set α :=
  minimals (·≤·) (s \ ⋃ (n' < n), Set.with_height s n')

lemma Set.with_height_subset (s : Set α) (n : ℕ) : s.with_height n ⊆ s := by
  intro x; unfold Set.with_height minimals; intro ⟨⟨h,_⟩, _⟩; exact h

lemma subtype_mk_mem_minimals_iff (α : Type*) [Preorder α] (s : Set α) (t : Set s) (x : α)
    (hx : x ∈ s) : (⟨x, hx⟩:s) ∈ minimals (α := s) (·≤·) t ↔
      x ∈ minimals (·≤·) { y | ∃ h, y ∈ s ∧ ⟨y,h⟩ ∈ t} := by
  wlog hxt : (⟨x, hx⟩:s) ∈ t
  · clear this
    have := Set.not_mem_subset (minimals_subset (·≤·) t) hxt
    simp only [exists_and_left, false_iff, this]; clear this
    contrapose! hxt
    have := minimals_subset _ _ hxt
    simp_all
  rw [← map_mem_minimals_iff (f := fun (x : s) => (x : α)) (s := (·≤·))]
  case hf => simp
  case ha => assumption
  simp
  congr! 2
  ext y
  simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Set.mem_setOf_eq,
    iff_and_self, forall_exists_index]
  intros hy _; exact hy

/-- `Set.with_height s n` contains those elements of `s` that have height `n` in `s` -/
lemma Set.with_height_eq (s : Set α) (n : Nat) :
    s.with_height n = { x | ∃ hx : x ∈ s, height (⟨x, hx⟩ : s) = n } := by
  induction n using Nat.strongRec with | ind n ih =>
  ext x
  simp only [mem_setOf_eq]
  wlog hxs : x ∈ s
  · simp only [hxs, IsEmpty.exists_iff, iff_false]
    contrapose! hxs; exact Set.with_height_subset s n hxs
  simp only [hxs, exists_true_left]
  rw [Set.with_height]
  simp_rw [← mem_minimal_le_height_iff_height]
  simp (config := {contextual:=true}) [ih]; clear ih
  rw [subtype_mk_mem_minimals_iff]
  congr! 2
  ext y
  wlog hys : y ∈ s
  · simp [hys]
  simp only [mem_diff, hys, mem_iUnion, exists_prop, not_exists, not_and, true_and, mem_setOf_eq,
    exists_and_left, exists_true_left]
  cases height (⟨y, hys⟩:s)
  next => simp
  next z =>
    simp only [Nat.cast_inj, Nat.cast_le]
    -- no single tactic for goal `∀ x < n, ¬z = x) ↔ n ≤ z`?
    constructor
    · intro h; contrapose! h; simp [h]
    · intro h m hm; omega

/- Variant of Set.mem_with_height_iff' expressed on the subtype of `s`  -/
lemma Set.mem_with_height_iff' (s : Set α) (n : Nat) (x : s) :
    x.val ∈ s.with_height n ↔ height x = n := by
  simp [s.with_height_eq]

lemma Set.Disjoint_with_height (s : Set α) {n n'} (h : n ≠ n') :
    Disjoint (s.with_height n) (s.with_height n') := by
  wlog hl : n < n'
  · exact (this s h.symm (by omega)).symm
  rw [disjoint_right]; intro p hp hp'
  rw [Set.with_height_eq] at hp hp'
  aesop

lemma Set.PairwiseDisjointSet.with_heig_with_height (s : Set α) : univ.PairwiseDisjoint s.with_height :=
    fun _ _ _ _ => Disjoint_with_height s

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
  · intro ⟨l, _hln, hx⟩
    apply Set.with_height_subset _ _ hx
  · intro hx
    simp_rw [Set.mem_with_height_iff' s _ ⟨x, hx⟩]
    cases hh : height (⟨x, hx⟩ : s)
    case top =>
      exfalso
      have : (n + 1 : ℕ) ≤ height (⟨x, hx⟩ : s) := by simp [hh]
      obtain ⟨p, _hpast, hlen⟩ := exists_series_of_le_height _ this
      specialize hlength p
      omega
    case coe l =>
      use l
      obtain ⟨p, _hlast, hp⟩ := exists_series_of_height_eq_coe _  hh
      specialize hlength p
      constructor; omega; rfl

lemma Set.IsAntichain_with_height {α} [PartialOrder α] (s : Set α) (n : ℕ) :
    IsAntichain (·≤·) (s.with_height n) := by
  rw [with_height]
  apply minimals_antichain

lemma Set.exists_series_of_mem_with_height {s : Set α} {a : α} {n : ℕ} (h : a ∈ s.with_height n) :
  ∃ p : LTSeries s, p.last = a ∧ p.length = n := by
  rw [with_height_eq] at h
  obtain ⟨p, hlast, hp⟩ := exists_series_of_height_eq_coe _  h.2
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
