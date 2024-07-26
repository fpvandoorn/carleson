/-
Copyright (c) 2024 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Mathlib.Order.RelSeries
import Mathlib.Order.WithBot
import Mathlib.Order.Height
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Lattice

/-!
This module contains a definition for the height of an element in a partial order
with assorted API.

This could replace the `height` definition in mathlib. I think it is preferrable,
due to the simpler construction and more precise type (the height cannot be -∞, even
though the `krullDim` could).
-/

/-
TODO
* An element of finite height n has a LTSeries ending in it of length n
* For an element of height n there exists a series of length n ending in it (this is almost all that's needed for the lemma that gives you a p' with s differing by at least n , and maybe allows to strengthen it to unblock Jeremy)
* A series of length n ends in an element of height at least n
* The element at position i of a series has height at least i
* Every series of length n ending in the element has at position I an element of height I
* The elements of height n are the minimal elements when removing elements of height <n. This lemma proves the recursive equation in the blueprint.
-/


lemma ENat.iSup_eq_coe_iff' {α : Type*} [Nonempty α] (f : α → ℕ∞) (n : Nat) :
  (⨆ x, f x = n) ↔ (∃ x, f x = n) ∧ (∀ y, f y ≤ n) := by
  sorry

lemma ENat.iSup_eq_coe_iff {α : Type*} [Nonempty α] (f : α → ℕ) (n : Nat) :
  (⨆ x, (f x : ℕ∞) = n) ↔ (∃ x, f x = n) ∧ (∀ y, f y ≤ n) := by
  simp [ENat.iSup_eq_coe_iff']

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


-- only true for finite height
lemma height_strictMono (x y : α) (hxy : x < y) (n : ℕ) (hfin : height y = n) :
    height x < height y := by
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


lemma height_eq_zero_iff_minimal (x : α) (n : ℕ) :
    height x = 0 ↔ (∀ y, ¬(y < x)) := by
  constructor
  · intro h y hyx
    have := h ▸ height_strictMono y x hyx n h
    -- this is silly
    revert this; cases height y <;> simp
  · intro h
    unfold height
    rw [ENat.iSup_eq_zero]
    intro ⟨p, hp⟩
    simp only
    cases hlen : p.length
    case zero => simp
    case succ m =>
      exfalso
      exact h p.eraseLast.last (by rw [←hp]; apply RelSeries.eraseLast_last_rel_last _ (by omega))

lemma height_eq_succ (x : α) (n : ℕ) :
    height x = n ↔ (∀ y, y < x → height y < n) := by
  constructor
  · intro h y hyx
    exact h ▸ height_strictMono y x hyx n h
  · intro h
    unfold height
    rw [ENat.iSup_eq_coe_iff]
    constructor
    · cases n
      case zero =>
        use ⟨RelSeries.singleton _ _, rfl⟩
        rfl
      case succ n =>
        by_cases (∃ y, y < x ∧ height y = n)
        next h' =>
          clear h
          obtain ⟨y, hyx, hy⟩ := h'
          obtain ⟨p, hp, hlen⟩ := exists_series_of_finite_height y hy
          use ⟨p.snoc x (hp ▸ hyx), by simp⟩
          simpa using hlen
        next h' =>
          push_neg at h'
          sorry
    · intro ⟨p, hp⟩
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

#exit


lemma height_eq_succ_iff (x : α) (n : ℕ) :
    height x = n + 1 ↔ ((∃ y < x, height y = n) ∧ (∀ y, y < x → height y ≤ n)) := by
  sorry

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

-- This is from mathlib, but has too strict requirements, PartialOrder is too strong, Preorder suffices
theorem mem_minimals_iff_forall_lt_not_mem'' {x : α} {s : Set α} :
    x ∈ minimals (· ≤ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, y < x → y ∉ s :=
  mem_minimals_iff_forall_lt_not_mem' (· < ·)

lemma mem_minimal_univ_iff_height_eq_zero (a : α) :
    a ∈ minimals (·≤·) Set.univ ↔ height a = 0 := by
  simp [mem_minimals_iff_forall_lt_not_mem'', height_eq_zero_iff]

lemma mem_minimal_le_height_iff_height (a : α) (n : ℕ):
    a ∈ minimals (·≤·) { y | n ≤ height y } ↔ height a = n := by
  induction n generalizing a
  case zero =>
    simp only [Nat.cast_zero, zero_le, Set.setOf_true]
    exact mem_minimal_univ_iff_height_eq_zero a
  case succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    simp [mem_minimals_iff_forall_lt_not_mem'']
    wlog hle : n + 1≤ height a
    · simp [mem_minimals_iff_forall_lt_not_mem'', hle]
      contrapose! hle
      simp [hle]
    simp only [hle, true_and]
    simp only [height_eq_succ_iff]
    sorry





#exit

/-
noncomputable def height_in {α : Type*} [Preorder α] (s : Set α) (a : α) : ℕ∞ :=
  ⨆ (l ∈ s.subchain) (_ : l.getLast? = some a), l.length - 1




variable {α : Type*} [Preorder α]
variable (s : Set α)
variable (a : α)



lemma exists_subchain_of_finite_height (a : α) {n : ℕ} (h : height_in s a = n) :
    ∃ l ∈ s.subchain, l.getLast? = some a ∧ l.length = n + 1 := by
  unfold height_in at h
  rw [ENat.iSup_eq_coe_iff (s := s.subchain)] at h
-/
