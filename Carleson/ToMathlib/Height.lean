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
* The element at position i of a series has height at least i
* Every series of length n ending in the element has at position I an element of height I
* A series of length n ends in an element of height at least n
* For an element of height n there exists a series of length n ending in it (this is almost all that's needed for the lemma that gives you a p' with s differing by at least n , and maybe allows to strengthen it to unblock Jeremy)
* The elements of height n are the minimal elements when removing elements of height <n. This lemma proves the recursive equation in the blueprint.
-/


lemma ENat.iSup_eq_coe_iff' {α : Type*} [Nonempty α] (f : α → ℕ∞) (n : Nat) :
  (⨆ x, f x = n) ↔ (∃ x, f x = n ∧ ∀ y, f y ≤ n) := by
  sorry

lemma ENat.iSup_eq_coe_iff {α : Type*} [Nonempty α] (f : α → ℕ) (n : Nat) :
  (⨆ x, (f x : ℕ∞) = n) ↔ (∃ x, f x = n ∧ ∀ y, f y ≤ n) := by
  simp [ENat.iSup_eq_coe_iff']

lemma ENat.iSup_mem_eq_coe_iff {α : Type*} (s : Set α) (f : α → ℕ∞) (n : Nat)
  (h : s.Nonempty) :
  (⨆ x ∈ s, f x = n) ↔ (∃ x ∈ s, f x = n ∧ ∀ y ∈ s, f y ≤ n) := by
  have : Nonempty α := ⟨h.choose⟩
  -- have : Nonempty (x ∈ s) := sorry
  simp [ENat.iSup_eq_coe_iff']
  sorry

variable {α : Type*} [Preorder α]

noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : {p : LTSeries α // p.last = a}), p.1.length

instance (a : α) : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩

lemma exists_series_of_finite_height (a : α) {n : ℕ} (h : height a = n) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n := by
  unfold height at h
  rw [ENat.iSup_eq_coe_iff'] at h
  obtain ⟨⟨p, hlast⟩, hlen, _hmax⟩ := h
  simp only [Nat.cast_inj] at hlen
  exact ⟨p, hlast, hlen⟩

lemma height_last_ge_length (p : LTSeries α) : p.length ≤ height p.last :=
  le_iSup (α := ℕ∞) (ι := {p' : LTSeries α // p'.last = p.last}) (f := fun p' =>↑p'.1.length) ⟨p, rfl⟩

def RelSeries.take {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r :=
  { length := i
    toFun := fun ⟨i, h⟩ => p.toFun ⟨i, by omega⟩
    step := fun ⟨i, h⟩ => p.step ⟨i, by omega⟩
  }

lemma height_ge_index (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  height_last_ge_length (p.take i)




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
