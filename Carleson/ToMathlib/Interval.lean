-- I have no idea how to determine the correct imports...
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.WLOG

open Function Order Set

namespace Set

variable {α : Type*} {a b c : α}

section Preorder

variable [Preorder α]

theorem Ico_subset_Ici (h : c ≤ a): Ico a b ⊆ Ici c := by
  trans Ico c b
  . exact Ico_subset_Ico_left h
  . exact Ico_subset_Ici_self

theorem Ioc_subset_Ioi (h : c ≤ a): Ioc a b ⊆ Ioi c := by
  trans Ioc c b
  . exact Ioc_subset_Ioc_left h
  . exact Ioc_subset_Ioi_self

end Preorder

section LinearOrder

variable [LinearOrder α]

/- Statement can be optimised (or a variant) to also work if α has a maximum and f attains it (in particular : α is finite)
  Possibly also Nat can be relaxed to something weaker (Archimedean with bot?) but that seems more hassle than it's worth
-/
theorem iUnion_Ico_eq_Ici {f : ℕ → α} (hf : Monotone f) (h2f : ¬BddAbove (range f)) :
    ⋃ (i : Nat), Ico (f i) (f (i+1)) = Ici (f 0) := by
  apply subset_antisymm
  . apply iUnion_subset
    intro i
    apply Ico_subset_Ici
    apply hf
    exact Nat.zero_le i
  . intro a ha
    rw [Ici, mem_setOf] at ha
    rw [mem_iUnion]
    by_contra hcontra
    rw [not_exists] at hcontra
    suffices BddAbove (range f) by
      contradiction
    rw [bddAbove_def]
    use a
    suffices ∀ i, f i ≤ a by
      intro y hy
      obtain ⟨i, hi⟩ := hy
      rw [← hi]
      exact this i
    intro i
    induction i
    case zero => exact ha
    case succ i hind =>
      let this := hcontra i
      rw [mem_Ico, not_and, not_lt] at this
      exact this hind

theorem iUnion_Ioc_eq_Ioi {f : ℕ → α} (hf : Monotone f) (h2f : ¬BddAbove (range f)) :
    ⋃ (i : Nat), Ioc (f i) (f (i+1)) = Ioi (f 0) := by
  apply subset_antisymm
  . apply iUnion_subset
    intro i
    apply Ioc_subset_Ioi
    apply hf
    exact Nat.zero_le i
  . intro a ha
    rw [Ioi, mem_setOf] at ha
    rw [mem_iUnion]
    by_contra hcontra
    rw [not_exists] at hcontra
    suffices BddAbove (range f) by
      contradiction
    rw [bddAbove_def]
    use a
    suffices ∀ i, f i < a by
      intro y hy
      obtain ⟨i, hi⟩ := hy
      rw [← hi]
      exact le_of_lt (this i)
    intro i
    induction i
    case zero => exact ha
    case succ i hind =>
      let this := hcontra i
      rw [mem_Ioc, not_and, not_le] at this
      exact this hind

/-
Pairwise disjoint statements to above results. It also holds for Ioo; is that valuable?
-/
theorem pairwise_disjoint_Ico_monotone {f : ℕ → α} (hf : Monotone f) :
    Pairwise (Function.onFun Disjoint fun (i : ℕ) => Ico (f i) (f (i+1))) := by
  simp (config := { unfoldPartialApp := true }) only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro i j hinej
  wlog hij : i < j generalizing i j
  . rw [not_lt] at hij
    have := @this j i (Ne.symm hinej) (lt_of_le_of_ne hij (Ne.symm hinej))
    rw [inter_comm] at this
    exact this
  intro a
  simp only [mem_empty_iff_false, mem_inter_iff, mem_Ico, imp_false, not_and, not_lt, and_imp]
  intro ha ha2 ha3
  rw [← Nat.add_one_le_iff] at hij
  have : ¬f j ≤ a := not_le.mpr (lt_of_lt_of_le ha2 (hf hij))
  contradiction

theorem pairwise_disjoint_Ioc_monotone {f : ℕ → α} (hf : Monotone f) :
    Pairwise (Function.onFun Disjoint fun (i : ℕ) => Ioc (f i) (f (i+1))) := by
  simp (config := { unfoldPartialApp := true }) only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro i j hinej
  wlog hij : i < j generalizing i j
  . rw [not_lt] at hij
    have := @this j i (Ne.symm hinej) (lt_of_le_of_ne hij (Ne.symm hinej))
    rw [inter_comm] at this
    exact this
  intro a
  simp only [mem_empty_iff_false, mem_inter_iff, mem_Ioc, imp_false, not_and, not_lt, and_imp]
  intro ha ha2 ha3
  rw [← Nat.add_one_le_iff] at hij
  have : ¬f j < a := not_lt.mpr (le_trans ha2 (hf hij))
  contradiction

end LinearOrder
