import Mathlib.Data.Set.Lattice
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic.Common

open Function Order Set

namespace Set

variable {α : Type*} {a b c : α}

section Preorder

variable [Preorder α]

theorem Ico_subset_Ici (h : c ≤ a): Ico a b ⊆ Ici c :=
  (Ico_subset_Ico_left h).trans Ico_subset_Ici_self

theorem Icc_subset_Ici (h : c ≤ a): Icc a b ⊆ Ici c :=
  (Icc_subset_Icc_left h).trans Icc_subset_Ici_self

theorem Ioc_subset_Ioi (h : c ≤ a): Ioc a b ⊆ Ioi c :=
  (Ioc_subset_Ioc_left h).trans Ioc_subset_Ioi_self

theorem Ioo_subset_Ioi (h : c ≤ a): Ioo a b ⊆ Ioi c :=
  (Ioo_subset_Ioo_left h).trans Ioo_subset_Ioi_self

end Preorder

section LinearOrder

variable [LinearOrder α]

theorem iUnion_Ico_eq_Ici {f : ℕ → α} (hf : ∀ n, f 0 ≤ f n) (h2f : ¬BddAbove (range f)) :
    ⋃ (i : Nat), Ico (f i) (f (i+1)) = Ici (f 0) := by
  apply subset_antisymm
  · exact iUnion_subset fun i ↦ Ico_subset_Ici (hf i)
  · intro a ha
    rw [mem_iUnion]
    by_contra! hcontra
    apply h2f
    rw [bddAbove_def]
    use a
    suffices ∀ i, f i ≤ a by simp [this]
    intro i
    induction i
    case zero => exact ha
    case succ i hind =>
      let this := hcontra i
      rw [mem_Ico, not_and, not_lt] at this
      exact this hind

theorem iUnion_Ioc_eq_Ioi {f : ℕ → α} (hf : ∀ n, f 0 ≤ f n) (h2f : ¬BddAbove (range f)) :
    ⋃ (i : Nat), Ioc (f i) (f (i+1)) = Ioi (f 0) := by
  apply subset_antisymm
  · exact iUnion_subset fun i ↦ Ioc_subset_Ioi (hf i)
  · intro a ha
    rw [mem_iUnion]
    by_contra! hcontra
    apply h2f
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

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]

theorem pairwise_disjoint_Ico_monotone {f : ι → α} (hf : Monotone f) :
    Pairwise (Function.onFun Disjoint fun (i : ι) => Ico (f i) (f (Order.succ i))) := by
  unfold Function.onFun
  simp_rw [Set.disjoint_iff]
  intro i j hinej
  wlog hij : i < j generalizing i j
  · rw [not_lt] at hij
    have := this hinej.symm (hij.lt_of_ne hinej.symm)
    rwa [inter_comm]
  intro a
  simp only [mem_empty_iff_false, mem_inter_iff, mem_Ico, imp_false, not_and, not_lt, and_imp]
  intro ha ha2 ha3
  have : ¬f j ≤ a := not_le.mpr (lt_of_lt_of_le ha2 (hf (SuccOrder.succ_le_of_lt hij)))
  contradiction

theorem pairwise_disjoint_Ioc_monotone {f : ι → α} (hf : Monotone f) :
    Pairwise (Function.onFun Disjoint fun (i : ι) => Ioc (f i) (f (Order.succ i))) := by
  unfold Function.onFun
  simp_rw [Set.disjoint_iff]
  intro i j hinej
  wlog hij : i < j generalizing i j
  · rw [not_lt] at hij
    have := this hinej.symm (hij.lt_of_ne hinej.symm)
    rwa [inter_comm]
  intro a
  simp only [mem_empty_iff_false, mem_inter_iff, mem_Ioc, imp_false, not_and, and_imp]
  intro ha ha2 ha3
  have : ¬f j < a := not_lt.mpr (le_trans ha2 (hf (SuccOrder.succ_le_of_lt hij)))
  contradiction

end LinearOrder

end Set
