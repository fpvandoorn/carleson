import Mathlib.Data.Set.Lattice
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic.Common

-- Upstreaming status: results seem useful in general, some should be generalised

open Function Order Set

namespace Set

variable {α : Type*} {a b c : α}

section Preorder

variable [Preorder α]

theorem Ico_subset_Ici (h : c ≤ a) : Ico a b ⊆ Ici c :=
  (Ico_subset_Ico_left h).trans Ico_subset_Ici_self

theorem Icc_subset_Ici (h : c ≤ a) : Icc a b ⊆ Ici c :=
  (Icc_subset_Icc_left h).trans Icc_subset_Ici_self

theorem Ioc_subset_Ioi (h : c ≤ a) : Ioc a b ⊆ Ioi c :=
  (Ioc_subset_Ioc_left h).trans Ioc_subset_Ioi_self

theorem Ioo_subset_Ioi (h : c ≤ a) : Ioo a b ⊆ Ioi c :=
  (Ioo_subset_Ioo_left h).trans Ioo_subset_Ioi_self

end Preorder

section LinearOrder

variable [LinearOrder α]

-- TODO: can or should these lemmas take a more general indexing type?
theorem iUnion_Ico_eq_Ici {f : ℕ → α} (hf : ∀ n, f 0 ≤ f n) (h2f : ¬BddAbove (range f)) :
    ⋃ (i : Nat), Ico (f i) (f (i+1)) = Ici (f 0) := by
  apply subset_antisymm
  · exact iUnion_subset fun i ↦ Ico_subset_Ici (hf i)
  · intro a ha
    by_contra! hcontra
    simp only [mem_iUnion, mem_Ico, not_exists, not_and, not_lt] at hcontra
    exact h2f ⟨a, forall_mem_range.mpr (Nat.rec ha fun i ih ↦ hcontra i ih)⟩

theorem iUnion_Ioc_eq_Ioi {f : ℕ → α} (hf : ∀ n, f 0 ≤ f n) (h2f : ¬BddAbove (range f)) :
    ⋃ (i : Nat), Ioc (f i) (f (i+1)) = Ioi (f 0) := by
  apply subset_antisymm
  · exact iUnion_subset fun i ↦ Ioc_subset_Ioi (hf i)
  · intro a ha
    by_contra! hcontra
    simp only [mem_iUnion, mem_Ioc, not_exists, not_and, not_le] at hcontra
    apply h2f ⟨a, forall_mem_range.mpr (fun i ↦ le_of_lt ?_)⟩
    exact Nat.rec ha (fun x ih ↦ hcontra x ih) i

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]

theorem pairwise_disjoint_Ico_monotone {f : ι → α} (hf : Monotone f) :
    Pairwise (Function.onFun Disjoint fun (i : ι) => Ico (f i) (f (Order.succ i))) := by
  intro i j hij
  wlog h : i < j with H
  · exact (H hf hij.symm (hij.lt_or_gt.resolve_left h)).symm
  exact disjoint_left.mpr fun _a hai haj ↦
    not_le.mpr (hai.2.trans_le (hf (Order.succ_le_of_lt h))) haj.1

theorem pairwise_disjoint_Ioc_monotone {f : ι → α} (hf : Monotone f) :
    Pairwise (Function.onFun Disjoint fun (i : ι) ↦ Ioc (f i) (f (Order.succ i))) := by
  intro i j hij
  wlog h : i < j with H
  · exact (H hf hij.symm (hij.lt_or_gt.resolve_left h)).symm
  exact disjoint_left.mpr fun _a hai haj ↦
    not_lt.mpr (hai.2.trans (hf (Order.succ_le_of_lt h))) haj.1

end LinearOrder

end Set
