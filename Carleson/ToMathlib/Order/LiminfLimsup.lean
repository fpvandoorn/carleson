import Mathlib.Order.LiminfLimsup

-- Upstreaming status: seems like a useful lemma; no obvious clean-up opportunities

theorem Filter.iSup_liminf_le_liminf_iSup {α β : Type*} {ι : Sort*} [CompleteLattice α]
    {f : Filter β} {u : ι → β → α} :
    ⨆ (i : ι), Filter.liminf (u i) f ≤ Filter.liminf (fun b ↦ ⨆ (i : ι), u i b) f := by
  simp only [iSup_le_iff]
  intro i
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  gcongr with s hs b hb
  apply le_iSup (fun i ↦ u i b)

theorem Filter.limsup_le_limsup' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u v : β → α} (h : u ≤ᶠ[f] v) : Filter.limsup u f ≤ Filter.limsup v f :=
  Filter.limsup_le_limsup h

theorem Filter.limsup_le_of_le' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u : β → α} {a : α} (h : ∀ᶠ (n : β) in f, u n ≤ a) :
  Filter.limsup u f ≤ a := sInf_le h
