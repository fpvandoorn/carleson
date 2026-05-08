import Mathlib.Order.LiminfLimsup

-- Upstreaming status: ready

theorem Filter.limsup_le_limsup' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u v : β → α} (h : u ≤ᶠ[f] v) : Filter.limsup u f ≤ Filter.limsup v f :=
  Filter.limsup_le_limsup h

theorem Filter.limsup_le_of_le' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u : β → α} {a : α} (h : ∀ᶠ (n : β) in f, u n ≤ a) :
  Filter.limsup u f ≤ a := sInf_le h
