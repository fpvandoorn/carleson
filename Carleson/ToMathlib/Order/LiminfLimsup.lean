import Mathlib.Order.LiminfLimsup

theorem Filter.liminf_le_limsup' {α : Type*} {β : Type*} [CompleteLattice α]
    {f : Filter β} [NeBot f] {u : β → α}
    --(h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    --(h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    :
    liminf u f ≤ limsup u f := by
  apply limsInf_le_limsSup
  · isBoundedDefault
  · isBoundedDefault
