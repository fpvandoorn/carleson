import Mathlib.Order.LiminfLimsup

theorem Filter.iSup_liminf_le_liminf_iSup {α : Type*} {β : Type*} {ι : Sort*} [CompleteLattice α]
  {f : Filter β} {u : ι → β → α} :
    ⨆ (i : ι), Filter.liminf (u i) f ≤ Filter.liminf (fun b ↦ ⨆ (i : ι), u i b) f := by
  simp only [iSup_le_iff]
  intro i
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  gcongr with s hs b hb
  apply le_iSup (fun i ↦ u i b)
