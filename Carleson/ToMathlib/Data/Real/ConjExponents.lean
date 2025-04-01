import Mathlib.Data.Real.ConjExponents

open scoped ENNReal

variable {p q : ℝ≥0∞} (h : p.HolderConjugate q)
include h

protected lemma ENNReal.HolderConjugate.toReal_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) :
    p.toReal.HolderConjugate q.toReal where
  left_pos := toReal_pos (HolderConjugate.ne_zero p q) hp
  right_pos := toReal_pos (HolderConjugate.ne_zero q p) hq
  inv_add_inv' := by
    rw [← toReal_inv, ← toReal_inv, ← toReal_add, h.inv_add_inv_eq_one, inv_one, toReal_one]
    · exact ENNReal.inv_ne_top.mpr (HolderConjugate.ne_zero p q)
    · exact ENNReal.inv_ne_top.mpr (HolderConjugate.ne_zero q p)
