import Mathlib.Data.Real.ConjExponents

open scoped ENNReal

variable {p q : ℝ≥0∞} (h : p.HolderConjugate q)
include h

-- Upstreaming status: seems useful to have and good to go

protected lemma ENNReal.HolderConjugate.toReal_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) :
    p.toReal.HolderConjugate q.toReal where
  left_pos := toReal_pos (HolderConjugate.ne_zero p q) hp
  right_pos := toReal_pos (HolderConjugate.ne_zero q p) hq
  inv_add_inv_eq_inv := by
    rw [← toReal_inv, ← toReal_inv, ← toReal_add, h.inv_add_inv_eq_one, inv_one, toReal_one]
    -- TODO: add a positivity extension for HolderConjugate.ne_zero; can finiteness then do this?
    · exact ENNReal.inv_ne_top.mpr (HolderConjugate.ne_zero p q)
    · exact ENNReal.inv_ne_top.mpr (HolderConjugate.ne_zero q p)
