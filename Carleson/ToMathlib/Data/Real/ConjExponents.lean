import Mathlib.Data.Real.ConjExponents

open scoped ENNReal

namespace ENNReal
namespace IsConjExponent

variable {p q : ℝ≥0∞} (h : p.IsConjExponent q)

section
include h

lemma conjExponent_toReal (hp : p ≠ ∞) (hq : q ≠ ∞) : p.toReal.IsConjExponent q.toReal := by
  constructor
  · rw [← ENNReal.ofReal_lt_iff_lt_toReal one_pos.le hp, ofReal_one]
    exact h.one_le.lt_of_ne (fun p_eq_1 ↦ hq (by simpa [p_eq_1] using h.conj_eq))
  · rw [← toReal_inv, ← toReal_inv, ← toReal_add, h.inv_add_inv_conj, ENNReal.toReal_eq_one_iff]
    · exact ENNReal.inv_ne_top.mpr h.ne_zero
    · exact ENNReal.inv_ne_top.mpr h.symm.ne_zero

end
end IsConjExponent
end ENNReal
