import Mathlib.Data.Nat.Defs
-- next line is just so that a linter doesn't fail because the file only has too basic imports
import Mathlib.MeasureTheory.Function.EssSup

namespace Nat

/-- Put close to `Nat.div_pow` -/
lemma le_pow_self {a : ℕ} (b : ℕ) (ha : 1 < a) : b ≤ a ^ b := by
  induction b with
  | zero => simp only [Nat.pow_zero, zero_le]
  | succ n IH =>
    calc
    n + 1 ≤ a ^ n + a ^ n := by
      apply add_le_add IH
      simpa only [Nat.one_pow] using Nat.pow_le_pow_left (le_of_lt ha) n
    _ = 2 * a ^ n := (Nat.two_mul (a ^ n)).symm
    _ ≤ a * a ^ n := Nat.mul_le_mul ha le_rfl
    _ = a ^ (n + 1) := pow_succ'.symm

end Nat
