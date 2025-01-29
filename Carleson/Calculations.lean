import Carleson.Defs
import Mathlib.Tactic.Rify

open ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

lemma calculation_1 (s : ℤ) : 4 * (D : ℝ) ^ (-2 : ℝ) * ↑D ^ (s + 3) = 4 * ↑D ^ (s + 1) := by
  have D_pos : (0 : ℝ) < D := defaultD_pos a
  calc 4 * (D : ℝ) ^ (-2 : ℝ) * ↑D ^ (s + 3)
  _ = 4 * (↑D ^ (-2 : ℝ) * ↑D ^ (s + 3)) := by
    ring
  _ = 4 * ↑D ^ (-2 + (s + 3)) := by
    congr
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-2)) (z := (s + 3)) D_pos
    rw_mod_cast [pow_th]
  _ = 4 * ↑D ^ (s + 1) := by
    ring_nf

lemma calculation_2 (s : ℤ) : ((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s + 3) = 8⁻¹ * ↑D ^ s := by
  have D_pos : (0 : ℝ) < D := defaultD_pos a
  calc (8 : ℝ)⁻¹ * (D : ℝ) ^ (-3 : ℝ) * ↑D ^ (s + 3)
  _ = (8 : ℝ)⁻¹ * (↑D ^ (-3 : ℝ) * ↑D ^ (s + 3)) := by
    ring
  _ = (8 : ℝ)⁻¹ * ↑D ^ (-3 + (s + 3)) := by
    congr
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-3)) (z := (s + 3)) D_pos
    rw_mod_cast [pow_th]
  _ = (8 : ℝ)⁻¹* ↑D ^ (s) := by
    norm_num

-- REFACTORED
theorem size_of_D (h: (100 : ℝ) < D) : ((100 : ℝ) + 4 * D ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (-1 : ℝ) < 2 := by
  calc ((100 : ℝ) + 4 * ↑D ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * ↑D ^ (-1 : ℝ)
  _ = (100 : ℝ) * ↑D ^ (-1 : ℝ) + 4 * ↑D ^ (-2 : ℝ) * ↑D ^ (-1 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ) * ↑D ^ (-1 : ℝ) := by
    ring
  _ = (100 : ℝ) * ↑D ^ (-1 : ℝ) + 4 * ↑D ^ (-3 : ℝ) + 8⁻¹ * ↑D ^ (-4 : ℝ) := by
    rw [mul_assoc, mul_assoc, ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
    congr <;> norm_num
  _ < (1 : ℝ) + 1 / 250 + 1 / 80000 := by
    have h1 : 100 * (D : ℝ) ^ (-1 : ℝ) < 1 := by
      nth_rw 2 [show (1 : ℝ) = 100 * 100 ^ (-1 : ℝ) by norm_num]
      gcongr 100 * ?_
      apply (Real.rpow_lt_rpow_iff_of_neg ..).mpr
      all_goals linarith
    have h2 : 4 * (D : ℝ) ^ (-3 : ℝ) < 1 / 250 := by
      rw [show (1 / 250 : ℝ) = 4 * ((10 : ℝ) ^ (-3 : ℝ)) by norm_num]
      gcongr 4 * ?_
      apply (Real.rpow_lt_rpow_iff_of_neg ..).mpr
      all_goals linarith
    have h3 : 8⁻¹ * (D : ℝ) ^ (-4 : ℝ) < 1 / 80000 := by
      rw [show (1 / 80000 : ℝ) = 8⁻¹ * ((10 : ℝ) ^ (-4 : ℝ)) by norm_num]
      gcongr 8⁻¹ * ?_
      apply (Real.rpow_lt_rpow_iff_of_neg ..).mpr
      all_goals linarith
    linarith
  _ < 2 := by
    norm_num

-- TODO
lemma calculation_3 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
  (xxx yyy : ℤ)
  (h: xxx + 3 < yyy) :
  100 * ↑D ^ (xxx + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (xxx + 3)) + (((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (xxx + 3)) + 8 * ↑D ^ yyy
  < 10 * ↑D ^ yyy := by
  have D_pos : (0 : ℝ) < D := by exact defaultD_pos a
  rw [← show (2 : ℝ) + 8 = 10 by norm_num, right_distrib]
  gcongr
  have D_big : (2 : ℝ) ≤ D := by linarith [twentyfive_le_realD X]

  have sss := distrib_three_right (100 : ℝ) (4 * D ^ (-2 : ℝ)) (8⁻¹ * D ^ (-3 : ℝ) : ℝ) (↑D ^ (xxx + 3))
  rw [← sss]

  calc (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * ↑D ^ (xxx + 3)
  _ ≤ (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * ↑D ^ (yyy - 1) := by
    have hi : xxx + 3 ≤ yyy - 1 := by omega
    gcongr
    linarith [D_big]
  _ = (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * (↑D ^ (yyy) * ↑D ^ (- 1 : ℝ)) := by
    congr
    have well : yyy - 1 = yyy + (- 1) := by rfl
    rw [well]
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (yyy)) (z:= (- 1)) D_pos
    norm_cast at pow_th
    norm_cast
  _ < 2 * ↑D ^ yyy := by
    nth_rw 4 [mul_comm]
    have well := mul_assoc (a:= (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ))) (b:= (D : ℝ) ^ (-1 : ℝ)) (c:= (D : ℝ) ^ yyy)
    rw [← well]
    gcongr
    exact size_of_D (hundred_lt_realD X)
