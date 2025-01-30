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
  have D_pos : (0 : ℝ) < D := defaultD_pos a
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

-- REFACTORED (though variable names are left)
lemma calculation_4 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
  {s_1 s_2 s_3: ℤ}
  {dist_a dist_b dist_c dist_d : ℝ}
  (xIn : dist_a < 100 * ↑D ^ (s_1 + 3))
  (xxx : dist_b < 8 * ↑D ^ s_3)
  (yyy : dist_c < 8⁻¹ * ↑D ^ s_1)
  (subset : dist_d < 4 * ↑D ^ s_2)
  (three : s_1 + 3 < s_3)
  (plusOne : s_2 = s_1 + 1)
  :
  dist_a + dist_d + dist_c + dist_b < 10 * ↑D ^ s_3 := by
  calc dist_a + dist_d + dist_c + dist_b
  _ ≤ 100 * ↑D ^ (s_1 + 3) + dist_d + dist_c + dist_b := by
    change dist_a < 100 * ↑D ^ (s_1 + 3) at xIn
    gcongr
  _ ≤ 100 * ↑D ^ (s_1 + 3) + 4 * ↑D ^ (s_1 + 1) + dist_c + dist_b := by
    gcongr
    apply le_of_lt
    rw [← plusOne]
    exact subset
  _ ≤ 100 * ↑D ^ (s_1 + 3) + 4 * ↑D ^ (s_1 + 1) + 8⁻¹ * ↑D ^ s_1 + dist_b := by
    gcongr
  _ ≤ 100 * ↑D ^ (s_1 + 3) + 4 * ↑D ^ (s_1 + 1) + 8⁻¹ * ↑D ^ s_1 + 8 * ↑D ^ s_3 := by
    gcongr
  _ = 100 * ↑D ^ (s_1 + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (s_1 + 3)) + 8⁻¹ * ↑D ^ s_1 + 8 * ↑D ^ s_3 := by
    rw [calculation_1 (s := s_1)]
  _ = 100 * ↑D ^ (s_1 + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (s_1 + 3)) + (((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s_1 + 3)) + 8 * ↑D ^ s_3 := by
    rw [calculation_2 (s := s_1)]
  _ < 10 * ↑D ^ s_3 := by
    exact calculation_3 (xxx := s_1) (yyy := s_3) (h := three) (X := X)

-- REFACTORED
lemma calculation_logD_64 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : Real.logb D 64 < 1 := by
  apply (Real.logb_lt_iff_lt_rpow (by linarith [hundred_lt_realD X]) (by linarith)).mpr
  rw [Real.rpow_one]
  linarith [hundred_lt_realD X]

-- REFACTORED
lemma calculation_5 {dist_1 dist_2: ℝ}
  (h : dist_1 ≤ (2^(a : ℝ))^(6 : ℝ) * dist_2)
  : 2^((-100 : ℝ) * a) * dist_1 ≤ 2 ^ ((-94 : ℝ) * a) * dist_2 := by
  apply (mul_le_mul_left (show 0 < (2 : ℝ) ^ (100 * (a : ℝ)) by positivity)).mp
  rw [
    ← mul_assoc,
    neg_mul,
    Real.rpow_neg (by positivity),
    LinearOrderedField.mul_inv_cancel (a:= (2 : ℝ) ^ (100 * (a : ℝ))) (by positivity),
    ← mul_assoc,
    ← Real.rpow_add (by positivity)
  ]
  ring_nf
  rw [Real.rpow_mul (x:= (2 : ℝ)) (hx:=by positivity) (y:=a) (z:= 6)]
  exact_mod_cast h

-- REFACTORED
lemma calculation_6 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
  (s : ℤ)
  : (D : ℝ) ^ (s + 3) = (D : ℝ) ^ (s + 2) * (D : ℝ) := by
  rw [
    zpow_add₀ (by linarith [defaultD_pos a]) s 3,
    zpow_add₀ (by linarith [defaultD_pos a]) s 2,
    mul_assoc
  ]
  congr

lemma calculation_7 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
  (s : ℤ)
  : 100 * (D ^ (s + 2) * D) = (defaultA a) ^ (100 * a) * (100 * (D : ℝ) ^ (s + 2)) := by
  rw [← mul_assoc (a:= 100), mul_comm]
  congr
  norm_cast
  rw [← pow_mul 2 a (100 * a), mul_comm (a:=a), defaultD]
  ring

lemma calculation_8 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
  {dist_1 dist_2 : ℝ}
  (h : dist_1 * 2 ^ ((100 : ℝ) * ↑a) ≤ dist_2)
  : dist_1 ≤ 2 ^ ((-100 : ℝ) * ↑a) * dist_2 := by
  rw [neg_mul, Real.rpow_neg (by positivity), mul_comm (a:=(2 ^ (100 * (a : ℝ)))⁻¹)]
  apply (le_mul_inv_iff₀ (by positivity)).mpr
  exact h

lemma calculation_9 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
  (h: 1 ≤ (2 : ℝ) ^ (-(94 : ℝ) * ↑a)) : False := by
  apply (show 94*a ≥ 376 ∧ 94*a < 376 → False by intros h1; linarith)
  constructor
  · exact Nat.mul_le_mul_left 94 (four_le_a X)
  rify
  suffices 0 ≤ -94 * (a : ℝ) by linarith
  apply (Real.rpow_le_rpow_left_iff (x := 2) (by linarith)).mp
  linarith
