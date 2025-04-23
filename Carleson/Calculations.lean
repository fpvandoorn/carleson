/-
This is a file for arithmetical lemmas -
lemmas that don't depend on any of Carleson's project definitions, or, really,
on any fancy definitions period.

Roughly speaking, if a lemma is in this file, it should be purely calculational/arithmetical,
e.g. `lemma calculation_1 : 2 + 2 = 4`.
All lemmas are prepended with a prefix `calculation_`.
-/
import Carleson.Defs
import Mathlib.Tactic.Rify
open ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

lemma calculation_1 (s : ℤ) :
    4 * (D : ℝ) ^ (-2 : ℝ) * D ^ (s + 3) = 4 * D ^ (s + 1) := by
  have D_pos : (0 : ℝ) < D := defaultD_pos a
  calc 4 * (D : ℝ) ^ (-2 : ℝ) * D ^ (s + 3)
  _ = 4 * (D ^ (-2 : ℝ) * D ^ (s + 3)) := by
    ring
  _ = 4 * D ^ (-2 + (s + 3)) := by
    congr
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-2)) (z := (s + 3)) D_pos
    rw_mod_cast [pow_th]
  _ = 4 * D ^ (s + 1) := by
    ring_nf

lemma calculation_2 (s : ℤ) :
    ((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s + 3) = 8⁻¹ * D ^ s := by
  have D_pos : (0 : ℝ) < D := defaultD_pos a
  calc (8 : ℝ)⁻¹ * (D : ℝ) ^ (-3 : ℝ) * D ^ (s + 3)
  _ = (8 : ℝ)⁻¹ * (D ^ (-3 : ℝ) * D ^ (s + 3)) := by
    ring
  _ = (8 : ℝ)⁻¹ * D ^ (-3 + (s + 3)) := by
    congr
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-3)) (z := (s + 3)) D_pos
    rw_mod_cast [pow_th]
  _ = (8 : ℝ)⁻¹ * D ^ s := by
    norm_num

lemma calculation_10 (h: (100 : ℝ) < D) :
    ((100 : ℝ) + 4 * D ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (-1 : ℝ) < 2 := by
  calc ((100 : ℝ) + 4 * D ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (-1 : ℝ)
  _ = (100 : ℝ) * D ^ (-1 : ℝ) + 4 * D ^ (-2 : ℝ) * D ^ (-1 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ) * D ^ (-1 : ℝ) := by
    ring
  _ = (100 : ℝ) * D ^ (-1 : ℝ) + 4 * D ^ (-3 : ℝ) + 8⁻¹ * D ^ (-4 : ℝ) := by
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

lemma calculation_3 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {x y : ℤ} (h: x + 3 < y) :
    100 * D ^ (x + 3) + ((4 * D ^ (-2 : ℝ)) * D ^ (x + 3)) + (((8 : ℝ)⁻¹ * D ^ (-3 : ℝ)) * D ^ (x + 3)) + 8 * D ^ y < 10 * D ^ y := by
  rw [← show (2 : ℝ) + 8 = 10 by norm_num, right_distrib]
  gcongr
  rw [← distrib_three_right ..]
  calc (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (x + 3)
  _ ≤ (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (y - 1) := by
    have h1 : x + 3 ≤ y - 1 := by omega
    gcongr
    linarith [four_le_realD X]
  _ = (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * (D ^ (y) * D ^ (- 1 : ℝ)) := by
    congr
    exact_mod_cast Real.rpow_add (y := y) (z:= (-1)) (hx := defaultD_pos a)
  _ < 2 * D ^ y := by
    nth_rw 4 [mul_comm ..]
    rw [← mul_assoc ..]
    have D_pos : (0 : ℝ) < D := defaultD_pos a
    gcongr
    exact calculation_10 (hundred_lt_realD X)

lemma calculation_4 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    {s_1 s_2 s_3 : ℤ} {dist_a dist_b dist_c dist_d : ℝ}
    (lt_1 : dist_a < 100 * D ^ (s_1 + 3))
    (lt_2 : dist_b < 8 * D ^ s_3)
    (lt_3 : dist_c < 8⁻¹ * D ^ s_1)
    (lt_4 : dist_d < 4 * D ^ s_2)
    (three : s_1 + 3 < s_3) (plusOne : s_2 = s_1 + 1) :
    dist_a + dist_d + dist_c + dist_b < 10 * D ^ s_3 := by
  calc dist_a + dist_d + dist_c + dist_b
  _ ≤ 100 * D ^ (s_1 + 3) + dist_d + dist_c + dist_b := by
    change dist_a < 100 * D ^ (s_1 + 3) at lt_1
    gcongr
  _ ≤ 100 * D ^ (s_1 + 3) + 4 * D ^ (s_1 + 1) + dist_c + dist_b := by
    gcongr
    apply le_of_lt
    rw [← plusOne]
    exact lt_4
  _ ≤ 100 * D ^ (s_1 + 3) + 4 * D ^ (s_1 + 1) + 8⁻¹ * D ^ s_1 + dist_b := by
    gcongr
  _ ≤ 100 * D ^ (s_1 + 3) + 4 * D ^ (s_1 + 1) + 8⁻¹ * D ^ s_1 + 8 * D ^ s_3 := by
    gcongr
  _ = 100 * D ^ (s_1 + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (s_1 + 3)) + 8⁻¹ * D ^ s_1 + 8 * D ^ s_3 := by
    rw [calculation_1 (s := s_1)]
  _ = 100 * D ^ (s_1 + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (s_1 + 3)) + (((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s_1 + 3)) + 8 * D ^ s_3 := by
    rw [calculation_2 (s := s_1)]
  _ < 10 * D ^ s_3 := by
    exact calculation_3 (h := three) (X := X)

lemma calculation_logD_64 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    Real.logb D 64 < 1 := by
  apply (Real.logb_lt_iff_lt_rpow (by linarith [hundred_lt_realD X]) (by linarith)).mpr
  rw [Real.rpow_one]
  linarith [hundred_lt_realD X]

lemma calculation_5 {dist_1 dist_2: ℝ}
    (h : dist_1 ≤ (2 ^ (a : ℝ)) ^ (6 : ℝ) * dist_2) :
    2 ^ ((-100 : ℝ) * a) * dist_1 ≤ 2 ^ ((-94 : ℝ) * a) * dist_2 := by
  apply (mul_le_mul_left (show 0 < (2 : ℝ) ^ (100 * (a : ℝ)) by positivity)).mp
  rw [
    ← mul_assoc,
    neg_mul,
    Real.rpow_neg (by positivity),
    mul_inv_cancel₀ (a := (2 : ℝ) ^ (100 * (a : ℝ))) (by positivity),
    ← mul_assoc,
    ← Real.rpow_add (by positivity)
  ]
  ring_nf
  rw [Real.rpow_mul (x := (2 : ℝ)) (hx:=by positivity) (y := a) (z := 6)]
  exact_mod_cast h

lemma calculation_6 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s : ℤ) :
    (D : ℝ) ^ (s + 3) = (D : ℝ) ^ (s + 2) * (D : ℝ) := by
  rw [
    zpow_add₀ (by linarith [defaultD_pos a]) s 3,
    zpow_add₀ (by linarith [defaultD_pos a]) s 2,
    mul_assoc
  ]
  congr

lemma calculation_7 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s : ℤ) :
    100 * (D ^ (s + 2) * D) = (defaultA a) ^ (100 * a) * (100 * (D : ℝ) ^ (s + 2)) := by
  rw [← mul_assoc (a := 100), mul_comm]
  congr
  norm_cast
  rw [← pow_mul 2 a (100 * a), mul_comm (a := a), defaultD]
  ring

lemma calculation_8 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {dist_1 dist_2 : ℝ}
    (h : dist_1 * 2 ^ ((100 : ℝ) * a) ≤ dist_2) :
    dist_1 ≤ 2 ^ ((-100 : ℝ) * a) * dist_2 := by
  rw [neg_mul, Real.rpow_neg (by positivity), mul_comm (a := (2 ^ (100 * (a : ℝ)))⁻¹)]
  apply (le_mul_inv_iff₀ (by positivity)).mpr
  exact h

lemma calculation_9 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    (h: 1 ≤ (2 : ℝ) ^ (-(94 : ℝ) * a)) :
    False := by
  apply (show 94 * a ≥ 376 ∧ 94 * a < 376 → False by intros h1; linarith)
  constructor
  · exact Nat.mul_le_mul_left 94 (four_le_a X)
  rify
  suffices 0 ≤ -94 * (a : ℝ) by linarith
  apply (Real.rpow_le_rpow_left_iff (x := 2) (by linarith)).mp
  linarith

lemma calculation_11 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s : ℤ) :
    100 * (D : ℝ) ^ (s + 2) + 4 * D ^ (s + 1) < 128 * D^(s + 2) := by
  rw [show (128 : ℝ) = 100 + 28 by norm_num]
  rw [right_distrib]
  gcongr
  · linarith
  · exact one_lt_D (X := X)
  · linarith

lemma calculation_12 (s : ℝ) :
    128 * (D : ℝ)^(s + 2) = 2^(200 * a ^ 2 + 4) * (8 * D ^ s) := by
  simp only [defaultD]
  have leftSide := calc 128 * ((2 : ℝ) ^ (100 * a ^ 2)) ^ (s + 2)
    _ = 128 * 2^(100 * a^2 * (s + 2)) := by
      congrm 128 * ?_
      have fact := Real.rpow_mul (x := 2) (y := 100 * a ^ 2) (z := s + 2) (by positivity)
      rw_mod_cast [fact]
    _ = 128 * 2^((100 * a^2 * s) + (100 * a^2 * 2)) := by
      congrm 128 * (2 ^ ?_)
      ring
    _ = (2 ^ 7) * 2^((100 * a^2 * s) + (100 * a^2 * 2)) := by
      norm_num
    _ = 2 ^ (7 + ((100 * a^2 * s) + (100 * a^2 * 2))) := by
      have fact := Real.rpow_add (x := 2) (y := 7) (z := 100 * a^2 * s + 100 * a^2 * 2) (by positivity)
      rw_mod_cast [fact]
  have rightSide := calc 2 ^ (200 * a ^ 2 + 4) * (8 * ((2 : ℝ) ^ (100 * a ^ 2)) ^ s)
    _ = 2 ^ (200*a^2 + 4) * ((2^3)*((2 ^ (100 * a ^ 2)) ^ s)) := by
      norm_num
    _ = 2 ^ (200*a^2 + 4) * (  2^3 * 2 ^ (100 * a ^ 2 * s)  ) := by
      rw [Real.rpow_mul (x:=2) (by positivity)]
      norm_cast
    _ = 2 ^ (200*a^2 + 4) * 2 ^ (3 + 100 * a ^ 2 * s) := by
      have fact := Real.rpow_add (x:=2) (y:= 3) (z:= 100 * a ^ 2 * s) (by positivity)
      rw_mod_cast [fact]
    _ = 2 ^ (200*a^2 + 4  + (3 + 100 * a ^ 2 * s)) := by
      nth_rw 2 [Real.rpow_add]
      norm_cast
      positivity
    _ = 2 ^ (7 + ((100 * a^2 * s) + (100 * a^2 * 2))) := by
      congrm 2 ^ ?_
      linarith
  rw_mod_cast [leftSide]
  rw_mod_cast [rightSide]

lemma calculation_13 : (2 : ℝ) ^ (200 * (a^3) + 4*a) = (defaultA a) ^ (200*a^2 + 4) := by
  simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat]
  have fact := Real.rpow_mul (x := 2) (y := a) (z := 200 * a ^ 2 + 4) (by positivity)
  rw_mod_cast [← fact]
  ring

lemma calculation_14 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (n: ℕ) :
    (2 : ℝ) ^ ((Z : ℝ) * n / 2 - 201 * a ^ 3) ≤ 2 ^ ((Z : ℝ) * n / 2 - (200 * a ^ 3 + 4 * a)) := by
  gcongr
  · linarith
  rw [show 201 * (a : ℝ) ^ 3 = 200 * (a : ℝ) ^ 3 + a ^ 3 by ring]
  gcongr 200 * (a : ℝ) ^ 3 + ?_
  rw [show (a : ℝ) ^ 3 = a ^ 2 * a by ring]
  gcongr
  suffices 4 ^ 2 ≤ (a : ℝ) ^ 2 by linarith
  apply pow_le_pow_left₀ (ha := by linarith)
  exact_mod_cast four_le_a X

lemma calculation_15 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    (dist: ℝ) (zon : ℝ)
    (h : 2 ^ zon ≤ 2 ^ (200 * a ^ 3 + 4 * a) * dist) :
    2 ^ (zon - (200 * a^3 + 4*a)) ≤ dist := by
  rw [Real.rpow_sub (hx := by linarith)]
  rw [show dist = 2 ^ (200 * a ^ 3 + 4 * a) * dist / 2 ^ (200 * a ^ 3 + 4 * a) by simp]
  have := (div_le_div_iff_of_pos_right (c := 2 ^ (200 * a ^ 3 + 4 * a)) (hc := by positivity)).mpr h
  exact_mod_cast this

lemma calculation_16 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s: ℤ) :
    4 * (D : ℝ) ^ s < 100 * D ^ (s + 1) := by
  gcongr
  · linarith
  · exact one_lt_D (X := X)
  · linarith

lemma calculation_7_7_4 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {n : ℕ}:
  (1:ℝ) ≤ 2 ^ (Z * (n + 1)) - 4 := by
  rw [le_sub_iff_add_le]
  trans 2 ^ 3
  · norm_num
  apply pow_right_mono₀ (one_le_two)
  rw [← mul_one 3]
  have : 3 ≤ Z := by
    simp only [defaultZ]
    have := a_pos X
    trans 2 ^ 12
    · norm_num
    gcongr
    · norm_num
    omega
  exact Nat.mul_le_mul this (Nat.le_add_left 1 n)
