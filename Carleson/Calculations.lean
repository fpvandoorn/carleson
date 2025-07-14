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
open scoped NNReal ENNReal
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

lemma add_le_pow_two {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q r s : ℕ} (hp : p ≤ r) (hq : q ≤ r) (hr : r + 1 ≤ s) :
    (2 : R) ^ p + 2 ^ q ≤ 2 ^ s := by
  grw [hp, hq, ← mul_two, ← pow_succ, hr] <;> norm_num

lemma add_le_pow_two_add_cube {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q r : ℕ} (ha : 4 ≤ a) (hp : p ≤ r) (hq : q ≤ r) :
    (2 : R) ^ p + 2 ^ q ≤ 2 ^ (r + a ^ 3) := by
  apply add_le_pow_two hp hq
  have : 1 ≤ a ^ 3 := one_le_pow₀ (by linarith)
  linarith

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

lemma calculation_10 (h: (60 : ℝ) < D) :
    ((60 : ℝ) + 4 * D ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (-1 : ℝ) < 2 := by
  calc ((60 : ℝ) + 4 * D ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (-1 : ℝ)
  _ ≤ ((60 : ℝ) + 4 * 60 ^ (-2 : ℝ) + 8⁻¹ * 60 ^ (-3 : ℝ)) * 60 ^ (-1 : ℝ) := by
    gcongr (60 + 4 * ?_ + 8⁻¹ * ?_) * ?_ <;>
    apply Real.rpow_le_rpow_of_exponent_nonpos (by norm_num) h.le (by norm_num)
  _ < _ := by norm_num

lemma calculation_3 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {x y : ℤ} (h: x + 3 < y) :
    60 * D ^ (x + 3) + ((4 * D ^ (-2 : ℝ)) * D ^ (x + 3)) + (((8 : ℝ)⁻¹ * D ^ (-3 : ℝ)) * D ^ (x + 3)) + 8 * D ^ y < 10 * D ^ y := by
  rw [← show (2 : ℝ) + 8 = 10 by norm_num, right_distrib]
  gcongr
  rw [← distrib_three_right ..]
  calc (60 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (x + 3)
  _ ≤ (60 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (y - 1) := by
    have h1 : x + 3 ≤ y - 1 := by omega
    gcongr
    linarith [four_le_realD X]
  _ = (60 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * (D ^ (y) * D ^ (- 1 : ℝ)) := by
    congr
    exact_mod_cast Real.rpow_add (y := y) (z:= (-1)) (hx := defaultD_pos a)
  _ < 2 * D ^ y := by
    nth_rw 4 [mul_comm ..]
    rw [← mul_assoc ..]
    have D_pos : (0 : ℝ) < D := defaultD_pos a
    gcongr
    exact calculation_10 (by linarith [hundred_lt_realD X])

lemma calculation_4 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    {s_1 s_2 s_3 : ℤ} {dist_a dist_b dist_c dist_d : ℝ}
    (lt_1 : dist_a < 60 * D ^ (s_1 + 3))
    (lt_2 : dist_b < 8 * D ^ s_3)
    (lt_3 : dist_c < 8⁻¹ * D ^ s_1)
    (lt_4 : dist_d < 4 * D ^ s_2)
    (three : s_1 + 3 < s_3) (plusOne : s_2 = s_1 + 1) :
    dist_a + dist_d + dist_c + dist_b < 10 * D ^ s_3 := by
  calc dist_a + dist_d + dist_c + dist_b
  _ ≤ 60 * D ^ (s_1 + 3) + dist_d + dist_c + dist_b := by
    change dist_a < 60 * D ^ (s_1 + 3) at lt_1
    gcongr
  _ ≤ 60 * D ^ (s_1 + 3) + 4 * D ^ (s_1 + 1) + dist_c + dist_b := by
    gcongr
    apply le_of_lt
    rw [← plusOne]
    exact lt_4
  _ ≤ 60 * D ^ (s_1 + 3) + 4 * D ^ (s_1 + 1) + 8⁻¹ * D ^ s_1 + dist_b := by
    gcongr
  _ ≤ 60 * D ^ (s_1 + 3) + 4 * D ^ (s_1 + 1) + 8⁻¹ * D ^ s_1 + 8 * D ^ s_3 := by
    gcongr
  _ = 60 * D ^ (s_1 + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (s_1 + 3)) + 8⁻¹ * D ^ s_1 + 8 * D ^ s_3 := by
    rw [calculation_1 (s := s_1)]
  _ = 60 * D ^ (s_1 + 3) + ((4 * D ^ (- 2 : ℝ)) * D ^ (s_1 + 3)) + (((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s_1 + 3)) + 8 * D ^ s_3 := by
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
    2 ^ ((-CDN : ℝ) * a) * dist_1 ≤ 2 ^ ((-(CDN - 6) : ℝ) * a) * dist_2 := by
  apply (mul_le_mul_left (show 0 < (2 : ℝ) ^ (CDN * (a : ℝ)) by positivity)).mp
  rw [
    ← mul_assoc,
    neg_mul,
    Real.rpow_neg (by positivity),
    mul_inv_cancel₀ (a := (2 : ℝ) ^ (CDN * (a : ℝ))) (by positivity),
    ← mul_assoc,
    ← Real.rpow_add (by positivity)
  ]
  ring_nf
  rw [Real.rpow_mul (x := (2 : ℝ)) (hx:=by positivity) (y := a) (z := 6)]
  exact_mod_cast h

lemma calculation_6 (a : ℕ) (s : ℤ) :
    (D : ℝ) ^ (s + 3) = (D : ℝ) ^ (s + 2) * (D : ℝ) := by
  rw [
    zpow_add₀ (by linarith [defaultD_pos a]) s 3,
    zpow_add₀ (by linarith [defaultD_pos a]) s 2,
    mul_assoc
  ]
  congr

lemma calculation_7 (a : ℕ) (s : ℤ) :
    60 * (D ^ (s + 2) * D) = (defaultA a) ^ (CDN * a) * (60 * (D : ℝ) ^ (s + 2)) := by
  rw [← mul_assoc (a := 60), mul_comm]
  congr
  norm_cast
  rw [← pow_mul 2 a (CDN * a), mul_comm (a := a), defaultD]
  ring

lemma calculation_8 {dist_1 dist_2 : ℝ}
    (h : dist_1 * 2 ^ ((CDN : ℝ) * a) ≤ dist_2) :
    dist_1 ≤ 2 ^ ((-CDN : ℝ) * a) * dist_2 := by
  rw [neg_mul, Real.rpow_neg (by positivity), mul_comm (a := (2 ^ (CDN * (a : ℝ)))⁻¹)]
  apply (le_mul_inv_iff₀ (by positivity)).mpr
  exact h

lemma calculation_9 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    (h : 1 ≤ (2 : ℝ) ^ (-((CDN - 6) : ℝ) * a)) :
    False := by
  have : (2 : ℝ) ^ (-((CDN - 6) : ℝ) * a) < 1 ^ (-((CDN - 6) : ℝ) * a) := by
    apply Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num)
    have : (4 : ℝ) ≤ a := mod_cast four_le_a X
    simp only [CDN, Nat.cast_ofNat, neg_sub, gt_iff_lt]
    linarith
  simp at h this
  linarith

lemma calculation_11 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s : ℤ) :
    60 * (D : ℝ) ^ (s + 2) + 4 * D ^ (s + 1) < 128 * D^(s + 2) := by
  rw [show (128 : ℝ) = 60 + 68 by norm_num]
  rw [right_distrib]
  gcongr
  · linarith
  · exact one_lt_D (X := X)
  · linarith

lemma calculation_12 (s : ℝ) :
    128 * (D : ℝ)^(s + 2) = 2^(2 * CDN * a ^ 2 + 4) * (8 * D ^ s) := by
  simp only [defaultD]
  have leftSide := calc 128 * ((2 : ℝ) ^ (CDN * a ^ 2)) ^ (s + 2)
    _ = 128 * 2^(CDN * a^2 * (s + 2)) := by
      congrm 128 * ?_
      have fact := Real.rpow_mul (x := 2) (y := CDN * a ^ 2) (z := s + 2) (by positivity)
      rw_mod_cast [fact]
    _ = 128 * 2^((CDN * a^2 * s) + (CDN * a^2 * 2)) := by
      congrm 128 * (2 ^ ?_)
      ring
    _ = (2 ^ 7) * 2^((CDN * a^2 * s) + (CDN * a^2 * 2)) := by
      norm_num
    _ = 2 ^ (7 + ((CDN * a^2 * s) + (CDN * a^2 * 2))) := by
      have fact := Real.rpow_add (x := 2) (y := 7) (z := CDN * a^2 * s + CDN * a^2 * 2) (by positivity)
      rw_mod_cast [fact]
  have rightSide := calc 2 ^ (2 * CDN * a ^ 2 + 4) * (8 * ((2 : ℝ) ^ (CDN * a ^ 2)) ^ s)
    _ = 2 ^ (2 * CDN *a^2 + 4) * ((2^3)*((2 ^ (CDN * a ^ 2)) ^ s)) := by
      norm_num
    _ = 2 ^ (2 * CDN *a^2 + 4) * (  2^3 * 2 ^ (CDN * a ^ 2 * s)  ) := by
      rw [Real.rpow_mul (x:=2) (by positivity)]
      norm_cast
    _ = 2 ^ (2 * CDN * a^2 + 4) * 2 ^ (3 + CDN * a ^ 2 * s) := by
      have fact := Real.rpow_add (x:=2) (y:= 3) (z:= CDN * a ^ 2 * s) (by positivity)
      rw_mod_cast [fact]
    _ = 2 ^ (2 * CDN * a^2 + 4  + (3 + CDN * a ^ 2 * s)) := by
      nth_rw 2 [Real.rpow_add]
      norm_cast
      positivity
    _ = 2 ^ (7 + ((CDN * a^2 * s) + (CDN * a^2 * 2))) := by
      congrm 2 ^ ?_
      linarith
  rw_mod_cast [leftSide]
  rw_mod_cast [rightSide]

lemma calculation_13 : (2 : ℝ) ^ (2 * CDN * (a^3) + 4*a) = (defaultA a) ^ (2 * CDN *a^2 + 4) := by
  simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat]
  have fact := Real.rpow_mul (x := 2) (y := a) (z := 2 * CDN * a ^ 2 + 4) (by positivity)
  rw_mod_cast [← fact]
  ring

lemma calculation_14 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (n: ℕ) :
    (2 : ℝ) ^ ((Z : ℝ) * n / 2 - (2 * CDN + 1) * a ^ 3) ≤
      2 ^ ((Z : ℝ) * n / 2 - (2 * CDN * a ^ 3 + 4 * a)) := by
  gcongr
  · linarith
  rw [show (2 * CDN + 1) * (a : ℝ) ^ 3 = 2 * CDN * (a : ℝ) ^ 3 + a ^ 3 by ring]
  gcongr _ + ?_
  rw [show (a : ℝ) ^ 3 = a ^ 2 * a by ring]
  gcongr
  suffices 4 ^ 2 ≤ (a : ℝ) ^ 2 by linarith
  apply pow_le_pow_left₀ (ha := by linarith)
  exact_mod_cast four_le_a X

lemma calculation_15 {dist zon : ℝ}
    (h : 2 ^ zon ≤ 2 ^ (2 * CDN * a ^ 3 + 4 * a) * dist) :
    2 ^ (zon - (2 * CDN * a^3 + 4*a)) ≤ dist := by
  rw [Real.rpow_sub (hx := by linarith)]
  rw [show dist = 2 ^ (2 * CDN * a ^ 3 + 4 * a) * dist / 2 ^ (2 * CDN * a ^ 3 + 4 * a) by simp]
  have := (div_le_div_iff_of_pos_right (c := 2 ^ (2 * CDN * a ^ 3 + 4 * a))
    (hc := by positivity)).mpr h
  exact_mod_cast this

lemma calculation_16 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s: ℤ) :
    4 * (D : ℝ) ^ s < 60 * D ^ (s + 1) := by
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

/-- A bound on the sum of a geometric series whose ratio is close to 1. -/
lemma near_1_geometric_bound {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1 - 2 ^ (-t))⁻¹ ≤ 2 * (ENNReal.ofReal t)⁻¹ := by
  obtain ⟨lb, ub⟩ := ht
  rw [ENNReal.inv_le_iff_inv_le, ENNReal.mul_inv (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top),
    inv_inv, ← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ← ENNReal.ofReal_sub _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal; change t / 2 ≤ 1 - 2 ^ (-t)
  have bne := rpow_one_add_le_one_add_mul_self (show -1 ≤ -1 / 2 by norm_num) lb ub
  rw [show (1 : ℝ) + -1 / 2 = 2⁻¹ by norm_num, Real.inv_rpow zero_le_two,
    ← Real.rpow_neg zero_le_two] at bne
  linarith only [bne]

lemma calculation_convexity_bound [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∑ k ∈ Finset.range n, ((D : ENNReal) ^ (-t)) ^ k ≤ 2 * (ENNReal.ofReal t)⁻¹ := by
  have a4 := four_le_a X
  refine le_trans ?_ (near_1_geometric_bound ht)
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((2 : ENNReal) ^ (-t)) ^ k := by
      refine Finset.sum_le_sum fun k mk ↦ pow_le_pow_left' ?_ k
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
      refine ENNReal.rpow_le_rpow ?_ ht.1
      unfold defaultD
      norm_cast
      apply Nat.le_pow
      simp only [CDN, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      positivity
    _ ≤ ∑' k : ℕ, ((2 : ENNReal) ^ (-t)) ^ k := ENNReal.sum_le_tsum _
    _ = _ := ENNReal.tsum_geometric _

lemma calculation_7_6_2 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {n : ℕ} :
    ∑ k ∈ Finset.range n, ((D : ENNReal) ^ (-(κ / 2))) ^ k ≤ 2 ^ (10 * a + 2) :=
  calc
    _ ≤ 2 * (ENNReal.ofReal (κ / 2))⁻¹ := by
      apply calculation_convexity_bound (X := X)
      have := κ_nonneg (a := a)
      have := κ_le_one (a := a)
      rw [Set.mem_Icc]; constructor <;> linarith
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
        ENNReal.inv_div (.inl ENNReal.ofNat_ne_top) (.inl two_ne_zero), ← mul_div_assoc,
        ENNReal.div_eq_inv_mul, defaultκ, ← ENNReal.ofReal_rpow_of_pos zero_lt_two,
        ← ENNReal.inv_rpow, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul,
        show -1 * (-10 * (a : ℝ)) = (10 * a : ℕ) by simp, ENNReal.rpow_natCast, ← sq,
        ENNReal.ofReal_ofNat, ← pow_add]

lemma calculation_150 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    CDN * (3/2) * a ^ 2 * κ ≤ 1 := by
  rw [defaultκ, neg_mul, Real.rpow_neg zero_le_two]
  refine mul_inv_le_one_of_le₀ ?_ (by positivity); norm_cast
  rw [show 2 ^ (10 * a) = 2 ^ (8 * a) * (2 ^ a) ^ 2 by ring]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  · calc
      _ ≤ (2 : ℝ) ^ (8 * 4) := by simp [CDN]; norm_num
      _ ≤ _ := by gcongr; exacts [one_le_two, four_le_a X]
  · norm_cast
    exact Nat.lt_two_pow_self.le

lemma sq_le_two_pow_of_four_le (a4 : 4 ≤ a) : a ^ 2 ≤ 2 ^ a := by
  induction a, a4 using Nat.le_induction with
  | base => omega
  | succ a a4 ih =>
    rw [pow_succ 2, mul_two, add_sq, one_pow, mul_one, add_assoc]; gcongr
    calc
      _ ≤ 3 * a := by omega
      _ ≤ a * a := by gcongr; omega
      _ ≤ _ := by rwa [← sq]

lemma calculation_6_1_6 (a4 : 4 ≤ a) : 8 * a ^ 4 ≤ 2 ^ (2 * a + 3) := by
  calc
    _ = 2 ^ 3 * a ^ 2 * a ^ 2 := by ring
    _ ≤ 2 ^ 3 * 2 ^ a * 2 ^ a := by gcongr _ * ?_ * ?_ <;> exact sq_le_two_pow_of_four_le a4
    _ = _ := by ring
