import Carleson.TileStructure

/-! This should roughly contain the contents of chapter 8. -/

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure
open scoped NNReal ENNReal ComplexConjugate

/-- `cutoff R t x y` is `L(x, y)` in the proof of Lemma 8.0.1. -/
def cutoff (R t : ℝ) (x y : X) : ℝ≥0 :=
  ⟨max 0 (1 - dist x y / (t * R)), by positivity⟩

variable {R t : ℝ} {x y : X}

lemma cutoff_comm : cutoff R t x y = cutoff R t y x := by
  unfold cutoff
  simp_rw [dist_comm x y]

lemma cutoff_Lipschitz (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ cutoff R t x y) := by
  -- Still working on this:
  -- mathlib is missing a lemma Lipschitz.smul_const for CommGroupWithZero (or so).
  sorry

@[fun_prop]
lemma cutoff_continuous (hR : 0 < R) (ht : 0 < t) : Continuous (fun y ↦ cutoff R t x y) :=
  (cutoff_Lipschitz hR ht (X := X)).continuous

omit [TileStructure Q D κ S o] in
/-- `cutoff R t x` is measurable in `y`. -/
@[fun_prop]
lemma cutoff_measurable (hR : 0 < R) (ht : 0 < t) : Measurable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).measurable

-- Is this useful for mathlib? neither exact? nor aesop can prove this. Same for the next lemma.
lemma leq_of_max_neq_left {a b : ℝ} (h : max a b ≠ a) : a < b := by
  by_contra! h'
  apply h (max_eq_left h')

lemma leq_of_max_neq_right {a b : ℝ} (h : max a b ≠ b) : b < a := by
  by_contra! h'
  exact h (max_eq_right h')

/-- Equation 8.0.4 from the blueprint -/
lemma aux_8_0_4 (hR : 0 < R) (ht : 0 < t) (h : cutoff R t x y ≠ 0) : y ∈ ball x (t * R) := by
  rw [mem_ball']
  have : 0 < 1 - dist x y / (t * R) := by
    apply leq_of_max_neq_left
    rw [cutoff] at h
    convert h
    exact eq_iff_eq_of_cmp_eq_cmp rfl
  exact (div_lt_one (by positivity)).mp (by linarith)

lemma aux_8_0_5 (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) :
    2 ^ (-1 : ℝ) ≤ cutoff R t x y := by
  rw [mem_ball', mul_assoc] at h
  have : dist x y / (t * R) < 2 ^ (-1 : ℝ) := (div_lt_iff₀ (by positivity)).mpr h
  calc 2 ^ (-1 : ℝ)
    _ ≤ 1 - dist x y / (t * R) := by
      norm_num at *; linarith only [h, this]
    _ ≤ cutoff R t x y := le_max_right _ _

lemma aux_8_0_5'' (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) :
    ((2 ^ (-1 : ℝ))) ≤ (cutoff R t x y : ℝ≥0∞) := by
  rw [show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← ENNReal.coe_rpow_of_ne_zero (by norm_num)]
  exact ENNReal.coe_le_coe.mpr (aux_8_0_5 (ht := ht) (hR := hR) h)

omit [TileStructure Q D κ S o] in
lemma aux_8_0_6 (hR : 0 < R) (ht : 0 < t) :
    (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) ≤ ∫⁻ y, (cutoff R t x y) := by
  calc (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R))
    _ = ∫⁻ y in ((ball x (2 ^ (-1: ℝ) * t * R))), (2 ^ (-1: ℝ)) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in (ball x (2 ^ (-1: ℝ) * t * R)), (cutoff R t x y) := by
      apply setLIntegral_mono (by fun_prop (discharger := assumption))
      intro y' hy'
      exact aux_8_0_5'' hy' (hR := hR) (ht := ht)
    _ ≤ ∫⁻ y, (cutoff R t x y) := setLIntegral_le_lintegral _ _

/-- The smallest integer `n` so that `2^n t ≥ 1`. -/
-- i.e., the real logarithm log₂ 1/t, rounded *up* to the nearest integer
private def n_8_0_7 (t : ℝ) : ℤ := Int.log 2 (1 / t) + 1

private lemma n_spec1 (ht : 0 < t) : 1 < 2 ^ (n_8_0_7 t) * t := calc
  1 = (1 / t) * t := by
    norm_num
    rw [mul_comm]
    exact (mul_inv_cancel₀ ht.ne').symm
  _ < 2 ^ (n_8_0_7 t) * t := by
    gcongr
    exact Int.lt_zpow_succ_log_self (by norm_num) (1 / t)

private lemma n_pos (ht : t ∈ Ioc 0 1) : 0 < n_8_0_7 t := sorry

-- This lemma is probably not needed.
-- private lemma n_spec2 : ∀ n' < n_8_0_7, 2 ^ n' * t < 1 := sorry

omit [TileStructure Q D κ S o] in
lemma aux_8_0_8_inner (N : ℕ) (r : ℝ) :
      2 ^ (- (a : ℝ) * (N + 2)) * volume (ball x (2 ^ (N + 2) * r)) ≤ volume (ball x r) := by
  have aux : volume (ball x (2 ^ (N + 2) * r)) ≤ 2 ^ ((a : ℝ) * (N + 2)) * volume (ball x r) := by
    convert measure_ball_le_pow_two' (x := x) (μ := volume)
    rw [show defaultA a = 2 ^ a from rfl]
    norm_cast
    ring
  set A : ℝ := (a * (↑N + 2))
  have : A ≠ 0 := by
    simp only [A]
    have : N + 2 ≠ 0:= by positivity
    sorry -- almost what I want: apply (Real.rpow_ne_zero (by norm_num) this).mpr
  have : (2 : ℝ) ^ A ≠ 0 := by rw [Real.rpow_ne_zero _ this]; norm_num; norm_num
  have h₁ : (2 : ℝ≥0∞) ^ A ≠ 0 := sorry -- ENNReal version of `this`
  have h₂ : (2 : ℝ≥0∞) ^ A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)
  rw [← ENNReal.mul_le_mul_left (a := 2 ^ A) h₁ h₂]
  rw [← mul_assoc]; convert aux
  nth_rw 2 [← one_mul (volume (ball x (2 ^ (N + 2) * r)))]; congr
  rw [show -↑a * (↑N + 2) = -A by ring,
    ← ENNReal.rpow_add A (-A) (by norm_num) (ENNReal.two_ne_top)]
  simp

lemma aux_8_0_8 (hR : 0 < R) (ht : t ∈ Ioc 0 1) :
    2 ^ ((-1 : ℤ) - a* ((n_8_0_7 t) +2)) * volume (ball x (2*R)) ≤ ∫⁻ y, cutoff R t x y := by
  have inside_computation1 (N : ℕ) (r : ℝ) :
      2 ^ (- (a : ℝ) * (N + 2)) * volume (ball x (2 ^ (N + 2) * r)) ≤ volume (ball x r) :=
    aux_8_0_8_inner N r
  set Nn := n_8_0_7 t with Nn_eq
  have h : 0 ≤ Nn := (@n_pos t ht).le
  set N : ℤ := n_8_0_7 t + 2 with N_eq
  have : 0 ≤ N := by have := @n_pos t ht; positivity
  clear_value N; lift N to ℕ using this
  clear_value Nn; lift Nn to ℕ using h
  calc (2 ^ ((-1:ℤ) - a * N)) * volume (ball x (2 * R))
    _ ≤ (2 ^ ((-1:ℤ) - a * N)) * volume (ball x (2 ^ N * 2 ^ (-1 : ℤ) * t * R)) := by
      gcongr
      calc -- or: apply the right lemma...
        2 ≤ (2 * 2 ^ Nn) * t := by
          rw [mul_assoc]; nth_rw 1 [← mul_one 2]; gcongr
          rw [← zpow_natCast]
          apply Nn_eq ▸ (n_spec1 ht.1).le
        _ = 2 ^ N * 2 ^ (-1 : ℤ) * t := by
          congr 1
          trans 2 ^ (Nn + 1)
          · norm_cast
            omega
          · symm
            rw [← zpow_natCast, ← zpow_add₀ (a := (2 :ℝ)) (by norm_num) (N : ℤ) (-1 : ℤ),
              ← zpow_natCast]
            congr
            rw [N_eq, ← Nn_eq]
            omega
    _ = (2 ^ (-1 : ℤ)) * 2 ^ (-(a * N : ℤ)) * volume (ball x (2 ^ N * 2 ^ (-1 : ℤ) * t * R)) := by
      congr
      exact ENNReal.zpow_add (by norm_num) (ENNReal.two_ne_top) (-1 :ℤ) (-(a * N : ℤ))
    _ ≤ (2 ^ (-1 : ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) := by
      rw [mul_assoc]
      gcongr
      · apply le_of_eq
        rw [← ENNReal.rpow_intCast]; congr; simp
      --set R'' := (2 ^ (-1: ℝ) * t * R)
      convert aux_8_0_8_inner N (2 ^ (-1: ℝ) * t * R) using 1
      -- ring used to work; doesn't close the goal any more
      sorry
    _ ≤ ∫⁻ y, cutoff R t x y := aux_8_0_6 hR ht.1

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `ϕ ↦ \tilde{ϕ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (ϕ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * ϕ y) / (∫⁻ y, cutoff R t x y).toReal

-- This surely exists in mathlib; how is it named?
omit [TileStructure Q D κ S o] in
lemma foo {φ : X → ℂ} (hf : ∫ x, φ x ≠ 0) : ∃ z, φ z ≠ 0 := by
  by_contra! h
  apply hf
  have : φ = 0 := by ext; apply h
  rw [this]
  simp

omit [TileStructure Q D κ S o] in
/-- Part of Lemma 8.0.1. -/
lemma support_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R)
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R) (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t ϕ) ⊆ ball z (2 * R) := by
  unfold support
  intro x hx
  rw [mem_setOf] at hx
  have hx'' := left_ne_zero_of_mul hx
  have : ∃ y, (cutoff R t x y) * ϕ y ≠ 0 := foo hx''
  choose y hy using this
  have : x ∈ ball y (t * R) := by
    apply aux_8_0_4 hR ht.1
    rw [cutoff_comm]
    exact NNReal.coe_ne_zero.mp fun a ↦ (left_ne_zero_of_mul hy) (congrArg ofReal a)
  have h : x ∈ ball y R := by
    refine Set.mem_of_mem_of_subset this ?_
    nth_rw 2 [← one_mul R]
    gcongr
    exact ht.2
  calc dist x z
    _ ≤ dist x y + dist y z := dist_triangle x y z
    _ < R + R := add_lt_add h (hϕ (right_ne_zero_of_mul hy))
    _ = 2 * R := by ring

/-- Part of Lemma 8.0.1. -/
lemma dist_holderApprox_le {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : X) :
    dist (ϕ x) (holderApprox R t ϕ x) ≤ t ^ τ * C := by
  sorry

/-- Part of Lemma 8.0.1. -/
lemma lipschitzWith_holderApprox {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    LipschitzWith (C8_0_1 a ⟨t, ht.1.le⟩) (holderApprox R t ϕ) := by
  sorry


/-- The constant occurring in Proposition 2.0.5. -/
def C2_0_5 (a : ℝ) : ℝ≥0 := 2 ^ (8 * a)

/-- Proposition 2.0.5. -/
theorem holder_van_der_corput {z : X} {R : ℝ≥0} (hR : 0 < R) {ϕ : X → ℂ}
    (hϕ : support ϕ ⊆ ball z R) (h2ϕ : hnorm (a := a) ϕ z R < ∞) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖₊ ≤
    (C2_0_5 a : ℝ≥0∞) * volume (ball z R) * hnorm (a := a) ϕ z R *
    (1 + nndist_{z, R} f g) ^ (2 * a^2 + a^3 : ℝ)⁻¹ := sorry
