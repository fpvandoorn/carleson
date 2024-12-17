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

-- auxiliary version, phrased in terms of `max 0 (the real constant)`
lemma cutoff_Lipschitz_aux (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith (max 0 ⟨(1 / (t * R)), by positivity⟩) (fun y ↦ cutoff R t x y) := by
  -- Still working on this:
  -- mathlib is missing a lemma Lipschitz.smul_const for CommGroupWithZero (or so).
  -- this one should be inlined, once aux1 works
  have aux0 : LipschitzWith 1 (fun y ↦ dist x y) := LipschitzWith.dist_right x
  have aux : LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ dist x y / (t * R)) := by
    -- add a mul_const version? (or, actually, smul_const and const_smul)
    -- WTF: this seems to be necessary
    --haveI : SeminormedCommGroup ℝ := sorry
    -- R is an additive group , wants a mult. group!
    let as := LipschitzWith.const (α := X) (1 / (t * R))
    -- but the next line still fails, no matter what
    --let asdf := LipschitzWith.mul (α := X) (E := ℝ) as aux0
    --apply LipschitzWith.mul (α := X) (E := ℝ) as aux0
    sorry
  unfold cutoff
  apply (LipschitzWith.const' (0 : ℝ)).max ?_
  convert LipschitzWith.sub (LipschitzWith.const' 1) (Kf := 0) aux; ring

lemma cutoff_Lipschitz (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ cutoff R t x y) := by
  convert cutoff_Lipschitz_aux hR ht
  symm
  apply max_eq_right (by positivity)

@[fun_prop]
lemma cutoff_continuous (hR : 0 < R) (ht : 0 < t) : Continuous (fun y ↦ cutoff R t x y) :=
  (cutoff_Lipschitz hR ht).continuous

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

lemma support_cutoff_subset_ball (hR : 0 < R) (ht : 0 < t) :
    support (fun y ↦ cutoff R t x y) ⊆ ball x (t * R) := fun _ hy ↦ aux_8_0_4 hR ht hy

lemma lintegral_cutoff_finite : ∫⁻ y, cutoff R t x y < ∞ := sorry

lemma setIntegral_cutoff_finite : ∫⁻ (y : X) in ball x (t * R), (cutoff R t x y) < ∞ := by
  -- deduce from lintegral_cutoff_finite (or perhaps the other way around)?
  -- idea: function is only non-zero if y in ball x t*r, that ball has finite volume
  sorry

lemma aux_8_0_5 (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) :
    2 ^ (-1 : ℝ) ≤ cutoff R t x y := by
  rw [mem_ball', mul_assoc] at h
  have : dist x y / (t * R) < 2 ^ (-1 : ℝ) := (div_lt_iff₀ (by positivity)).mpr h
  calc 2 ^ (-1 : ℝ)
    _ ≤ 1 - dist x y / (t * R) := by
      norm_num at *; linarith only [h, this]
    _ ≤ cutoff R t x y := le_max_right _ _

-- FIXME: decide which version I prefer, rename accordingly!

lemma aux_8_0_5'' (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) :
    2 ^ (-1 : ℝ) ≤ (cutoff R t x y : ℝ≥0∞) := by
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
private def n_8_0_7 {t : ℝ} : ℤ := Int.log 2 (1 / t) + 1

private lemma n_spec1 (ht : 0 < t) : 1 < 2 ^ (@n_8_0_7 t) * t := calc
  1 = (1 / t) * t := by
    norm_num
    rw [mul_comm]
    exact (mul_inv_cancel₀ ht.ne').symm
  _ < 2 ^ (@n_8_0_7 t) * t := by
    gcongr
    exact Int.lt_zpow_succ_log_self (by norm_num) (1 / t)

private lemma n_pos (ht : 0 < t) : 0 < @n_8_0_7 t := sorry -- TODO

-- This lemma is probably not needed.
-- private lemma n_spec2 : ∀ n' < n_8_0_7, 2 ^ n' * t < 1 := sorry

-- should be in mathlib. otherwise, an easy exercise
lemma missing' {I a b : ℝ≥0∞} (hI : 0 ≤ I) (h : I * a ≤ I * b) : a ≤ b := by
  have : 0 ≤ 1 / I := by positivity
  sorry

lemma missing {I a b : ℝ} (hI : 0 ≤ I) (h : I * a ≤ I * b) : a ≤ b := by
  have : 0 ≤ 1 / I := by positivity
  sorry

omit [TileStructure Q D κ S o] in
lemma aux_8_0_8_inner (N : ℕ) (r : ℝ) :
      2 ^ (- (a : ℝ) * (N + 2)) * volume (ball x (2 ^ (N + 2) * r)) ≤ volume (ball x r) := by
  have aux : volume (ball x (2 ^ (N + 2) * r)) ≤ 2 ^ ((a : ℝ) * (N + 2)) * volume (ball x r) := by
    convert measure_ball_le_pow_two' (x := x) (μ := volume)
    rw [show defaultA a = 2 ^ a from rfl]
    norm_cast
    ring
  set A : ℝ := (↑a * (↑N + 2))
  apply missing' (I := 2 ^ A) (by positivity)
  rw [← mul_assoc]; convert aux
  nth_rw 2 [← one_mul (volume (ball x (2 ^ (N + 2) * r)))]; congr
  rw [show -↑a * (↑N + 2) = -A by ring,
    ← ENNReal.rpow_add A (-A) (by norm_num) (ENNReal.two_ne_top)]
  simp

lemma aux_8_0_8 (hR : 0 < R) (ht : 0 < t) (ht' : t ≤ 1) :
    2 ^ ((-1 : ℤ) - a* ((@n_8_0_7 t) +2)) * volume (ball x (2*R)) ≤ ∫⁻ y, cutoff R t x y := by
  have inside_computation1 (N : ℕ) (r : ℝ) :
      2 ^ (- (a : ℝ) * (N + 2)) * volume (ball x (2 ^ (N + 2) * r)) ≤ volume (ball x r) :=
    aux_8_0_8_inner N r
  set Nn := @n_8_0_7 t with Nn_eq
  have h : 0 ≤ Nn := (@n_pos t ht).le
  set N : ℤ := @n_8_0_7 t + 2 with N_eq
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

          apply Nn_eq ▸ (n_spec1 ht).le
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
      ring
      sorry -- 'ring' used to work
    _ ≤ ∫⁻ y, cutoff R t x y := aux_8_0_6 (ht := ht) (hR := hR)

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `ϕ ↦ \tilde{ϕ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (ϕ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * ϕ y) / (∫⁻ y, cutoff R t x y).toReal

-- This surely exists in mathlib; how is it named?
-- if not, PR welcome?
omit [TileStructure Q D κ S o] in
lemma foo {φ : X → ℂ} (hf : ∫ x, φ x ≠ 0) : ∃ z, φ z ≠ 0 := by
  by_contra! h
  apply hf (by simp [h])

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

/-- Equation 8.0.9/8.0.10 from the blueprint:
  the first estimate towards `dist_holderApprox_le`. -/
-- missing hypotheses? right notion of integral?
lemma aux_8_0_9 (ϕ : X → ℂ) :
    (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
      = |∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y)))| := by
  -- use lintegral_cutoff_finite, to argue the .toReal

  -- pull the dist ... inside the integral
  -- cutoff R t x y is non-negative, so both parts are -> so can add the absolute value,
  -- and take it out again
  -- calc (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
  --   _ = (∫⁻ y, (cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))) := sorry
  --   _ = (∫⁻ y, (cutoff R t x y) * (dist (ϕ x) (holderApprox R t ϕ x))) := sorry
  --   _ = |∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y)))| := sorry
  sorry

-- ext: structure of types proven equal (e.g., functions, sets)
-- congr, gcongr: structure of terms proven equal (using injectivity/monotonicity for = or ≤)

#check norm_integral_le_lintegral_norm
omit [TileStructure Q D κ S o] y in
/-- Equation 8.0.11 from the blueprint: the first estimate towards `dist_holderApprox_le`. -/
-- right notion of integral? right formalisation of absolute value?
lemma aux_8_0_11 (hR : 0 < R) (ht : t ∈ Ioc 0 1) (ϕ : X → ℂ) :
    |∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y)))|
      ≤ ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y)) := by
  calc |∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y)))|
    _ ≤ ∫ y, |(cutoff R t x y) * (dist (ϕ x) (ϕ y))| :=
    norm_integral_le_integral_norm (fun y ↦ (cutoff R t x y) * (dist (ϕ x) (ϕ y)))
    _ = ∫ y, ((cutoff R t x y) * dist (ϕ x) (ϕ y)) := by
      congr! 2 with y
      exact _root_.abs_of_nonneg (by positivity)
    _ = ∫ y in ball x (t * R), ((cutoff R t x y) * dist (ϕ x) (ϕ y)) := by
      set f := fun y ↦ ((cutoff R t x y) * dist (ϕ x) (ϕ y))
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have : cutoff R t x y = 0 := by by_contra! h; exact hy (aux_8_0_4 hR ht.1 h)
      simp [this]

-- #check norm_integral_le_lintegral_norm

-- TODO: copy over the proof of 8_0_11, somehow/adapt it!
-- decision: re-doing the proof is annoying; don't want to pass to just the ball
-- or: prove the RHS has finite integral, thus .toReal equals what I want
lemma aux_8_0_11'' (hR : 0 < R) (ht : t ∈ Ioc 0 1) (ϕ : X → ℂ) :
    |∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y)))|
      ≤ (∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist (ϕ x) (ϕ y))).toReal := by
  have : |∫ (y : X), ↑(cutoff R t x y) * dist (ϕ x) (ϕ y)| ≤
      ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y)) := by
    apply aux_8_0_11 hR ht
  --convert this; symm
  set B := ball x (t * R)
  simp_rw [← coe_nndist]
  norm_cast
  --simp_rw [ENNReal.coe_mul]
  convert this; symm
  -- now, prove that the RHS has finite integral
  -- (nndist is bounded, cutoff has finite integral)
  -- and thus the .toReal is superfluous
  sorry

lemma aux_8_0_12'' {ϕ : X → ℂ} {R C : ℝ≥0} (hR : R ≠ 0) (ht : t ∈ Ioc 0 1) (h2ϕ : HolderWith C nnτ ϕ) :
    ∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist (ϕ x) (ϕ y))
    ≤ (∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist x y) ^ τ) * C := by
  calc ∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist (ϕ x) (ϕ y))
    _ ≤ (∫⁻ y in ball x (t * R), (cutoff R t x y) * C * (nndist x y) ^ τ) := by
      simp_rw [mul_assoc]
      gcongr with y
      have : nndist (ϕ x) (ϕ y) ≤ C * nndist x y ^ τ := h2ϕ.dist_le (x := x) (y := y)
      -- convert this -- convert h2ϕ.nndist_le (x := x) (y := y)
      sorry
    _ = (∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist x y) ^ τ * C) := by
      simp_rw [← mul_comm (C : ℝ≥0∞) _, mul_assoc]
    _ = (∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist x y) ^ τ) * C := by
      rw [lintegral_mul_const]
      have : 0 < R := pos_iff_ne_zero.mpr hR
      have aux := cutoff_measurable (R := R) this ht.1 (X := X) (x := x)
      apply Measurable.mul (by fun_prop) (by fun_prop)

  -- heuristic: if both sides are ℝ≥0, use lintegral
  -- use lintegral if I can
  -- estimates with ≤, generally use lintegral (or Bochner with real numbers)

/-- Equation 8.0.12 from the blueprint: the second estimate towards `dist_holderApprox_le`. -/
-- missing hypotheses?
-- right notion of integral? right formalisation of absolute value?
lemma aux_8_0_12 {ϕ : X → ℂ} {C : ℝ≥0} (h2ϕ : HolderWith C nnτ ϕ) :
    ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y))
    ≤ (∫ y in ball x (t * R), (cutoff R t x y) * (dist x y) ^ τ) * C * R ^ (-τ) := by
  calc ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y))
    _ ≤ (∫ y in ball x (t * R), (cutoff R t x y) * (dist x y) ^ τ * C) := by
      apply setIntegral_mono
      · sorry -- integrability goal ---> use Lebesgue integral instead?? yes!
      · sorry -- another
      intro y
      -- now, the real goal I wanted to prove
      beta_reduce
      have : dist (ϕ x) (ϕ y) ≤ C * dist x y ^ τ := h2ϕ.dist_le (x := x) (y := y)
      -- is the R^-τ wrong and should just be deleted?
      have : dist (ϕ x) (ϕ y) ≤ dist x y ^ τ * ↑C * R ^ (-τ) := by
        convert h2ϕ.dist_le
        sorry -- mismatch, h2ϕ expects an edist! --
        --convert h2ϕ (x := x) (y := y)
      -- associativity orders, be careful!
      sorry--rw [mul_assoc ((cutoff R t x y) : ℝ), mul_assoc]
      --gcongr
    _ = (∫ y in ball x (t * R), (cutoff R t x y) * (dist x y) ^ τ) * C * R ^ (-τ) := by
      -- move the constant out of the integral
      set DDD := C * R ^ (-τ) -- sth types, does not extract
      sorry


-- TODO: this equation is wrong, I think; need to divide by R^τ or something
/-- Equation 8.0.13 from the blueprint: the last estimate towards `dist_holderApprox_le`. -/
-- XXX: this version or its cousin? will see!
lemma aux_8_0_13'' {ϕ : X → ℂ} {R t C : ℝ≥0} (h2ϕ : HolderWith C nnτ ϕ) : -- R also superfluous?
   ((∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist x y) ^ τ) * C).toReal
   ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ := sorry

lemma aux_8_0_13''' {ϕ : X → ℂ} (hR : 0 ≤ R) (ht : 0 ≤ t) {C : ℝ≥0} (h2ϕ : HolderWith C nnτ ϕ) : -- R also superfluous?
    ((∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist x y) ^ τ) * C).toReal
    ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ := by
  sorry

-- just divide cutoff by R^τ instead? feel free to fix yourself... but should do it on paper first :-)

include x y in
/-- Part of Lemma 8.0.1. Equation (8.0.1) in the blueprint. -/
lemma dist_holderApprox_le {z : X} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : X) :
    dist (ϕ x) (holderApprox R t ϕ x) ≤ t ^ τ * C := by
  suffices (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
      ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ by
    set I := (∫⁻ y, cutoff R t x y).toReal
    apply missing (I := I) (by positivity)
    convert this using 1
    ring
  calc (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
    _ = |∫ y, (cutoff R t x y) * (dist (ϕ x) (ϕ y))| := by apply aux_8_0_9
    _ ≤ (∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist (ϕ x) (ϕ y))).toReal := by
      apply aux_8_0_11'' hR ht
      --_ ≤ ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y)) := by apply aux_8_0_11 (y := y) ϕ
    _ ≤ ((∫⁻ y in ball x (t * R), (cutoff R t x y) * (nndist x y) ^ τ) * C).toReal := by
      -- side effect of using different types: need to prove the integral is bounded,
      -- to use monotonicity of .toReal
      gcongr
      · have : ((nndist x y) ^ τ) * ↑C < ∞ := by sorry -- obvious, right?
        have := setIntegral_cutoff_finite (x := x) (t := t) (R := R)
        sorry -- exact? doesn't find anything
      apply aux_8_0_12'' (R := ⟨R, by positivity⟩) (Ne.symm (ne_of_lt hR)) ht h2ϕ
    _ ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ := by
      apply aux_8_0_13''' hR.le ht.1.le h2ϕ

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
