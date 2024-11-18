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
private def n_8_0_7 {t : ℝ} : ℤ := Int.log 2 (1 / t) + 1

private lemma n_spec1 (ht : 0 < t) : 1 < 2 ^ (@n_8_0_7 t) * t := calc
  1 = (1 / t) * t := by
    norm_num
    rw [mul_comm]
    exact (mul_inv_cancel₀ ht.ne').symm
  _ < 2 ^ (@n_8_0_7 t) * t := by
    gcongr
    exact Int.lt_zpow_succ_log_self (by norm_num) (1 / t)

-- This lemma is probably not needed.
-- private lemma n_spec2 : ∀ n' < n_8_0_7, 2 ^ n' * t < 1 := sorry

-- I'm looking for a theorem like this for the two sorries below
theorem barXX {a b : ℝ} : ((2 : ℝ≥0) ^ a) * (2 ^ b) = 2 ^ (a + b) := by
  sorry

lemma baz {A X : ℝ} : X = 2 ^ (-A) * (2 ^ A * X) := by
  rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
  ring_nf

lemma baz' {A : ℝ} {X : ℝ≥0∞} : X = 2 ^ (-A) * (2 ^ A * X) := by
  rw [← mul_assoc]
  nth_rw 1 [← one_mul X]
  congr
  -- doesn't fire as the base is an ℝ≥0∞ now...
  -- rw [← Real.rpow_add (by norm_num)]
  ring_nf
  sorry

lemma aux_8_0_8 (hR : 0 < R) (ht : 0 < t) (ht' : t ≤ 1) :
    2 ^ ((-1 : ℝ) - a* ((@n_8_0_7 t) +2)) * volume (ball x (2*R)) ≤ ∫⁻ y, cutoff R t x y := by
  have inside_computation (N : ℕ) (r : ℝ) :
      2 ^ (- (a : ℝ) * (N + 2)) * volume (ball x (2 ^ (N + 2) * r)) ≤ volume (ball x r) := by
    have : volume.real (ball x (2 ^ (N + 2) * r)) ≤ 2 ^ ((a : ℝ) * (N + 2)) * volume.real (ball x r) := by
      convert measure_ball_le_pow_two (x := x) (r := r) (n := N + 2) (μ := volume)
      rw [show defaultA a = 2 ^ a from rfl]
      norm_cast
      ring
    have : volume (ball x (2 ^ (N + 2) * r)) ≤ 2 ^ ((a : ℝ) * (N + 2)) * volume (ball x r) := by
      rw [Measure.real] at this
      set A := volume (ball x (2 ^ (N + 2) * r))
      set B := volume (ball x r) with hB
      set D' : ℝ := ↑a * (↑N + 2)
      set D'' : ℝ≥0∞ := 2 ^ D'
      have : A.toReal ≤ D''.toReal * B.toReal := by
        convert this
        sorry -- D' is non-negative and finite, so obvious
      show A ≤ D'' * B
      -- A, B and D'' are finite, so this should be obvious. how to prove this best?
      -- (A being finite is necessary, otherwise this is false)
      sorry
    set A : ℝ := (↑a * (↑N + 2))
    set X := volume (ball x r)
    convert mul_le_mul_of_nonneg_left (a := 2 ^ (-(a : ℝ) * (↑N + 2))) this (by positivity)
    rw [show (-↑a * (↑N + 2)) = -A by ring]
    -- XXX: at this point, neither `ring` nor `field_simp` work.
    -- the former tries to "unfold A"; can I prevent this?
    -- baz fires, but I want baz'
    exact baz' (X := X)

  set N : ℝ := @n_8_0_7 t + 2 with N_eq
  calc (2 ^ ((-1 : ℝ) - a * N)) * volume (ball x (2 * R))
    _ ≤ (2 ^ ((-1 : ℝ) - a * N)) * volume (ball x (2 ^ N * 2 ^ (-1 : ℝ) * t * R)) := by
      gcongr
      calc -- or: apply the right lemma...
        2 ≤ (2 * 2 ^ (@n_8_0_7 t)) * t := by
          rw [mul_assoc]
          -- future: linear_combination should do this! multiply (n_spec ht).lt with 2
          nth_rewrite 1 [show (2 : ℝ) = 2 * 1 by norm_num]
          gcongr
          exact (n_spec1 ht).le
        _ = 2 ^ N * 2 ^ (-1 : ℝ) * t := by
          rw [N_eq]
          set Nn : ℤ := @n_8_0_7 t
          norm_cast
          rw [show Int.negSucc 0 = -1 by rfl]
          congr 1
          set A : ℝ := 2
          -- now, it should be obvious
          sorry
          -- nth_rw 1 [show (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) by norm_num]
          -- trans (2 : ℝ) ^ (@n_8_0_7 t + 1)
          -- · sorry
          -- · sorry
    _ ≤ (2 ^ (-1 : ℝ)) * 2 ^ (- a * N) * volume (ball x (2 ^ N * 2 ^ (-1 : ℝ) * t * R)) := by
      gcongr
      set N' := a * N -- note: one N' uses ℝ, the other ℤ
      apply le_of_eq
      -- now, it's almost an rpow thing --- but need to rewrite by that cast
      sorry
    _ ≤ (2 ^ (-1 : ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) := by
      sorry -- use inside_computation
    _ ≤ ∫⁻ y, cutoff R t x y := aux_8_0_6 (ht := ht) (hR := hR)

/-
  calc ∫⁻ y, cutoff R t x y
    _ ≥ (2 ^ (-1 : ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) := aux_8_0_6 (ht := ht) (hR := hR)
    _ ≥ (2 ^ (-1 : ℝ)) * 2 ^ (- a * ((@n_8_0_7 t) + 2)) * volume (ball x (2 ^ ((@n_8_0_7 t) + 2) * 2 ^ (-1 : ℝ) * t * R)) := by
      -- use inside_computation
      sorry
    _ ≥ (2 ^ ((-1 : ℝ) - a * ((@n_8_0_7 t) + 2))) * volume (ball x (2 ^ ((@n_8_0_7 t) + 2) * 2 ^ (-1 : ℝ) * t * R)) := by
      -- hopefully, the previous step will make this moot,
      -- and also simplify the next calc step
      sorry
    _ ≥ (2 ^ ((-1 : ℝ) - a * ((@n_8_0_7 t) + 2))) * volume (ball x (2 * R)) := by
      gcongr
      calc
        2 ≤ (2 * 2 ^ (@n_8_0_7 t)) * t := by
          rw [mul_assoc]
          nth_rewrite 1 [show (2 : ℝ) = 2 * 1 by norm_num]
          gcongr
          exact (n_spec1 ht).le
        _ = (2 ^ (n_8_0_7 + 2) * 2 ^ (-1 : ℝ)) * t := by
          apply congrFun (congrArg HMul.hMul _)
          -- there should be a nicer way!
          calc 2 * (2 : ℝ) ^ (@n_8_0_7 t)
            _ = 2 ^ ((@n_8_0_7 t) + 1) := by
              sorry
            _ = 2 ^ (((@n_8_0_7 t) + 2) - 1) := by ring_nf
            _ = 2 ^ (n_8_0_7 + 2) * 2 ^ (-1 : ℝ) := by
              sorry
-/

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

/-- Equation 8.0.9/8.0.10 from the blueprint:
  the first estimate towards `dist_holderApprox_le`. -/
-- missing hypotheses? right notion of integral?
lemma aux_8_0_9 (ϕ : X → ℂ) :
    (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
      = ∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y))) := sorry

include x y R t in
/-- Equation 8.0.11 from the blueprint: the first estimate towards `dist_holderApprox_le`. -/
-- missing hypotheses?
-- right notion of integral? right formalisation of absolute value?
lemma aux_8_0_11 (ϕ : X → ℂ) :
    ∫ y, ((cutoff R t x y) * (dist (ϕ x) (ϕ y)))
      ≤ ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y)) := sorry

/-- Equation 8.0.12 from the blueprint: the second estimate towards `dist_holderApprox_le`. -/
-- missing hypotheses?
-- right notion of integral? right formalisation of absolute value?
lemma aux_8_0_12 {ϕ : X → ℂ} {C : ℝ≥0} (h2ϕ : HolderWith C nnτ ϕ) :
    ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y))
    ≤ (∫ y in ball x (t * R), (cutoff R t x y) * (dist x y) ^ τ) * C * R ^ (-τ) := sorry

/-- Equation 8.0.13 from the blueprint: the last estimate towards `dist_holderApprox_le`. -/
-- missing hypotheses?
-- right notion of integral? right formalisation of absolute value?
lemma aux_8_0_13 {ϕ : X → ℂ} {C : ℝ≥0} (h2ϕ : HolderWith C nnτ ϕ) :
    True :=
  -- TODO: this statement doesn't compile yet
  --  (∫⁻ y in ball x (t * R), (cutoff R t x y) * (dist x y) ^ τ) * C * R ^ (-τ)
  --  ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ := sorry
  sorry

-- should be in mathlib. otherwise, an easy exercise
lemma missing {I a b : ℝ} (hI : 0 ≤ I) (h : I * a ≤ I * b) : a ≤ b := by
  have : 0 ≤ 1 / I := by positivity
  sorry

include x y in
/-- Part of Lemma 8.0.1. Equation (8.0.1) in the blueprint. -/
lemma dist_holderApprox_le {z : X} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : X) :
    dist (ϕ x) (holderApprox R t ϕ x) ≤ t ^ τ * C := by
  have : (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
      ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ := by
    calc (∫⁻ y, cutoff R t x y).toReal * (dist (ϕ x) (holderApprox R t ϕ x))
      _ = ∫ y, (cutoff R t x y) * (dist (ϕ x) (ϕ y)) := by apply aux_8_0_9
      _ ≤ ∫ y in ball x (t * R), (cutoff R t x y) * (dist (ϕ x) (ϕ y)) := by apply aux_8_0_11 (y := y) ϕ
      _ ≤ (∫ y in ball x (t * R), (cutoff R t x y) * (dist x y) ^ τ) * C * R ^ (-τ) := by apply aux_8_0_12 h2ϕ
      _ ≤ (∫⁻ y, cutoff R t x y).toReal * C * t ^ τ := by
        sorry -- will be `apply aux_8_0_13 h2ϕ`, once that is fixed...
  set I := (∫⁻ y, cutoff R t x y).toReal
  apply missing (I := I) (by positivity)
  convert this using 1
  ring

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
