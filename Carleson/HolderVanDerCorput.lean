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

section new

def cutoff' (R t : ℝ) (x y : X) : ℝ :=
  max 0 (1 - dist x y / (t * R))

variable {R t : ℝ} {x y : X}

lemma cutoff_Lipschitz (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith (max 0 ⟨(1 / (t * R)), by positivity⟩) (fun y ↦ cutoff R t x y) := by
  -- this one should be inlined, once aux1 works
  have aux0 : LipschitzWith 1 (fun y ↦ dist x y) := LipschitzWith.dist_right x
  have aux : LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ dist x y / (t * R)) := by
    -- WTF: this seems to be necessary
    haveI : SeminormedCommGroup ℝ := sorry
    let as := LipschitzWith.const (α := X) (1 / (t * R))
    -- but the next line still fails, no matter what
    --let asdf := LipschitzWith.mul (α := X) (E := ℝ) as aux0
    --apply LipschitzWith.mul (α := X) (E := ℝ) as aux0
    sorry
  have : LipschitzWith (max 0 ⟨(1 / (t * R)), by positivity⟩) (fun y ↦ cutoff' R t x y) := by
    unfold cutoff'
    apply (LipschitzWith.const' (0 : ℝ)).max ?_
    convert LipschitzWith.sub (LipschitzWith.const' 1) (Kf := 0) aux; ring
  convert this

@[fun_prop]
lemma cutoff_continuous (hR : 0 < R) (ht : 0 < t) : Continuous (fun y ↦ cutoff R t x y) := by
  apply (cutoff_Lipschitz hR ht (X := X)).continuous

/-- `cutoff R t x` is measurable in `y`. -/
@[fun_prop]
lemma cutoff_measurable (hR : 0 < R) (ht : 0 < t) : Measurable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).measurable

-- is this useful for mathlib? none of exact? and aesop both cannot prove this
lemma leq_of_max_neq_left {a b : ℝ} (h : max a b ≠ a) : a < b := by
  by_contra! h'
  apply h (max_eq_left h')

lemma leq_of_max_neq_right {a b : ℝ} (h : max a b ≠ b) : b < a := by
  by_contra! h'
  exact h (max_eq_right h')

/-- equation 8.0.4 from the blueprint -/
lemma aux_8_0_4 (hR : 0 < R) (ht : 0 < t) (h : cutoff R t x y ≠ 0) : y ∈ ball x (t * R) := by
  rw [mem_ball']
  have : 0 < 1 - dist x y / (t * R) := by
    apply leq_of_max_neq_left
    rw [cutoff] at h
    -- best way now?
    convert h
    exact eq_iff_eq_of_cmp_eq_cmp rfl
  -- also works: field_simp at this; exact this
  exact (div_lt_one (by positivity)).mp (by linarith)

-- XXX: lemma names are `div_lt_iff` vs `div_le_iff₀`; ping Yael!

lemma aux_8_0_5 (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) :
    2 ^ (-1 : ℝ) ≤ cutoff R t x y := by
  rw [mem_ball', mul_assoc] at h
  have : dist x y / (t * R) < 2 ^ (-1 : ℝ) := (div_lt_iff (by positivity)).mpr h
  calc 2 ^ (-1 : ℝ)
    _ ≤ 1 - dist x y / (t * R) := by
      norm_num at *; linarith only [h, this]
      -- bug: putting the cursor on the previous line shows 'no goals', but also
      -- "Error: The requested module 'blob:vscode-webview://1rd9dtr7c96784kh96b2qlls7kpl0nadnnmhqp1v0dsavkhrgljh/a2aa2681-8a8a-42aa-8c1e-e9fcde1af97c' does not provide an export named 'useRpcSession'"
    _ ≤ cutoff R t x y := le_max_right _ _

lemma aux_8_0_5'' (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) :
    ((2 ^ (-1 : ℝ))) ≤ (cutoff R t x y : ℝ≥0∞) := by
  rw [show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← ENNReal.coe_rpow_of_ne_zero (by norm_num)]
  exact ENNReal.coe_le_coe.mpr (aux_8_0_5 (ht := ht) (hR := hR) h)

lemma aux_8_0_6 (hR : 0 < R) (ht : 0 < t) :
    (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) ≤ ∫⁻ y, (cutoff R t x y) := by
  calc (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R))
    _ = ∫⁻ y in ((ball x (2 ^ (-1: ℝ) * t * R))), (2 ^ (-1: ℝ)) :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in (ball x (2 ^ (-1: ℝ) * t * R)), (cutoff R t x y) := by
      -- 'gcongr with y'' does too much: I want y in the ball, not in X
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

-- private lemma n_spec2 : ∀ n' < n_8_0_7, 2 ^ n' * t < 1 := sorry

-- I'm looking for a theorem like this for the two sorries below
theorem barXX {a b : ℝ} : ((2 : ℝ≥0) ^ a) * (2 ^ b) = 2 ^ (a + b) := by
  sorry

lemma aux_8_0_8 (hR : 0 < R) (ht : 0 < t) (ht' : t ≤ 1) :
    ∫⁻ y, cutoff R t x y ≥ 2 ^ ((-1 : ℝ) - a* ((@n_8_0_7 t) +2)) * volume (ball x (2*R)) := by
  calc ∫⁻ y, cutoff R t x y
    _ ≥ (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) := by
      apply aux_8_0_6
      exact hR
      exact ht
    _ ≥ (2 ^ ((-1 : ℝ) - a * ((@n_8_0_7 t) + 2))) * volume (ball x (2 ^ ((@n_8_0_7 t) + 2) * 2 ^ (-1 : ℝ) * t * R)) := by
      -- apply doubling n + 2 times; basic formula is `measure_ball_le_pow_two`
      sorry
    _ ≥ (2 ^ ((-1 : ℝ) - a * ((@n_8_0_7 t) + 2))) * volume (ball x (2 * R)) := by
      gcongr
      calc
        2 ≤ (2 * 2 ^ (@n_8_0_7 t)) * t := by
          rw [mul_assoc]
          -- more elegant way than these two lines?
          have h : (2 : ℝ) = 2 * 1 := by norm_num
          nth_rewrite 1 [h]
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

end new

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `ϕ ↦ \tilde{ϕ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (ϕ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * ϕ y) / (∫⁻ y, cutoff R t x y).toReal

/-- Part of Lemma 8.0.1. -/
lemma support_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t ϕ) ⊆ ball z (2 * R) := by
  unfold support
  intro x hx
  rw [mem_setOf] at hx
  have hx'' := left_ne_zero_of_mul hx
  have : ∃ y, (cutoff R t x y) * ϕ y ≠ 0 := sorry -- use hx'', somehow
  choose y hy using this
  have : y ∈ ball z R := hϕ (right_ne_zero_of_mul hy)
  have : x ∈ ball y (t * R) := by
    have hy'' : (cutoff R t x y) ≠ 0 := sorry -- have hy'' := (left_ne_zero_of_mul hy)
    have hy''' : (cutoff R t y x) ≠ 0 := sorry -- easy, dist is commutative
    exact aux_8_0_4 hR ht.1 hy'''
    -- XXX: why the extra factor t * R?
  -- then triangle inequality and done
  sorry

#exit

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
