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

lemma cutoff_Lipschitz (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith (max 0 ⟨(1 / (t * R)), by positivity⟩) (fun y ↦ cutoff R t x y) := by
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

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `ϕ ↦ \tilde{ϕ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (ϕ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * ϕ y) / (∫⁻ y, cutoff R t x y).toReal

/-- Part of Lemma 8.0.1. -/
lemma support_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t ϕ) ⊆ ball z (2 * R) := by
  sorry

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
