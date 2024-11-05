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

lemma aux {α : Type*} [PseudoEMetricSpace α] {K : ℝ≥0} {f : α → ℝ} (hf : LipschitzWith K f) (c : ℝ) :
    LipschitzWith K (fun x ↦ c - f x) := by
  intro x y
  rw [edist_sub_left]
  apply hf

variable {R t : ℝ} {hR : 0 < R} {ht : 0 < t} {x y : X}

variable (hR ht) in
lemma cutoff_Lipschitz :
    LipschitzWith (max 0 ⟨(1 / (t * R)), by positivity⟩) (fun y ↦ cutoff R t x y) := by
  have aux0 : LipschitzWith 1 (fun y ↦ dist x y) := LipschitzWith.dist_right x
  have aux1 : LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ dist x y / (t * R)) := by
    -- WTF: this seems to be necessary
    haveI : SeminormedCommGroup ℝ := sorry
    let as := LipschitzWith.const (α := X) (1 / (t * R))
    -- but the next line still fails, no matter what
    --let asdf := LipschitzWith.mul (α := X) (E := ℝ) as aux0
    --apply LipschitzWith.mul (α := X) (E := ℝ) as aux0
    sorry
  have aux1' : LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ 1 - dist x y / (t * R)) := by
    intro y y'; apply aux aux1
  have : LipschitzWith (max 0 ⟨(1 / (t * R)), by positivity⟩) (fun y ↦ cutoff' R t x y) := by
    unfold cutoff'
    apply LipschitzWith.max (LipschitzWith.const' (0 : ℝ)) aux1'
  convert this

include hR ht in
@[fun_prop]
lemma cutoff_continuous : Continuous (fun y ↦ cutoff R t x y) := by
  apply (cutoff_Lipschitz hR ht (X := X)).continuous

include hR ht in
/-- `cutoff R t x` is measurable in `y`. -/
@[fun_prop]
lemma cutoff_measurable : Measurable (fun y ↦ cutoff R t x y) := by
  apply cutoff_continuous.measurable
  apply hR
  apply ht

-- xxx: exact? and aesop both cannot prove this
lemma leq_of_max_neq_left {a b : ℝ} (h : max a b ≠ a) : a < b := by
  by_contra! h'
  apply h (max_eq_left h')

lemma leq_of_max_neq_right {a b : ℝ} (h : max a b ≠ b) : b < a := by
  by_contra! h'
  exact h (max_eq_right h')

variable {ht': t ≤ 1}

include hR ht in
/-- equation 8.0.4 from the blueprint -/
lemma aux_8_0_4 (h : cutoff R t x y ≠ 0) : y ∈ ball x (t * R) := by
  rw [mem_ball']
  have : 0 < 1 - dist x y / (t * R) := by
    apply leq_of_max_neq_left
    rw [cutoff] at h
    -- best way now?
    convert h
    exact eq_iff_eq_of_cmp_eq_cmp rfl
  -- also works: field_simp at this; exact this
  apply (div_lt_one (by positivity)).mp (by linarith)

-- XXX: lemma names are `div_lt_iff` vs `div_le_iff₀`; ping Yael!

include hR ht in
lemma aux_8_0_5 (h : y ∈ ball x (2 ^ (-1: ℝ) * t * R)) : 2 ^ (-1 : ℝ) ≤ cutoff R t x y := by
  rw [mem_ball', mul_assoc] at h
  have : dist x y / (t * R) < 2 ^ (-1 : ℝ) := (div_lt_iff (by positivity)).mpr h
  calc 2 ^ (-1 : ℝ)
    _ ≤ 1 - dist x y / (t * R) := by
      norm_num at *; linarith only [h, this]
      -- bug: putting the cursor on the previous line shows 'no goals', but also
      -- "Error: The requested module 'blob:vscode-webview://1rd9dtr7c96784kh96b2qlls7kpl0nadnnmhqp1v0dsavkhrgljh/a2aa2681-8a8a-42aa-8c1e-e9fcde1af97c' does not provide an export named 'useRpcSession'"
    _ ≤ cutoff R t x y := le_max_right _ _

-- naming oddity: names with L take a monotonicity hypothesis *on s*,
-- names without L ask for global monotonicity
-- #check setLIntegral_mono_ae
-- #check setLIntegral_mono

include hR ht in
lemma aux_8_0_6 : (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) ≤ ∫⁻ y, (cutoff R t x y) := by
  calc (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R))
    _ = ∫⁻ y in ((ball x (2 ^ (-1: ℝ) * t * R))), (2 ^ (-1: ℝ)) :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in (ball x (2 ^ (-1: ℝ) * t * R)), (cutoff R t x y) := by
      -- 'gcongr with y'' does too much: I want y in the ball, not in X
      apply setLIntegral_mono (by fun_prop (discharger := assumption))
      intro y' hy'
      convert aux_8_0_5 hy' (hR := hR) (ht := ht)
      sorry -- mismatch: one side has NNReal, other has ENNReal
    _ ≤ ∫⁻ y, (cutoff R t x y) := setLIntegral_le_lintegral _ _

include ht' in
/-- The smallest integer `n` so that `2^n t ≥ 1`. -/
private def n_8_0_7 : ℕ := sorry -- log_2 of 1/t, rounded up to an integer

include ht' in -- use 1/t > 1 for existence/not being junk and the property of the log
private lemma n_spec1 : 1 ≤ 2 ^ n_8_0_7 * t := sorry

-- might not be needed
-- private lemma n_spec2 : ∀ n' < n_8_0_7, 2 ^ n' * t < 1 := sorry

-- xxx: simplify variable management; include hypotheses explicitly?

include hR ht ht' in
lemma aux_8_0_8 : ∫⁻ y, cutoff R t x y ≥ 2 ^ ((-1 : ℝ) - a* (n_8_0_7 +2)) * volume (ball x (2*R)) := by
  calc ∫⁻ y, cutoff R t x y
    _ ≥ (2 ^ (-1: ℝ)) * volume (ball x (2 ^ (-1: ℝ) * t * R)) := by
      apply aux_8_0_6
      exact hR
      exact ht
    _ ≥ (2 ^ ((-1 : ℝ) - a * (n_8_0_7 + 2))) * volume (ball x (2 ^ (n_8_0_7 + 2) * 2 ^ (-1 : ℝ) * t * R)) := by
      sorry -- apply doubling n + 2 times; use induction (for all k) and specialize to n + 2?
    _ ≥ (2 ^ ((-1 : ℝ) - a * (n_8_0_7 + 2))) * volume (ball x (2 * R)) := by
      gcongr
      calc
        2 ≤ (2 * 2 ^ n_8_0_7) * t := by
          rw [mul_assoc]
          -- more elegant way than these two lines?
          have h : (2 : ℝ) = 2 * 1 := by norm_num
          nth_rewrite 1 [h]
          gcongr
          exact n_spec1 (ht' := ht')
        _ = (2 ^ (n_8_0_7 + 2) * 2 ^ (-1 : ℝ)) * t := by
          ring

end new

#exit

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
