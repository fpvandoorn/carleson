import Carleson.MetricCarleson.Basic
import Carleson.Psi
import Carleson.FinitaryCarleson

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Bornology Metric Complex

noncomputable section

-- move to ENNReal.Inv
lemma ENNReal.div_div {x y z : ℝ≥0∞} (h1 : y ≠ 0 ∨ z ≠ ∞) (h2 : y ≠ ∞ ∨ z ≠ 0) :
    x / y / z = x / (y * z) := by
  simp_rw [div_eq_mul_inv, ENNReal.mul_inv h1 h2, mul_assoc]

variable {X : Type*} {a : ℕ} [MetricSpace X]
variable {q q' : ℝ} {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}

variable {F G : Set X} {f : X → ℂ} {s : ℤ} {σ₁ σ₂ : X → ℤ}

section Defs

variable [KernelProofData a K]
variable {x : X} {θ : Θ X} {R₁ R₂ : ℝ}
variable {Q : SimpleFunc X (Θ X)}
variable [IsCancellative X τ]

/-- The operator T_{R₁, R₂, R} introduced in Lemma 3.0.2. -/
def T_R (K : X → X → ℂ) (Q : SimpleFunc X (Θ X)) (R₁ R₂ R : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  (ball o R).indicator (fun x ↦ carlesonOperatorIntegrand K (Q x) R₁ R₂ f x) x

/-- The operator T_{s₁, s₂} introduced in Lemma 3.0.3. -/
def T_S (Q : SimpleFunc X (Θ X)) (s₁ s₂ : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y, ∑ s ∈ Finset.Icc s₁ s₂, Ks s x y * f y * exp (I * Q x y)

/-- The operator T_{2, σ₁, σ₂} introduced in Lemma 3.0.4. -/
def T_lin (Q : SimpleFunc X (Θ X)) (σ₁ σ₂ : X → ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ s ∈ Finset.Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * (Q x y - Q x x))

/-- The constant used in `linearized_truncation`.
Has value `2 ^ (445 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C3_0_4 (a : ℕ) (q : ℝ) : ℝ≥0 := 2 ^ (445 * a ^ 3) / (q.toNNReal - 1) ^ 6

end Defs

section Finitary

variable [FinitaryData a q K σ₁ σ₂ F]
/-- The sets `G_n` in Lemma 3.0.4, together with their properties. -/
def GData.Gn (G0 : GData a q K σ₁ σ₂ F) (n : ℕ) : GData a q K σ₁ σ₂ F :=
  GData.next^[n] G0

lemma Gn_succ (G0 : GData a q K σ₁ σ₂ F) (n : ℕ) : G0.Gn (n + 1) = (G0.Gn n).next :=
  Function.iterate_succ_apply' ..

lemma Gn_succ_G (G0 : GData a q K σ₁ σ₂ F) (n : ℕ) : (G0.Gn (n + 1)).G = (G0.Gn n).G' := by
  rw [Gn_succ]; rfl

lemma GData.volume_Gn_le (h : GData a q K σ₁ σ₂ F) (n : ℕ) :
    volume (h.Gn n).G ≤ volume h.G / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n _ =>
    calc volume (h.Gn (n + 1)).G
        = volume (h.Gn n).G' := by rw [Gn_succ_G]
      _ ≤ volume (h.Gn n).G / 2 := (h.Gn n).volume_G'_le
      _ ≤ volume h.G / 2 ^ n / 2 := by gcongr
      _ = volume h.G / 2 ^ (n + 1) := by rw [pow_succ, ENNReal.div_div] <;> norm_num

lemma GData.lintegral_Gn_sdiff_le (h : GData a q K σ₁ σ₂ F) (n : ℕ)
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in (h.Gn n).G \ (h.Gn (n+1)).G,
      ‖∑ s ∈ Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖ₑ ≤
    C2_0_1 a nnq * (volume (h.Gn n).G) ^ (1 - q⁻¹) * (volume F) ^ q⁻¹ := by
  rw [Gn_succ]; exact (h.Gn n).lintegral_sdiff_le hf h2f

lemma GData.lintegral_sdiff_Gn_le (h : GData a q K σ₁ σ₂ F) (n : ℕ)
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in (h.Gn n).G \ (h.Gn (n+1)).G,
      ‖∑ s ∈ Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖ₑ ≤
    C2_0_1 a nnq * (volume (h.Gn n).G) ^ (1 - q⁻¹) * (volume F) ^ q⁻¹ := by
  rw [Gn_succ]; exact (h.Gn n).lintegral_sdiff_le hf h2f


/- `S'` is `S` in the blueprint. -/
lemma linearized_truncation {S' : ℤ}
    (hqq' : q.HolderConjugate q') (G0 : GData a q K σ₁ σ₂ F)
    -- (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a))
    -- (hq : q ∈ Ioc 1 2)
    -- (hF : IsBounded F) (h2F : MeasurableSet F)
    -- (hG : IsBounded G) (h2G : MeasurableSet G)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1)
    -- (hσ₁ : Measurable σ₁) (hσ₂ : Measurable σ₂)
    -- (h2σ₁ : range σ₁ ⊆ Icc (- S') S') (h2σ₂ : range σ₂ ⊆ Icc (- S') S')
    -- (hσ : σ₁ ≤ σ₂)
    :
    ∫⁻ x in G, ‖T_lin Q σ₁ σ₂ f x‖ₑ ≤
    C3_0_4 a q * volume G ^ q'⁻¹ * volume F ^ q⁻¹ := by

  sorry

end Finitary

variable [PreProofData a q K σ₁ σ₂ F G]

/-- The constant used in `S_truncation`.
Has value `2 ^ (446 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C3_0_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (446 * a ^ 3) / (q - 1) ^ 6

/- `S'` is `S` in the blueprint. -/
lemma S_truncation {S' : ℤ}
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a))
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : IsBounded F) (h2F : MeasurableSet F) (hG : IsBounded G) (h2G : MeasurableSet G)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1) :
    ∫⁻ x in G, ⨆ (s₁ : ℤ) (s₂ : ℤ) (_ : - S' < s₁) (_ : s₁ < s₂) (_ : s₂ < S'), ‖T_S Q s₁ s₂ f x‖ₑ ≤
    C3_0_3 a q * volume G ^ q'⁻¹ * volume F ^ q⁻¹ := by
  sorry


/-- The constant used in `metric_carleson` and `R_truncation`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C1_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

lemma C1_0_2_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C1_0_2 a q := by
  rw [C1_0_2]
  apply div_pos
  · positivity
  · exact pow_pos (tsub_pos_of_lt hq) _


lemma R_truncation
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a))
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : volume F < ∞) (hG : volume G < ∞)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1)
    {n : ℤ} {R : ℝ} (hR : R = 2 ^ n) :
    ∫⁻ x in G, ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R⁻¹ < R₁) (_ : R₁ < R₂) (_ : R₂ < R), ‖T_R K Q R₁ R₂ R f x‖ₑ ≤
    C1_0_2 a q * volume G ^ q'⁻¹ * volume F ^ q⁻¹ := by
  sorry
