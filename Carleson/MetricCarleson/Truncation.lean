import Carleson.MetricCarleson.Basic
import Carleson.Psi
import Carleson.FinitaryCarleson

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Bornology Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X]
variable {q q' : ℝ≥0} {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}

variable [KernelProofData a K]
  {x : X} {θ : Θ X} {R₁ R₂ : ℝ}

variable {Q : SimpleFunc X (Θ X)}
variable {F G : Set X} {f : X → ℂ} {s : ℤ} {σ₁ σ₂ : X → ℤ}


variable
    [IsCancellative X (defaultτ a)]

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
def C3_0_4 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (445 * a ^ 3) / (q - 1) ^ 6

/- `S'` is `S` in the blueprint. -/
lemma linearized_truncation {S' : ℤ}
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : IsBounded F) (h2F : MeasurableSet F) (hG : IsBounded G) (h2G : MeasurableSet G)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1)
    (hσ₁ : Measurable σ₁) (hσ₂ : Measurable σ₂)
    (h2σ₁ : range σ₁ ⊆ Icc (- S') S') (h2σ₂ : range σ₂ ⊆ Icc (- S') S')
    (hσ : σ₁ ≤ σ₂) :
    ∫⁻ x in G, ‖T_lin Q σ₁ σ₂ f x‖ₑ ≤
    C3_0_4 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  let _ : PreProofData a q K σ₁ σ₂ F G :=
    { }
  sorry


/-- The constant used in `S_truncation`.
Has value `2 ^ (446 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C3_0_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (446 * a ^ 3) / (q - 1) ^ 6

/- `S'` is `S` in the blueprint. -/
lemma S_truncation {S' : ℤ}
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : IsBounded F) (h2F : MeasurableSet F) (hG : IsBounded G) (h2G : MeasurableSet G)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1) :
    ∫⁻ x in G, ⨆ (s₁ : ℤ) (s₂ : ℤ) (_ : - S' < s₁) (_ : s₁ < s₂) (_ : s₂ < S'), ‖T_S Q s₁ s₂ f x‖ₑ ≤
    C3_0_3 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
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
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : volume F < ∞) (hG : volume G < ∞)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1)
    {n : ℤ} {R : ℝ} (hR : R = 2 ^ n) :
    ∫⁻ x in G, ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R⁻¹ < R₁) (_ : R₁ < R₂) (_ : R₂ < R), ‖T_R K Q R₁ R₂ R f x‖ₑ ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  sorry
