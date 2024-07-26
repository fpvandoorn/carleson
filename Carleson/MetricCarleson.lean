-- import Carleson.FinitaryCarleson
import Carleson.Defs
import Mathlib.Tactic.Positivity.Basic

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators
open scoped ENNReal
noncomputable section

/- The constant used in `metric_carleson` -/
def C1_2 (a : ℕ) (q : ℝ) : ℝ := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

lemma C1_2_pos {a : ℕ} {q : ℝ} (hq : 1 < q) : 0 < C1_2 a q := by
  rw [C1_2]
  apply div_pos
  · positivity
  · apply pow_pos
    linarith [hq]

def C10_1 (a : ℕ) (q : ℝ) : ℝ := (C_K a) ^ 2 * C1_2 a q

lemma C10_1_pos {a : ℕ} {q : ℝ} (hq : 1 < q) : 0 < C10_1 a q := mul_pos (pow_two_pos_of_ne_zero (C_K_pos a).ne.symm) (C1_2_pos hq)

-- /- The constant used in equation (2.2) -/
-- def Ce2_2 (A : ℝ) (τ q : ℝ) : ℝ := sorry

-- lemma Ce2_2_pos (A : ℝ) (τ q : ℝ) : Ce2_2 A τ q > 0 := sorry

-- /- The constant used in equation (3.1) -/
-- def Ce3_1 (A : ℝ) (τ q : ℝ) : ℝ := sorry

-- lemma Ce3_1_pos (A : ℝ) (τ q : ℝ) : Ce3_1 A τ q > 0 := sorry

section -- todo: old code

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (2 ^ a : ℕ)] [Inhabited X]
variable {τ q q' : ℝ} {C : ℝ}
variable {F G : Set X}
variable (K : X → X → ℂ)

-- def D1_1 (A : ℝ) (τ q : ℝ) : ℝ := sorry

-- lemma two_lt_D1_1 (A : ℝ) (τ q : ℝ) : 2 < D1_1 A τ q := sorry

-- lemma D1_1_pos (A : ℝ) (τ q : ℝ) : D1_1 A τ q > 0 := zero_lt_two.trans (two_lt_D1_1 A τ q)

-- def Cψ1_1 (A : ℝ) (τ q : ℝ) : ℝ≥0 := sorry

-- lemma Cψ1_1_pos (A : ℝ) (τ : ℝ) : Cψ1_1 A τ C > 0 := sorry

-- old
-- /- (No need to take the supremum over the assumption `σ < σ'`.) -/
-- lemma equation3_1 {f : X → ℂ} (hf : LocallyIntegrable f)
--     (hΘ : ∀ Q ∈ Θ, ∀ x, (Q x).im = 0) :
--     let rhs := Ce3_1 a τ q * maximalFunction f x + ⨆ (Q ∈ Θ) (σ : ℤ) (σ' : ℤ),
--     ‖∑ s in Finset.Icc σ σ', ∫ y, Ks K D ψ s x y * f y * exp (I * (Q y - Q x))‖
--     CarlesonOperator K Θ f x ≤ rhs := by
--   intro rhs
--   have h_rhs : 0 ≤ rhs := by
--     sorry
--   rw [CarlesonOperator]
--   refine Real.iSup_le (fun Q ↦ ?_) h_rhs
--   refine Real.iSup_le (fun hQ ↦ ?_) h_rhs
--   refine Real.iSup_le (fun r ↦ ?_) h_rhs
--   refine Real.iSup_le (fun R ↦ ?_) h_rhs
--   refine Real.iSup_le (fun hrR ↦ ?_) h_rhs
--   let σ : ℤ := ⌊Real.logb D (2 * r)⌋ + 1
--   let σ' : ℤ := ⌈Real.logb D (4 * R)⌉
--   trans Ce3_1 a τ q * maximalFunction f x +
--     ‖∑ s in Finset.Icc σ σ', ∫ y, Ks K D ψ s x y * f y * exp (I * (Q y - Q x))‖
--   rw [← sub_le_iff_le_add]
--   simp_rw [mul_sub, Complex.exp_sub, mul_div, integral_div, ← Finset.sum_div,
--     norm_div]
--   have h1 : ‖cexp (I * Q x)‖ = 1 := by
--     lift Q x to ℝ using hΘ Q hQ x with qx
--     simp only [mul_comm I qx, norm_exp_ofReal_mul_I]
--   rw [h1, div_one]
--   /- use h3ψ here to rewrite the RHS -/
--   apply (norm_sub_norm_le _ _).trans
--   rw [← integral_finset_sum]
--   simp_rw [← Finset.sum_mul]
--   have h3 :
--     ∫ (y : X) in {y | dist x y ∈ Set.Ioo r R}, K x y * f y * cexp (I * Q y) =
--       ∫ (y : X) in {y | dist x y ∈ Set.Ioo r R}, (∑ x_1 in Finset.Icc σ σ', Ks K D ψ x_1 x y) * f y * cexp (I * Q y) := by
--     sorry
--   -- after we rewrite, we should have only 4 terms of our finset left, all others are 0. These can be estimated using |K x y| ≤ 1 / volume (ball x (dist x y)).
--   rw [h3, ← neg_sub, ← integral_univ, ← integral_diff]
--   all_goals sorry

  /- Proof should be straightforward from the definition of maximalFunction and conditions on `Θ`.
  We have to approximate `Q` by an indicator function.
  2^σ ≈ r, 2^σ' ≈ R
  There is a small difference in integration domain, and for that we use the estimate IsOneSidedKernel.norm_K_le_vol_inv
  -/

-- variable (C F G) in
-- /-- G₀-tilde in the paper -/
-- def G₀' : Set X :=
--   { x : X | maximalFunction (F.indicator (1 : X → ℂ)) x > C * volume.real F / volume.real G }

/- estimation of the volume of G₀' -/
-- lemma volume_G₀'_pos (hC : C1_2 A τ q < C) : volume.real (G₀' C F G) ≤ volume.real G / 4 := sorry

/- estimate first term (what does this mean exactly?) -/

/- for the second term, get Qtilde, σ, σ' as `MeasureTheory.SimpleFunc`.
Lars' argument:
* We can make the suprema countable, and then only consider a finite initial
segment. -/

/- define smin, smax -/

/- Lemma 3.1: obtain a Grid structure. Proof: [Chr90, Thm 11]. Taken by Joe Trate -/

/- Lemma 3.2: estimate local oscillation -/

/- Lemma 3.3: obtain tile structure -/

/- finish proof of equation (2.2) -/
-- old
-- theorem equation2_2
--     (hA : 1 < a) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
--     (hF : MeasurableSet F) (hG : MeasurableSet G)
--     (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞)
--     (hT : NormBoundedBy (ANCZOperatorLp 2 K) (2 ^ a ^ 3)) :
--     ∃ G', volume G' ≤ volume G / 2 ∧
--     ‖∫ x in G \ G', CarlesonOperator K Θ (indicator F 1) x‖₊ ≤
--     Ce2_2 a τ q * (volume.real G) ^ (1 / q') * (volume.real F) ^ (1 / q) := by
--   sorry

/- to prove theorem 1.1 from (2.2): bootstrapping argument, recursing over excised sets.
(section 2). -/

/- Theorem 1.2, written using constant C1_2 -/
theorem metric_carleson [CompatibleFunctions ℝ X (2 ^ a)]
  [IsCancellative X (defaultτ a)] [IsOneSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : HasBoundedStrongType (ANCZOperator K) 2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, CarlesonOperator K f x ≤
    ENNReal.ofReal (C1_2 a q) * (volume G) ^ q'⁻¹ * (volume F) ^ q⁻¹ := by
  sorry

/- Theorem 10.0.1, written using constant C1_2 -/
theorem two_sided_metric_carleson [CompatibleFunctions ℝ X (2 ^ a)]
  [IsCancellative X (defaultτ a)] [IsTwoSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, CarlesonOperator K f x ≤
    ENNReal.ofReal (C10_1 a q) * (volume G) ^ q'⁻¹ * (volume F) ^ q⁻¹ := by
  sorry

end

/- maybe investigate: making `volume` implicit in both `hg` and `h3g` of `metric_carleson` causes slow
elaboration. -/
