import Carleson.Operators
import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities

open scoped ShortVariables

section

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

open ENNReal Set
namespace ShortVariables
-- q tilde in def. 6.1.9. TODO: Clean up bad notation
scoped notation "nnq'" => 2*nnq/(nnq + 1)

end ShortVariables

lemma inv_nnq'_eq : (nnq' : ℝ)⁻¹ = 2⁻¹ + 2⁻¹ * q⁻¹ := by
  have : 2 * q ≠ 0 := mul_ne_zero (by norm_num) (by linarith only [(q_mem_Ioc X).1])
  field_simp [show (nnq : ℝ) = q by rfl]

lemma inv_nnq'_mem_Ico : (nnq' : ℝ)⁻¹ ∈ Ico (3 / 4) 1 := by
  rw [inv_nnq'_eq]
  exact ⟨by linarith only [inv_q_mem_Ico X |>.1], by linarith only [inv_q_mem_Ico X |>.2]⟩

lemma one_lt_nnq' : 1 < nnq' := by
  rw [one_lt_div (add_pos_iff.mpr (Or.inr zero_lt_one)), two_mul, _root_.add_lt_add_iff_left]
  exact (q_mem_Ioc X).1

lemma one_lt_nnq'_coe : (1 : ℝ≥0∞) < nnq' := by
  rw [← coe_ofNat, ← ENNReal.coe_one, ← coe_add, ← coe_mul, ← coe_div (by simp), ENNReal.coe_lt_coe]
  exact one_lt_nnq'

lemma nnq'_lt_nnq : nnq' < nnq := by
  rw [add_comm, div_lt_iff₀ (add_pos (zero_lt_one) (nnq_pos X)), mul_comm,
    mul_lt_mul_iff_of_pos_left (nnq_pos X), ← one_add_one_eq_two, _root_.add_lt_add_iff_left]
  exact (nnq_mem_Ioc X).1

lemma nnq'_lt_nnq_coe: (nnq' : ℝ≥0∞) < nnq := by
  rw [← coe_ofNat, ← ENNReal.coe_one, ← coe_add, ← coe_mul, ← coe_div (by simp), ENNReal.coe_lt_coe]
  exact nnq'_lt_nnq

lemma nnq'_lt_two : nnq' < 2 := lt_of_lt_of_le nnq'_lt_nnq (nnq_mem_Ioc X).2

lemma nnq'_lt_two_coe : (nnq' : ℝ≥0∞) < 2 := by
  rw [← coe_ofNat, ← ENNReal.coe_one, ← coe_add, ← coe_mul, ← coe_div (by simp), ENNReal.coe_lt_coe]
  exact nnq'_lt_two

end

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

noncomputable section

open scoped GridStructure ComplexConjugate
open Set Complex MeasureTheory

-- Lemma 6.1.1
lemma E_disjoint {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
     {p p' : 𝔓 X} (hp : p ∈ 𝔄) (hp' : p' ∈ 𝔄) (hE : ¬Disjoint (E p) (E p')) : p = p' := by
  wlog h𝔰 : 𝔰 p ≤ 𝔰 p'
  · have hE' : ¬Disjoint (E p') (E p) := by rwa [disjoint_comm]
    exact (this h𝔄 hp' hp hE' (not_le.mp h𝔰).le).symm
  obtain ⟨x, hx, hx'⟩ := not_disjoint_iff.mp hE
  obtain ⟨hx𝓓p, hxΩp, -⟩ := hx; obtain ⟨hx𝓓p', hxΩp', -⟩ := hx'
  have h𝓓 : 𝓘 p ≤ 𝓘 p' :=
    (or_iff_left (not_disjoint_iff.mpr ⟨x, hx𝓓p, hx𝓓p'⟩)).mp (le_or_disjoint h𝔰)
  have hΩ : Ω p' ≤ Ω p :=
    (or_iff_right (not_disjoint_iff.mpr ⟨Q x, hxΩp, hxΩp'⟩)).mp (relative_fundamental_dyadic h𝓓)
  have hle : p ≤ p' := ⟨h𝓓, hΩ⟩
  exact h𝔄.eq hp hp' hle

--variable (K) (σ₁ σ₂) (p : 𝔓 X)

open MeasureTheory Metric
open ENNReal NNReal Real

/-- Constant appearing in Lemma 6.1.2. -/
noncomputable def C6_1_2 (a : ℕ) : ℕ := 2 ^ (107 * a ^ 3)

lemma C6_1_2_ne_zero (a : ℕ) : (C6_1_2 a : ℝ≥0∞) ≠ 0 := by rw [C6_1_2]; positivity

open MeasureTheory Metric Bornology Set

private lemma ineq_6_1_7 (x : X) {𝔄 : Set (𝔓 X)} (p : 𝔄) :
    (2 : ℝ≥0) ^ a ^ 3 / volume.real (ball x (↑D ^ 𝔰 p.1 / (↑D * 4))) ≤
      2 ^ (5 * a + 101 * a ^ 3) / volume.real (ball x (8 * ↑D ^ 𝔰 p.1)) := by
  calc (2 : ℝ≥0) ^ a ^ 3 / volume.real (ball x ((D : ℝ) ^ 𝔰 p.1 / (↑D * 4)))
    _ = 2 ^ a ^ 3 / volume.real (ball x ((1 / ((D : ℝ) * 32)) * (8 * D ^ 𝔰 p.1))) := by
      congr
      ring_nf
    _ = 2 ^ a ^ 3 * 2 ^ (5 * a + 100 * a ^ 3) / (2 ^ (5 * a + 100 * a ^ 3) *
          volume.real (ball x ((1 / ((D : ℝ) * 32)) * (8 * D ^ 𝔰 p.1)))) := by
        have hvol : volume.real (ball x (1 / ↑D / 32 * (8 * ↑D ^ 𝔰 p.1))) ≠ 0 :=
          ne_of_gt (measure_real_ball_pos _
            (mul_pos (div_pos (one_div_pos.mpr (defaultD_pos _)) (by positivity))
              (mul_pos (by positivity) (zpow_pos (defaultD_pos _) _))))
        rw [mul_div_assoc, ← div_div, div_eq_mul_inv]
        congr
        rw [eq_div_iff_mul_eq (by positivity), mul_comm, mul_assoc,
          mul_inv_cancel₀ hvol, mul_one]
    _ ≤ 2 ^ a ^ 3 * 2 ^ (5 * a + 100 * a ^ 3) / volume.real (ball x (8 * D ^ 𝔰 p.1)) := by
      gcongr
      · exact (measure_real_ball_pos x (mul_pos (by positivity) (zpow_pos (defaultD_pos _) _)))
      · have heq : 2 ^ (100 * a ^ 2) * 2 ^ 5 * (1 / (↑D * 32) * (8 * (D : ℝ) ^ 𝔰 p.1)) =
            (8 * ↑D ^ 𝔰 p.1) := by
          have hD : (D : ℝ) = 2 ^ (100 * a^2) := by simp
          rw [← hD]
          ring_nf
          rw [mul_inv_cancel₀ (defaultD_pos _).ne', one_mul]
        convert (DoublingMeasure.volume_real_ball_two_le_same_repeat x
          ((1 / ((D : ℝ) * 32)) * (8 * D ^ 𝔰 p.1)) (100*a^2 + 5)) using 1
        · conv_lhs => rw [← heq, ← pow_add]
        · congr 1
          simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat]
          ring
    _ = 2 ^ (5 * a + 101 * a ^ 3) / volume.real (ball x (8 * ↑D ^ 𝔰 p.1)) := by ring_nf

private lemma ineq_6_1_7' (x : X) {𝔄 : Set (𝔓 X)} (p : 𝔄) :
    (2 : ℝ≥0) ^ a ^ 3 / (volume (ball x (↑D ^ 𝔰 p.1 / (↑D * 4)))).toNNReal ≤
      2 ^ (5 * a + 101 * a ^ 3) / (volume (ball x (8 * ↑D ^ 𝔰 p.1))).toNNReal := by
  suffices (2 : ℝ≥0) ^ a ^ 3 / volume.real (ball x (↑D ^ 𝔰 p.1 / (↑D * 4))) ≤
      2 ^ (5 * a + 101 * a ^ 3) / volume.real (ball x (8 * ↑D ^ 𝔰 p.1)) by
    simp only [← NNReal.coe_le_coe, ← NNReal.val_eq_coe]
    exact this
  exact ineq_6_1_7 x p

-- Composition of inequalities 6.1.6, 6.1.7, 6.1.8.
lemma norm_Ks_le' {x y : X} {𝔄 : Set (𝔓 X)} (p : 𝔄) (hxE : x ∈ E ↑p) (hy : Ks (𝔰 p.1) x y ≠ 0)  :
    ‖Ks (𝔰 p.1) x y‖₊ ≤
      (2 : ℝ≥0) ^ (6*a + 101*a^3) / (volume (ball (𝔠 p.1) (8*D ^ 𝔰 p.1))).toNNReal := by
  have hDpow_pos : 0 < (D : ℝ) ^ 𝔰 p.1 := defaultD_pow_pos ..
  have h8Dpow_pos : 0 < 8 * (D : ℝ) ^ 𝔰 p.1 := mul_defaultD_pow_pos _ (by linarith) _
  have hdist_cp : dist x (𝔠 p) ≤ 4*D ^ 𝔰 p.1 := le_of_lt (mem_ball.mp (Grid_subset_ball hxE.1))
  have h : ‖Ks (𝔰 p.1) x y‖₊ ≤ (2 : ℝ≥0)^(a^3) / (volume (ball x (D ^ (𝔰 p.1 - 1)/4))).toNNReal := by
    apply le_trans (NNReal.coe_le_coe.mpr kernel_bound_old)
    rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, ← NNReal.val_eq_coe]
    exact div_le_div_of_nonneg_left (pow_nonneg zero_le_two _)
      (measure_ball_pos_real x _ (div_pos (zpow_pos (defaultD_pos _) _) zero_lt_four))
      (measureReal_mono (Metric.ball_subset_ball (dist_mem_Icc_of_Ks_ne_zero hy).1)
        measure_ball_ne_top)
  apply le_trans h
  rw [zpow_sub₀ (by simp), zpow_one, div_div]
  apply le_trans (ineq_6_1_7' x p)
  have ha : 6 * a + 101 * a ^ 3 = (5 * a + 101 * a ^ 3) + a := by omega
  simp only [div_eq_mul_inv, ge_iff_le]
  rw [ha, pow_add _ (5 * a + 101 * a ^ 3) a, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (zero_le _)
  suffices (volume (ball (𝔠 p.1) (8 * ↑D ^ 𝔰 p.1))).toNNReal ≤
      2 ^ a * (volume (ball x (8 * ↑D ^ 𝔰 p.1))).toNNReal by
    rw [le_mul_inv_iff₀, ← le_inv_mul_iff₀ , mul_comm _ (_^a), inv_inv]
    exact this
    · exact inv_pos.mpr (measure_ball_pos_nnreal _ _ h8Dpow_pos)
    · exact measure_ball_pos_nnreal _ _ h8Dpow_pos
  have h2 : dist x (𝔠 p) + 8 * ↑D ^ 𝔰 p.1 ≤ 2 * (8 * ↑D ^ 𝔰 p.1) :=
    calc dist x (𝔠 p) + 8 * ↑D ^ 𝔰 p.1
      ≤ 4 * ↑D ^ 𝔰 p.1 + 8 * ↑D ^ 𝔰 p.1 := (add_le_add_iff_right _).mpr hdist_cp
    _ ≤ 2 * (8 * ↑D ^ 𝔰 p.1) := by
      ring_nf
      exact mul_le_mul_of_nonneg (le_refl _) (by linarith) (le_of_lt hDpow_pos) (by linarith)
  convert measureNNReal_ball_le_of_dist_le' (μ := volume) zero_lt_two h2
  simp only [As, defaultA, Nat.cast_pow, Nat.cast_ofNat, Nat.one_lt_ofNat, logb_self_eq_one,
    Nat.ceil_one, pow_one]

-- lemma 6.1.2
lemma MaximalBoundAntichain {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (·≤·) 𝔄)
    {f : X → ℂ} (hfm : Measurable f) (x : X) :
    ‖carlesonSum 𝔄 f x‖ₑ ≤ (C6_1_2 a) * MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x := by
  classical
  by_cases hx : ∃ (p : 𝔄), carlesonOn p f x ≠ 0
  · obtain ⟨p, hpx⟩ := hx
    have hDpow_pos : 0 < (D : ℝ) ^ 𝔰 p.1 := defaultD_pow_pos ..
    have h8Dpow_pos : 0 < 8 * (D : ℝ) ^ 𝔰 p.1 := mul_defaultD_pow_pos _ (by linarith) _
    have hxE : x ∈ E ↑p := mem_of_indicator_ne_zero hpx
    have hne_p : ∀ b ∈ ({p | p ∈ 𝔄} : Finset (𝔓 X)), b ≠ ↑p → carlesonOn b f x = 0 := by
      intro p' hp' hpp'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp'
      by_contra hp'x
      exact hpp' (E_disjoint h𝔄 hp' p.2 <|
        not_disjoint_iff.mpr ⟨x, mem_of_indicator_ne_zero hp'x, hxE⟩)
    have hdist_cp : dist x (𝔠 p) ≤ 4*D ^ 𝔰 p.1 := le_of_lt (mem_ball.mp (Grid_subset_ball hxE.1))
    have hdist_y : ∀ {y : X} (hy : Ks (𝔰 p.1) x y ≠ 0),
        dist x y ∈ Icc ((D ^ ((𝔰 p.1) - 1) : ℝ) / 4) (D ^ (𝔰 p.1) / 2) := fun hy ↦
      dist_mem_Icc_of_Ks_ne_zero hy
    -- Ineq. 6.1.5. NOTE: I changed this to a strict inequality in the blueprint.
    have hdist_cpy : ∀ (y : X), (Ks (𝔰 p.1) x y ≠ 0) → dist (𝔠 p) y < 8*D ^ 𝔰 p.1 := by
      intro y hy
      calc dist (𝔠 p) y
        ≤ dist (𝔠 p) x + dist x y := dist_triangle (𝔠 p.1) x y
      _ ≤ 4*D ^ 𝔰 p.1 + dist x y := by simp only [add_le_add_iff_right, dist_comm, hdist_cp]
      _ ≤ 4*D ^ 𝔰 p.1 + D ^ 𝔰 p.1 /2 := by
        simp only [add_le_add_iff_left, (mem_Icc.mpr (hdist_y hy)).2]
      _ < 8*D ^ 𝔰 p.1 := by
        rw [div_eq_inv_mul, ← add_mul]
        exact mul_lt_mul_of_pos_right (by norm_num) (defaultD_pow_pos ..)
    -- 6.1.6, 6.1.7, 6.1.8
    have hKs : ∀ (y : X) (hy : Ks (𝔰 p.1) x y ≠ 0), ‖Ks (𝔰 p.1) x y‖₊ ≤
        (2 : ℝ≥0) ^ (6*a + 101*a^3) / (volume (ball (𝔠 p.1) (8*D ^ 𝔰 p.1))).toNNReal :=
      fun y hy ↦ norm_Ks_le' _ hxE hy
    calc (‖carlesonSum 𝔄 f x‖₊ : ℝ≥0∞)
      = ↑‖carlesonOn p f x‖₊:= by
          have hp : ↑p ∈ ({p | p ∈ 𝔄} : Finset (𝔓 X)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, Subtype.coe_prop, and_self]
          rw [carlesonSum, Finset.sum_eq_single_of_mem p.1 hp hne_p]
    _ ≤ ∫⁻ (y : X), ‖cexp (I * (↑((Q x) y) - ↑((Q x) x))) * Ks (𝔰 p.1) x y * f y‖ₑ := by
        rw [carlesonOn, indicator, if_pos hxE]
        refine le_trans (enorm_integral_le_lintegral_enorm _) (lintegral_mono fun z w h ↦ ?_)
        simp only [nnnorm_mul, coe_mul, some_eq_coe', zpow_neg, Ks, mul_assoc,
          enorm_eq_nnnorm] at h ⊢
        use w
    _ ≤ ∫⁻ (y : X), ‖Ks (𝔰 p.1) x y * f y‖ₑ := by
      simp only [enorm_mul]
      refine lintegral_mono_nnreal fun y ↦ ?_
      rw [mul_assoc]
      conv_rhs => rw [← one_mul (‖Ks (𝔰 p.1) x y‖₊ * ‖f y‖₊)]
      apply mul_le_mul_of_nonneg_right _ (zero_le _)
      · apply le_of_eq
        rw [mul_comm, ← Complex.ofReal_sub, NNReal.eq_iff,
          coe_nnnorm, NNReal.coe_one, Complex.norm_exp_ofReal_mul_I]
    _ = ∫⁻ (y : X) in ball (𝔠 ↑p) (8 * ↑D ^ 𝔰 p.1), ‖Ks (𝔰 p.1) x y * f y‖ₑ := by
        rw [MeasureTheory.setLIntegral_eq_of_support_subset]
        intro y hy
        simp only [enorm_mul, Function.support_mul, mem_inter_iff, Function.mem_support, ne_eq,
          enorm_eq_zero] at hy
        rw [mem_ball, dist_comm]
        exact hdist_cpy y hy.1
    _ ≤ ∫⁻ (y : X) in ball (𝔠 ↑p) (8 * ↑D ^ 𝔰 p.1),
        (((2 : ℝ≥0) ^ (6*a + 101*a^3) /
          (volume (ball (𝔠 p.1) (8*D ^ 𝔰 p.1))).toNNReal) * ‖f y‖₊ : ℝ≥0) := by
      refine lintegral_mono_nnreal fun y ↦ ?_
      rw [nnnorm_mul]
      gcongr
      by_cases hy : Ks (𝔰 p.1) x y = 0
      · simp [hy]
      · exact hKs y hy
    _ = (2 : ℝ≥0)^(5*a + 101*a^3 + a) *
        ⨍⁻ y, ‖f y‖ₑ ∂volume.restrict (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)) := by
      rw [laverage_eq, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      simp_rw [div_eq_mul_inv, coe_mul, enorm_eq_nnnorm]
      rw [lintegral_const_mul _ hfm.nnnorm.coe_nnreal_ennreal, ENNReal.coe_pow, coe_inv
        (ne_of_gt (measure_ball_pos_nnreal _ _ h8Dpow_pos)),
        ENNReal.coe_toNNReal measure_ball_ne_top]
      ring
    _ ≤ (C6_1_2 a) * (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)).indicator (x := x)
        (fun _ ↦ ⨍⁻ y, ‖f y‖ₑ ∂volume.restrict (ball (𝔠 p.1) (8*D ^ 𝔰 p.1))) := by
      simp only [coe_ofNat, indicator, mem_ball, mul_ite, mul_zero]
      rw [if_pos]
      · gcongr
        rw [C6_1_2, add_comm (5*a), add_assoc]; norm_cast
        apply pow_le_pow_right₀ one_le_two
        calc
        _ ≤ 101 * a ^ 3  + 6 * a ^ 3:= by
          rw [add_le_add_iff_left]
          ring_nf
          gcongr
          exact le_self_pow₀ (by linarith [four_le_a X]) (by omega)
        _ = 107 * a ^ 3 := by ring
      · exact lt_of_le_of_lt hdist_cp
          (mul_lt_mul_of_nonneg_of_pos (by linarith) (le_refl _) (by linarith) hDpow_pos)
    _ ≤ (C6_1_2 a) * MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x := by
      rw [mul_le_mul_left (C6_1_2_ne_zero a) coe_ne_top, MB, maximalFunction,
        inv_one, ENNReal.rpow_one, le_iSup_iff]
      simp only [iSup_le_iff, ENNReal.rpow_one]
      exact (fun _ hc ↦ hc p.1 p.2)
  · simp only [ne_eq, Subtype.exists, exists_prop, not_exists, not_and, Decidable.not_not] at hx
    have h0 : (carlesonSum 𝔄 f x) = 0 := by
      apply Finset.sum_eq_zero (fun p hp ↦ ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hx p hp
    simp only [h0, enorm_zero, zero_le]

-- TODO: PR to Mathlib
omit [MetricSpace X] in
lemma _root_.Set.eq_indicator_one_mul {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    f = (F.indicator 1) * f := by
  ext y
  simp only [Pi.mul_apply, indicator, Pi.one_apply, ite_mul, one_mul, zero_mul]
  split_ifs with hy
  · rfl
  · specialize hf y
    simp only [indicator, hy, ↓reduceIte] at hf
    rw [← norm_eq_zero]
    exact le_antisymm hf (norm_nonneg _)

/-- Constant appearing in Lemma 6.1.3. -/
noncomputable def C6_1_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (111 * a ^ 3) * (q - 1)⁻¹

-- -- Inequality 6.1.16
-- @[nolint unusedHavesSuffices]
-- lemma eLpNorm_maximal_function_le' {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
--     {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hfm : Measurable f) :
--     eLpNorm (fun x ↦ (maximalFunction volume (↑𝔄) 𝔠 (fun 𝔭 ↦ 8 * ↑D ^ 𝔰 𝔭)
--       ((2*nnq')/(3*nnq' - 2)) f x).toReal) 2 volume ≤
--       (2 ^ (2 * a)) * (3*nnq' - 2) / (2*nnq' - 2) * eLpNorm f 2 volume := by
--   set p₁ := (2*nnq')/(3*nnq' - 2) with hp₁
--   have aux : 0 < 3 * (2 * nnq / (nnq + 1)) - 2 := lt_trans (by norm_cast)
--     (tsub_lt_tsub_right_of_le (by norm_cast)
--       ((_root_.mul_lt_mul_left zero_lt_three).mpr one_lt_nnq'))
--   have hp₁_ge : 1 ≤ p₁ := by -- Better proof?
--     have h32 : (3 : ℝ≥0) - 2 = 1 := by norm_cast
--     rw [hp₁, one_le_div aux, tsub_le_iff_tsub_le, ← tsub_mul, h32, one_mul]
--     exact nnq'_lt_two.le
--   have hp₁_lt : p₁ < 2 := by
--     have rhs : 2 * (3 * (2 * nnq / (nnq + 1))) - 2 * (2 * nnq / (nnq + 1)) =
--       4 * (2 * nnq / (nnq + 1)) := by ring_nf; rw [← mul_tsub]; norm_cast
--     rw [hp₁, div_lt_iff₀ aux, mul_tsub, lt_tsub_comm, rhs, ← mul_one (2 * 2)]
--     exact _root_.mul_lt_mul' (by norm_cast) one_lt_nnq' zero_le_one zero_lt_four
--   /- have hF1 : AEStronglyMeasurable (F.indicator (1 : X → ℝ≥0∞)) volume :=
--     AEStronglyMeasurable.indicator aestronglyMeasurable_one measurableSet_F -/
--   -- Could this be deduced from hF1?
--   have hf1 : AEStronglyMeasurable f volume := hfm.aestronglyMeasurable
--   by_cases hf_top : eLpNorm f 2 volume < ⊤
--   · --have hf2 :  MemLp f 2 volume := ⟨hf1, hf_top⟩
--     have : HasStrongType (fun (f : X → ℂ) (x : X) ↦ maximalFunction volume 𝔄 𝔠
--         (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) p₁ f x) 2 2 volume volume (C2_0_6 (2^a) p₁ 2) :=
--       sorry
--       --hasStrongType_maximalFunction (X := X) hp₁_ge hp₁_lt (u := f) (r := fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) hf1
--     have hh := (this.toReal f ⟨hf1, hf_top⟩).2
--     simp only [hp₁, C2_0_6] at hh

--     convert hh
--     · congr
--       norm_cast
--       rw [← NNReal.coe_ofNat]
--       rw [NNReal.toReal]
--       simp only [val_eq_coe, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_add,
--         NNReal.coe_one]


--       /- rw [NNReal.coe_sub (r₁ := 3 * (2 * nnq / (nnq + 1))) (r₂ := 2)]
--       rw [← Real.coe_sub] -/

--       sorry
--     · norm_cast
--       --rw [ENNReal.coe_div]

--       --rw [← ENNReal.div_mul]
--       sorry
--   · simp only [not_lt, top_le_iff] at hf_top
--     rw [hf_top, mul_top]
--     · exact le_top
--     simp only [ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff',
--     OfNat.ofNat_ne_zero, false_or, false_and, sub_eq_top_iff, ofNat_ne_top, not_false_eq_true,
--     and_true, not_or]
--     refine ⟨?_, mul_ne_top ofNat_ne_top (mul_ne_top (mul_ne_top ofNat_ne_top coe_ne_top)
--       (inv_ne_top.mpr (by simp)))⟩
--     rw [tsub_eq_zero_iff_le]
--     exact not_le.mpr (lt_trans (by norm_cast)
--       (ENNReal.mul_lt_mul_left' three_ne_zero ofNat_ne_top one_lt_nnq'_coe))

-- Namespace for auxiliaries used in the proof of Lemma 6.1.3
namespace Lemma6_1_3

variable (𝔄 : Set (𝔓 X)) {f g : X → ℂ}

/-- The maximal function used in the proof of Lemma 6.1.3 -/
def 𝓜 := MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8 * D ^ 𝔰 𝔭) (E := ℂ)

section

include a q K σ₁ σ₂ F G
variable (X)
set_option linter.unusedSectionVars false

/-- The exponent $\tilde{q}$ in Lemma 6.1.3 -/
def qt := (nnq' : ℝ)

lemma inv_qt_eq : (qt X)⁻¹ = 2⁻¹ + 2⁻¹ * q⁻¹ := inv_nnq'_eq

/-- Exponent used for the application of H\"older's inequality in the proof of Lemma 6.1.3 -/
def p := (3 / 2 - (qt X)⁻¹)⁻¹

lemma inv_p_eq : (p X)⁻¹ = 3 / 2 - (qt X)⁻¹ := by simp only [p, inv_inv]

lemma inv_p_eq' : (p X)⁻¹ = 1 - 2⁻¹ * q⁻¹ := by simp only [inv_p_eq, inv_qt_eq]; ring

lemma p_pos : 0 < p X := by
  simp only [p, inv_qt_eq, inv_pos, sub_pos]; linarith only [inv_q_mem_Ico X |>.2]

lemma one_lt_p : 1 < p X := inv_one (G := ℝ) ▸ inv_lt_inv₀ (p_pos X)
  zero_lt_one |>.mp (inv_p_eq' X ▸ by linarith only [inv_q_mem_Ico X |>.1])

lemma p_lt_two : p X < 2 := inv_lt_inv₀ (by norm_num) (p_pos X)
  |>.mp (inv_p_eq' X ▸ by linarith only [inv_q_mem_Ico X |>.2])

end

/-- The `p` maximal function used in the proof. -/
def 𝓜p (p : ℝ) := maximalFunction volume 𝔄 𝔠 (fun 𝔭 ↦ 8 * D ^ 𝔰 𝔭) p.toNNReal (E := ℂ)

/-- Maximal function bound needed in the proof -/
lemma eLpNorm_𝓜p_le (hf : MemLp f 2) :
    eLpNorm (𝓜p 𝔄 (p X) f) 2 ≤ C2_0_6 (defaultA a) (p X).toNNReal 2 * eLpNorm f 2 :=
  hasStrongType_maximalFunction 𝔄.to_countable
    (by simp [p_pos X]) (by simp [p_lt_two X]) f hf |>.2

/-- A maximal function bound via an application of H\"older's inequality -/
lemma eLpNorm_𝓜_le_eLpNorm_𝓜p_mul (hf : Measurable f)
    (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    {p p' : ℝ} (hpp : p.HolderConjugate p') :
    eLpNorm (𝓜 𝔄 f) 2 ≤ (dens₂ 𝔄) ^ (p'⁻¹) * eLpNorm (𝓜p 𝔄 p f) 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf hfF

  have p_pos : 0 < p := hpp.left_pos
  have p'_pos : 0 < p' := hpp.right_pos
  have inv_p_pos : 0 < p⁻¹ := by positivity
  have inv_p'_pos : 0 < p'⁻¹ := by positivity
  have : ENNReal.ofReal p ≠ 0 := ofReal_ne_zero_iff.mpr p_pos
  have : ENNReal.ofReal p ≠ ⊤ := ofReal_ne_top
  have : ENNReal.ofReal p' ≠ 0 := ofReal_ne_zero_iff.mpr p'_pos
  have : ENNReal.ofReal p' ≠ ⊤ := ofReal_ne_top
  have hp_coe : p.toNNReal.toReal = p := Real.coe_toNNReal _ (by positivity)

  conv_lhs => rw [eq_indicator_one_mul hfF]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul''
  · exact AEStronglyMeasurable.maximalFunction 𝔄.to_countable
  · refine ae_of_all _ <| fun x ↦ ?_
    simp only [enorm_eq_self, 𝓜, MB_def]
    apply iSup_le_iff.mpr <| fun 𝔭 ↦ iSup_le_iff.mpr <| fun h𝔭 ↦ ?_
    apply indicator_le <| fun x hx ↦ ?_
    rw [laverage_eq] --, ← lintegral_indicator measurableSet_ball]
    conv_lhs => enter [1, 2, x]; rw [Pi.mul_apply, enorm_mul, mul_comm]
    set B := ball (𝔠 𝔭) (8 * ↑D ^ 𝔰 𝔭)
    set dB := volume.restrict B
    set mB := volume.restrict B univ
    have mB_pos : 0 < mB := by
      simp only [Measure.restrict_apply_univ B, mB]
      apply measure_ball_pos
      exact pos_of_mem_ball hx
    have mB_ne_top : mB ≠ ⊤ := by
      simpa only [Measure.restrict_apply_univ B, mB] using measure_ball_ne_top
    have hmeas : AEMeasurable (fun x ↦ ‖(F.indicator 1 x : ℂ)‖ₑ) (volume.restrict B) :=
      aemeasurable_const.indicator measurableSet_F |>.enorm
    calc
      _ ≤  eLpNorm (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal p) dB *
            eLpNorm (fun x ↦ ‖(F.indicator 1 x : ℂ)‖ₑ) (ENNReal.ofReal p') dB / mB := by
        gcongr
        exact ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm hpp.ennrealOfReal
          bf.enorm.aestronglyMeasurable.aemeasurable.restrict hmeas
      _ = (eLpNorm (fun x ↦ ‖(F.indicator 1 x : ℂ)‖ₑ) (ENNReal.ofReal p') dB / mB ^ (p'⁻¹))
          * (eLpNorm (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal p) dB / mB ^ (p⁻¹)) := by
        rw [mul_comm, div_eq_mul_inv]
        have := hpp.inv_add_inv_eq_one
        have : mB⁻¹ = (mB ^ (p⁻¹))⁻¹ * (mB ^ (p'⁻¹))⁻¹ := by
          rw [← ENNReal.mul_inv, ← ENNReal.rpow_add, hpp.inv_add_inv_eq_one, ENNReal.rpow_one]
          · exact ne_of_gt mB_pos
          · exact mB_ne_top
          · exact Or.inl <| ne_of_gt <| ENNReal.rpow_pos mB_pos mB_ne_top
          · exact Or.inr <| ne_of_gt <| ENNReal.rpow_pos mB_pos mB_ne_top
        rw [this, div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ _ := by
        gcongr
        · rw [eLpNorm_eq_lintegral_rpow_enorm (by assumption) (by assumption),
            toReal_ofReal <| le_of_lt p'_pos, one_div,
            ← div_rpow_of_nonneg _ _ (le_of_lt inv_p'_pos), dens₂]
          gcongr
          refine le_trans ?_ <| le_iSup₂ 𝔭 h𝔭
          refine le_trans ?_ <| le_iSup _ (8 * (D : ℝ) ^ 𝔰 𝔭)
          refine le_trans (le_of_eq ?_) <| le_iSup _ (by gcongr; norm_num)
          simp_rw [enorm_enorm]
          congr
          · rw [← lintegral_indicator_one <| measurableSet_F.inter measurableSet_ball,
              inter_indicator_one]
            conv_rhs => enter [2, x]; rw [Pi.mul_apply, ← indicator_mul_right]
            rw [lintegral_indicator measurableSet_ball]
            refine lintegral_congr (fun x ↦ ?_)
            rw [Pi.one_apply, mul_one, enorm_indicator_eq_indicator_enorm, indicator, indicator]
            split_ifs <;> simp [p'_pos]
          · exact Measure.restrict_apply_univ B
        · rw [eLpNorm_eq_lintegral_rpow_enorm (by assumption) (by assumption),
            toReal_ofReal <| le_of_lt p_pos, 𝓜p, maximalFunction, one_div,
            ← div_rpow_of_nonneg _ _ (le_of_lt inv_p_pos), ← laverage_eq, hp_coe]
          gcongr
          refine le_trans (le_of_eq ?_) <| le_iSup₂ 𝔭 h𝔭
          simp_rw [enorm_enorm]
          rw [indicator_of_mem hx]

/-- Tedious check that the constants work out -/
lemma const_check : C6_1_2 a * C2_0_6 (defaultA a) (p X).toNNReal 2 ≤ C6_1_3 a nnq := by
  sorry

end Lemma6_1_3

#check ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
#check eLpNorm_const_smul


-- Note: `(nnq' : ℝ)⁻¹ - 2⁻¹ = 2⁻¹ * q⁻¹`.
open Lemma6_1_3 in
/-- Lemma 6.1.3, inequality 6.1.11. -/
@[nolint unusedHavesSuffices]
lemma dens2_antichain {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (·≤·) 𝔄)
    {f : X → ℂ} (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hf : Measurable f)
    {g : X → ℂ} (hgG : ∀ x, ‖g x‖ ≤ G.indicator 1 x) (hg : Measurable g) :
    ‖∫ x, ((starRingEnd ℂ) (g x)) * carlesonSum 𝔄 f x‖ₑ ≤
      (C6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((nnq' : ℝ)⁻¹ - 2⁻¹) *
        eLpNorm f 2 * eLpNorm g 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf hfF
  have bg := bcs_of_measurable_of_le_indicator_g hg hgG

  apply le_trans <| enorm_integral_le_lintegral_enorm _
  simp_rw [enorm_mul]

  letI p := p X
  letI p' := ((qt X)⁻¹ - 2⁻¹)⁻¹
  have hp'_inv : p'⁻¹ = 2⁻¹ * q⁻¹ := by simp only [p', inv_inv, qt, inv_nnq'_eq]; simp
  have hpp : p.HolderConjugate p' := by
    refine Real.holderConjugate_iff.mpr ⟨one_lt_p X, ?_⟩
    rw [hp'_inv, inv_p_eq X]
    rw [div_eq_mul_inv, inv_qt_eq]
    ring

  letI C2_0_6' := C2_0_6 (defaultA a) p.toNNReal 2

  have := eLpNorm_𝓜_le_eLpNorm_𝓜p_mul 𝔄 hf hfF hpp
  have := eLpNorm_𝓜p_le 𝔄 <| bf.memLp 2

  calc
    _ ≤ eLpNorm g 2 * eLpNorm (carlesonSum 𝔄 f) 2 := by
      simpa [RCLike.enorm_conj, ← eLpNorm_enorm] using
        ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance
          bg.enorm.aestronglyMeasurable.aemeasurable
          bf.carlesonSum.enorm.aestronglyMeasurable.aemeasurable
    _ ≤ eLpNorm g 2 * (C6_1_2 a * eLpNorm (𝓜 𝔄 f) 2) := by
      gcongr
      exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
        (ae_of_all _ <| fun x ↦ MaximalBoundAntichain h𝔄 hf x) 2
    _ ≤ eLpNorm g 2 * (C6_1_2 a * ((dens₂ 𝔄) ^ (p'⁻¹) * eLpNorm (𝓜p 𝔄 p f) 2)) := by gcongr
    _ ≤ eLpNorm g 2 * (C6_1_2 a * ((dens₂ 𝔄) ^ (p'⁻¹) * (C2_0_6' * eLpNorm f 2))) := by gcongr
    _ = (C6_1_2 a * C2_0_6') * (dens₂ 𝔄) ^ (p'⁻¹) * eLpNorm f 2 * eLpNorm g 2 := by ring
    _ ≤ _ := by
      gcongr ?_ * ?_ * eLpNorm f 2 * eLpNorm g 2
      · exact_mod_cast const_check
      · simp only [hp'_inv, inv_nnq'_eq]; simp

  -- have ha : 4 ≤ a := four_le_a X
  -- have hf1 : f = (F.indicator 1) * f := eq_indicator_one_mul hf
  -- have hq0 : 0 < nnq := nnq_pos X
  -- -- have h1q' : 1 ≤ nnq' := le_of_lt one_lt_nnq'
  -- -- have hqq' : nnq' ≤ nnq := le_of_lt nnq'_lt_nnq
  -- have hq'_inv : (nnq' - 1)⁻¹ ≤ 3 * (nnq - 1)⁻¹ := by
  --   have : (nnq' - 1)⁻¹ = (nnq + 1)/(nnq -1) := by
  --     nth_rewrite 2 [← div_self (a := nnq + 1) (by simp)]
  --     rw [← NNReal.sub_div, inv_div, two_mul, NNReal.sub_def, NNReal.coe_add, NNReal.coe_add,
  --       add_sub_add_left_eq_sub]
  --     rfl
  --   rw [this, div_eq_mul_inv]
  --   gcongr
  --   rw [← two_add_one_eq_three, add_le_add_iff_right]
  --   exact (nnq_mem_Ioc X).2

  -- -- 6.1.14
  -- -- I am not sure if this is correctly stated
  -- have hMB_le : MB volume (𝔄 : Set (𝔓 X)) 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) (fun x ↦ ‖f x‖) ≤
  --   ((maximalFunction volume (𝔄 : Set (𝔓 X)) 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) ((2*nnq')/(3*nnq' - 2))
  --     (fun x ↦ ‖f x‖ * (dens₂ (𝔄 : Set (𝔓 X))).toReal ^ ((nnq' : ℝ)⁻¹ - 2⁻¹)))) := by
  --   sorry

  -- -- 6.1.14' : it seems what is actually used is the following:
  -- have hMB_le' : (eLpNorm (fun x ↦ ((MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x).toNNReal : ℂ))
  --     2 volume) ≤ (eLpNorm (fun x ↦ ((maximalFunction volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭)
  --       ((2*nnq')/(3*nnq' - 2)) f x).toNNReal : ℂ)) 2 volume) * (dens₂ (𝔄 : Set (𝔓 X))) := by
  --   sorry

  -- -- Trivial inequality used in 6.1.16 (long proof because of coercions)
  -- have h_div_le_div : (3*nnq' - 2 : ℝ≥0∞) / (2*nnq' - 2) ≤ 2^2 / (nnq' - 1) := by
  --   have heq : (2^2 : ℝ≥0∞) / (nnq' - 1) = 8 / (2 * nnq' - 2) := by
  --     have h8 : (8 : ℝ≥0∞) =  2 * 4 := by norm_cast
  --     have h2 : ((2 : ℝ≥0∞) * nnq' - 2) = 2 * (nnq' - 1) := by
  --       rw [ENNReal.mul_sub (fun _ _ ↦ ofNat_ne_top), mul_one]
  --     rw [h8, h2, ENNReal.mul_div_mul_left _ _ two_ne_zero ofNat_ne_top]
  --     ring_nf
  --   rw [heq]
  --   apply ENNReal.div_le_div_right
  --   calc 3 * (2 * ↑nnq / (↑nnq + 1)) - 2
  --     _ ≤ (3 * 2 : ℝ≥0∞) - 2 := by
  --       apply tsub_le_tsub_right
  --         ((ENNReal.mul_le_mul_left three_ne_zero ofNat_ne_top).mpr nnq'_lt_two_coe.le)
  --     _ ≤ (8 : ℝ≥0∞) := by norm_cast -- could just be ≤ 4

  --   -- 6.1.16. Note: could have 2 ^ (2*a + 1) in the RHS.
  -- have hMBp₁_le : eLpNorm (fun x ↦
  --     (maximalFunction volume (↑𝔄) 𝔠 (fun 𝔭 ↦ 8 * ↑D ^ 𝔰 𝔭) ((2*nnq')/(3*nnq' - 2)) f x).toReal)
  --     2 volume ≤ (2 ^ (2*a + 2) / (nnq' - 1)) * eLpNorm f 2 volume := by
  --   calc eLpNorm (fun x ↦ (maximalFunction volume (↑𝔄) 𝔠
  --       (fun 𝔭 ↦ 8 * ↑D ^ 𝔰 𝔭) ((2*nnq')/(3*nnq' - 2)) f x).toReal) 2 volume
  --     _ ≤ (2 ^ (2 * a)) * (3*nnq' - 2) / (2*nnq' - 2) * eLpNorm f 2 volume :=
  --       sorry --eLpNorm_maximal_function_le' h𝔄 hf hfm
  --     _ ≤ (2 ^ (2*a + 2) / (nnq' - 1)) * eLpNorm f 2 volume := by
  --       apply mul_le_mul_right'
  --       rw [pow_add, mul_div_assoc (2 ^ (2 * a)), mul_div_assoc (2 ^ (2 * a))]
  --       exact mul_le_mul_left' h_div_le_div _

  -- calc ↑‖∫ x, ((starRingEnd ℂ) (g x)) * carlesonSum 𝔄 f x‖₊
  --   _ ≤ (eLpNorm (carlesonSum 𝔄 f) 2 volume) * (eLpNorm g 2 volume) := by
  --     -- 6.1.18. Use Cauchy-Schwarz
  --     rw [mul_comm]
  --     sorry
  --   _ ≤ 2 ^ (107*a^3) * (eLpNorm (fun x ↦ ((MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x).toNNReal : ℂ))
  --         2 volume) * (eLpNorm g 2 volume) := by
  --     -- 6.1.19. Use Lemma 6.1.2.
  --     gcongr
  --     have h2 : (2 : ℝ≥0∞) ^ (107 * a ^ 3) = ‖(2 : ℝ) ^ (107 * a ^ 3)‖₊ := by
  --       simp only [nnnorm_pow, nnnorm_two, ENNReal.coe_pow, coe_ofNat]
  --     rw [h2, ← enorm_eq_nnnorm, ← eLpNorm_const_smul]
  --     sorry
  --     /- apply eLpNorm_mono_nnnorm
  --     intro z
  --     have MB_top : MB volume (↑𝔄) 𝔠 (fun 𝔭 ↦ 8 * ↑D ^ 𝔰 𝔭) f z ≠ ⊤ := by
  --      -- apply ne_top_of_le_ne_top _ (MB_le_eLpNormEssSup)
  --       --apply ne_of_lt
  --       --apply eLpNormEssSup_lt_top_of_ae_nnnorm_bound
  --       sorry
  --     rw [← ENNReal.coe_le_coe, Finset.sum_apply]
  --     convert (MaximalBoundAntichain h𝔄 hfm z)
  --     · sorry
  --     sorry/- simp only [Pi.smul_apply, real_smul, nnnorm_mul, nnnorm_eq, nnnorm_mul,
  --        nnnorm_real, nnnorm_pow, nnnorm_two,
  --       nnnorm_eq, coe_mul, C6_1_2, ENNReal.coe_toNNReal MB_top]
  --       norm_cast -/ -/
  --   _ ≤ 2 ^ (107*a^3 + 2*a + 2) * (nnq' - 1)⁻¹ * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((nnq' : ℝ)⁻¹ - 2⁻¹) *
  --       (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
  --     -- 6.1.20. use 6.1.14 and 6.1.16.
  --     rw [add_assoc, pow_add]
  --     apply mul_le_mul_of_nonneg_right _ (zero_le _)
  --     simp only [mul_assoc]
  --     apply mul_le_mul_of_nonneg_left _ (by norm_num)
  --     --apply le_trans hMB_le' hMBp₁_le
  --     sorry
  --   _ ≤ (C6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((nnq' : ℝ)⁻¹ - 2⁻¹) *
  --       (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
  --     -- use 4 ≤ a, hq'_inv.
  --     have h3 : 3 * ((C6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((nnq' : ℝ)⁻¹ - 2⁻¹) *
  --         (eLpNorm f 2 volume) * (eLpNorm g 2 volume)) =
  --         (2 : ℝ≥0)^(111*a^3) * (3 * (nnq-1)⁻¹) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((nnq' : ℝ)⁻¹ - 2⁻¹) *
  --         (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
  --       conv_lhs => simp only [C6_1_3, ENNReal.coe_mul, ← mul_assoc]
  --       rw [mul_comm 3, mul_assoc _ 3]
  --       norm_cast
  --     rw [← ENNReal.mul_le_mul_left (Ne.symm (NeZero.ne' 3)) ofNat_ne_top, h3]
  --     conv_lhs => simp only [← mul_assoc]
  --     gcongr
  --     · norm_cast
  --       calc 3 * 2 ^ (107 * a ^ 3 + 2 * a + 2)
  --         _ ≤ 4 * 2 ^ (107 * a ^ 3 + 2 * a + 2) := by gcongr; omega
  --         _ = 2 ^ (107 * a ^ 3 + 2 * a + 4) := by ring
  --         _ ≤ 2 ^ (107 * a ^ 3) * 2 ^ (4 * a ^ 3) := by
  --           rw [add_assoc, pow_add]
  --           gcongr
  --           · norm_num
  --           apply Nat.add_le_of_le_sub'
  --           · have h4a3 : 4 * a ^ 3 = 2 * a * (2 * a^2) := by ring
  --             exact h4a3 ▸ Nat.le_mul_of_pos_right _ (by positivity)
  --           · apply le_trans ha
  --             calc a
  --               _ ≤ a * (4 * a ^ 2 - 2) := by
  --                 apply Nat.le_mul_of_pos_right _
  --                 rw [tsub_pos_iff_lt]
  --                 exact lt_of_lt_of_le (by linarith)
  --                   (Nat.mul_le_mul_left 4 (pow_le_pow_left₀ zero_le_four ha 2))
  --               _ = 4 * a ^ 3 - 2 * a := by
  --                 rw [Nat.mul_sub]
  --                 ring_nf
  --         _ = 2 ^ (111 * a ^ 3) := by ring
  --     · norm_cast -- uses hq'_inv
