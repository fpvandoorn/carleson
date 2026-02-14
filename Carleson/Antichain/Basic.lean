import Carleson.Calculations
import Carleson.Operators
import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities

/-!
# 6.1. The density arguments

This file contains the proofs of lemmas 6.1.1, 6.1.2 and 6.1.3 from the blueprint.

## Main results
- `tile_disjointness`: Lemma 6.1.1.
- `maximal_bound_antichain`: Lemma 6.1.2.
- `dens2_antichain`: Lemma 6.1.3.
-/

open scoped ShortVariables

section

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

open ENNReal Set

namespace ShortVariables

/-- $\tilde{q}$ from definition 6.1.10, as a nonnegative real number. Note that
`(nnqt : ℝ)⁻¹ - 2⁻¹ = 2⁻¹ * q⁻¹`. -/
scoped notation "nnqt" => 2*nnq/(nnq + 1)

end ShortVariables

lemma inv_nnqt_eq : (nnqt : ℝ)⁻¹ = 2⁻¹ + 2⁻¹ * q⁻¹ := by
  have : q ≠ 0 := by linarith only [(q_mem_Ioc X).1]
  simp [show (nnq : ℝ) = q by rfl]
  field_simp

lemma inv_nnqt_mem_Ico : (nnqt : ℝ)⁻¹ ∈ Ico (3 / 4) 1 := by
  rw [inv_nnqt_eq]
  exact ⟨by linarith only [inv_q_mem_Ico X |>.1], by linarith only [inv_q_mem_Ico X |>.2]⟩

lemma one_lt_nnqt : 1 < nnqt := by
  rw [one_lt_div (add_pos_iff.mpr (Or.inr zero_lt_one)), two_mul, add_lt_add_iff_left]
  exact (q_mem_Ioc X).1

lemma one_lt_nnqt_coe : (1 : ℝ≥0∞) < nnqt := by
  rw [← coe_ofNat, ← coe_one, ← coe_add, ← coe_mul, ← coe_div (by simp), coe_lt_coe]
  exact one_lt_nnqt

lemma nnqt_lt_nnq : nnqt < nnq := by
  rw [add_comm, div_lt_iff₀ (add_pos (zero_lt_one) (nnq_pos X)), mul_comm,
    mul_lt_mul_iff_of_pos_left (nnq_pos X), ← one_add_one_eq_two, _root_.add_lt_add_iff_left]
  exact (nnq_mem_Ioc X).1

lemma nnqt_lt_nnq_coe : (nnqt : ℝ≥0∞) < nnq := by
  rw [← coe_ofNat, ← coe_one, ← coe_add, ← coe_mul, ← coe_div (by simp), coe_lt_coe]
  exact nnqt_lt_nnq

lemma nnqt_lt_two : nnqt < 2 := lt_of_lt_of_le nnqt_lt_nnq (nnq_mem_Ioc X).2

lemma nnqt_lt_two_coe : (nnqt : ℝ≥0∞) < 2 := by
  rw [← coe_ofNat, ← coe_one, ← coe_add, ← coe_mul, ← coe_div (by simp), coe_lt_coe]
  exact nnqt_lt_two

end

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

noncomputable section

open Complex MeasureTheory Set

/-- Lemma 6.1.1. -/
lemma tile_disjointness {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) (𝔄 : Set (𝔓 X)))
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
  exact h𝔄.eq hp hp' ⟨h𝓓, hΩ⟩

open ENNReal Metric NNReal Real

/-- Constant appearing in Lemma 6.1.2.
Has value `2 ^ (102 * a ^ 3)` in the blueprint. -/
noncomputable def C6_1_2 (a : ℕ) : ℕ := 2 ^ ((𝕔 + 2) * a ^ 3)

lemma C6_1_2_ne_zero (a : ℕ) : (C6_1_2 a : ℝ≥0∞) ≠ 0 := by rw [C6_1_2]; positivity

private lemma ineq_6_1_7 (x : X) {𝔄 : Set (𝔓 X)} (p : 𝔄) :
    (2 : ℝ≥0∞) ^ a ^ 3 / volume (ball x (D ^ 𝔰 p.1 / (D * 4))) ≤
    2 ^ (5 * a + (𝕔 + 1) * a ^ 3) / volume (ball x (8 * D ^ 𝔰 p.1)) := by
  calc
    _ = 2 ^ a ^ 3 / volume (ball x (1 / (D * 32) * (8 * D ^ 𝔰 p.1))) := by congr! 3; ring
    _ = 2 ^ a ^ 3 * 2 ^ (5 * a + 𝕔 * a ^ 3) / (2 ^ (5 * a + 𝕔 * a ^ 3) *
        volume (ball x (1 / (D * 32) * (8 * D ^ 𝔰 p.1)))) := by
      rw [mul_div_assoc, ← div_div, div_eq_mul_inv]
      conv_rhs => rw [← inv_inv (volume _), ← div_eq_mul_inv,
        ENNReal.div_div_cancel (by positivity) (by finiteness)]
    _ ≤ 2 ^ a ^ 3 * 2 ^ (5 * a + 𝕔 * a ^ 3) / volume (ball x (8 * D ^ 𝔰 p.1)) := by
      gcongr
      · have heq : 2 ^ (𝕔 * a ^ 2) * 2 ^ 5 * (1 / (D * 32) * (8 * (D : ℝ) ^ 𝔰 p.1)) =
            8 * D ^ 𝔰 p.1 := by
          have hD : (D : ℝ) = 2 ^ (𝕔 * a^2) := by simp
          rw [← hD]
          ring_nf
          rw [mul_inv_cancel₀ (realD_pos _).ne', one_mul]
        convert measure_ball_two_le_same_iterate (μ := volume) x
          (1 / (D * 32) * (8 * D ^ 𝔰 p.1)) (𝕔*a^2 + 5) using 2
        · conv_lhs => rw [← heq, ← pow_add]
        · rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.coe_pow, coe_ofNat]; ring
    _ = _ := by ring_nf

-- Composition of inequalities 6.1.6, 6.1.7, 6.1.8.
lemma norm_Ks_le' {x y : X} {𝔄 : Set (𝔓 X)} (p : 𝔄) (hxE : x ∈ E ↑p) (hy : Ks (𝔰 p.1) x y ≠ 0) :
    ‖Ks (𝔰 p.1) x y‖ₑ ≤ 2 ^ (6 * a + (𝕔 + 1) * a ^ 3) / volume (ball (𝔠 p.1) (8 * D ^ 𝔰 p.1)) := by
  have hDpow_pos : 0 < (D : ℝ) ^ 𝔰 p.1 := defaultD_pow_pos ..
  have h8Dpow_pos : 0 < 8 * (D : ℝ) ^ 𝔰 p.1 := mul_defaultD_pow_pos _ (by linarith) _
  have hdist_cp : dist x (𝔠 p) ≤ 4 * D ^ 𝔰 p.1 := (mem_ball.mp (Grid_subset_ball hxE.1)).le
  have h : ‖Ks (𝔰 p.1) x y‖ₑ ≤ 2 ^ a ^ 3 / volume (ball x (D ^ (𝔰 p.1 - 1) / 4)) := by
    apply kernel_bound.trans
    grw [C_K, ← Nat.cast_pow, NNReal.rpow_natCast, ENNReal.coe_pow, coe_ofNat, vol,
      (dist_mem_Icc_of_Ks_ne_zero hy).1]
  apply h.trans
  rw [zpow_sub₀ (by simp), zpow_one, div_div]
  apply (ineq_6_1_7 x p).trans
  have ha : 6 * a + (𝕔 + 1) * a ^ 3 = (5 * a + (𝕔 + 1) * a ^ 3) + a := by lia
  simp only [div_eq_mul_inv, ge_iff_le]
  rw [ha, pow_add _ (5 * a + (𝕔 + 1) * a ^ 3) a, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (zero_le _)
  suffices volume (ball (𝔠 p.1) (8 * D ^ 𝔰 p.1)) ≤ 2 ^ a * volume (ball x (8 * D ^ 𝔰 p.1)) by
    grw [← inv_inv (2 ^ a), ← ENNReal.mul_inv (.inl (by simp)) (.inl (by finiteness)),
      ENNReal.inv_le_inv, ← ENNReal.div_eq_inv_mul, ENNReal.div_le_of_le_mul' this]
  have h2 : dist x (𝔠 p) + 8 * D ^ 𝔰 p.1 ≤ 2 * (8 * D ^ 𝔰 p.1) :=
    calc
      _ ≤ (4 : ℝ) * D ^ 𝔰 p.1 + 8 * D ^ 𝔰 p.1 := (add_le_add_iff_right _).mpr hdist_cp
      _ ≤ _ := by linarith
  convert measure_ball_le_of_dist_le' (μ := volume) zero_lt_two h2
  simp [As]

/-- Lemma 6.1.2. -/
lemma maximal_bound_antichain {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
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
      rw [Finset.mem_filter_univ] at hp'
      by_contra hp'x
      exact hpp' (tile_disjointness h𝔄 hp' p.2 <|
        not_disjoint_iff.mpr ⟨x, mem_of_indicator_ne_zero hp'x, hxE⟩)
    have hdist_cp : dist x (𝔠 p) ≤ 4*D ^ 𝔰 p.1 := le_of_lt (mem_ball.mp (Grid_subset_ball hxE.1))
    have hdist_y : ∀ {y : X} (hy : Ks (𝔰 p.1) x y ≠ 0),
        dist x y ∈ Icc ((D ^ ((𝔰 p.1) - 1) : ℝ) / 4) (D ^ (𝔰 p.1) / 2) := fun hy ↦
      dist_mem_Icc_of_Ks_ne_zero hy
    -- Ineq. 6.1.5.
    have hdist_cpy : ∀ (y : X), (Ks (𝔰 p.1) x y ≠ 0) → dist (𝔠 p) y < 8*D ^ 𝔰 p.1 := fun y hy ↦
      calc dist (𝔠 p) y
        ≤ dist (𝔠 p) x + dist x y := dist_triangle (𝔠 p.1) x y
      _ ≤ 4*D ^ 𝔰 p.1 + dist x y := by simp only [add_le_add_iff_right, dist_comm, hdist_cp]
      _ ≤ 4*D ^ 𝔰 p.1 + D ^ 𝔰 p.1 /2 := by
        simp only [add_le_add_iff_left, (mem_Icc.mpr (hdist_y hy)).2]
      _ < 8*D ^ 𝔰 p.1 := by
        rw [div_eq_inv_mul, ← add_mul]
        exact mul_lt_mul_of_pos_right (by norm_num) (defaultD_pow_pos ..)
    calc
    _ = ‖carlesonOn p f x‖ₑ := by
        have hp : ↑p ∈ ({p | p ∈ 𝔄} : Finset (𝔓 X)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, Subtype.coe_prop, and_self]
        rw [carlesonSum, Finset.sum_eq_single_of_mem p.1 hp hne_p]
    _ ≤ ∫⁻ y, ‖exp (I * (Q x y - Q x x)) * Ks (𝔰 p.1) x y * f y‖ₑ := by
        rw [carlesonOn, indicator, if_pos hxE]
        exact le_trans (enorm_integral_le_lintegral_enorm _) (lintegral_mono fun z ↦ le_rfl)
    _ ≤ ∫⁻ y, ‖Ks (𝔰 p.1) x y * f y‖ₑ := by
      simp only [enorm_mul]
      exact lintegral_mono fun y ↦ (by simp [← Complex.ofReal_sub])
    _ = ∫⁻ y in ball (𝔠 p) (8 * D ^ 𝔰 p.1), ‖Ks (𝔰 p.1) x y * f y‖ₑ := by
        rw [setLIntegral_eq_of_support_subset]
        intro y hy
        simp only [enorm_mul, Function.support_mul, mem_inter_iff, Function.mem_support, ne_eq,
          enorm_eq_zero] at hy
        rw [mem_ball, dist_comm]
        exact hdist_cpy y hy.1
    _ ≤ ∫⁻ y in ball (𝔠 p) (8 * D ^ 𝔰 p.1),
        2 ^ (6 * a + (𝕔 + 1) * a ^ 3) / volume (ball (𝔠 p.1) (8 * D ^ 𝔰 p.1)) * ‖f y‖ₑ := by
      refine lintegral_mono fun y ↦ ?_
      rw [enorm_mul]; gcongr
      by_cases hy : Ks (𝔰 p.1) x y = 0
      · simp [hy]
      · exact norm_Ks_le' _ hxE hy -- Composition of ineq. 6.1.6, 6.1.7, 6.1.8
    _ = 2 ^ (5 * a + (𝕔 + 1) * a ^ 3 + a) *
        ⨍⁻ y in ball (𝔠 p.1) (8 * D ^ 𝔰 p.1), ‖f y‖ₑ ∂volume := by
      rw [lintegral_const_mul _ hfm.enorm, ENNReal.mul_comm_div, setLAverage_eq]
      congr 2; ring
    _ ≤ C6_1_2 a * (ball (𝔠 p.1) (8 * D ^ 𝔰 p.1)).indicator (x := x)
        (fun _ ↦ ⨍⁻ y in ball (𝔠 p.1) (8 * D ^ 𝔰 p.1), ‖f y‖ₑ ∂volume) := by
      simp only [indicator, mem_ball, mul_ite, mul_zero]
      rw [if_pos]
      · gcongr
        rw [C6_1_2, add_comm (5 * a), add_assoc]; norm_cast
        apply pow_le_pow_right₀ one_le_two
        ring_nf
        suffices 6 * a ≤ a ^ 3 by lia
        linarith [sixteen_times_le_cube (four_le_a X)]
      · exact lt_of_le_of_lt hdist_cp
          (mul_lt_mul_of_nonneg_of_pos (by linarith) (le_refl _) (by linarith) hDpow_pos)
    _ ≤ C6_1_2 a * MB volume 𝔄 𝔠 (8 * D ^ 𝔰 ·) f x := by
      rw [ENNReal.mul_le_mul_iff_right (C6_1_2_ne_zero a) coe_ne_top, MB, maximalFunction,
        inv_one, ENNReal.rpow_one, le_iSup_iff]
      simp only [iSup_le_iff, ENNReal.rpow_one]
      exact (fun _ hc ↦ hc p.1 p.2)
  · simp only [ne_eq, Subtype.exists, exists_prop, not_exists, not_and, not_not] at hx
    have h0 : carlesonSum 𝔄 f x = 0 :=
      Finset.sum_eq_zero (fun p hp ↦ hx p ((Finset.mem_filter_univ _).mp hp))
    simp [h0]

/-- Constant appearing in Lemma 6.1.3.
Has value `2 ^ (103 * a ^ 3)` in the blueprint. -/
noncomputable def C6_1_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ ((𝕔 + 3) * a ^ 3) * (q - 1)⁻¹

-- Namespace for auxiliaries used in the proof of Lemma 6.1.3.
namespace Lemma6_1_3

variable (𝔄 : Set (𝔓 X)) {f g : X → ℂ}

/-- The maximal function used in the proof of Lemma 6.1.3 -/
def 𝓜 := MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8 * D ^ 𝔰 𝔭) (E := ℂ)

-- Define exponents used in the proof and collect some basic facts about them.
section

include a q K σ₁ σ₂ F G
variable (X)
--set_option linter.unusedSectionVars false
omit [TileStructure Q D κ S o]

/-- $\tilde{q}$ from definition 6.1.10, as a real number. -/
def qt := (nnqt : ℝ)

lemma inv_qt_eq : (qt X)⁻¹ = 2⁻¹ + 2⁻¹ * q⁻¹ := inv_nnqt_eq

/-- Exponent used for the application of Hölder's inequality in the proof of Lemma 6.1.3. -/
def p := (3 / 2 - (qt X)⁻¹)⁻¹

lemma inv_p_eq : (p X)⁻¹ = 3 / 2 - (qt X)⁻¹ := by simp only [p, inv_inv]

lemma inv_p_eq' : (p X)⁻¹ = 1 - 2⁻¹ * q⁻¹ := by simp only [inv_p_eq, inv_qt_eq]; ring

lemma p_pos : 0 < p X := by
  simp only [p, inv_qt_eq, inv_pos, sub_pos]; linarith [inv_q_mem_Ico X |>.2]

lemma one_lt_p : 1 < p X := inv_one (G := ℝ) ▸ inv_lt_inv₀ (p_pos X)
  zero_lt_one |>.mp (inv_p_eq' X ▸ by linarith [inv_q_mem_Ico X |>.1])

lemma p_lt_two : p X < 2 := inv_lt_inv₀ (by norm_num) (p_pos X)
  |>.mp (inv_p_eq' X ▸ by linarith [inv_q_mem_Ico X |>.2])

end

/-- The `p` maximal function used in the proof. -/
def 𝓜p (p : ℝ) := maximalFunction volume 𝔄 𝔠 (fun 𝔭 ↦ 8 * D ^ 𝔰 𝔭) p.toNNReal (E := ℂ)

/-- Maximal function bound needed in the proof -/
lemma eLpNorm_𝓜p_le (hf : MemLp f 2) :
    eLpNorm (𝓜p 𝔄 (p X) f) 2 ≤ C2_0_6 (defaultA a) (p X).toNNReal 2 * eLpNorm f 2 :=
  hasStrongType_maximalFunction 𝔄.to_countable
    (by simp [p_pos X]) (by simp [p_lt_two X]) f hf |>.2

/-- A maximal function bound via an application of H\"older's inequality -/
lemma eLpNorm_𝓜_le_eLpNorm_𝓜p_mul (hf : Measurable f) (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
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
  conv_lhs => rw [eq_indicator_one_mul_of_norm_le hfF]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _
    (AEStronglyMeasurable.maximalFunction 𝔄.to_countable) (ae_of_all _ <| fun x ↦ ?_)
  simp only [enorm_eq_self, 𝓜, MB_def]
  apply iSup_le_iff.mpr <| fun 𝔭 ↦ iSup_le_iff.mpr <| fun h𝔭 ↦ ?_
  apply indicator_le <| fun x hx ↦ ?_
  rw [laverage_eq]
  conv_lhs => enter [1, 2, x]; rw [Pi.mul_apply, enorm_mul, mul_comm]
  set B := ball (𝔠 𝔭) (8 * ↑D ^ 𝔰 𝔭)
  set dB := volume.restrict B
  set mB := volume.restrict B univ
  have mB_pos : 0 < mB := by
    simp only [Measure.restrict_apply_univ B, mB]
    exact measure_ball_pos _ _ (pos_of_mem_ball hx)
  have mB_ne_top : mB ≠ ⊤ := by
    simpa [Measure.restrict_apply_univ B, mB] using measure_ball_ne_top
  have hmeas : AEMeasurable (fun x ↦ ‖(F.indicator 1 x : ℂ)‖ₑ) (volume.restrict B) :=
    aemeasurable_const.indicator measurableSet_F |>.enorm
  calc
    _ ≤  eLpNorm (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal p) dB *
          eLpNorm (fun x ↦ ‖(F.indicator 1 x : ℂ)‖ₑ) (ENNReal.ofReal p') dB / mB := by
      gcongr
      exact lintegral_mul_le_eLpNorm_mul_eLqNorm hpp.ennrealOfReal
        bf.enorm.aestronglyMeasurable.aemeasurable.restrict hmeas
    _ = (eLpNorm (fun x ↦ ‖(F.indicator 1 x : ℂ)‖ₑ) (ENNReal.ofReal p') dB / mB ^ (p'⁻¹))
        * (eLpNorm (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal p) dB / mB ^ (p⁻¹)) := by
      rw [mul_comm, div_eq_mul_inv]
      have : mB⁻¹ = (mB ^ (p⁻¹))⁻¹ * (mB ^ (p'⁻¹))⁻¹ := by
        rw [← ENNReal.mul_inv (Or.inl <| ne_of_gt <| ENNReal.rpow_pos mB_pos mB_ne_top)
          (Or.inr <| ne_of_gt <| ENNReal.rpow_pos mB_pos mB_ne_top), ← ENNReal.rpow_add _ _
          (ne_of_gt mB_pos) mB_ne_top, hpp.inv_add_inv_eq_one, ENNReal.rpow_one]
      rw [this, div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ ≤ _ := by
      gcongr
      · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by assumption) (by assumption), toReal_ofReal <|
          le_of_lt p'_pos, one_div, ← div_rpow_of_nonneg _ _ (le_of_lt inv_p'_pos), dens₂]
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
      · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by assumption) (by assumption),
          toReal_ofReal <| le_of_lt p_pos, 𝓜p, maximalFunction, one_div,
          ← div_rpow_of_nonneg _ _ (le_of_lt inv_p_pos), ← laverage_eq, hp_coe]
        gcongr
        refine le_trans (le_of_eq ?_) <| le_iSup₂ 𝔭 h𝔭
        simp_rw [enorm_enorm]
        rw [indicator_of_mem hx]

omit [TileStructure Q D κ S o] in
/-- Tedious check that the constants work out. -/
lemma const_check : C6_1_2 a * C2_0_6 (defaultA a) (p X).toNNReal 2 ≤ C6_1_3 a nnq := by
  have hp_coe : (p X).toNNReal.toReal = p X := Real.coe_toNNReal _ <| le_of_lt <| p_pos X
  have hp_pos := p_pos X
  have : (p X)⁻¹ ≤ 1 := by rw [inv_p_eq']; linarith only [inv_q_mem_Ico X |>.1]
  have hip1 : 1 < 2 * (p X).toNNReal⁻¹  := by
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_mul, NNReal.coe_inv, hp_coe, inv_p_eq']
    push_cast
    linarith [inv_q_mem_Ico X |>.2]
  have : 2 / (p X).toNNReal = (2 / p X).toNNReal := by
    rw [toNNReal_div' (by positivity), Real.toNNReal_ofNat]
  have hp_coe' : (2 * (p X).toNNReal⁻¹ - 1).toReal = 2 * (p X)⁻¹ - 1 := by
    simpa (discharger := positivity) using NNReal.coe_sub <| le_of_lt <| hip1
  have hq_coe : (nnq - 1).toReal = q - 1 := by
    rw [NNReal.coe_sub <| le_of_lt <| one_lt_nnq X, NNReal.coe_one, sub_left_inj]; rfl
  set iq := q⁻¹ with iq_eq
  have hqiq : q = iq⁻¹ := by rw [iq_eq, inv_inv]
  have : 0 < 1 - iq := by linarith [inv_q_mem_Ico X |>.2]
  have hpdiv' : 2 / (p X) / (2 / (p X).toNNReal - 1).toReal = (2 - iq) * (1 - iq)⁻¹ := by
    simp [div_eq_mul_inv, hp_coe', inv_p_eq', ← iq_eq, field, show 2 - iq - 1 = 1 - iq by ring]
  have : 2⁻¹ ≤ iq := inv_q_mem_Ico X |>.1
  have hiq1 : 2 ≤ (1 - iq)⁻¹ := by
    apply (le_inv_comm₀ (by positivity) (by positivity)).mp
    linarith only [inv_q_mem_Ico X |>.1]
  have : 1 < 2 - iq := by linarith only [inv_q_mem_Ico X |>.2]
  have : 0 < q - 1 := by linarith only [q_mem_Ioc X |>.1]
  have haux : 1 ≤ (2 - iq) * (1 - iq)⁻¹ * 2 ^ (2 * a) := by
    conv_lhs => rw [← one_mul 1, ← mul_one (1 * 1)]
    gcongr
    · linarith [hiq1]
    · exact one_le_pow₀ (by norm_num)
  have hc_le : C2_0_6 (2 ^ a) (p X).toNNReal 2 ≤ 2 ^ (2 * a + 4) * (q - 1)⁻¹ := by
    rw [C2_0_6, CMB_eq_of_one_lt_q (by rw [div_eq_mul_inv]; assumption)]
    push_cast
    rw [hp_coe, hpdiv', ← pow_mul, mul_comm a 2]
    refine le_trans (rpow_le_self_of_one_le ?_ ?_) ?_
    · conv_lhs => rw [← one_mul 1]
      gcongr
      · norm_num
      · exact Real.one_le_rpow haux (by positivity)
    · assumption
    · rw [pow_add, pow_succ _ 3, mul_comm (2 ^ 3), ← mul_assoc, mul_comm _ 2]
      conv_rhs => rw [mul_assoc, mul_assoc]
      gcongr
      refine le_trans (rpow_le_self_of_one_le haux ?_) ?_
      · rw [inv_div 2 (p X)]; linarith only [p_lt_two X]
      · rw [mul_comm (2 ^ _)]
        gcongr ?_ * 2 ^ (2 * a)
        calc
          _ = (2 * q - 1) * (q - 1)⁻¹ := by simp [hqiq]; field_simp
          _ ≤ _ := by gcongr; linarith only [q_mem_Ioc X |>.2]
  calc
    _ ≤ 2 ^ ((𝕔 + 2) * a ^ 3) * (2 ^ (2 * a + 4) * (q - 1)⁻¹) := by simp [C6_1_2, hc_le]
    _ ≤ 2 ^ ((𝕔 + 3) * a ^ 3) * (q - 1)⁻¹ := by
      rw [← mul_assoc, ← pow_add]
      gcongr
      · norm_num
      · ring_nf
        linarith [sixteen_times_le_cube (four_le_a X), four_le_a X]
    _ = _ := by simp [C6_1_3, hq_coe]

end Lemma6_1_3

open Lemma6_1_3 in
/-- Lemma 6.1.3 (inequality 6.1.11). -/
lemma dens2_antichain {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    {f : X → ℂ} (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hf : Measurable f)
    {g : X → ℂ} (hgG : ∀ x, ‖g x‖ ≤ G.indicator 1 x) (hg : Measurable g) :
    ‖∫ x, ((starRingEnd ℂ) (g x)) * carlesonSum 𝔄 f x‖ₑ ≤
      (C6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((nnqt : ℝ)⁻¹ - 2⁻¹) *
        eLpNorm f 2 * eLpNorm g 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf hfF
  have bg := bcs_of_measurable_of_le_indicator_g hg hgG
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  simp_rw [enorm_mul]
  let p' := ((qt X)⁻¹ - 2⁻¹)⁻¹
  have hp'_inv : p'⁻¹ = 2⁻¹ * q⁻¹ := by simp only [p', inv_inv, qt, inv_nnqt_eq]; simp
  have hpp : (p X).HolderConjugate p' := by
    refine Real.holderConjugate_iff.mpr ⟨one_lt_p X, ?_⟩
    rw [hp'_inv, inv_p_eq X, div_eq_mul_inv, inv_qt_eq]
    ring
  let C2_0_6' := C2_0_6 (defaultA a) (p X).toNNReal 2
  have := eLpNorm_𝓜_le_eLpNorm_𝓜p_mul 𝔄 hf hfF hpp
  have := eLpNorm_𝓜p_le 𝔄 <| bf.memLp 2
  calc
    _ ≤ eLpNorm g 2 * eLpNorm (carlesonSum 𝔄 f) 2 := by
      simpa [RCLike.enorm_conj, ← eLpNorm_enorm] using lintegral_mul_le_eLpNorm_mul_eLqNorm
        inferInstance bg.enorm.aestronglyMeasurable.aemeasurable
          bf.carlesonSum.enorm.aestronglyMeasurable.aemeasurable
    _ ≤ eLpNorm g 2 * (C6_1_2 a * eLpNorm (𝓜 𝔄 f) 2) := by
      gcongr
      exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
        (ae_of_all _ <| fun x ↦ maximal_bound_antichain h𝔄 hf x) 2
    _ ≤ eLpNorm g 2 * (C6_1_2 a * ((dens₂ 𝔄) ^ (p'⁻¹) * eLpNorm (𝓜p 𝔄 (p X) f) 2)) := by gcongr
    _ ≤ eLpNorm g 2 * (C6_1_2 a * ((dens₂ 𝔄) ^ (p'⁻¹) * (C2_0_6' * eLpNorm f 2))) := by gcongr
    _ = (C6_1_2 a * C2_0_6') * (dens₂ 𝔄) ^ (p'⁻¹) * eLpNorm f 2 * eLpNorm g 2 := by ring
    _ ≤ _ := by
      gcongr ?_ * ?_ * eLpNorm f 2 _ * eLpNorm g 2 _
      · exact_mod_cast const_check
      · rw [hp'_inv, inv_nnqt_eq]; simp
