import Carleson.HolderVanDerCorput
import Carleson.Operators

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ComplexConjugate ENNReal NNReal ShortVariables

open MeasureTheory Metric Set Complex Function Measure

namespace Tile

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X]
  [ProofData a q K σ₁ σ₂ F G]

/-- Def 6.2.1 (Lemma 6.2.1). -/
def correlation (s₁ s₂ : ℤ) (x₁ x₂ y : X) : ℂ := conj (Ks s₁ x₁ y) * Ks s₂ x₂ y

section FunProp

attribute [fun_prop] Complex.measurable_exp Complex.measurable_ofReal

-- TODO: PR to Mathlib
@[fun_prop]
lemma Complex.measurable_starRingEnd : Measurable (starRingEnd ℂ) :=
   Complex.continuous_conj.measurable

@[fun_prop]
lemma measurable_correlation :
    Measurable (fun (s₁ s₂ : ℤ) (x y z : X) ↦ correlation s₁ s₂ x y z) := by
  unfold correlation
  fun_prop

end FunProp

-- Eq. 6.2.2 (Lemma 6.2.1)
lemma mem_ball_of_correlation_ne_zero {s₁ s₂ : ℤ} {x₁ x₂ y : X}
    (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0) : y ∈ (ball x₁ (D ^s₁)) := by
  have hKs : Ks s₁ x₁ y ≠ 0 := by
    simp only [correlation, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
    exact hy.1
  rw [mem_ball, dist_comm]
  exact lt_of_le_of_lt (dist_mem_Icc_of_Ks_ne_zero hKs).2
    (half_lt_self_iff.mpr (defaultD_pow_pos a s₁))

lemma mem_ball_of_mem_tsupport_correlation {s₁ s₂ : ℤ} {x₁ x₂ y : X}
    (hy : y ∈ tsupport (correlation s₁ s₂ x₁ x₂)) : y ∈ (ball x₁ (D ^s₁)) := by
  have hKs : (x₁, y) ∈ tsupport fun x ↦ (Ks s₁ x.1 x.2) := by
    simp only [tsupport, closure, support_subset_iff, ne_eq, Prod.forall, mem_sInter,
      mem_setOf_eq, and_imp] at hy ⊢
    intro C hC h
    let f : X → X × X := fun x ↦ (x₁, x)
    have hf : Continuous f := by continuity
    set C' : Set X := f ⁻¹' C
    specialize hy C' (hC.preimage hf)
    have hfC : f '' C' ⊆ C := by simp [image_subset_iff, subset_refl, C']
    apply hfC
    refine ⟨y, ?_, by simp [f, C']⟩
    apply hy
    intro z hz
    simp only [correlation, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hz
    exact h x₁ z hz.1
  rw [mem_ball, dist_comm]
  exact lt_of_le_of_lt (dist_mem_Icc_of_mem_tsupport_Ks hKs).2
    (half_lt_self_iff.mpr (defaultD_pow_pos a s₁))

/-- The constant from lemma 6.2.1. -/
def C6_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (254 * a ^ 3)

--TODO: PR to Mathlib
lemma ENNReal.mul_div_mul_comm {a b c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inr hd) (Or.inl hc)]
  ring

lemma aux_6_2_3 (s₁ s₂ : ℤ) (x₁ x₂ y y' : X) :
  ‖Ks s₂ x₂ y‖ₑ * ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ ≤
  C2_1_3 a / volume (ball x₂ (D ^ s₂)) *
  (D2_1_3 a / volume (ball x₁ (D ^ s₁)) * (edist y y' ^ τ / (D ^ s₁) ^ τ)) := by
  apply mul_le_mul enorm_Ks_le _ (zero_le _) (zero_le _)
  convert nnnorm_Ks_sub_Ks_le
  rw [← ENNReal.div_rpow_of_nonneg _ _ (τ_nonneg X)]
  simp only [defaultτ]; congr
  simp only [coe_nnreal_ennreal_nndist]

/-- Equation (6.2.5) of Lemma 6.2.1. -/
lemma e625 {s₁ s₂ : ℤ} {x₁ x₂ y y' : X} (hy' : y ≠ y') (hs : s₁ ≤ s₂) :
    (2 * D ^ s₁) ^ τ *
    (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖ₑ / (edist y y') ^ τ) ≤
    2 ^ (253 * a ^ 3) / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) := by
  rw [mul_comm]
  refine ENNReal.mul_le_of_le_div ?_
  rw [ENNReal.div_le_iff_le_mul (.inl _) (.inl _)]; rotate_left
  · rw [← ENNReal.inv_ne_top, ← ENNReal.rpow_neg]
    exact ENNReal.rpow_ne_top_of_nonneg' (edist_pos.mpr hy') (edist_ne_top y y')
  · exact ENNReal.rpow_ne_top_of_nonneg (τ_nonneg X) (edist_ne_top y y')
  calc
    _ = ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y +
        (conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y')‖ₑ := by
      simp only [correlation, sub_add_sub_cancel]
    _ ≤ ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y ‖ₑ +
        ‖conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y'‖ₑ := enorm_add_le _ _
    _ = ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y‖ₑ +
        ‖Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖ₑ := by
      simp only [← sub_mul, ← mul_sub, enorm_mul, RCLike.enorm_conj, ← map_sub]
    _ ≤ 2 ^ (252 * a ^ 3) / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) *
        (edist y y' ^ τ / (D ^ s₁) ^ τ + edist y y' ^ τ / (D ^ s₂) ^ τ) := by
      have h2 : (2 : ℝ≥0∞) ^ (252 * a ^ 3) = C2_1_3 a * D2_1_3 a := by
        simp only [C2_1_3, NNReal.coe_natCast, D2_1_3]
        norm_cast
        ring
      rw [mul_comm, mul_add, h2, mul_comm (volume _)]
      rw [ENNReal.mul_div_mul_comm measure_ball_ne_top measure_ball_ne_top, mul_assoc]
      apply add_le_add (aux_6_2_3 s₁ s₂ x₁ x₂ y y')
      rw [← neg_sub, enorm_neg]
      convert aux_6_2_3 s₂ s₁ x₂ x₁ y' y using 1
      simp only [← mul_assoc, ← ENNReal.mul_div_mul_comm measure_ball_ne_top measure_ball_ne_top]
      rw [mul_comm (volume _), edist_comm]
    _ ≤ 2 ^ (252 * a ^ 3) / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) *
        (2 * (edist y y' ^ τ / (D ^ s₁) ^ τ)) := by
      rw [two_mul]; gcongr
      · exact τ_nonneg X
      · exact_mod_cast one_le_D
    _ = 2 ^ (252 * a ^ 3) * 2 / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) *
        (edist y y' ^ τ / (D ^ s₁) ^ τ) := by
      rw [← mul_assoc, mul_comm _ 2]
      congr 1
      rw [← mul_div_assoc, mul_comm]
    _ ≤ 2 ^ (253 * a ^ 3) / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) *
        (edist y y' ^ τ / (2 * D ^ s₁) ^ τ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (τ_nonneg X)]
      nth_rw 4 [← neg_neg τ]; rw [ENNReal.rpow_neg, ← ENNReal.div_eq_inv_mul, ← ENNReal.div_mul]
      rotate_left
      · right; rw [← ENNReal.inv_ne_top, ENNReal.rpow_neg, inv_inv]
        exact ENNReal.rpow_ne_top_of_nonneg' zero_lt_two ENNReal.ofNat_ne_top
      · exact .inr (ENNReal.rpow_ne_top_of_nonneg' zero_lt_two ENNReal.ofNat_ne_top)
      rw [← mul_assoc, ← mul_rotate, ← mul_div_assoc (2 ^ (-τ))]; gcongr ?_ / _ * _
      rw [show (2 : ℝ≥0∞) ^ (-τ) * 2 ^ (253 * a ^ 3) =
        2 ^ (252 * a ^ 3) * (2 ^ (a ^ 3) * 2 ^ (-τ)) by ring]; gcongr
      nth_rw 1 [← ENNReal.rpow_one 2, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      rw [← sub_eq_add_neg, le_sub_iff_add_le']
      calc
        _ ≤ (1 : ℝ) + 1 := by gcongr; exact τ_le_one (X := X)
        _ ≤ a := by norm_cast; linarith only [four_le_a X]
        _ ≤ _ := mod_cast Nat.le_self_pow three_ne_zero _
    _ = _ := by rw [← ENNReal.mul_comm_div]

-- TODO: update statement in blueprint
-- Eq. 6.2.3 (Lemma 6.2.1)
lemma correlation_kernel_bound {s₁ s₂ : ℤ} {x₁ x₂ : X} (hs : s₁ ≤ s₂) :
    iHolENorm (correlation s₁ s₂ x₁ x₂) x₁ (2 * D ^ s₁) ≤
    C6_2_1 a / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) := by
  -- 6.2.4
  have hφ' (y : X) : ‖correlation s₁ s₂ x₁ x₂ y‖ₑ ≤
      (C2_1_3 a) ^ 2 / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))):= by
    simp only [correlation, enorm_mul, RCLike.enorm_conj, pow_two,
      ENNReal.mul_div_mul_comm measure_ball_ne_top measure_ball_ne_top]
    exact mul_le_mul enorm_Ks_le enorm_Ks_le (zero_le _) (zero_le _)
  -- 6.2.6 + 6.2.7
  calc
    _ ≤ (C2_1_3 a) ^ 2 / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) +
        2 ^ (253 * a ^ 3) / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) := by
      apply add_le_add (iSup₂_le fun x _ ↦ hφ' x)
      simp only [ENNReal.mul_iSup, iSup_le_iff]
      intro z hz z' hz' hzz'
      convert e625 hzz' hs
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ← Real.rpow_intCast,
        ← ENNReal.ofReal_rpow_of_pos (defaultD_pos _), ENNReal.ofReal_natCast,
        ENNReal.rpow_intCast]
    _ ≤ _ := by
      rw [← ENNReal.add_div]; refine ENNReal.div_le_div_right ?_ _
      rw [C2_1_3, C6_2_1]; norm_cast
      calc
        _ ≤ 2 ^ (253 * a ^ 3) + 2 ^ (253 * a ^ 3) := by
          rw [← pow_mul, show 102 * a ^ 3 * 2 = 204 * a ^ 3 by ring]; gcongr <;> norm_num
        _ ≤ _ := by
          rw [← two_mul, ← pow_succ', show 1 = 1 ^ 3 by norm_num,
            show 254 * a ^ 3 = 253 * a ^ 3 + a ^ 3 by ring]
          gcongr
          · exact one_le_two
          · linarith only [four_le_a X]

variable [TileStructure Q D κ S o]

-- TODO: PR both versions to Mathlib
theorem MeasureTheory.exists_ne_zero_of_setIntegral_ne_zero {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → E} {U : Set α}
    (hU : ∫ (u : α) in U, f u ∂μ ≠ 0) : ∃ u : α, u ∈ U ∧ f u ≠ 0 := by
  contrapose! hU
  exact setIntegral_eq_zero_of_forall_eq_zero hU

theorem MeasureTheory.exists_ne_zero_of_integral_ne_zero {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → E}
    (h : ∫ (u : α), f u ∂μ ≠ 0) : ∃ u : α, f u ≠ 0 := by
  contrapose! h
  exact integral_eq_zero_of_ae ((eqOn_univ f 0).mp fun ⦃x⦄ a ↦ h x).eventuallyEq

-- Lemma 6.2.2
lemma range_support {p : 𝔓 X} {g : X → ℂ} {y : X} (hpy : adjointCarleson p g y ≠ 0) :
    y ∈ (ball (𝔠 p) (5 * D ^𝔰 p)) := by
  simp only [adjointCarleson] at hpy
  obtain ⟨x, hxE, hx0⟩ := MeasureTheory.exists_ne_zero_of_setIntegral_ne_zero hpy
  have hxp : dist x (𝔠 p) < 4 * D ^𝔰 p := -- 6.2.13
    Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) hxE)
  have hyx : dist y x ≤ (1/2) * D ^𝔰 p := by -- 6.2.14
    have hK : Ks (𝔰 p) x y ≠ 0 := by
      by_contra h0
      simp only [h0, map_zero, zero_mul, ne_eq, not_true_eq_false] at hx0
    rw [dist_comm]
    convert (dist_mem_Icc_of_Ks_ne_zero hK).2 using 1
    ring
  have hpos := defaultD_pow_pos a (𝔰 p)
  have hle : (9 : ℝ) / 2 < 5 := by norm_num
  calc dist y (𝔠 p) ≤ dist y x + dist x (𝔠 p) := dist_triangle y x (𝔠 p)
    _ ≤ (1/2) * D ^𝔰 p + 4 * D ^ 𝔰 p := add_le_add hyx (le_of_lt hxp)
    _ < 5 * D ^ 𝔰 p := by
      ring_nf
      gcongr -- uses hpos, hle.

/-- The constant from lemma 6.2.3. -/
def C6_2_3 (a : ℕ) : ℝ≥0 := 2^(8 * a)

lemma ineq_6_2_16 {p : 𝔓 X} {x : X} (hx : x ∈ E p) : dist_(p) (Q x) (𝒬 p) < 1 :=
  subset_cball hx.2.1

-- Lemma 6.2.3
lemma uncertainty (ha : 1 ≤ a) {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂)
  (hinter : (ball (𝔠 p₁) (5 * D^𝔰 p₁) ∩ ball (𝔠 p₂) (5 * D^𝔰 p₂)).Nonempty) {x₁ x₂ : X}
  (hx₁ : x₁ ∈ E p₁) (hx₂ : x₂ ∈ E p₂) :
    1  + dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ (C6_2_3 a) * (1 + dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) := by
  -- Inequalities 6.2.16.
  have hp₁ : dist_(p₁) (𝒬 p₁) (Q x₁) < 1 := by rw [dist_comm]; exact ineq_6_2_16 hx₁
  have hp₂ := ineq_6_2_16 hx₂
  --Needed for ineq. 6.2.17
  have hss : ↑(𝓘 p₁) ⊆ ball (𝔠 p₂) (14 * D^𝔰 p₂) := by
    have h1D : 1 ≤ (D : ℝ) := one_le_defaultD a
    have hdist : dist (𝔠 p₁) (𝔠 p₂) < 10 * D ^ 𝔰 p₂ := by
      have h5 : 10 * (D : ℝ)^ 𝔰 p₂ = 5 * D ^ 𝔰 p₂ + 5 * D ^ 𝔰 p₂ := by ring
      obtain ⟨y, hy₁, hy₂⟩ := hinter
      rw [mem_ball, dist_comm] at hy₁
      apply lt_of_le_of_lt (dist_triangle (𝔠 p₁) y (𝔠 p₂))
      apply lt_of_lt_of_le (add_lt_add hy₁ hy₂)
      rw [h5]
      gcongr -- uses h1D
    apply subset_trans Grid_subset_ball
    intro x hx
    simp only [mem_ball] at hx ⊢
    calc dist x (𝔠 p₂)
      _ ≤ dist x (𝔠 p₁) + dist (𝔠 p₁) (𝔠 p₂) := dist_triangle _ _ _
      _ < 4 * D ^ 𝔰 p₁ + 10 * D ^ 𝔰 p₂ := add_lt_add hx hdist
      _ ≤ 4 * D ^ 𝔰 p₂ + 10 * D ^ 𝔰 p₂ := by gcongr -- uses h1D, hle
      _ = 14 * D ^ 𝔰 p₂ := by ring
  -- Inequality 6.2.17.
  have hp₁p₂ : dist_(p₁) (Q x₂) (𝒬 p₂) < 2^(6*a) := by
    calc dist_(p₁) (Q x₂) (𝒬 p₂)
      _ ≤ 2^(6*a) * dist_(p₂) (Q x₂) (𝒬 p₂) := by
        set r := (D : ℝ)^𝔰 p₂ / 4 with hr_def
        have hr : 0 < (D : ℝ)^𝔰 p₂ / 4 := by
          rw [div_pos_iff_of_pos_right (by positivity)]
          exact defaultD_pow_pos a (𝔰 p₂)
        have haux : dist_{𝔠 p₂, 2 ^ 6 * r} (Q x₂) (𝒬 p₂) ≤
          (2 : ℝ) ^ (6 * a)* dist_{𝔠 p₂, r} (Q x₂) (𝒬 p₂) := by
          have h6a : (2 : ℝ) ^ (6 * a) = (defaultA a)^ 6 := by simp; ring
          convert cdist_le_iterate hr (Q x₂) (𝒬 p₂) 6
        exact le_trans (cdist_mono (subset_trans ball_subset_Grid
          (le_trans hss (ball_subset_ball (by linarith))))) haux
      _ < 2^(6*a) := by
        nth_rewrite 2 [← mul_one (2^(6*a))]
        exact mul_lt_mul_of_nonneg_of_pos' (le_refl _) hp₂ dist_nonneg (by positivity)
  -- Auxiliary ineq. for 6.2.18
  have haux : dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ (1 + 2^(6*a)) + dist_(p₁) (Q x₁) (Q x₂) :=
    calc dist_(p₁) (𝒬 p₁) (𝒬 p₂)
      _ ≤ dist_(p₁) (𝒬 p₁) (Q x₁) + dist_(p₁) (Q x₁) (𝒬 p₂) := dist_triangle _ _ _
      _ ≤ dist_(p₁) (𝒬 p₁) (Q x₁) + dist_(p₁) (Q x₁) (Q x₂) + dist_(p₁) (Q x₂) (𝒬 p₂) := by
        rw [add_assoc]
        exact add_le_add (le_refl _) (dist_triangle _ _ _)
      _ ≤ 1 + dist_(p₁) (Q x₁) (Q x₂) + 2^(6*a) :=
        add_le_add_three (le_of_lt hp₁) (le_refl _) (le_of_lt hp₁p₂)
      _ = (1 + 2^(6*a)) + dist_(p₁) (Q x₁) (Q x₂) := by ring
  calc 1  + dist_(p₁) (𝒬 p₁) (𝒬 p₂)
    -- 6.2.18
    _ ≤ 2 + 2^(6*a) + dist_(p₁) (Q x₁) (Q x₂) := by
      have h2 : (2 + 2^(6*a) : ℝ) = 1 + (1 + 2^(6*a)) := by ring
      rw [h2, add_assoc]
      exact add_le_add (le_refl _) haux
    -- 6.2.21
    _ ≤ 2 + 2^(6*a) + dist_{x₁, 8 * D^𝔰 p₁} (Q x₁) (Q x₂) := by
      apply add_le_add (le_refl _)
      -- 6.2.19
      have h1 : dist (𝔠 p₁) x₁ < 4 * D^𝔰 p₁ := by
        rw [dist_comm]
        exact Grid_subset_ball hx₁.1
      -- 6.2.20
      have hI : ↑(𝓘 p₁) ⊆ ball x₁ (8 * D^𝔰 p₁) := by
        apply subset_trans Grid_subset_ball
        intro x hx
        calc dist x x₁
          _ ≤ dist x (𝔠 p₁) + dist (𝔠 p₁) x₁ := dist_triangle _ _ _
          _ < 4 * D ^ 𝔰 p₁ + 4 * D ^ 𝔰 p₁ := add_lt_add hx h1
          _ = 8 * D ^ 𝔰 p₁ := by ring
      exact cdist_mono (subset_trans ball_subset_Grid hI)
    -- 6.2.22
    _ ≤ 2 + 2^(6*a) + 2^(3*a) * dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂) := by
      apply add_le_add (le_refl _)
      have hr : 0 < (D : ℝ)^𝔰 p₁ := by exact defaultD_pow_pos a (𝔰 p₁)
      have h8 : (8 : ℝ) = 2^3 := by ring
      have h3a : (2 : ℝ) ^ (3 * a) = (defaultA a)^ 3 := by simp; ring
      convert cdist_le_iterate hr (Q x₁) (Q x₂) 3 -- uses h8, h3a
    -- 6.2.15
    _ ≤ (C6_2_3 a) * (1 + dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) := by
      have hpow : (2 : ℝ) + 2 ^ (6 * a) ≤ 2 ^ (a * 8) :=
        calc (2 : ℝ) + 2 ^ (6 * a)
          _ ≤ (2 : ℝ)^ (6 * a) + 2 ^ (6 * a)  := by
            apply add_le_add_right
            norm_cast
            nth_rewrite 1 [← pow_one 2]
            exact Nat.pow_le_pow_right zero_lt_two (by omega)
          _ = 2 * (2 : ℝ)^ (6 * a) := by ring
          _ ≤ 2 ^ (a * 8) := by
            nth_rewrite 1 [← pow_one 2, ← pow_add]
            norm_cast
            exact Nat.pow_le_pow_right zero_lt_two (by omega)
      have h38 : 3 ≤ 8 := by omega
      have h12 : (1 : ℝ) ≤ 2 := by linarith
      rw [C6_2_3]
      conv_rhs => ring_nf
      push_cast
      rw [mul_comm 3]
      gcongr

-- Lemma 6.2.3 (edist version)
lemma uncertainty' (ha : 1 ≤ a) {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂)
    (hinter : (ball (𝔠 p₁) (5 * D^𝔰 p₁) ∩ ball (𝔠 p₂) (5 * D^𝔰 p₂)).Nonempty) {x₁ x₂ : X}
    (hx₁ : x₁ ∈ E p₁) (hx₂ : x₂ ∈ E p₂) :
      1  + edist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ (C6_2_3 a) * (1 + edist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) := by
  have hC : (C6_2_3 a : ℝ≥0∞) = ENNReal.ofReal (C6_2_3 a : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
  simp only [edist_dist, ← ENNReal.ofReal_one, hC, ← ENNReal.ofReal_add zero_le_one dist_nonneg,
    ← ENNReal.ofReal_add zero_le_one dist_nonneg, ← ENNReal.ofReal_mul NNReal.zero_le_coe]
  exact ENNReal.ofReal_le_ofReal (uncertainty ha hle hinter hx₁ hx₂)

section lemma_6_1_5

/-- The constant from lemma 6.1.5. -/
def C6_1_5 (a : ℕ) : ℝ≥0 := 2^(255 * a^3)

-- TODO : 4 ≤ a in blueprint
@[nolint unusedHavesSuffices] -- nlinarith does use h255.
lemma C6_1_5_bound (ha : 4 ≤ a) : 2 ^ (254 * a ^ 3 + 1) * 2 ^ (11 * a) ≤ C6_1_5 a := by
  have h255 : 255 * a ^ 3 = 254 * a ^ 3  + (a ^ 2 * a) := by
    have : a ^ 2 * a = a^3 := rfl
    rw [← one_mul (a ^ 2 * a), this, ← add_mul]
    rfl
  rw [C6_1_5, ← pow_add]
  exact pow_le_pow (le_refl _) one_le_two (by nlinarith)

open GridStructure

lemma complex_exp_lintegral {p : 𝔓 X} {g : X → ℂ} (y : X) :
    (starRingEnd ℂ) (∫ (y1 : X) in E p, (starRingEnd ℂ) (Ks (𝔰 p) y1 y) *
      Complex.exp (Complex.I * (↑((Q y1) y1) - ↑((Q y1) y))) * g y1) =
      (∫ (y1 : X) in E p, (Ks (𝔰 p) y1 y) *
        Complex.exp (Complex.I * (- ((Q y1) y1) + ↑((Q y1) y))) * (starRingEnd ℂ) (g y1)) := by
  simp only [← integral_conj, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  congr
  ext x
  rw [← Complex.exp_conj]
  congr
  simp only [map_mul, Complex.conj_I, map_sub, Complex.conj_ofReal]
  ring

/-- Definition 6.2.27 -/
def I12 (p p' : 𝔓 X) (g : X → ℂ) := fun (x1 : X) (x2 : X) ↦
  ‖(∫ y, (Complex.exp (Complex.I * (- ((Q x1) y) + ↑((Q x2) y))) *
    (correlation (𝔰 p') (𝔰 p) x1 x2 y))) * (g x1) * (g x2)‖ₑ

/-- Inequality 6.2.28 -/ -- TODO: add ‖g ↑x1‖ₑ * ‖g ↑x2‖ₑ in blueprint's RHS
lemma I12_le' (p p' : 𝔓 X) (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ) (x1 : E p') (x2 : E p) :
    I12 p p' g x1 x2 ≤ (2^(254 * a^3 + 8 * a)) *
      ((1 + edist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume (ball (x2 : X) (D ^𝔰 p))) * ‖g ↑x1‖ₑ * ‖g ↑x2‖ₑ := by
  have hD' : 0 < (D : ℝ) ^ 𝔰 p' := defaultD_pow_pos a (𝔰 p')
  have hsupp : support (correlation (𝔰 p') (𝔰 p) (x1 : X) x2) ⊆ ball x1 (D ^ 𝔰 p') :=
    (subset_tsupport _).trans <| fun _ hx ↦  mem_ball_of_mem_tsupport_correlation hx
  -- For compatibility with holder_van_der_corput
  have heq : (2^(254 * a^3 + 8 * a)) *
      ((1 + edist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume (ball (x2 : X) (D ^𝔰 p))) =
      (2^(254 * a^3 + 8 * a)) / (volume (ball (x2 : X) (D ^𝔰 p))) *
      ((1 + edist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) := by
    rw [ENNReal.mul_comm_div, mul_comm, mul_comm _ (2 ^ _), mul_div_assoc]
  rw [I12]
  -- TODO: fix s₁ in blueprint
  simp only [enorm_mul]
  gcongr
  --rw [← ENNReal.coe_le_coe]
  simp_rw [← sub_eq_neg_add]
  apply le_trans (holder_van_der_corput hsupp)
  rw [heq, edist_comm]
  --push_cast
  gcongr
  · have hbdd := correlation_kernel_bound (a := a) (X := X) hle (x₁ := x1) (x₂ := x2)
    have hle : (C2_0_5 ↑a : ℝ≥0∞) * volume (ball (x1 : X) (D ^ 𝔰 p')) *
        iHolENorm (a := a) (correlation (𝔰 p') (𝔰 p) (x1 : X) ↑x2) (↑x1) (2 * D ^ 𝔰 p') ≤
        ↑(C2_0_5 ↑a) * volume (ball ((x1 : X)) (D ^ 𝔰 p')) * (↑(C6_2_1 a) /
          (volume (ball (x1 : X) (D ^ 𝔰 p')) * volume (ball (x2 : X) (D ^ 𝔰 p)))) := by
      gcongr
    -- simp, ring_nf, field_simp did not help.
    have heq : ↑(C2_0_5 a) * volume (ball (x1 : X) (D ^ 𝔰 p')) *
      (↑(C6_2_1 a) / (volume (ball (x1 : X) (D ^ 𝔰 p')) * volume (ball (x2 : X) (D ^ 𝔰 p)))) =
      ↑(C2_0_5 a) * (↑(C6_2_1 a) / volume (ball (x2 : X) (D ^ 𝔰 p))) := by
      simp only [mul_assoc]
      congr 1
      rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr measure_ball_ne_top)
        (Or.inl measure_ball_ne_top), ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel
        (ne_of_gt (measure_ball_pos volume _ hD')) measure_ball_ne_top, one_mul,
        ENNReal.div_eq_inv_mul]
    apply le_trans hle
    rw [heq, mul_div]
    apply ENNReal.div_le_div _ (le_refl _)
    simp only [C2_0_5, C6_2_1, ENNReal.coe_pow, ENNReal.coe_ofNat]
    rw [pow_add, mul_comm]
    norm_cast
    gcongr
    · exact one_le_two
    · omega

lemma exp_ineq (ha : 4 ≤ a) : 0 < ((8 * a  : ℕ) : ℝ) * -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ + 1 := by
  have hpos : 0 < (a : ℝ) ^ 2 * 2 + a ^ 3 := by norm_cast; nlinarith
  ring_nf
  rw [Nat.cast_mul, Nat.cast_ofNat, sub_pos, ← div_eq_mul_inv, div_lt_one hpos]
  norm_cast
  nlinarith

-- TODO: PR to Mathlib
lemma _root_.ENNReal.rpow_lt_rpow_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) (h : x < y) :
    y ^ z < x ^ z := by
  rw [← neg_neg z, ENNReal.rpow_neg y, ENNReal.rpow_neg x, ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
  exact ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.mpr h) (neg_pos.mpr hz)

-- TODO: PR to Mathlib

lemma _root_.ENNReal.rpow_lt_rpow_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) :
    x ^ z < y ^ z ↔ y < x :=
  ⟨lt_imp_lt_of_le_imp_le (fun h ↦ ENNReal.rpow_le_rpow_of_nonpos (le_of_lt hz) h),
    fun h ↦ ENNReal.rpow_lt_rpow_of_neg hz h⟩

lemma _root_.ENNReal.rpow_le_rpow_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) :
    x ^ z ≤ y ^ z ↔ y ≤ x :=
  le_iff_le_iff_lt_iff_lt.2 <| ENNReal.rpow_lt_rpow_iff_of_neg hz

/-- Inequality 6.2.29. -/ -- TODO: add ‖g ↑x1‖ₑ * ‖g ↑x2‖ₑ in blueprint's RHS
lemma I12_le (ha : 4 ≤ a) (p p' : 𝔓 X) (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty)
    (x1 : E p') (x2 : E p) :
    I12 p p' g x1 x2 ≤
    (2^(254 * a^3 + 8 * a + 1) * ((1 + edist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹))) /
      (volume (ball (x2 : X) (D ^𝔰 p))) * ‖g ↑x1‖ₑ * ‖g ↑x2‖ₑ := by
  apply (I12_le' p p' hle g x1 x2).trans
  gcongr ?_ * ‖g ↑x1‖ₑ * ‖g ↑x2‖ₑ
  rw [pow_add 2 _ 1, pow_one, mul_comm _ 2, mul_assoc, mul_comm 2 (_ * _), mul_assoc]
  gcongr
  -- Now we need to use Lemma 6.2.3. to conclude this inequality.
  have h623 := uncertainty' (le_of_lt (by linarith)) hle hinter x1.2 x2.2
  rw [C6_2_3, ENNReal.coe_pow, ENNReal.coe_ofNat] at h623
  have hneg : -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ < 0 :=
    neg_neg_iff_pos.mpr (inv_pos.mpr (by norm_cast; nlinarith))
  have hexp : 0 < ((8 * a  : ℕ) : ℝ) * -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ + 1 := exp_ineq ha
  rw [← ENNReal.rpow_le_rpow_iff_of_neg hneg] at h623
  have h0 : ((2 : ℝ≥0∞) ^ (8 * a)) ^ (-(2 * ↑a ^ 2 + (a : ℝ) ^ 3)⁻¹) ≠ 0 := by simp
  have h210 : (2 : ℝ≥0∞) ^ (1 : ℝ) ≠ 0 := by rw [ENNReal.rpow_one]; exact two_ne_zero
  rw [ENNReal.mul_rpow_of_ne_top (Ne.symm (not_eq_of_beq_eq_false rfl)) (by simp [edist_dist]),
    mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inr (by simp [edist_dist]))] at h623
  apply le_trans h623
  rw [ENNReal.div_eq_inv_mul, mul_comm _ 2]
  gcongr
  conv_rhs => rw [← ENNReal.rpow_one (2 : ℝ≥0∞)]
  rw [ENNReal.inv_le_iff_le_mul (fun _ ↦ h0) (fun _ ↦ h210), ← ENNReal.rpow_natCast 2, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.one_le_rpow one_le_two hexp

/-- Inequality 6.2.28 -/ -- TODO: add ‖g ↑x1‖₊ * ‖g ↑x2‖₊ in blueprint's RHS
lemma I12_nnreal_le' (p p' : 𝔓 X) (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ) (x1 : E p') (x2 : E p) :
    (I12 p p' g x1 x2).toNNReal ≤ (2^(254 * a^3 + 8 * a)) *
      ((1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal * ‖g ↑x1‖₊ * ‖g ↑x2‖₊ := by
  have hD : 0 < (D : ℝ) ^ 𝔰 p := defaultD_pow_pos a (𝔰 p)
  have hD' : 0 < (D : ℝ) ^ 𝔰 p' := defaultD_pow_pos a (𝔰 p')
  have hsupp : support (correlation (𝔰 p') (𝔰 p) (x1 : X) x2) ⊆ ball x1 (D ^ 𝔰 p') :=
    (subset_tsupport _).trans <| fun _ hx ↦ (mem_ball_of_mem_tsupport_correlation hx)
  have heq : (2^(254 * a^3 + 8 * a)) *
      ((1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x2) (Q x1))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal =
      (2^(254 * a^3 + 8 * a)) / (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal *
      ((1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x2) (Q x1))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) := by
    rw [div_mul_comm, mul_comm _ (2 ^ _), mul_div_assoc]
  rw [I12]
  -- TODO: fix s₁ in blueprint
  simp only [enorm_mul, ENNReal.toNNReal_mul]
  have : ‖g ↑x1‖ₑ.toNNReal ≤ ‖g ↑x1‖₊ := by simp
  have : ‖g ↑x2‖ₑ.toNNReal ≤ ‖g ↑x2‖₊ := by simp
  gcongr
  rw [← ENNReal.coe_le_coe]
  simp_rw [← sub_eq_neg_add]
  apply le_trans (holder_van_der_corput hsupp)
  rw [nndist_comm, heq]
  push_cast
  gcongr
  · have hbdd := correlation_kernel_bound (a := a) (X := X) hle (x₁ := x1) (x₂ := x2)
    have hle : (C2_0_5 ↑a : ℝ≥0∞) * volume (ball (x1 : X) (D ^ 𝔰 p')) *
        iHolENorm (a := a) (correlation (𝔰 p') (𝔰 p) (x1 : X) ↑x2) (↑x1) (2 * D ^ 𝔰 p') ≤
        ↑(C2_0_5 ↑a) * volume (ball ((x1 : X)) (D ^ 𝔰 p')) * (↑(C6_2_1 a) /
          (volume (ball (x1 : X) (D ^ 𝔰 p')) * volume (ball (x2 : X) (D ^ 𝔰 p)))) := by
      gcongr
    -- simp, ring_nf, field_simp did not help.
    have heq : ↑(C2_0_5 a) * volume (ball (x1 : X) (D ^ 𝔰 p')) *
      (↑(C6_2_1 a) / (volume (ball (x1 : X) (D ^ 𝔰 p')) * volume (ball (x2 : X) (D ^ 𝔰 p)))) =
      ↑(C2_0_5 a) * (↑(C6_2_1 a) / volume (ball (x2 : X) (D ^ 𝔰 p))) := by
      simp only [mul_assoc]
      congr 1
      rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr measure_ball_ne_top)
        (Or.inl measure_ball_ne_top), ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel
        (ne_of_gt (measure_ball_pos volume _ hD')) measure_ball_ne_top, one_mul,
        ENNReal.div_eq_inv_mul]
    apply le_trans hle
    rw [heq, ENNReal.coe_div (ne_of_gt (measure_ball_pos_nnreal _ _ hD)),
      ENNReal.coe_toNNReal measure_ball_ne_top, mul_div]
    apply ENNReal.div_le_div _ (le_refl _)
    simp only [C2_0_5, C6_2_1, ENNReal.coe_pow, ENNReal.coe_ofNat]
    rw [pow_add, mul_comm]
    norm_cast
    gcongr
    · exact one_le_two
    · omega
  · norm_cast
    apply le_of_eq
    suffices 1 + @edist (WithFunctionDistance (x1 : X) (D ^ 𝔰 p')) _ (Q ↑x2) (Q ↑x1) =
        1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x2) (Q x1) by
      rw [this, ENNReal.coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one le_self_add)),
        ENNReal.coe_add, ENNReal.coe_one]
    congr
    rw [coe_nnreal_ennreal_nndist]

lemma exp_ineq' (ha : 1 < a) : 0 ≤ 1 + ((8 * a  : ℕ) : ℝ) * -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ := by
  have hpos : 0 < (a : ℝ) ^ 2 * 2 + a ^ 3 := by norm_cast; nlinarith
  ring_nf
  rw [Nat.cast_mul, Nat.cast_ofNat, sub_nonneg, ← div_eq_mul_inv, div_le_one hpos]
  norm_cast
  nlinarith

/-- Inequality 6.2.29. -/ -- TODO: add ‖g ↑x1‖₊ * ‖g ↑x2‖₊ in blueprint's RHS
lemma I12_nnreal_le (ha : 1 < a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ)
    (hinter : (ball (𝔠 p') (5 * D ^ 𝔰 p') ∩ ball (𝔠 p) (5 * D ^ 𝔰 p)).Nonempty)
    (x1 : E p') (x2 : E p) :
    (I12 p p' g x1 x2).toNNReal ≤
    (2^(254 * a^3 + 8 * a + 1) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹))) /
      (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal * ‖g ↑x1‖₊ * ‖g ↑x2‖₊ := by
  apply le_trans (NNReal.coe_le_coe.mpr (I12_nnreal_le' p p' hle g x1 x2))
  simp only [Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, NNReal.coe_rpow, NNReal.coe_add, NNReal.coe_one, coe_nndist, coe_nnnorm]
  gcongr ?_ *  ‖g ↑x1‖ * ‖g ↑x2‖
  rw [pow_add 2 _ 1, pow_one, mul_comm _ 2, mul_assoc, mul_comm 2 (_ * _), mul_assoc]
  gcongr
  -- Now we need to use Lemma 6.2.3. to conclude this inequality.
  have h623 := uncertainty (le_of_lt ha) hle hinter x1.2 x2.2
  rw [C6_2_3, NNReal.coe_pow, NNReal.coe_ofNat] at h623
  have hneg : -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ < 0 :=
    neg_neg_iff_pos.mpr (inv_pos.mpr (by norm_cast; nlinarith))
  have hpos : 0 < ((2 : ℝ) ^ (8 * a)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) :=
    Real.rpow_pos_of_pos (pow_pos zero_lt_two _) _
  have hexp : 0 ≤ 1 + ((8 * a  : ℕ) : ℝ) * -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ := exp_ineq' ha
  have h28a : (0 : ℝ) < 2 ^ (8 * a) := pow_pos zero_lt_two _
  have hmul_pos : 0 < 2 ^ (8 * a) *
      (1 + dist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q (x1 : X)) (Q (x2 : X))) :=
    mul_pos h28a (add_pos_of_pos_of_nonneg zero_lt_one dist_nonneg)
  have hdist : 0 < 1 + dist_(p') (𝒬 p') (𝒬 p) := add_pos_of_pos_of_nonneg zero_lt_one dist_nonneg
  have h1dist : 0 ≤ 1 + dist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q (x1 : X)) (Q (x2 : X)) :=
    add_nonneg zero_le_one dist_nonneg
  rw [← Real.rpow_le_rpow_iff_of_neg hmul_pos hdist hneg] at h623
  rw [Real.mul_rpow (le_of_lt h28a) h1dist, mul_comm, ← le_div_iff₀ hpos] at h623
  apply le_trans h623
  rw [div_eq_inv_mul, mul_comm _ 2]
  gcongr
  conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
  rw [inv_le_iff_one_le_mul₀ hpos, ← Real.rpow_natCast 2, ← Real.rpow_mul zero_le_two,
    ← Real.rpow_add zero_lt_two]
  exact Real.one_le_rpow one_le_two hexp

/-- Inequality 6.2.32 -/
lemma volume_nnreal_coeGrid_le (p : 𝔓 X) (x2 : E p) :
    (volume (coeGrid (𝓘 p))).toNNReal ≤ 2 ^ (3*a) * (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal := by
  -- Inequality 6.2.30
  have hdist : dist (𝔠 p) (x2 : X) < 4 * D ^𝔰 p := by --TODO: < in blueprint
    rw [dist_comm]
    exact Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) x2.prop)
  -- Inclusion 6.2.31
  have hsub : (coeGrid (𝓘 p)) ⊆ (ball (x2 : X) (8 * D ^𝔰 p)) := by
    apply le_trans Grid_subset_ball
    intro x hx
    calc dist x x2
      _ ≤ dist x (𝔠 p) + dist (𝔠 p) x2 := dist_triangle _ _ _
      _ < 4 * D ^ 𝔰 p + 4 * D ^ 𝔰 p := by
        apply add_lt_add hx hdist
      _ = 8 * D ^ 𝔰 p := by ring
  have h : (volume (coeGrid (𝓘 p))).toNNReal ≤ (volume (ball (x2 : X) (8 * D ^𝔰 p))).toNNReal := by
    gcongr; finiteness
  have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
  have h23a : (2 : ℝ≥0) ^ (3 * a) = ((2 : ℝ≥0∞) ^ (3 * a)).toNNReal := by
    simp only [ENNReal.toNNReal_pow, zero_le]; rfl
  apply le_trans h
  simp only [h23a, h8]
  rw [← ENNReal.toNNReal_mul]
  rw [ENNReal.toNNReal_le_toNNReal (by finiteness)]
  · convert DoublingMeasure.volume_ball_two_le_same_repeat (x2 : X) (D ^𝔰 p) 3 using 1
    rw [mul_comm 3, pow_mul]
    simp only [NNReal.coe_pow, NNReal.coe_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  · exact ENNReal.mul_ne_top (by exact Ne.symm (not_eq_of_beq_eq_false rfl)) (by finiteness)

/-- Inequality 6.2.32 -/
lemma volume_coeGrid_le (p : 𝔓 X) (x2 : E p) :
    volume (coeGrid (𝓘 p)) ≤ 2 ^ (3*a) * (volume (ball (x2 : X) (D ^𝔰 p))) := by
  -- Inequality 6.2.30
  have hdist : dist (𝔠 p) (x2 : X) < 4 * D ^𝔰 p := --TODO: < in blueprint
    dist_comm (𝔠 p) (x2 : X) ▸ Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) x2.prop)
  -- Inclusion 6.2.31
  have hsub : (coeGrid (𝓘 p)) ⊆ (ball (x2 : X) (8 * D ^𝔰 p)) := by
    apply le_trans Grid_subset_ball
    intro x hx
    calc dist x x2
      _ ≤ dist x (𝔠 p) + dist (𝔠 p) x2 := dist_triangle _ _ _
      _ < 4 * D ^ 𝔰 p + 4 * D ^ 𝔰 p := add_lt_add hx hdist
      _ = 8 * D ^ 𝔰 p := by ring
  have h : volume (coeGrid (𝓘 p)) ≤ volume (ball (x2 : X) (8 * D ^𝔰 p)) :=
    measure_mono hsub
  have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
  apply le_trans h
  simp only [NNReal.coe_mul, ← NNReal.coe_le_coe, h8]
  convert DoublingMeasure.volume_ball_two_le_same_repeat (x2 : X) (D ^𝔰 p) 3 using 1
  rw [mul_comm 3, pow_mul]
  simp [NNReal.coe_pow, NNReal.coe_ofNat, Nat.cast_pow, Nat.cast_ofNat]

-- Bound 6.2.29 using 6.2.32 and `4 ≤ a`.
lemma bound_6_2_29 (ha : 4 ≤ a) (p p' : 𝔓 X) (x2 : E p) : 2 ^ (254 * a^3 + 8 * a + 1) *
      ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume (ball (x2 : X) (D ^𝔰 p))) ≤ (C6_1_5 a) *
          ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume (coeGrid (𝓘 p))).toNNReal := by
  have h4 : (2 : ℝ≥0∞) ^ (254 * a ^ 3 + 1) * 2 ^ (11 * a) ≤ C6_1_5 a :=
    ENNReal.coe_le_coe.mpr (C6_1_5_bound ha)
  -- Inequality 6.2.32
  have hvol : ∀ (x2 : E p), volume (coeGrid (𝓘 p)) ≤
      2 ^ (3*a) * (volume (ball (x2 : X) (D ^𝔰 p))) := volume_coeGrid_le p
  calc 2 ^ (254 * a^3 + 8 * a + 1) *
    ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume (ball (x2 : X) (D ^𝔰 p)))
    _ = 2^ (254 * a^3 + 1) * 2 ^ (11 * a) * 2 ^ (- (3 : ℤ) * a) *
        ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume (ball (x2 : X) (D ^𝔰 p))) := by
      simp only [← zpow_natCast, ← ENNReal.zpow_add two_ne_zero
        ENNReal.ofNat_ne_top]
      congr
      push_cast
      ring_nf
    _ = 2 ^ (254 * a^3 + 1) * 2 ^ (11 * a) *
        ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (2 ^ (3 * a) * volume (ball (x2 : X) (D ^𝔰 p))) := by
      simp only [Int.reduceNeg, neg_mul,  Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      rw [ENNReal.mul_inv (by right; finiteness) (by left; simp)]
      simp only [← mul_assoc]
      congr 1
      ring_nf
      rw [ENNReal.zpow_neg two_ne_zero ENNReal.ofNat_ne_top]
      norm_cast
    _ ≤ (C6_1_5 a) * ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (2 ^ (3 * a) * volume (ball (x2 : X) (D ^𝔰 p))) := by gcongr
    _ ≤ (C6_1_5 a) * ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume (coeGrid (𝓘 p))).toNNReal := by
        gcongr;
        convert hvol x2
        rw [ENNReal.coe_toNNReal (by finiteness)]

-- Bound 6.2.29 using 6.2.32 and `4 ≤ a`.
lemma bound_6_2_29' (ha : 4 ≤ a) (p p' : 𝔓 X) (x2 : E p) : 2 ^ (254 * a^3 + 8 * a + 1) *
      ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal ≤ (C6_1_5 a) *
          ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume (coeGrid (𝓘 p))).toNNReal := by
  have h1 : 0 < (volume (𝓘 p : Set X)).toNNReal :=
    ENNReal.toNNReal_pos (ne_of_gt (volume_coeGrid_pos (defaultD_pos' a))) (by finiteness)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h4 : 2 ^ (254 * a ^ 3 + 1) * 2 ^ (11 * a) ≤ C6_1_5 a := C6_1_5_bound ha
  -- Inequality 6.2.32
  have hvol : ∀ (x2 : E p), (volume (coeGrid (𝓘 p))).toNNReal ≤
      2 ^ (3*a) * (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal := by
    intro x2
    apply volume_nnreal_coeGrid_le
  calc 2 ^ (254 * a^3 + 8 * a + 1) *
    ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal
    _ = 2^ (254 * a^3 + 1) * 2 ^ (11 * a) * 2 ^ (- (3 : ℤ) * a) *
        ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal := by
      simp only [← zpow_natCast, ← zpow_add₀ h2]
      congr
      push_cast
      ring
    _ = 2 ^ (254 * a^3 + 1) * 2 ^ (11 * a) *
        ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (2 ^ (3 * a) * (volume (ball (x2 : X) (D ^𝔰 p)))).toNNReal := by
      simp only [mul_div_assoc, mul_assoc, neg_mul, zpow_neg]
      rw [inv_mul_eq_div, div_div, mul_comm (2 ^ (3 * a))]
      simp only [mul_div]
      congr
      rw [ENNReal.toNNReal_mul, NNReal.coe_mul]
      rfl
    _ ≤ (C6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (2 ^ (3 * a) * (volume (ball (x2 : X) (D ^𝔰 p))).toNNReal) := by
          gcongr
          · simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.ofNat_pos, pow_pos,
              mul_pos_iff_of_pos_left, NNReal.coe_pos]
            exact ENNReal.toNNReal_pos (ne_of_gt (measure_ball_pos _ _
              (defaultD_pow_pos a (𝔰 p)))) (by finiteness)
          · exact_mod_cast h4
          · simp only [defaultA, defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultD.eq_1,
            defaultκ.eq_1, ENNReal.toNNReal_mul, ENNReal.toNNReal_pow, NNReal.coe_mul,
            NNReal.coe_pow]
            gcongr
            exact le_refl _
    _ ≤ (C6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume (coeGrid (𝓘 p))).toNNReal := by gcongr; exact hvol x2

-- TODO: PR to Mathlib
omit [MetricSpace X] in
lemma _root_.Set.indicator_one_le_one (x : X) : G.indicator (1 : X → ℝ) x ≤ 1 := by
  classical
  exact le_trans (ite_le_sup _ _ _) (by simp)

omit [TileStructure Q D κ S o] in
lemma enorm_eq_zero_of_notMem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4))) :
    ‖g x‖ₑ = 0 := by
  rw [enorm_eq_zero, ← norm_eq_zero]
  apply le_antisymm _ (norm_nonneg _)
  apply le_trans (hg1 _)
  rw [Set.indicator_of_notMem (Set.notMem_subset ProofData.G_subset
    (Set.notMem_subset ball_subset_closedBall hx))]

/- omit [TileStructure Q D κ S o] in
lemma nnnorm_eq_zero_of_notMem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4))) :
    ‖g x‖₊ = 0 := by
  rw [nnnorm_eq_zero, ← enorm_eq_zero, enorm_eq_zero_of_notMem_closedBall hg1 hx]
 -/

omit [TileStructure Q D κ S o] in
lemma eq_zero_of_notMem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4))) :
    g x = 0 := by
  simpa [coe_nnnorm, norm_eq_zero] using enorm_eq_zero_of_notMem_closedBall hg1 hx

omit [TileStructure Q D κ S o] in
lemma boundedCompactSupport_g {g : X → ℂ} (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport g := by
  constructor
  · constructor
    · exact hg.aestronglyMeasurable
    · have hg1' : ∀ᵐ x, ‖g x‖₊ ≤ 1 := by
        apply Filter.Eventually.of_forall
          (fun x ↦ (le_trans (hg1 x) (indicator_one_le_one _)))
      exact lt_of_le_of_lt (eLpNorm_le_of_ae_nnnorm_bound hg1') (by simp)
  · exact exists_compact_iff_hasCompactSupport.mp ⟨(closedBall o (D ^ S / 4)),
      ⟨isCompact_closedBall o ((D : ℝ) ^ S / 4), fun _ hx ↦ eq_zero_of_notMem_closedBall hg1 hx⟩⟩

lemma boundedCompactSupport_star_Ks_mul_g (p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport (fun (x : X × X) ↦ ((starRingEnd ℂ) (Ks (𝔰 p') x.1 x.2) *  g x.1)) := by
  apply BoundedCompactSupport.mul_bdd_left' (boundedCompactSupport_g hg hg1) continuous_fst
    ?_ ?_ ?_ ?_
  · exact quasiMeasurePreserving_fst
  · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    fun_prop
  · intros K hK
    obtain ⟨C, hC⟩ := isBounded_iff.1 hK.isBounded
    apply isCompact_of_isClosed_isBounded
      ((IsClosed.preimage continuous_fst hK.isClosed).inter (isClosed_tsupport _))
    rw [isBounded_iff]
    use (D ^ (𝔰 p')) + C
    intros x hx y hy
    rw [Prod.dist_eq, sup_le_iff]
    constructor
    · calc dist x.1 y.1
        _ ≤ C := hC hx.1 hy.1
        _ ≤ D ^ 𝔰 p' + C := le_add_of_nonneg_left (by positivity)
    · calc dist x.2 y.2
        _ ≤ dist x.2 y.1 + dist y.1 y.2 := dist_triangle x.2 y.1 y.2
        _ ≤ dist x.2 x.1 + dist x.1 y.1 + dist y.1 y.2 := by
          gcongr
          exact dist_triangle x.2 x.1 y.1
        _ ≤ (D ^ 𝔰 p' / 2) + C + (D ^ 𝔰 p' / 2) := by
          gcongr
          · rw [dist_comm]
            have hx' : x ∈ tsupport fun x ↦ (Ks (𝔰 p') x.1 x.2) := by
              convert hx.2 using 1
              simp only [tsupport]
              apply congr_arg
              ext z
              simp only [mem_support, ne_eq, map_eq_zero]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hx').2
          · exact hC hx.1 hy.1
          · have hy' : y ∈ tsupport fun x ↦ (Ks (𝔰 p') x.1 x.2) := by
              convert hy.2 using 1
              simp only [tsupport]
              apply congr_arg
              ext z
              simp only [mem_support, ne_eq, map_eq_zero]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hy').2
        _ = D ^ 𝔰 p' + C := by ring
  · intros A hA
    rw [isBounded_image_iff]
    obtain ⟨C, hC0, hC⟩ := Bornology.IsBounded.exists_bound_of_norm_Ks hA (𝔰 p')
    use 2 * C
    intros x hx y hy
    rw [dist_conj_conj]
    calc dist (Ks (𝔰 p') x.1 x.2) (Ks (𝔰 p') y.1 y.2)
      _ ≤ ‖(Ks (𝔰 p') x.1 x.2)‖ + ‖(Ks (𝔰 p') y.1 y.2)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖(Ks (𝔰 p') x.1 x.2)‖ + C := by gcongr; exact hC y.1 y.2 hy
      _ ≤ C + C := by gcongr; exact hC x.1 x.2 hx
      _ = 2 * C := by ring

lemma boundedCompactSupport_Ks_mul_star_g (p : 𝔓 X)  {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport (fun (x : X × X) ↦ ((Ks (𝔰 p) x.1 x.2 * ((starRingEnd ℂ) ∘ g) x.1))) := by
  refine BoundedCompactSupport.mul_bdd_left' (ν := volume) ?_ continuous_fst ?_ ?_ ?_ ?_
  · apply BoundedCompactSupport.comp_left_norm (boundedCompactSupport_g hg hg1) (by simp)
      (continuous_conj) (by simp)
  · exact quasiMeasurePreserving_fst
  · apply StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    fun_prop
  · intros K hK
    obtain ⟨C, hC⟩ := isBounded_iff.1 hK.isBounded
    apply isCompact_of_isClosed_isBounded
      ((IsClosed.preimage continuous_fst hK.isClosed).inter (isClosed_tsupport _))
    rw [isBounded_iff]
    use (D ^ (𝔰 p)) + C
    intros x hx y hy
    rw [Prod.dist_eq, sup_le_iff]
    constructor
    · calc dist x.1 y.1
        _ ≤ C := hC hx.1 hy.1
        _ ≤ D ^ 𝔰 p + C := le_add_of_nonneg_left (by positivity)
    · calc dist x.2 y.2
        _ ≤ dist x.2 y.1 + dist y.1 y.2 := dist_triangle x.2 y.1 y.2
        _ ≤ dist x.2 x.1 + dist x.1 y.1 + dist y.1 y.2 := by
          gcongr
          exact dist_triangle x.2 x.1 y.1
        _ ≤ (D ^ 𝔰 p / 2) + C + (D ^ 𝔰 p / 2) := by
          gcongr
          · rw [dist_comm]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hx.2).2
          · exact hC hx.1 hy.1
          · exact (dist_mem_Icc_of_mem_tsupport_Ks hy.2).2
        _ = D ^ 𝔰 p + C := by ring
  · intros A hA
    rw [isBounded_image_iff]
    obtain ⟨C, hC0, hC⟩ := Bornology.IsBounded.exists_bound_of_norm_Ks hA (𝔰 p)
    use 2 * C
    intros x hx y hy
    calc dist (Ks (𝔰 p) x.1 x.2) (Ks (𝔰 p) y.1 y.2)
      _ ≤ ‖(Ks (𝔰 p) x.1 x.2)‖ + ‖(Ks (𝔰 p) y.1 y.2)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖(Ks (𝔰 p) x.1 x.2)‖ + C := by gcongr; exact hC y.1 y.2 hy
      _ ≤ C + C := by gcongr; exact hC x.1 x.2 hx
      _ = 2 * C := by ring


-- This was deleted from `BoundedCompactSupport.lean`, but I need it.
open Bornology in
lemma _root_.isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by convert isBounded_iff_forall_norm_le; simp

-- memLp_top_of_bound
lemma boundedCompactSupport_aux_6_2_26 (p p' : 𝔓 X) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport (fun (x, z1, z2) ↦ (starRingEnd ℂ) (Ks (𝔰 p') z1 x) *
      Complex.exp (Complex.I * (((Q z1) z1) - ((Q z1) x))) * g z1 * (Ks (𝔰 p) z2 x *
        Complex.exp (Complex.I * (-((Q z2) z2) + ((Q z2) x))) * (starRingEnd ℂ) (g z2))) := by
  suffices BoundedCompactSupport (fun (x, z1, z2) ↦ ((starRingEnd ℂ) (Ks (𝔰 p') z1 x) *  g z1) *
      ((Ks (𝔰 p) z2 x  * (starRingEnd ℂ) (g z2)))) by
    have heq : (fun (x, z1, z2) ↦ (starRingEnd ℂ) (Ks (𝔰 p') z1 x) *
        Complex.exp (Complex.I * (((Q z1) z1) - ((Q z1) x))) * g z1 * (Ks (𝔰 p) z2 x *
          Complex.exp (Complex.I * (-((Q z2) z2) + ((Q z2) x))) * (starRingEnd ℂ) (g z2))) =
        (fun (x, z1, z2) ↦ ((starRingEnd ℂ) (Ks (𝔰 p') z1 x) *  g z1) *
        ((Ks (𝔰 p) z2 x  * (starRingEnd ℂ) (g z2))) *
        ((Complex.exp (Complex.I * (((Q z1) z1) - ((Q z1) x)))) *
           (Complex.exp (Complex.I * (-((Q z2) z2) + ((Q z2) x)))))) := by ext; ring
    rw [heq]
    apply BoundedCompactSupport.mul_bdd_right this
    · constructor
      · apply StronglyMeasurable.aestronglyMeasurable
        apply Measurable.stronglyMeasurable
        fun_prop
      · refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound (C := 1) ?_) (by simp)
        apply Filter.Eventually.of_forall
        intro x
        rw [← ofReal_sub, ← ofReal_neg, ← ofReal_add]
        simp only [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  constructor
  · --MemLP
    constructor
    · -- AEStronglyMeasurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply Measurable.stronglyMeasurable
      fun_prop
    · --eLpNorm_lt_top
      simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
      have h1 : Filter.IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) (ae volume) fun (x : X × X) ↦
          ‖(starRingEnd ℂ) (Ks (𝔰 p') x.1 x.2) * g x.1 ‖₊ := by
        rw [← eLpNormEssSup_lt_top_iff_isBoundedUnder, ← eLpNorm_exponent_top]
        exact (boundedCompactSupport_star_Ks_mul_g p' hg hg1).memLp_top.eLpNorm_lt_top
      have h2 : Filter.IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) (ae volume) fun (x : X × X) ↦
          ‖Ks (𝔰 p) x.1 x.2 * (starRingEnd ℂ) (g x.1)‖₊ := by
        rw [← eLpNormEssSup_lt_top_iff_isBoundedUnder, ← eLpNorm_exponent_top]
        exact (boundedCompactSupport_Ks_mul_star_g p hg hg1).memLp_top.eLpNorm_lt_top
      obtain ⟨B, hB⟩ := h1
      obtain ⟨C, hC⟩ := h2
      use B * C
      simp only [nnnorm_mul, RCLike.nnnorm_conj, Filter.eventually_map] at hB hC ⊢
      have hp1 : QuasiMeasurePreserving (fun z : X × X × X ↦ (z.2.1, z.1)) volume volume := by
        suffices QuasiMeasurePreserving (Prod.map (id (α := X)) (Prod.fst (α := X) (β := X)))
            volume volume from
          measurePreserving_swap.quasiMeasurePreserving.comp this
        fun_prop
      have hp2 : QuasiMeasurePreserving (fun z : X × X × X ↦ (z.2.2, z.1)) volume volume := by
        suffices QuasiMeasurePreserving (Prod.map (id (α := X)) (Prod.snd (α := X) (β := X)))
            volume volume from
          measurePreserving_swap.quasiMeasurePreserving.comp this
        fun_prop
      filter_upwards [hp1.ae hB, hp2.ae hC] with x h1x h2x
      exact mul_le_mul h1x h2x (zero_le _) (zero_le _)
  · -- HasCompactSupport
    rw [← exists_compact_iff_hasCompactSupport]
    use (closedBall (cancelPt X) (defaultD a ^ defaultS X)) ×ˢ
      (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4)) ×ˢ
      (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4))
    refine ⟨(isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)), ?_⟩
    intros x hx
    simp only [mem_prod, not_and_or] at hx
    simp only [mul_eq_zero, map_eq_zero, Complex.exp_ne_zero, or_false]
    rcases hx with (hx | (hx | hx))
    · left
      by_cases hx2 : x.2.1 ∈ (closedBall o (D ^ S / 4))
      · left
        simp only [mem_closedBall, not_le] at hx hx2
        apply Ks_eq_zero_of_le_dist
        calc (D : ℝ) ^ 𝔰 p' / 2
          _ ≤ (D : ℝ) ^ defaultS X / 2 := by
            rw [← zpow_natCast]
            have : 1 ≤ (D : ℝ) := one_le_D
            have : 𝔰 p' ≤ S := (range_s_subset (X := X) (mem_range_self (𝓘 p'))).2
            gcongr
          _ ≤ (D : ℝ) ^ defaultS X - (D : ℝ) ^ defaultS X / 4 := by
            ring_nf
            gcongr _ * ?_
            linarith
          _ ≤ dist x.1 o - (D : ℝ) ^ defaultS X / 4 := by gcongr
          _ ≤ dist x.1 o - dist x.2.1 o := by gcongr
          _ ≤ dist x.2.1 x.1 := by
            rw [tsub_le_iff_right]
            exact dist_triangle_left _ _ _
      · exact Or.inr (eq_zero_of_notMem_closedBall hg1 hx2)
    · exact Or.inl (Or.inr (eq_zero_of_notMem_closedBall hg1 hx))
    · exact Or.inr (Or.inr (eq_zero_of_notMem_closedBall hg1 hx))

lemma boundedCompactSupport_bound (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport (fun (x : X × X) ↦ (((C6_1_5 a : ℝ≥0∞) *
      (1 + (nndist_(p') (𝒬 p') (𝒬 p) : ℝ≥0∞)) ^ (-(2 * (a : ℝ) ^ 2 + (a : ℝ) ^ 3)⁻¹) /
        volume (𝓘 p : Set X)).toNNReal : ℝ) * ‖g x.1‖ * ‖g x.2‖) := by
  constructor
  · -- MemLp
    · refine ⟨(Measurable.stronglyMeasurable (by fun_prop)).aestronglyMeasurable, ?_⟩
      refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound
          (C := (C6_1_5 a) * (1 + nndist_(p') (𝒬 p') (𝒬 p)) ^
        (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) / (volume (𝓘 p : Set X)).toNNReal) ?_) ?_
      · apply Filter.Eventually.of_forall
        intro x
        calc ‖(((C6_1_5 a : ℝ≥0∞) * (1 + (nndist_(p') (𝒬 p') (𝒬 p))) ^
                (-(2 * (a : ℝ) ^ 2 + (a : ℝ) ^ 3)⁻¹) / volume (𝓘 p : Set X)).toNNReal : ℝ) *
                  ‖g x.1‖ * ‖g x.2‖‖
          _ =  ‖(C6_1_5 a) * (1 + nndist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
              (volume (𝓘 p : Set X)).toNNReal * ‖g x.1‖ * ‖g x.2‖‖ := by
              congr
              simp only [coe_nnreal_ennreal_nndist, edist_dist, ENNReal.toNNReal_div,
                ENNReal.toNNReal_mul, ENNReal.toNNReal_coe,
                ENNReal.toNNReal_rpow, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_rpow,
                coe_nndist]
              congr
              norm_cast
              rw [ENNReal.toReal_add ENNReal.one_ne_top (by simp)]
              simp only [ENNReal.toReal_one, _root_.add_right_inj, ENNReal.toReal_ofReal_eq_iff]
              exact dist_nonneg
          _ = ↑(C6_1_5 a) * (1 + nndist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
              (volume (𝓘 p : Set X)).toNNReal * ↑‖g x.1‖ * ↑‖g x.2‖  := by
            simp only [norm_mul, norm_mul, Real.norm_eq_abs, NNReal.abs_eq, coe_nnnorm,
              _root_.abs_of_nonneg (norm_nonneg _), _root_.abs_of_nonneg
              (div_nonneg (mul_nonneg NNReal.zero_le_coe
                (Real.rpow_nonneg ( add_nonneg zero_le_one dist_nonneg) _)) NNReal.zero_le_coe)]
            simp only [coe_nndist, mul_eq_mul_right_iff, abs_eq_self, norm_eq_zero]
            exact Or.inl (Or.inl (by positivity))
          _ ≤ ↑(C6_1_5 a) * (1 + nndist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
              (volume (𝓘 p : Set X)).toNNReal * 1 * 1 := by
            gcongr <;>
            exact le_trans (hg1 _) (indicator_one_le_one _)
          _ = ↑(C6_1_5 a) * (1 + nndist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
              (volume (𝓘 p : Set X)).toNNReal := by
            simp only [mul_one]
      · simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero]
        exact compareOfLessAndEq_eq_lt.mp rfl
  · -- Compact support
    simp_rw [mul_assoc]
    apply HasCompactSupport.mul_left
    rw [← exists_compact_iff_hasCompactSupport]
    use (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4) ×ˢ
      (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4)))
    refine ⟨(isCompact_closedBall _ _).prod (isCompact_closedBall _ _), ?_⟩
    intros x hx
    simp only [mem_prod, not_and_or] at hx
    rcases hx with (hx | hx)
    · convert zero_mul _
      rw [norm_eq_zero, eq_zero_of_notMem_closedBall hg1 hx]
    · convert mul_zero _
      rw [norm_eq_zero, eq_zero_of_notMem_closedBall hg1 hx]

lemma integrableOn_bound (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    IntegrableOn (fun x ↦ (((C6_1_5 a : ℝ≥0∞) *
      (1 + (nndist_{𝔠 p', (D : ℝ) ^ 𝔰 p' / 4} (𝒬 p') (𝒬 p) : ℝ≥0∞)) ^
        (-(2 * (a : ℝ) ^ 2 + (a : ℝ) ^ 3)⁻¹) / volume (𝓘 p : Set X)).toNNReal : ℝ) * ‖g x.1‖ *
      ‖g x.2‖) (E p' ×ˢ E p) volume :=
  (boundedCompactSupport_bound p p' hg hg1).integrable.integrableOn

-- NOTE: `unfold correlation` is still needed after adding the measurability lemma.
lemma stronglyMeasurable_I12 (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun (x : X × X) ↦ (I12 p p' g x.1 x.2)) := by
  simp only [I12, nnnorm_mul, NNReal.coe_mul, coe_nnnorm, mul_assoc]
  apply Measurable.stronglyMeasurable
  exact (((Measurable.stronglyMeasurable
    (by unfold correlation; fun_prop)).integral_prod_left.measurable).mul (by fun_prop)).enorm

lemma stronglyMeasurable_I12'' (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun (x : X × X) ↦ (I12 p p' g x.1 x.2).toReal) :=
  (ENNReal.measurable_toReal.comp (stronglyMeasurable_I12 p p' hg).measurable).stronglyMeasurable

lemma stronglyMeasurable_I12' (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun (x : X × X) ↦ ((I12 p p' g x.1 x.2).toReal : ℂ)) :=
  (Complex.measurable_ofReal.comp
    (ENNReal.measurable_toReal.comp (stronglyMeasurable_I12 p p' hg).measurable)).stronglyMeasurable

lemma integrableOn_I12 (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    IntegrableOn (fun x ↦ ((I12 p p' g x.1 x.2).toNNReal : ℝ)) (E p' ×ˢ E p) volume
    /- IntegrableOn (fun x ↦ (I12 p p' g x.1 x.2).toNNReal) (E p' ×ˢ E p) volume -/ := by
  classical
  set f : X × X → ℝ := fun x ↦ if x ∈ E p' ×ˢ E p then ((I12 p p' g x.1 x.2).toNNReal : ℝ) else 0
  have hf : IntegrableOn f (E p' ×ˢ E p) volume := by
    apply Integrable.integrableOn
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.mono_norm (boundedCompactSupport_bound p p' hg hg1)
    · exact (StronglyMeasurable.ite (measurableSet_E.prod measurableSet_E)
        (stronglyMeasurable_I12'' p p' hg) stronglyMeasurable_const).aestronglyMeasurable
    · intro z
      by_cases hz : z ∈ (E p') ×ˢ (E p)
      · have ha1 : 1 < a := by omega
        simp only [f, if_pos hz, Real.norm_eq_abs, NNReal.abs_eq]
        apply le_trans (I12_nnreal_le ha1 hle g hinter ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩)
        simp only [coe_nnnorm]
        gcongr ?_ *  ‖g ↑_‖ * ‖g ↑_‖
        convert (bound_6_2_29' ha p p' ⟨z.2, hz.2⟩)
        simp only [coe_nnreal_ennreal_nndist,
          ENNReal.toNNReal_div, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe, ENNReal.toNNReal_rpow,
          NNReal.coe_div, NNReal.coe_mul, NNReal.coe_rpow, f]
        congr
        rw [edist_dist]
        rw [ENNReal.toNNReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toNNReal_one, NNReal.coe_add, NNReal.coe_one, _root_.add_right_inj]
        norm_cast
        rw [ENNReal.toReal_ofReal dist_nonneg]
      · simp only [f, if_neg hz, norm_zero]
        positivity
  exact MeasureTheory.IntegrableOn.congr_fun hf (fun _ hx ↦ by simp only [f, if_pos hx])
    (measurableSet_E.prod measurableSet_E)

/- TODO: it should be way easier to deduce this from `integrableOn_I12`, right? -/
lemma integrableOn_I12' (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    IntegrableOn (fun x ↦ ((I12 p p' g x.1 x.2).toReal : ℂ)) (E p' ×ˢ E p) volume :=
  ContinuousLinearMap.integrable_comp (Complex.ofRealCLM) (integrableOn_I12 ha hle hg hg1 hinter)

lemma bound_6_2_26_aux (p p' : 𝔓 X) (g : X → ℂ) :
    let f := fun (x, z1, z2) ↦ (starRingEnd ℂ) (Ks (𝔰 p') z1 x) *
      exp (I * (((Q z1) z1) - ((Q z1) x))) * g z1 * (Ks (𝔰 p) z2 x *
        exp (I * (-((Q z2) z2) + ((Q z2) x))) * (starRingEnd ℂ) (g z2))
    ∫ (x : X × X) in E p' ×ˢ E p, ‖(∫ (y : X) in univ, f (x, y).swap)‖ ∂volume.prod volume =
      ∫ (z : X × X) in E p' ×ˢ E p, (I12 p p' g z.1 z.2).toReal := by
  congr
  ext x
  /- We move `exp (I * (↑((Q x.1) x.1))`, `exp (I * (-↑((Q x.2) x.2)` and `g x.1` to the right
  so that we can take their product with `(starRingEnd ℂ) (g x.2))` out of the integral -/
  have heq : ∫ (y : X), (starRingEnd ℂ) (Ks (𝔰 p') x.1 y) *
    exp (I * (↑((Q x.1) x.1) - ↑((Q x.1) y))) * g x.1 *
    (Ks (𝔰 p) x.2 y * exp (I * (-↑((Q x.2) x.2) + ↑((Q x.2) y))) * (starRingEnd ℂ) (g x.2)) =
      ∫ (y : X), ((starRingEnd ℂ) (Ks (𝔰 p') x.1 y) * exp (I * (- ↑((Q x.1) y))) *
        (Ks (𝔰 p) x.2 y * exp (I * (↑((Q x.2) y)))) * ((exp (I * (↑((Q x.1) x.1)))) *
          (exp (I * (-↑((Q x.2) x.2)))) * g x.1 * (starRingEnd ℂ) (g x.2))) := by
      congr
      ext y
      simp_rw [mul_add I, mul_sub I, sub_eq_add_neg, exp_add]
      ring_nf
  have hx1 : ‖(exp (I * ↑((Q x.1) x.1)))‖  = 1 := by
    simp only [norm_exp, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
      mul_zero, _root_.sub_self, Real.exp_zero]
  have hx2 : ‖(exp (I * -↑((Q x.2) x.2)))‖ = 1 := by
    simp only [mul_neg, norm_exp, neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im,
      ofReal_im, mul_zero, _root_.sub_self, neg_zero, Real.exp_zero]
  simp only [restrict_univ, Prod.swap_prod_mk, I12, enorm_mul, ENNReal.toReal_mul,
    toReal_enorm]
  simp_rw [heq, integral_mul_const, norm_mul, norm_conj, ← mul_assoc]
  rw [hx1, hx2]
  simp only [mul_neg, mul_one, correlation]
  congr
  ext y
  rw [mul_add I, exp_add]
  ring_nf

-- Estimate 6.2.24 -- 6.2.25 by 6.2.26
lemma bound_6_2_26 (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖ₑ ≤
      ‖ ∫ (z : X × X) in E p' ×ˢ E p, ((I12 p p' g z.fst z.snd).toReal : ℂ) ‖ₑ := by
  have haux : ∀ (y : X), (starRingEnd ℂ) (∫ (y1 : X) in E p, (starRingEnd ℂ) (Ks (𝔰 p) y1 y) *
      exp (I * (↑((Q y1) y1) - ↑((Q y1) y))) * g y1) =
      (∫ (y1 : X) in E p, (Ks (𝔰 p) y1 y) * exp (I * (- ((Q y1) y1) + ↑((Q y1) y))) *
        (starRingEnd ℂ) (g y1)) := complex_exp_lintegral
  simp only [adjointCarleson, haux] --LHS is now 6.2.24 -- 6.2.25. TODO: fix in blueprint
  simp_rw [← MeasureTheory.setIntegral_prod_mul]
  rw [← setIntegral_univ]
  set f := fun (x, z1, z2) ↦ (starRingEnd ℂ) (Ks (𝔰 p') z1 x) *
    exp (I * (((Q z1) z1) - ((Q z1) x))) * g z1 * (Ks (𝔰 p) z2 x *
      exp (I * (-((Q z2) z2) + ((Q z2) x))) * (starRingEnd ℂ) (g z2))
  have hf : IntegrableOn f (univ ×ˢ E p' ×ˢ E p) (volume.prod (volume.prod volume)) :=
    (boundedCompactSupport_aux_6_2_26 p p' hg hg1).integrable.integrableOn
  have hf' : IntegrableOn (fun z ↦ f z.swap) ((E p' ×ˢ E p) ×ˢ univ)
    ((volume.prod volume).prod volume) := hf.swap
  rw [← MeasureTheory.setIntegral_prod (f := f) hf, ← MeasureTheory.setIntegral_prod_swap,
    MeasureTheory.setIntegral_prod _ hf']
  simp only [restrict_univ, Prod.swap_prod_mk, enorm_eq_nnnorm,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, ge_iff_le]
  calc
    _ = ‖∫ (x : X × X) in E p' ×ˢ E p, (∫ (y : X) in univ, f (x, y).swap) ∂volume.prod volume‖ := by
      simp only [restrict_univ, Prod.swap_prod_mk]
    _ ≤ ∫ (x : X × X) in E p' ×ˢ E p, ‖(∫ (y : X) in univ, f (x, y).swap)‖ ∂volume.prod volume :=
      norm_integral_le_integral_norm fun a_1 ↦ ∫ (y : X) in univ, f (a_1, y).swap
    _ = ∫ (z : X × X) in E p' ×ˢ E p, (I12 p p' g z.1 z.2).toReal := bound_6_2_26_aux p p' g
    _ = ‖∫ (z : X × X) in E p' ×ˢ E p, ((I12 p p' g z.1 z.2).toReal : ℂ)‖ := by
      conv_rhs => rw [← setIntegral_re_add_im (integrableOn_I12' ha hle hg hg1 hinter)]
      simp only [norm_real, NNReal.norm_eq, RCLike.re_to_complex,ofReal_re, coe_algebraMap,
        RCLike.im_to_complex, ofReal_im, integral_zero, ofReal_zero, RCLike.I_to_complex,
        zero_mul, add_zero]
      rw [Real.norm_of_nonneg (integral_nonneg (fun x ↦ by simp))]

-- We assume 6.2.23.
lemma correlation_le_of_nonempty_inter (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    ‖∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y)‖ₑ ≤
      C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) /
        volume (coeGrid (𝓘 p)) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
  -- Definition 6.2.27
  set I12 := I12 p p' g
  -- Inequality 6.2.29
  have hI12 : ∀ (x1 : E p') (x2 : E p), I12 x1 x2 ≤
      (2^(254 * a^3 + 8 * a + 1) * ((1 + edist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹))) /
      (volume (ball (x2 : X) (D ^𝔰 p))) * ‖g ↑x1‖ₑ * ‖g ↑x2‖ₑ :=
    I12_le (by omega) p p' hle g hinter
  -- Bound 6.2.29 using 6.2.32 and `4 ≤ a`.
  have hle' : ∀ (x2 : E p), 2 ^ (254 * a^3 + 8 * a + 1) *
      ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume (ball (x2 : X) (D ^𝔰 p))) ≤ (C6_1_5 a) *
          ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume (coeGrid (𝓘 p))).toNNReal := bound_6_2_29 ha p p'
  -- Estimate 6.2.24 -- 6.2.25 by 6.2.26
  have hbdd : ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖ₑ ≤
      ‖ ∫ (z : X × X) in E p' ×ˢ E p, ((I12 z.fst z.snd).toReal : ℂ) ‖ₑ :=
    bound_6_2_26 ha hle hg hg1 hinter
  apply le_trans hbdd
  have hcoe : ∫ (z : X × X) in E p' ×ˢ E p, ((I12 z.fst z.snd).toReal : ℂ) =
    ∫ (z : X × X) in E p' ×ˢ E p, (I12 z.fst z.snd).toReal := by
    rw [← setIntegral_re_add_im]
    simp only [RCLike.re_to_complex, ofReal_re, coe_algebraMap, RCLike.im_to_complex, ofReal_im,
      integral_zero, ofReal_zero, RCLike.I_to_complex, zero_mul, add_zero]
    · have hre := integrableOn_I12 ha hle hg hg1 hinter
      rw [IntegrableOn] at hre ⊢
      exact MeasureTheory.Integrable.re_im_iff.mp
        ⟨hre, by simp only [RCLike.im_to_complex, ofReal_im, integrable_zero]⟩
  have h : ‖∫ (z : X × X) in E p' ×ˢ E p, ((I12 z.1 z.2).toReal : ℂ)‖ₑ ≤
      ‖∫ (z : X × X) in E p' ×ˢ E p, ((C6_1_5 a) *
          ((1 + nndist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume (coeGrid (𝓘 p)))).toNNReal * ‖g z.1‖ * ‖g z.2‖ ‖ₑ := by
    rw [hcoe, enorm_le_iff_norm_le]
    simp only [norm_real, Real.norm_eq_abs]
    apply abs_le_abs_of_nonneg (setIntegral_nonneg (measurableSet_E.prod measurableSet_E)
        (fun _ _ ↦ NNReal.zero_le_coe))
    apply setIntegral_mono_on (integrableOn_I12 ha hle hg hg1 hinter)
      (integrableOn_bound p p' hg hg1) (measurableSet_E.prod measurableSet_E)
    intro z hz
    simp only [← coe_nnnorm, ← NNReal.coe_toRealHom, ← map_mul NNReal.toRealHom]
    simp only [NNReal.coe_toRealHom]
    rw [NNReal.coe_le_coe, ← ENNReal.coe_le_coe]
    apply le_trans (hI12 ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩)
    simp only [ENNReal.toNNReal_div, ENNReal.toNNReal_mul, ENNReal.coe_mul, ← enorm_eq_nnnorm]
    gcongr ?_ *  ‖g ↑_‖ₑ * ‖g ↑_‖ₑ
    simp only [edist_nndist]
    convert (hle' ⟨z.2, hz.2⟩)
    rw [ENNReal.coe_div (ENNReal.toNNReal_ne_zero.mpr ⟨ne_of_gt (volume_coeGrid_pos
      (defaultD_pos' a)), ne_of_lt volume_coeGrid_lt_top⟩)]
    congr
    rw [← ENNReal.toNNReal_mul, ENNReal.coe_toNNReal]
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    simp only [coe_nnreal_ennreal_nndist, ne_eq, ENNReal.rpow_eq_top_iff, add_eq_zero,
      one_ne_zero, false_and, Left.neg_neg_iff, inv_pos, ENNReal.add_eq_top, ENNReal.one_ne_top,
      false_or, Left.neg_pos_iff, inv_neg'', not_and, not_lt]
    intro
    positivity
  apply le_trans h
  rw [enorm_eq_nnnorm]
  simp only [coe_nnnorm, I12,  mul_assoc]
  rw [integral_const_mul]
  simp only [nnnorm_mul, nnnorm_div]
  have hprod : ‖∫ (a : X × X) in E p' ×ˢ E p, ‖g a.1‖ * ‖g a.2‖ ‖₊ ≤
      ((∫⁻  (y : X) in E p', ‖g y‖ₑ) * ∫⁻ (y : X) in E p, ‖g y‖ₑ) := by
    rw [← lintegral_prod_mul (by fun_prop) (by fun_prop), ← enorm_eq_nnnorm]
    convert (MeasureTheory.enorm_integral_le_lintegral_enorm _)
    · rw [prod_restrict]; rfl
    · simp [enorm_mul, enorm_norm]
  rw [ENNReal.coe_mul]
  gcongr
  simp only  [ENNReal.toNNReal_div, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe, ENNReal.toNNReal_rpow,
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_rpow, nnnorm_div, nnnorm_mul, NNReal.nnnorm_eq]
  norm_cast
  rw [ENNReal.coe_div (ENNReal.toNNReal_ne_zero.mpr
      ⟨ne_of_gt (volume_coeGrid_pos (defaultD_pos' a)), by finiteness⟩), ENNReal.coe_mul,
      NNReal.nnnorm_eq, edist_nndist, ENNReal.coe_rpow_of_ne_zero (by simp),
      ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal (by finiteness)]

-- If 6.2.23 does not hold, then the LHS equals zero and the result follows trivially.
lemma correlation_le_of_empty_inter {p p' : 𝔓 X} {g : X → ℂ}
    (hinter : ¬ (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    ‖∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y)‖ₑ ≤
      C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) /
        volume (coeGrid (𝓘 p)) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
  calc ‖∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y)‖ₑ
      _ = 0 := by
        simp only [inter_nonempty, not_exists, not_and_or] at hinter
        rw [enorm_eq_zero]
        apply MeasureTheory.integral_eq_zero_of_ae (Eq.eventuallyEq _)
        ext y
        rcases hinter y with hp'y | hpy
        · have hp'0 : adjointCarleson p' g y = 0 := by
            by_contra hy
            exact hp'y (range_support hy)
          simp [hp'0, zero_mul, Pi.zero_apply]
        · have hp'0 : adjointCarleson p g y = 0 := by
            by_contra hy
            exact hpy (range_support hy)
          simp [hp'0, map_zero, mul_zero, Pi.zero_apply]
      _ ≤ C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) /
        volume (coeGrid (𝓘 p)) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
        positivity

-- Lemma 6.1.5 (part I)
lemma correlation_le (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y)‖ₑ ≤
      C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) /
        volume (coeGrid (𝓘 p)) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
  by_cases hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty
  · exact correlation_le_of_nonempty_inter ha hle hg hg1 hinter
  · exact correlation_le_of_empty_inter hinter

-- Lemma 6.1.5 (part II)
lemma correlation_zero_of_ne_subset (p p' : 𝔓 X) (g : X → ℂ)
    (hp : ¬ coeGrid (𝓘 p) ⊆ ball (𝔠 p) (15 * D ^𝔰 p)) :
    ‖∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y)‖ₑ = 0 := by
  simp only [enorm_eq_nnnorm, ENNReal.coe_eq_zero]
  have hD : 1 ≤ (D : ℝ) := one_le_defaultD _
  have h415 : (4 : ℝ) ≤ 15 := by linarith
  have hsp : 𝔰 p = GridStructure.s (𝓘 p) := rfl
  by_contra h0
  simp only [nnnorm_eq_zero] at h0
  apply hp
  obtain ⟨y, hy⟩ := MeasureTheory.exists_ne_zero_of_integral_ne_zero h0 --6.2.33
  simp only [ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
  -- 6.2.35
  rw [hsp]
  exact subset_trans Grid_subset_ball (ball_subset_ball (by gcongr))

end lemma_6_1_5

end Tile
