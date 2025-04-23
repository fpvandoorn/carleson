import Carleson.Antichain.ForMathlib
import Carleson.ForestOperator.AlmostOrthogonality
import Carleson.HolderVanDerCorput

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ComplexConjugate ENNReal NNReal ShortVariables

open MeasureTheory Metric Set Complex

namespace Tile

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X]
  [ProofData a q K σ₁ σ₂ F G]

-- Def 6.2.1 (Lemma 6.2.1)
def correlation (s₁ s₂ : ℤ) (x₁ x₂ y : X) : ℂ := (conj (Ks s₁ x₁ y)) * (Ks s₂ x₂ y)

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
    (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0) : y ∈ (ball x₁ (↑D ^s₁)) := by
  have hKs : Ks s₁ x₁ y ≠ 0 := by
    simp only [correlation, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
    exact hy.1
  rw [mem_ball, dist_comm]
  exact lt_of_le_of_lt (dist_mem_Icc_of_Ks_ne_zero hKs).2
    (half_lt_self_iff.mpr (defaultD_pow_pos a s₁))

def C_6_2_1 (a : ℕ) : ℝ≥0 := 2^(254 * a^3)

--TODO: PR to Mathlib
lemma ENNReal.mul_div_mul_comm {a b c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inr hd) (Or.inl hc)]
  ring

lemma aux_6_2_3 (s₁ s₂ : ℤ) (x₁ x₂ y y' : X)  :
  ‖Ks s₂ x₂ y‖ₑ * ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ ≤
  ↑(C2_1_3 ↑a) / volume (ball x₂ (↑D ^ s₂)) *
    (↑(D2_1_3 ↑a) / volume (ball x₁ (↑D ^ s₁)) * (↑(nndist y y') ^ τ / ↑((D : ℝ≥0) ^ s₁) ^ τ)) := by
  have hτ : 0 ≤ τ := by simp only [defaultτ, inv_nonneg, Nat.cast_nonneg]
  apply mul_le_mul enorm_Ks_le _ (zero_le _) (zero_le _)
  convert nnnorm_Ks_sub_Ks_le
  rw [← ENNReal.div_rpow_of_nonneg _ _ hτ]
  simp only [defaultτ]
  congr
  rw [ENNReal.coe_zpow (by simp)]
  rfl

-- Eq. 6.2.3 (Lemma 6.2.1)
lemma correlation_kernel_bound (ha : 1 < a) {s₁ s₂ : ℤ} (hs₁ : s₁ ∈ Icc (- (S : ℤ)) s₂)
   {x₁ x₂ : X} :
    iHolENorm (correlation s₁ s₂ x₁ x₂) x₁ (↑D ^s₁) ≤
      (C_6_2_1 a : ℝ≥0∞) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂))) := by
  -- 6.2.4
  have hφ' (y : X) : ‖correlation s₁ s₂ x₁ x₂ y‖ₑ ≤
      (C2_1_3 a)^2 / ((volume (ball x₁ (D ^ s₁))) * (volume (ball x₂ (D ^ s₂)))) := by
    intro y
    simp only [correlation, nnnorm_mul, RCLike.nnnorm_conj, ENNReal.coe_mul, pow_two,
      ENNReal.mul_div_mul_comm (measure_ball_ne_top _ _) (measure_ball_ne_top _ _)]
    exact mul_le_mul nnnorm_Ks_le nnnorm_Ks_le (zero_le _) (zero_le _)
    simp only [correlation, enorm_mul, RCLike.enorm_conj, pow_two,
      ENNReal.mul_div_mul_comm (.inr (measure_ball_ne_top _ _)) (.inl (measure_ball_ne_top _ _))]
    exact mul_le_mul enorm_Ks_le enorm_Ks_le (zero_le _) (zero_le _)
  -- 6.2.6 + 6.2.7
  have hsimp : ∀ (y y' : X),
      ‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖ₑ ≤
        ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y‖ₑ +
          ‖Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖ₑ := by
    intro y y'
    calc ‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖ₑ
      _ = ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y +
          (conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * (Ks s₂ x₂ y'))‖ₑ := by
        simp only [correlation, sub_add_sub_cancel]
      _ ≤ ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y ‖ₑ +
          ‖conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * (Ks s₂ x₂ y')‖ₑ :=
            enorm_add_le _ _
      _ = ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y‖ₑ +
          ‖Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖ₑ := by
          simp only [← sub_mul, ← mul_sub, enorm_mul, RCLike.enorm_conj, ← map_sub]
  -- 6.2.5
  have hyy' : ∀ (y y' : X) (hy' : y ≠ y'), (((D  ^ s₁ : ℝ≥0)) ^ τ)  *
    (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖ₑ / (nndist y y')^τ) ≤
      (2^(253*a^3) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂)))) := by
    intros y y' hy'
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le, ENNReal.div_le_iff_le_mul]
    calc ‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖ₑ
      _ ≤ ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y‖ₑ +
          ‖Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖ₑ := hsimp y y' -- 6.2.6 + 6.2.7
      _ ≤ 2 ^ (252 * a ^ 3) / (volume (ball x₁ (↑D ^ s₁)) * volume (ball x₂ (↑D ^ s₂))) *
        (↑(nndist y y') ^ τ / ((D ^ s₁ : ℝ≥0) : ℝ≥0∞) ^ τ +
          ↑(nndist y y') ^ τ / ((D ^ s₂ : ℝ≥0) : ℝ≥0∞) ^ τ) := by
        have h2 : (2 : ℝ≥0∞) ^ (252 * a ^ 3) = C2_1_3 a * D2_1_3 a := by
          simp only [C2_1_3, NNReal.coe_natCast, D2_1_3]
          norm_cast
          ring
        rw [mul_comm, mul_add, h2, mul_comm (volume _)]
        simp only [ENNReal.mul_div_mul_comm (.inr (measure_ball_ne_top _ _))
          (.inl (measure_ball_ne_top _ _)), mul_assoc]
        apply add_le_add (aux_6_2_3 s₁ s₂ x₁ x₂ y y')
        rw [← neg_sub, enorm_neg]
        convert aux_6_2_3 s₂ s₁ x₂ x₁ y' y using 1
        simp only [← mul_assoc, ← ENNReal.mul_div_mul_comm (.inr (measure_ball_ne_top _ _))
          (.inl (measure_ball_ne_top _ _))]
        rw [mul_comm (volume _), nndist_comm]
      _ ≤ 2 ^ (252 * a ^ 3) / (volume (ball x₁ (↑D ^ s₁)) * volume (ball x₂ (↑D ^ s₂))) *
        (2 * (↑(nndist y y') ^ τ / ((D ^ s₁ : ℝ≥0) : ℝ≥0∞) ^ τ)) := by
        have hτ : 0 < τ := by
          simp only [defaultτ, inv_pos, Nat.cast_pos]
          omega
        rw [ENNReal.mul_le_mul_left, two_mul, ENNReal.add_le_add_iff_left]
        apply ENNReal.div_le_div_left
        rw [ENNReal.rpow_le_rpow_iff, ENNReal.coe_le_coe]
        exact zpow_le_zpow_right₀ one_le_D hs₁.2
        · exact hτ
        · -- I also used this in Psi.lean, with slightly different coercions.
          have hnetop : (nndist y y' : ℝ≥0∞) / ((D ^ s₁  : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by
            simp only [Nat.cast_pow, Nat.cast_ofNat,
              ENNReal.coe_pow, ENNReal.coe_ofNat, ne_eq, ENNReal.div_eq_top, not_or, not_and',
              Decidable.not_not]
            have h' : ((D^ s₁ : ℝ≥0) : ℝ≥0∞)  ≠ 0 := by
                exact ENNReal.coe_ne_zero.mpr (ne_of_gt (defaultD_pow_pos a s₁))
            exact ⟨fun h ↦ absurd h h', fun _ ↦ ENNReal.coe_ne_top⟩
          rw [← ENNReal.div_rpow_of_nonneg _ _ (le_of_lt hτ)]
          simp only [defaultτ, ne_eq, ENNReal.rpow_eq_top_iff, ENNReal.div_eq_zero_iff,
            ENNReal.coe_eq_zero, nndist_eq_zero, ENNReal.coe_ne_top, or_false, inv_neg'', inv_pos,
            Nat.cast_pos, not_or, not_and, not_lt, Nat.cast_nonneg, implies_true,
            nonpos_iff_eq_zero, true_and]
          intro htop
          exact absurd htop hnetop
        · simp only [ne_eq, ENNReal.div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
          mul_eq_zero, not_false_eq_true, pow_eq_zero_iff, false_or, false_and]
          exact ENNReal.mul_ne_top (measure_ball_ne_top x₁ (D ^ s₁))
            (measure_ball_ne_top x₂ (D ^ s₂))
        · simp only [ne_eq, ENNReal.div_eq_top,
          pow_eq_zero_iff', OfNat.ofNat_ne_zero, mul_eq_zero, not_false_eq_true, pow_eq_zero_iff,
          false_or, false_and, true_and, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, or_false,
          not_or]
          exact ⟨ne_of_gt (measure_ball_pos volume x₁ (defaultD_pow_pos a s₁)),
            ne_of_gt (measure_ball_pos volume x₂ (defaultD_pow_pos a s₂))⟩
      _ = 2 ^ (252 * a ^ 3) * 2 / (volume (ball x₁ (↑D ^ s₁)) * volume (ball x₂ (↑D ^ s₂))) *
        ((↑(nndist y y') ^ τ / ((D ^ s₁ : ℝ≥0) : ℝ≥0∞) ^ τ)) := by
        rw [← mul_assoc, mul_comm _ 2]
        congr 1
        rw [← mul_div_assoc, mul_comm]
      _ ≤ 2 ^ (253 * a ^ 3) / (volume (ball x₁ (↑D ^ s₁)) * volume (ball x₂ (↑D ^ s₂))) *
        (↑(nndist y y') ^ τ / ((D ^ s₁ : ℝ≥0) : ℝ≥0∞) ^ τ) := by
        have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
        have : 252 * a ^ 3 + 1 ≤ 253 * a ^ 3 := by --used by the second gcongr below
          rw [Nat.succ_mul 252 (a ^ 3)]
          exact add_le_add_left (le_of_lt (Nat.one_lt_pow three_ne_zero ha)) _
        gcongr
        nth_rewrite 2 [← pow_one 2]
        rw [← pow_add]
        gcongr --uses h12
      _ = 2 ^ (253 * a ^ 3) / (volume (ball x₁ (↑D ^ s₁)) * volume (ball x₂ (↑D ^ s₂))) /
        ((D ^ s₁ : ℝ≥0) : ℝ≥0∞) ^ τ * ↑(nndist y y') ^ τ := by rw [← ENNReal.mul_comm_div]
    · left
      simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
      refine ⟨?_, Or.inl ENNReal.coe_ne_top⟩
      · left
        simp only [coe_nnreal_ennreal_nndist, edist_eq_zero, hy', not_false_eq_true]
    · left
      refine ENNReal.rpow_ne_top_of_nonneg ?hbt.h.hy0 ENNReal.coe_ne_top
      simp only [defaultτ, inv_nonneg, Nat.cast_nonneg]
    · left
      simp only [ne_eq, ENNReal.rpow_eq_zero_iff, not_or, not_and_or]
      refine ⟨?_, Or.inr <| not_lt.mpr (by simp only [defaultτ, inv_nonneg, Nat.cast_nonneg])⟩
      · left
        norm_cast
        exact ne_of_gt (defaultD_pow_pos a _)
    · left
      refine ENNReal.rpow_ne_top_of_nonneg ?ht.h.hy0 ENNReal.coe_ne_top
      simp only [defaultτ, inv_nonneg, Nat.cast_nonneg]
  calc iHolENorm (correlation s₁ s₂ x₁ x₂) x₁ (↑D ^s₁)
    _ ≤ (C2_1_3 a)^2 / ((volume (ball x₁ (D ^ s₁))) * (volume (ball x₂ (D ^ s₂)))) +
        (2^(253*a^3) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂)))) := by
        simp only [iHolENorm]
        apply add_le_add
        · simp only [iSup_le_iff, hφ', implies_true]
        simp only [ENNReal.mul_iSup, iSup_le_iff]
        intro z hz z' hz' hzz'
        convert hyy' z z' hzz'
        · rw [ENNReal.ofReal, Real.toNNReal_zpow D_nonneg, Real.toNNReal_coe_nat]
        · exact edist_nndist z z'
    _ ≤ (C_6_2_1 a : ℝ≥0∞) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂))) := by
      have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
      have h204 : 204 ≤ 253 := by omega
      have haux : ((2 ^ (102 * ((a : ℝ≥0) : ℝ) ^ 3) : ℝ≥0) : ℝ≥0∞) ^ 2 ≤ 2 ^ (253 * a ^ 3) :=
        calc ((2 ^ (102 * ((a : ℝ≥0) : ℝ) ^ 3) : ℝ≥0) : ℝ≥0∞) ^ 2
          _ = 2 ^ (204 * a ^ 3) := by
            rw [NNReal.coe_natCast, ← ENNReal.rpow_natCast]
            norm_cast
            ring
          _ ≤ 2 ^ (253 * a ^ 3) := by
            gcongr -- uses h12, h204
      simp only [C2_1_3, C_6_2_1]
      rw [← ENNReal.add_div]
      gcongr
      refine le_trans (add_le_add_right haux (2^(253 * a ^ 3))) ?_
      norm_cast
      nth_rewrite 1 [← Nat.two_mul, ← pow_one 2, ← pow_add]
      have ha1 : 1 < a ^ 3 := Nat.one_lt_pow three_ne_zero ha
      gcongr <;> omega

variable [TileStructure Q D κ S o]

open TileStructure.Forest

-- TODO: PR both versions to Mathlib
theorem MeasureTheory.exists_ne_zero_of_setIntegral_ne_zero {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → E} {U : Set α}
    (hU : ∫ (u : α) in U, f u ∂μ ≠ 0) :
    ∃ u : α, u ∈ U ∧ f u ≠ 0 := by
  contrapose! hU
  exact setIntegral_eq_zero_of_forall_eq_zero hU

theorem MeasureTheory.exists_ne_zero_of_integral_ne_zero {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → E}
    (h : ∫ (u : α), f u ∂μ ≠ 0) :
    ∃ u : α, f u ≠ 0 := by
  contrapose! h
  exact integral_eq_zero_of_ae ((eqOn_univ f 0).mp fun ⦃x⦄ a ↦ h x).eventuallyEq

-- Lemma 6.2.2
lemma range_support {p : 𝔓 X} {g : X → ℂ} {y : X} (hpy : adjointCarleson p g y ≠ 0) :
    y ∈ (ball (𝔠 p) (5 * ↑D ^𝔰 p)) := by
  simp only [adjointCarleson] at hpy
  obtain ⟨x, hxE, hx0⟩ := MeasureTheory.exists_ne_zero_of_setIntegral_ne_zero hpy
  have hxp : dist x (𝔠 p) < 4 * ↑D ^𝔰 p := -- 6.2.13
    Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) hxE)
  have hyx : dist y x ≤ (1/2) * ↑D ^𝔰 p := by -- 6.2.14
    have hK : Ks (𝔰 p) x y ≠ 0 := by
      by_contra h0
      simp only [h0, map_zero, zero_mul, ne_eq, not_true_eq_false] at hx0
    rw [dist_comm]
    convert (dist_mem_Icc_of_Ks_ne_zero hK).2 using 1
    ring
  have hpos := defaultD_pow_pos a (𝔰 p)
  have hle : (9 : ℝ) / 2 < 5 := by norm_num
  calc dist y (𝔠 p) ≤ dist y x + dist x (𝔠 p) := dist_triangle y x (𝔠 p)
    _ ≤ (1/2) * ↑D ^𝔰 p + 4 * ↑D ^ 𝔰 p := add_le_add hyx (le_of_lt hxp)
    _ < 5 * ↑D ^ 𝔰 p := by
      ring_nf
      gcongr -- uses hpos, hle.

def C_6_2_3 (a : ℕ) : ℝ≥0 := 2^(8 * a)

lemma ineq_6_2_16 {p : 𝔓 X} {x : X} (hx : x ∈ E p) : dist_(p) (Q x) (𝒬 p) < 1 :=
  subset_cball hx.2.1

-- Lemma 6.2.3
lemma uncertainty (ha : 1 ≤ a) {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂)
  (hinter : (ball (𝔠 p₁) (5 * D^𝔰 p₁) ∩ ball (𝔠 p₂) (5 * D^𝔰 p₂)).Nonempty) {x₁ x₂ : X}
  (hx₁ : x₁ ∈ E p₁) (hx₂ : x₂ ∈ E p₂) :
    1  + dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ (C_6_2_3 a) * (1 + dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) := by
  -- Inequalities 6.2.16.
  have hp₁ : dist_(p₁) (𝒬 p₁) (Q x₁) < 1 := by rw [dist_comm]; exact ineq_6_2_16 hx₁
  have hp₂ := ineq_6_2_16 hx₂
  --Needed for ineq. 6.2.17
  have hss : ↑(𝓘 p₁) ⊆ ball (𝔠 p₂) (14 * D^𝔰 p₂) := by
    have h1D : 1 ≤ (D : ℝ) := one_le_defaultD a
    have hdist : dist (𝔠 p₁) (𝔠 p₂) < 10 * ↑D ^ 𝔰 p₂ := by
      have h5 : 10 * (D : ℝ)^ 𝔰 p₂ = 5 * ↑D ^ 𝔰 p₂ + 5 * ↑D ^ 𝔰 p₂ := by ring
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
      _ < 4 * ↑D ^ 𝔰 p₁ + 10 * ↑D ^ 𝔰 p₂ := add_lt_add hx hdist
      _ ≤ 4 * ↑D ^ 𝔰 p₂ + 10 * ↑D ^ 𝔰 p₂ := by gcongr -- uses h1D, hle
      _ = 14 * ↑D ^ 𝔰 p₂ := by ring
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
          _ < 4 * ↑D ^ 𝔰 p₁ + 4 * ↑D ^ 𝔰 p₁ := add_lt_add hx h1
          _ = 8 * ↑D ^ 𝔰 p₁ := by ring
      exact cdist_mono (subset_trans ball_subset_Grid hI)
    -- 6.2.22
    _ ≤ 2 + 2^(6*a) + 2^(3*a) * dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂) := by
      apply add_le_add (le_refl _)
      have hr : 0 < (D : ℝ)^𝔰 p₁ := by exact defaultD_pow_pos a (𝔰 p₁)
      have h8 : (8 : ℝ) = 2^3 := by ring
      have h3a : (2 : ℝ) ^ (3 * a) = (defaultA a)^ 3 := by simp; ring
      convert cdist_le_iterate hr (Q x₁) (Q x₂) 3 -- uses h8, h3a
    -- 6.2.15
    _ ≤ (C_6_2_3 a) * (1 + dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) := by
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
      rw [C_6_2_3]
      conv_rhs => ring_nf
      push_cast
      rw [mul_comm 3]
      gcongr
section lemma_6_1_5

def C_6_1_5 (a : ℕ) : ℝ≥0 := 2^(255 * a^3)

-- TODO : 4 ≤ a in blueprint
lemma C_6_1_5_bound (ha : 4 ≤ a) : 2 ^ (254 * a ^ 3 + 1) * 2 ^ (11 * a) ≤ C_6_1_5 a := by
  have h255 : 255 * a ^ 3 = 254 * a ^ 3  + (a ^ 2 * a) := by
    have : a ^ 2 * a = a^3 := rfl
    rw [← one_mul (a ^ 2 * a), this, ← add_mul]
    rfl
  rw [C_6_1_5, ← pow_add]
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
    (correlation (𝔰 p') (𝔰 p) x1 x2 y))) * (g x1) * (g x2)‖₊

/-- Inequality 6.2.28 -/ -- TODO: add ‖g ↑x1‖₊ * ‖g ↑x2‖₊ in blueprint's RHS
lemma I12_le' (ha : 1 < a) (p p' : 𝔓 X) (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ) (x1 : E p') (x2 : E p) :
    I12 p p' g x1 x2 ≤ (2^(254 * a^3 + 8 * a)) *
      ((1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) * ‖g ↑x1‖₊ * ‖g ↑x2‖₊ := by
  have hD : 0 < (D : ℝ) ^ 𝔰 p := defaultD_pow_pos a (𝔰 p)
  have hD' : 0 < (D : ℝ) ^ 𝔰 p' := defaultD_pow_pos a (𝔰 p')
  have hsupp : Function.support (correlation (𝔰 p') (𝔰 p) (x1 : X) x2) ⊆
      ball x1 (D ^ 𝔰 p') := fun _ hx ↦ mem_ball_of_correlation_ne_zero hx
  have hs : 𝔰 p' ∈ Icc (- (S : ℤ)) (𝔰 p) := ⟨scale_mem_Icc.1, hle⟩
  have hnrm : hnorm (a := a) (correlation (𝔰 p') (𝔰 p) (x1 : X) x2) x1 (↑D ^ 𝔰 p') < ⊤ :=
    lt_of_le_of_lt (correlation_kernel_bound ha hs) (ENNReal.mul_lt_top
      ENNReal.coe_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.mul_pos_iff.mpr
        ⟨measure_ball_pos volume (x1 : X) hD', measure_ball_pos volume (x2 : X) hD⟩)))
  -- For compatibility with holder_van_der_corput
  have heq : (2^(254 * a^3 + 8 * a)) *
      ((1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) =
      (2^(254 * a^3 + 8 * a)) / (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) *
      ((1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) := by
    rw [div_mul_comm, mul_comm _ (2 ^ _), mul_div_assoc]
  rw [I12]
  -- TODO: fix s₁ in blueprint
  simp only [nnnorm_mul, NNReal.coe_mul]
  gcongr
  rw [← ENNReal.coe_le_coe]
  simp_rw [← sub_eq_neg_add]
  apply le_trans (holder_van_der_corput hD' hsupp hnrm)
  rw [nndist_comm, heq]
  push_cast
  gcongr
  · have hbdd := correlation_kernel_bound ha hs (x₁ := x1) (x₂ := x2)
    have : (C2_0_5 ↑a : ℝ≥0∞) * volume (ball (x1 : X) (↑D ^ 𝔰 p')) *
        hnorm (a := a) (correlation (𝔰 p') (𝔰 p) (x1 : X) ↑x2) (↑x1) (↑D ^ 𝔰 p') ≤
        ↑(C2_0_5 ↑a) * volume (ball ((x1 : X)) (↑D ^ 𝔰 p')) * (↑(C_6_2_1 a) /
          (volume (ball (x1 : X) (↑D ^ 𝔰 p')) * volume (ball (x2 : X) (↑D ^ 𝔰 p)))) := by
      gcongr
    -- simp, ring_nf, field_simp did not help.
    have heq : ↑(C2_0_5 a) * volume (ball (x1 : X) (↑D ^ 𝔰 p')) *
      (↑(C_6_2_1 a) / (volume (ball (x1 : X) (↑D ^ 𝔰 p')) * volume (ball (x2 : X) (↑D ^ 𝔰 p)))) =
      ↑(C2_0_5 a) * (↑(C_6_2_1 a) / volume (ball (x2 : X) (↑D ^ 𝔰 p))) := by
      simp only [mul_assoc]
      congr 1
      rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr (measure_ball_ne_top _ _))
        (Or.inl (measure_ball_ne_top _ _)), ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel
        (ne_of_gt (measure_ball_pos volume _ hD')) (measure_ball_ne_top _ _), one_mul,
        ENNReal.div_eq_inv_mul]
    apply le_trans this
    rw [heq, ENNReal.coe_div (ne_of_gt (measure_ball_pos_nnreal _ _ hD)), measureNNReal_def,
      ENNReal.coe_toNNReal (measure_ball_ne_top _ _), mul_div]
    apply ENNReal.div_le_div _ (le_refl _)
    simp only [C2_0_5, C_6_2_1, ENNReal.coe_pow, ENNReal.coe_ofNat]
    rw [pow_add, mul_comm]
  · norm_cast
    apply le_of_eq
    suffices 1 + @edist (WithFunctionDistance (x1 : X) (D ^ 𝔰 p')) _ (Q ↑x1) (Q ↑x2) =
        1 + nndist_{(x1 : X), ((D : ℝ) ^ 𝔰 p')} (Q x1) (Q x2) by
      rw [this, ENNReal.coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one le_self_add)),
        ENNReal.coe_add, ENNReal.coe_one]
    congr
    rw [coe_nnreal_ennreal_nndist]

lemma exp_ineq (ha : 1 < a) : 0 ≤ 1 + ((8 * a  : ℕ) : ℝ) * -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ := by
  have hpos : 0 < (a : ℝ) ^ 2 * 2 + a ^ 3 := by norm_cast; nlinarith
  ring_nf
  rw [Nat.cast_mul, Nat.cast_ofNat, sub_nonneg, ← div_eq_mul_inv, div_le_one hpos]
  norm_cast
  nlinarith

/-- Inequality 6.2.29. -/ -- TODO: add ‖g ↑x1‖₊ * ‖g ↑x2‖₊ in blueprint's RHS
lemma I12_le (ha : 1 < a) (p p' : 𝔓 X) (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty)
    (x1 : E p') (x2 : E p) :
    I12 p p' g x1 x2 ≤
    (2^(254 * a^3 + 8 * a + 1) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹))) /
      (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) * ‖g ↑x1‖₊ * ‖g ↑x2‖₊ := by
  apply le_trans (NNReal.coe_le_coe.mpr (I12_le' ha p p' hle g x1 x2))
  simp only [Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, NNReal.coe_rpow, NNReal.coe_add, NNReal.coe_one, coe_nndist, coe_nnnorm]
  gcongr ?_ *  ‖g ↑x1‖ * ‖g ↑x2‖
  rw [pow_add 2 _ 1, pow_one, mul_comm _ 2, mul_assoc, mul_comm 2 (_ * _), mul_assoc]
  gcongr
  -- Now we need to use Lemma 6.2.3. to conclude this inequality.
  have h623 := uncertainty (le_of_lt ha) hle hinter x1.2 x2.2
  rw [C_6_2_3, NNReal.coe_pow, NNReal.coe_ofNat] at h623
  have hneg : -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ < 0 :=
    neg_neg_iff_pos.mpr (inv_pos.mpr (by norm_cast; nlinarith))
  have hpos : 0 < ((2 : ℝ) ^ (8 * a)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) :=
    Real.rpow_pos_of_pos (pow_pos zero_lt_two _) _
  have hexp : 0 ≤ 1 + ((8 * a  : ℕ) : ℝ) * -(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹ := exp_ineq ha
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
    volume.nnreal (coeGrid (𝓘 p)) ≤ 2 ^ (3*a) * (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := by
  -- Inequality 6.2.30
  have hdist : dist (𝔠 p) (x2 : X) < 4 * ↑D ^𝔰 p := --TODO: < in blueprint
    dist_comm (𝔠 p) (x2 : X) ▸ Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) x2.prop)
  -- Inclusion 6.2.31
  have hsub : (coeGrid (𝓘 p)) ⊆ (ball (x2 : X) (8 * ↑D ^𝔰 p)) := by
    apply le_trans Grid_subset_ball
    intro x hx
    calc dist x x2
      _ ≤ dist x (𝔠 p) + dist (𝔠 p) x2 := dist_triangle _ _ _
      _ < 4 * ↑D ^ 𝔰 p + 4 * ↑D ^ 𝔰 p := add_lt_add hx hdist
      _ = 8 * ↑D ^ 𝔰 p := by ring
  have h : volume.nnreal (coeGrid (𝓘 p)) ≤ volume.nnreal (ball (x2 : X) (8 * ↑D ^𝔰 p)) :=
    measureNNReal_mono hsub
  have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
  apply le_trans h
  simp only [NNReal.coe_mul, ← NNReal.coe_le_coe, measureNNReal_toReal, h8]
  convert DoublingMeasure.volume_ball_two_le_same_repeat (x2 : X) (↑D ^𝔰 p) 3 using 1
  rw [mul_comm 3, pow_mul]
  simp [NNReal.coe_pow, NNReal.coe_ofNat, Nat.cast_pow, Nat.cast_ofNat]

-- Bound 6.2.29 using 6.2.32 and `4 ≤ a`.
lemma bound_6_2_29 (ha : 4 ≤ a) (p p' : 𝔓 X) (x2 : E p) : 2 ^ (254 * a^3 + 8 * a + 1) *
      ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) ≤ (C_6_1_5 a) *
          ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume.nnreal (coeGrid (𝓘 p))) := by
  have h1 : 0 < volume.nnreal (𝓘 p : Set X) := volumeNNReal_coeGrid_pos (defaultD_pos' a)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h4 : 2 ^ (254 * a ^ 3 + 1) * 2 ^ (11 * a) ≤ C_6_1_5 a := C_6_1_5_bound ha
  -- Inequality 6.2.32
  have hvol : ∀ (x2 : E p), volume.nnreal (coeGrid (𝓘 p)) ≤
      2 ^ (3*a) * (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := volume_nnreal_coeGrid_le p
  calc 2 ^ (254 * a^3 + 8 * a + 1) *
    ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
      (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p)))
    _ = 2^ (254 * a^3 + 1) * 2 ^ (11 * a) * 2 ^ (- (3 : ℤ) * a) *
        ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := by
      simp only [← zpow_natCast, ← zpow_add₀ h2]
      congr
      push_cast
      ring
    _ = 2 ^ (254 * a^3 + 1) * 2 ^ (11 * a) *
        ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (2 ^ (3 * a) * volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := by
      simp only [mul_div_assoc, mul_assoc, neg_mul, zpow_neg]
      rw [inv_mul_eq_div, div_div, mul_comm (2 ^ (3 * a))]
      simp only [mul_div]
      rfl
    _ ≤ (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (2 ^ (3 * a) * volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := by gcongr; exact h4
    _ ≤ (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume.nnreal (coeGrid (𝓘 p))) := by gcongr; exact hvol x2

-- TODO: PR to Mathlib
omit [MetricSpace X] in
lemma _root_.Set.indicator_one_le_one (x : X) : G.indicator (1 : X → ℝ) x ≤ 1 := by
  classical
  exact le_trans (ite_le_sup _ _ _) (by simp)

omit [TileStructure Q D κ S o] in
lemma nnnorm_eq_zero_of_not_mem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4))) :
    (‖g x‖₊ : ℝ) = 0 := by
  simp only [coe_nnnorm]
  apply le_antisymm _ (norm_nonneg _)
  apply le_trans (hg1 _)
  rw [Set.indicator_of_not_mem (Set.not_mem_subset ProofData.G_subset
    (Set.not_mem_subset ball_subset_closedBall hx))]

omit [TileStructure Q D κ S o] in
lemma eq_zero_of_not_mem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ (closedBall (cancelPt X) (defaultD a ^ defaultS X / 4))) :
    g x = 0 := by
  simpa [coe_nnnorm, norm_eq_zero] using nnnorm_eq_zero_of_not_mem_closedBall hg1 hx

omit [TileStructure Q D κ S o] in
lemma boundedCompactSupport_g {g : X → ℂ} (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport g :=
  ⟨isBounded_range_iff_forall_norm_le.mpr ⟨1, fun x ↦ le_trans (hg1 x) (indicator_one_le_one x)⟩,
    hg.stronglyMeasurable,
    exists_compact_iff_hasCompactSupport.mp ⟨(closedBall o (D ^ S / 4)),
      ⟨isCompact_closedBall o ((D : ℝ) ^ S / 4), fun _ hx ↦ eq_zero_of_not_mem_closedBall hg1 hx⟩⟩⟩

lemma boundedCompactSupport_star_Ks_mul_g (p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport (fun (x : X × X) ↦ ((starRingEnd ℂ) (Ks (𝔰 p') x.1 x.2) *  g x.1)) := by
  apply BoundedCompactSupport.mul_bdd_left' (boundedCompactSupport_g hg hg1) continuous_fst
    measurable_fst ?_ ?_ ?_
  · apply Measurable.stronglyMeasurable
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
        _ ≤ (↑D ^ 𝔰 p' / 2) + C + (↑D ^ 𝔰 p' / 2) := by
          gcongr
          · rw [dist_comm]
            have hx' : x ∈ tsupport fun x ↦ (Ks (𝔰 p') x.1 x.2) := by
              convert hx.2 using 1
              simp only [tsupport]
              apply congr_arg
              ext z
              simp only [Function.mem_support, ne_eq, map_eq_zero]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hx').2
          · exact hC hx.1 hy.1
          · have hy' : y ∈ tsupport fun x ↦ (Ks (𝔰 p') x.1 x.2) := by
              convert hy.2 using 1
              simp only [tsupport]
              apply congr_arg
              ext z
              simp only [Function.mem_support, ne_eq, map_eq_zero]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hy').2
        _ = ↑D ^ 𝔰 p' + C := by ring
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
  refine BoundedCompactSupport.mul_bdd_left' ?_ continuous_fst measurable_fst ?_ ?_ ?_
  · exact BoundedCompactSupport.comp_left (boundedCompactSupport_g hg hg1) hg (by simp)
      (by fun_prop) (by simp)
  · apply Measurable.stronglyMeasurable
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
        _ ≤ (↑D ^ 𝔰 p / 2) + C + (↑D ^ 𝔰 p / 2) := by
          gcongr
          · rw [dist_comm]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hx.2).2
          · exact hC hx.1 hy.1
          · exact (dist_mem_Icc_of_mem_tsupport_Ks hy.2).2
        _ = ↑D ^ 𝔰 p + C := by ring
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
    · rw [isBounded_range_iff_forall_norm_le]
      use 1
      intro x
      rw [← ofReal_sub, ← ofReal_neg, ← ofReal_add]
      simp only [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
    · apply Measurable.stronglyMeasurable
      fun_prop
  constructor
  · -- IsBounded
    obtain ⟨B, hB⟩ := isBounded_range_iff_forall_norm_le.1
      (boundedCompactSupport_star_Ks_mul_g p' hg hg1).isBounded
    obtain ⟨C, hC⟩ := isBounded_range_iff_forall_norm_le.1
      (boundedCompactSupport_Ks_mul_star_g p hg hg1).isBounded
    rw [isBounded_range_iff_forall_norm_le]
    use (max 0 B) * (max 0 C)
    intro z
    rw [norm_mul]
    gcongr
    · exact le_max_of_le_right (hB ⟨z.2.1, z.1⟩)
    · exact le_max_of_le_right (hC ⟨z.2.2, z.1⟩)
  · -- StronglyMeasurable
    apply Measurable.stronglyMeasurable
    fun_prop
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
      · exact Or.inr (eq_zero_of_not_mem_closedBall hg1 hx2)
    · exact Or.inl (Or.inr (eq_zero_of_not_mem_closedBall hg1 hx))
    · exact Or.inr (Or.inr (eq_zero_of_not_mem_closedBall hg1 hx))

-- TODO: delete after updating
lemma Complex.abs_re_eq_norm {z : ℂ} : |z.re| = ‖z‖ ↔ z.im = 0 := sorry

lemma boundedCompactSupport_bound (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport (fun (x : X × X) ↦ (C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^
      (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) / (volume.nnreal (𝓘 p : Set X)) * ‖g x.1‖₊ * ‖g x.2‖₊) := by
  constructor
  · -- Bounded
    rw [isBounded_iff_forall_norm_le]
    use ↑(C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^
      (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) / (volume.nnreal (𝓘 p : Set X))
    rintro r ⟨x, rfl⟩
    simp only
    calc ‖↑(C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
          (volume.nnreal (𝓘 p : Set X)) * ↑‖g x.1‖₊ * ↑‖g x.2‖₊‖
      _ = ↑(C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
          (volume.nnreal (𝓘 p : Set X)) * ↑‖g x.1‖₊ * ↑‖g x.2‖₊  := by
        simp only [norm_mul, norm_mul, Real.norm_eq_abs, NNReal.abs_eq, coe_nnnorm,
          _root_.abs_of_nonneg (norm_nonneg _), _root_.abs_of_nonneg
          (div_nonneg (mul_nonneg NNReal.zero_le_coe
            (Real.rpow_nonneg ( add_nonneg zero_le_one dist_nonneg) _)) NNReal.zero_le_coe)]
      _ ≤ ↑(C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
          (volume.nnreal (𝓘 p : Set X)) * 1 * 1 := by
        gcongr <;>
        exact le_trans (hg1 _) (indicator_one_le_one _)
      _ = ↑(C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) /
          (volume.nnreal (𝓘 p : Set X)) := by
        simp only [mul_one]
  · -- Strongly measurable
    exact Measurable.stronglyMeasurable (by fun_prop)
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
    · rw [nnnorm_eq_zero_of_not_mem_closedBall hg1 hx, zero_mul]
    · rw [nnnorm_eq_zero_of_not_mem_closedBall hg1 hx, mul_zero]

lemma integrableOn_bound (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    IntegrableOn (fun x ↦ ↑(C_6_1_5 a) * (1 + dist_(p') (𝒬 p') (𝒬 p)) ^
      (-(2 * (a : ℝ) ^ 2 + ↑a ^ 3)⁻¹) / (volume.nnreal (𝓘 p : Set X)) * ‖g x.1‖₊ * ‖g x.2‖₊)
      (E p' ×ˢ E p) volume :=
  (boundedCompactSupport_bound p p' hg hg1).integrable.integrableOn

-- NOTE: `unfold correlation` is still needed after adding the measurability lemma.
lemma stronglyMeasurable_I12 (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun (x : X × X) ↦ (I12 p p' g x.1 x.2 : ℝ)) := by
  simp only [I12, nnnorm_mul, NNReal.coe_mul, coe_nnnorm, mul_assoc]
  exact (Measurable.stronglyMeasurable
      (by unfold correlation; fun_prop)).integral_prod_left.norm.mul
    (((hg.comp measurable_fst).norm).mul (hg.comp measurable_snd).norm).stronglyMeasurable

lemma stronglyMeasurable_I12' (p p' : 𝔓 X) {g : X → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun (x : X × X) ↦ ((I12 p p' g x.1 x.2 : ℝ) : ℂ)) :=
  (Complex.measurable_ofReal.comp (stronglyMeasurable_I12 p p' hg).measurable).stronglyMeasurable

lemma integrableOn_I12 (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    IntegrableOn (fun x ↦ (I12 p p' g x.1 x.2 : ℝ)) (E p' ×ˢ E p) volume := by
  classical
  set f : X × X → ℝ := fun x ↦ if x ∈ E p' ×ˢ E p then (I12 p p' g x.1 x.2 : ℝ) else 0
  have hf : IntegrableOn f (E p' ×ˢ E p) volume := by
    apply Integrable.integrableOn
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.mono (boundedCompactSupport_bound p p' hg hg1)
    · exact StronglyMeasurable.ite (measurableSet_E.prod measurableSet_E)
        (stronglyMeasurable_I12 p p' hg) stronglyMeasurable_const
    · intro z
      by_cases hz : z ∈ (E p') ×ˢ (E p)
      · have ha1 : 1 < a := by omega
        simp only [f, if_pos hz, Real.norm_eq_abs, NNReal.abs_eq]
        apply le_trans (I12_le ha1 p p' hle g hinter ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩)
        gcongr ?_ *  ‖g ↑_‖ * ‖g ↑_‖
        exact (bound_6_2_29 ha p p' ⟨z.2, hz.2⟩)
      · simp only [f, if_neg hz, norm_zero]
        positivity
  exact MeasureTheory.IntegrableOn.congr_fun hf (fun _ hx ↦ by simp only [f, if_pos hx])
    (measurableSet_E.prod measurableSet_E)

/- TODO: it should be way easier to deduce this from `integrableOn_I12`, right? -/
lemma integrableOn_I12' (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    IntegrableOn (fun x ↦ ((I12 p p' g x.1 x.2 : ℝ) : ℂ)) (E p' ×ˢ E p) volume := by
  classical
  set f : X × X → ℂ := fun x ↦ if x ∈ E p' ×ˢ E p then ((I12 p p' g x.1 x.2 : ℝ) : ℂ) else 0
  have hf : IntegrableOn f (E p' ×ˢ E p) volume := by
    apply Integrable.integrableOn
    apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.mono (boundedCompactSupport_bound p p' hg hg1)
    · exact StronglyMeasurable.ite (measurableSet_E.prod measurableSet_E)
        (stronglyMeasurable_I12' p p' hg) stronglyMeasurable_const
    · intro z
      by_cases hz : z ∈ (E p') ×ˢ (E p)
      · have ha1 : 1 < a := by omega
        simp only [f, if_pos hz, Real.norm_eq_abs, NNReal.abs_eq]
        simp only [Complex.norm_real, NNReal.norm_eq]
        apply le_trans (I12_le ha1 p p' hle g hinter ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩)
        gcongr ?_ *  ‖g ↑_‖ * ‖g ↑_‖
        exact (bound_6_2_29 ha p p' ⟨z.2, hz.2⟩)
      · simp only [f, if_neg hz, norm_zero]
        positivity
  exact MeasureTheory.IntegrableOn.congr_fun hf (fun _ hx ↦ by simp only [f, if_pos hx])
    (measurableSet_E.prod measurableSet_E)

lemma bound_6_2_26_aux (p p' : 𝔓 X)  (g : X → ℂ) :
    let f := fun (x, z1, z2) ↦ (starRingEnd ℂ) (Ks (𝔰 p') z1 x) *
      exp (I * (((Q z1) z1) - ((Q z1) x))) * g z1 * (Ks (𝔰 p) z2 x *
        exp (I * (-((Q z2) z2) + ((Q z2) x))) * (starRingEnd ℂ) (g z2))
    ∫ (x : X × X) in E p' ×ˢ E p, ‖(∫ (y : X) in univ, f (x, y).swap)‖ ∂volume.prod volume =
      ∫ (z : X × X) in E p' ×ˢ E p, (I12 p p' g z.1 z.2 : ℝ) := by
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
  have hx1 : abs (exp (I * ↑((Q x.1) x.1))) = 1 := by
    simp only [abs_exp, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
      mul_zero, sub_self, Real.exp_zero]
  have hx2 : abs (exp (I * -↑((Q x.2) x.2))) = 1 := by
    simp only [mul_neg, abs_exp, neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im,
      ofReal_im, mul_zero, sub_self, neg_zero, Real.exp_zero]
  simp only [I12, Measure.restrict_univ, Prod.swap_prod_mk, norm_eq_abs,
    nnnorm_mul, NNReal.coe_mul, coe_nnnorm, ofReal_mul, norm_mul,
    abs_ofReal, abs_abs]
  simp_rw [heq, ← smul_eq_mul (a' := _ * g x.1 * (starRingEnd ℂ) (g x.2)),
    integral_smul_const, smul_eq_mul, AbsoluteValue.map_mul, abs_conj, ← mul_assoc]
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
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      ‖ ∫ (z : X × X) in E p' ×ˢ E p, (I12 p p' g z.fst z.snd : ℂ) ‖₊ := by
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
    MeasureTheory.setIntegral_prod _ hf', ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  calc ‖∫ (x : X × X) in E p' ×ˢ E p, (∫ (y : X) in univ, f (x, y).swap) ∂volume.prod volume‖
    _ ≤ ∫ (x : X × X) in E p' ×ˢ E p, ‖(∫ (y : X) in univ, f (x, y).swap)‖ ∂volume.prod volume :=
      norm_integral_le_integral_norm fun a_1 ↦ ∫ (y : X) in univ, f (a_1, y).swap
    _ = ∫ (z : X × X) in E p' ×ˢ E p, (I12 p p' g z.1 z.2 : ℝ) := bound_6_2_26_aux p p' g
    _ = ‖∫ (z : X × X) in E p' ×ˢ E p, ((I12 p p' g z.1 z.2 : ℝ) : ℂ)‖ := by
      have him : (∫ (z : X × X) in E p' ×ˢ E p, ((I12 p p' g z.1 z.2 : ℝ) : ℂ)).im = 0 := by
        rw [← RCLike.im_to_complex, ← integral_im (integrableOn_I12' ha hle hg hg1 hinter)]
        simp [RCLike.im_to_complex, ofReal_im, integral_zero]
      conv_rhs => rw [← setIntegral_re_add_im (integrableOn_I12' ha hle hg hg1 hinter)]
      simp only [norm_real, NNReal.norm_eq, RCLike.re_to_complex,ofReal_re, coe_algebraMap,
        RCLike.im_to_complex, ofReal_im, integral_zero, ofReal_zero, RCLike.I_to_complex,
        zero_mul, add_zero]
      rw [Real.norm_of_nonneg (integral_nonneg (fun x ↦ by simp))]

-- We assume 6.2.23.
lemma correlation_le_of_nonempty_inter (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume.nnreal (coeGrid (𝓘 p))) * (∫ y in E p', ‖ g y‖) * (∫ y in E p, ‖ g y‖) := by
  -- Definition 6.2.27
  set I12 := I12 p p' g
  -- Inequality 6.2.29
  have hI12 : ∀ (x1 : E p') (x2 : E p), I12 x1 x2 ≤
      (2^(254 * a^3 + 8 * a + 1) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹))) /
      (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) * ‖g ↑x1‖₊ * ‖g ↑x2‖₊ :=
    I12_le (by omega) p p' hle g hinter
  -- Bound 6.2.29 using 6.2.32 and `4 ≤ a`.
  have hle' : ∀ (x2 : E p), 2 ^ (254 * a^3 + 8 * a + 1) *
      ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) ≤ (C_6_1_5 a) *
          ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume.nnreal (coeGrid (𝓘 p))) := bound_6_2_29 ha p p'
  -- Estimate 6.2.24 -- 6.2.25 by 6.2.26
  have hbdd : ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      ‖ ∫ (z : X × X) in E p' ×ˢ E p, (I12 z.fst z.snd : ℂ) ‖₊ :=
    bound_6_2_26 ha hle hg hg1 hinter
  rw [← NNReal.coe_le_coe] at hbdd
  apply le_trans hbdd
  have hcoe : ∫ (z : X × X) in E p' ×ˢ E p, (I12 z.fst z.snd : ℂ) =
    ∫ (z : X × X) in E p' ×ˢ E p, (I12 z.fst z.snd : ℝ) := by
    rw [← setIntegral_re_add_im]
    simp only [RCLike.re_to_complex, ofReal_re, coe_algebraMap, RCLike.im_to_complex, ofReal_im,
      integral_zero, ofReal_zero, RCLike.I_to_complex, zero_mul, add_zero]
    · have hre := integrableOn_I12 ha hle hg hg1 hinter
      rw [IntegrableOn] at hre ⊢
      exact MeasureTheory.Integrable.re_im_iff.mp
        ⟨hre, by simp only [RCLike.im_to_complex, ofReal_im, integrable_zero]⟩
  simp only [hcoe, nnnorm_real, coe_nnnorm, Real.norm_eq_abs, norm_eq_abs, ge_iff_le]
  have h : |∫ (z : X × X) in E p' ×ˢ E p, (I12 z.1 z.2 : ℝ)| ≤
      |∫ (z : X × X) in E p' ×ˢ E p, ((C_6_1_5 a) *
          ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
            (volume.nnreal (coeGrid (𝓘 p)))) * ‖g z.1‖₊ * ‖g z.2‖₊| := by
    apply abs_le_abs_of_nonneg (setIntegral_nonneg (measurableSet_E.prod measurableSet_E)
        (fun _ _ ↦ NNReal.zero_le_coe))
    apply setIntegral_mono_on (integrableOn_I12 ha hle hg hg1 hinter)
      (integrableOn_bound p p' hg hg1) (measurableSet_E.prod measurableSet_E)
    intro z hz
    apply le_trans (hI12 ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩)
    gcongr ?_ *  ‖g ↑_‖ * ‖g ↑_‖
    exact (hle' ⟨z.2, hz.2⟩)
  have hprod : |∫ (a : X × X) in E p' ×ˢ E p, abs (g a.1) * abs (g a.2)| =
      ((∫ (y : X) in E p', abs (g y)) * ∫ (y : X) in E p, abs (g y)) := by
    rw [← setIntegral_prod_mul, _root_.abs_of_nonneg (setIntegral_nonneg
      (measurableSet_E.prod measurableSet_E) (fun _ _ ↦
        mul_nonneg (AbsoluteValue.nonneg _ _) (AbsoluteValue.nonneg _ _)))]; rfl
  apply le_trans h
  simp only [coe_nnnorm, norm_eq_abs, I12, mul_assoc]
  rw [integral_mul_left]
  simp only [abs_mul, abs_div, NNReal.abs_eq]
  rw [_root_.abs_of_nonneg (Real.rpow_nonneg (add_nonneg zero_le_one dist_nonneg) _), hprod]

-- If 6.2.23 does not hold, then the LHS equals zero and the result follows trivially.
lemma correlation_le_of_empty_inter {p p' : 𝔓 X} {g : X → ℂ}
    (hinter : ¬ (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume.nnreal (coeGrid (𝓘 p))) * (∫ y in E p', ‖ g y‖) * (∫ y in E p, ‖ g y‖) := by
    calc (‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ : ℝ)
      _ = 0 := by
        simp only [inter_nonempty, not_exists, not_and_or] at hinter
        simp only [defaultA, coe_nnnorm, Complex.norm_eq_abs, map_eq_zero]
        apply MeasureTheory.integral_eq_zero_of_ae (Eq.eventuallyEq _)
        ext y
        rcases hinter y with hp'y | hpy
        · have hp'0 : adjointCarleson p' g y = 0 := by
            by_contra hy
            exact hp'y (range_support hy)
          simp only [hp'0, zero_mul, Pi.zero_apply]
        · have hp'0 : adjointCarleson p g y = 0 := by
            by_contra hy
            exact hpy (range_support hy)
          simp only [hp'0, map_zero, mul_zero, Pi.zero_apply]
      _ ≤ (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
          (volume.nnreal (coeGrid (𝓘 p))) * (∫ y in E p', ‖ g y‖) * ∫ y in E p, ‖ g y‖ := by
        positivity

lemma correlation_le (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(2 * a^2 + a^3 : ℝ)⁻¹)) /
        (volume.nnreal (coeGrid (𝓘 p))) * (∫ y in E p', ‖ g y‖) * (∫ y in E p, ‖ g y‖) := by
  by_cases hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty
  · exact correlation_le_of_nonempty_inter ha hle hg hg1 hinter
  · exact correlation_le_of_empty_inter hinter
