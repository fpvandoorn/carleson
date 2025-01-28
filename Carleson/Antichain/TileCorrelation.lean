import Carleson.ForestOperator.AlmostOrthogonality
import Carleson.ToMathlib.HardyLittlewood
import Carleson.Psi
import Carleson.TileStructure

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ComplexConjugate ENNReal NNReal ShortVariables

open MeasureTheory Metric Set

namespace Tile

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X]
  [ProofData a q K σ₁ σ₂ F G]

-- Def 6.2.1 (Lemma 6.2.1)
def correlation (s₁ s₂ : ℤ) (x₁ x₂ y : X) : ℂ := (conj (Ks s₁ x₁ y)) * (Ks s₂ x₂ y)

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

--TODO: PR
lemma ENNReal.mul_div_mul_comm {a b c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inr hd) (Or.inl hc)]
  ring

lemma aux_6_2_3 (s₁ s₂ : ℤ) (x₁ x₂ y y' : X)  :
  (‖Ks s₂ x₂ y‖₊ : ℝ≥0∞) * (‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖₊ : ℝ≥0∞) ≤
  ↑(C2_1_3 ↑a) / volume (ball x₂ (↑D ^ s₂)) *
    (↑(D2_1_3 ↑a) / volume (ball x₁ (↑D ^ s₁)) * (↑(nndist y y') ^ τ / ↑((D : ℝ≥0) ^ s₁) ^ τ)) := by
  have hτ : 0 ≤ τ := by simp only [defaultτ, inv_nonneg, Nat.cast_nonneg]
  apply mul_le_mul nnnorm_Ks_le _ (zero_le _) (zero_le _)
  convert nnnorm_Ks_sub_Ks_le
  rw [← ENNReal.div_rpow_of_nonneg _ _ hτ]
  simp only [defaultτ]
  congr
  rw [ENNReal.coe_zpow (by simp)]
  rfl

-- Eq. 6.2.3 (Lemma 6.2.1)
lemma correlation_kernel_bound (ha : 1 < a) {s₁ s₂ : ℤ} (hs₁ : s₁ ∈ Icc (- (S : ℤ)) s₂)
   {x₁ x₂ : X} :
    hnorm (a := a) (correlation s₁ s₂ x₁ x₂) x₁ (↑D ^s₁) ≤
      (C_6_2_1 a : ℝ≥0∞) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂))) := by
  -- 6.2.4
  have hφ' : ∀ y : X, ‖correlation s₁ s₂ x₁ x₂ y‖₊ ≤
      (C2_1_3 a)^2 / ((volume (ball x₁ (D ^ s₁))) * (volume (ball x₂ (D ^ s₂)))) := by
    intro y
    simp only [correlation, nnnorm_mul, RCLike.nnnorm_conj, ENNReal.coe_mul, pow_two,
      ENNReal.mul_div_mul_comm (measure_ball_ne_top _ _) (measure_ball_ne_top _ _)]
    exact mul_le_mul nnnorm_Ks_le nnnorm_Ks_le (zero_le _) (zero_le _)

  -- 6.2.6 + 6.2.7
  have hsimp :  ∀ (y y' : X),
      (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖₊ : ℝ≥0∞) ≤
        ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y‖₊ +
          ‖Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖₊ := by
    intro y y'
    calc (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖₊ : ℝ≥0∞)
      _ = ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y +
          (conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * (Ks s₂ x₂ y'))‖₊ := by
        simp only [correlation, sub_add_sub_cancel]
      _ ≤ ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y ‖₊ +
          ‖conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * (Ks s₂ x₂ y')‖₊ := by
            norm_cast
            exact nnnorm_add_le _ _
      _ = ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y‖₊ +
          ‖Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖₊ := by
          norm_cast
          simp only [← sub_mul, ← mul_sub, nnnorm_mul, RCLike.nnnorm_conj, ← map_sub]
  -- 6.2.5
  have hyy' : ∀ (y y' : X) (hy' : y ≠ y'), (((D  ^ s₁ : ℝ≥0)) ^ τ)  *
    (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖₊ / (nndist y y')^τ) ≤
      (2^(253*a^3) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂)))) := by
    intros y y' hy'
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le, ENNReal.div_le_iff_le_mul]
    calc (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖₊ : ℝ≥0∞)
      _ ≤ ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y‖₊ +
          ‖Ks s₁ x₁ y'‖₊ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖₊ := hsimp y y' -- 6.2.6 + 6.2.7
      _ ≤ 2 ^ (252 * a ^ 3) / (volume (ball x₁ (↑D ^ s₁)) * volume (ball x₂ (↑D ^ s₂))) *
        (↑(nndist y y') ^ τ / ((D ^ s₁ : ℝ≥0) : ℝ≥0∞) ^ τ +
          ↑(nndist y y') ^ τ / ((D ^ s₂ : ℝ≥0) : ℝ≥0∞) ^ τ) := by
        have h2 : (2 : ℝ≥0∞) ^ (252 * a ^ 3) = C2_1_3 a * D2_1_3 a := by
          simp only [C2_1_3, NNReal.coe_natCast, D2_1_3]
          norm_cast
          ring
        rw [mul_comm, mul_add, h2, mul_comm (volume _)]
        simp only [ENNReal.mul_div_mul_comm (measure_ball_ne_top _ _) (measure_ball_ne_top _ _),
          mul_assoc]
        apply add_le_add (aux_6_2_3 s₁ s₂ x₁ x₂ y y')
        rw [← neg_sub, nnnorm_neg]
        convert aux_6_2_3 s₂ s₁ x₂ x₁ y' y using 1
        simp only [← mul_assoc, ← ENNReal.mul_div_mul_comm (measure_ball_ne_top _ _)
          (measure_ball_ne_top _ _)]
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
          false_or, false_and, true_and, ENNReal.pow_eq_top_iff, ENNReal.two_ne_top, or_false,
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
  calc hnorm (a := a) (correlation s₁ s₂ x₁ x₂) x₁ (↑D ^s₁)
    _ ≤ (C2_1_3 a)^2 / ((volume (ball x₁ (D ^ s₁))) * (volume (ball x₂ (D ^ s₂)))) +
        (2^(253*a^3) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂)))) := by
        simp only [hnorm]
        refine iSup₂_le ?h
        intro y _
        apply add_le_add (hφ' y)
        simp only [ENNReal.mul_iSup, iSup_le_iff]
        exact fun z _ z' _ hzz' ↦ hyy' z z' hzz'
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

-- TODO: PR both versions
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

--TODO: move to correct file
lemma one_le_defaultD : 1 ≤ (D : ℝ) := by
  rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_zero 2]
  exact pow_le_pow_right₀ (one_le_two) (by omega)

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
    have h1D : 1 ≤ (D : ℝ) := one_le_defaultD
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
            exact Nat.pow_le_pow_of_le_right zero_lt_two (by omega)
          _ = 2 * (2 : ℝ)^ (6 * a) := by ring
          _ ≤ 2 ^ (a * 8) := by
            nth_rewrite 1 [← pow_one 2, ← pow_add]
            norm_cast
            exact Nat.pow_le_pow_of_le_right zero_lt_two (by omega)
      have h38 : 3 ≤ 8 := by omega
      have h12 : (1 : ℝ) ≤ 2 := by linarith
      rw [C_6_2_3]
      conv_rhs => ring_nf
      push_cast
      rw [mul_comm 3]
      gcongr

def C_6_1_5 (a : ℕ) : ℝ≥0 := 2^(255 * a^3)

open GridStructure

--TODO: replace p1, p2 in blueprint proof by p, p'
-- Lemma 6.1.5 (part I)
lemma correlation_le {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(1 : ℝ)/(2*a^2 + a^3))) /
        (volume.nnreal (coeGrid (𝓘 p))) * (∫ y in E p', ‖ g y‖) * (∫ y in E p, ‖ g y‖) := by
  by_cases hinter : (ball (𝔠 p') (5 * D^𝔰 p') ∩ ball (𝔠 p) (5 * D^𝔰 p)).Nonempty
  · -- We assume 6.2.23.
    -- Express (LHS of 6.1.43) = 6.2.24 -- 6.2.25.
    have haux : ∀ (y : X), (starRingEnd ℂ) (∫ (y1 : X) in E p, (starRingEnd ℂ) (Ks (𝔰 p) y1 y) *
        Complex.exp (Complex.I * (↑((Q y1) y1) - ↑((Q y1) y))) * g y1) =
        (∫ (y1 : X) in E p, (Ks (𝔰 p) y1 y) *
        Complex.exp (Complex.I * (- ((Q y1) y1) + ↑((Q y1) y))) * (starRingEnd ℂ) (g y1)) := by
      intro y
      simp only [← integral_conj, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      congr
      ext x
      rw [← Complex.exp_conj]
      congr
      simp only [map_mul, Complex.conj_I, map_sub, Complex.conj_ofReal]
      ring
    -- Definition 6.2.27
    set I12 := fun (x1 : X) (x2 : X) ↦
      ‖(∫ y, (Complex.exp (Complex.I * (- ((Q x1) y) + ↑((Q x2) y))) *
        (correlation (𝔰 p') (𝔰 p) x1 x2 y))) * (g x1) * (g x2)‖₊

    -- Inequality 6.2.28
    have hI12' : ∀ (x1 : E p') (x2 : E p), I12 x1 x2 ≤
      (2^(254 * a^3 + 8 * a)) * ((1 + dist_(p') (Q x1) (Q x2))^(-(1 : ℝ)/(2*a^2 + a^3))) /
        (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := sorry

    -- Inequality 6.2.29
    have hI12 : ∀ (x1 : E p') (x2 : E p), I12 x1 x2 ≤
      (2^(254 * a^3 + 8 * a + 1)) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(1 : ℝ)/(2*a^2 + a^3))) /
        (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := sorry

    -- Inequality 6.2.32
    have hvol : ∀ (x2 : E p), volume.nnreal (coeGrid (𝓘 p)) ≤
        (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) := by
      intro x2
      -- Inequality 6.2.30
      have hdist : dist (x2 : X) (𝔠 p) ≤ 4 * ↑D ^𝔰 p := sorry
      -- Inclusion 6.2.31
      have hsub : (coeGrid (𝓘 p)) ⊆ (ball (x2 : X) (8 * ↑D ^𝔰 p)) := sorry
      sorry
    -- Bound 6.2.29 using 6.2.32.
    have hle : ∀ (x2 : E p), (2^(254 * a^3 + 8 * a + 1)) *
      ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(1 : ℝ)/(2*a^2 + a^3))) /
        (volume.nnreal (ball (x2 : X) (↑D ^𝔰 p))) ≤ (C_6_1_5 a) *
          ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(1 : ℝ)/(2*a^2 + a^3))) /
            (volume.nnreal (coeGrid (𝓘 p))) := sorry

    -- Estimate 6.2.24 -- 6.2.25 by 6.2.26
    have hbdd : ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
        ‖ ∫ (z : X × X) in E p' ×ˢ E p, (I12 z.fst z.snd : ℂ) ‖₊ := by
      simp only [adjointCarleson, haux] --LHS is now 6.2.24 -- 6.2.25. TODO: fix in blueprint
      simp_rw [← MeasureTheory.setIntegral_prod_mul]
      sorry
    rw [← NNReal.coe_le_coe] at hbdd
    apply le_trans hbdd
    simp only [nnnorm_mul, NNReal.coe_mul, coe_nnnorm, Complex.ofReal_mul, I12]
    sorry
  · -- If 6.2.23 does not hold, then the LHS equals zero and the result follows trivially.
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
      _ ≤ (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(1 : ℝ)/(2*a^2 + a^3))) /
          (volume.nnreal (coeGrid (𝓘 p))) * (∫ y in E p', ‖ g y‖) * ∫ y in E p, ‖ g y‖ := by
        positivity


-- Lemma 6.1.5 (part II)
lemma correlation_zero_of_ne_subset {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) (g : X → ℂ)
    (hpp' : ¬ coeGrid (𝓘 p) ⊆ ball (𝔠 p) (15 * ↑D ^𝔰 p)) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ = 0 := by
  have hD : 1 ≤ (D : ℝ) := one_le_defaultD
  have h415 : (4 : ℝ) ≤ 15 := by linarith
  have hsp : 𝔰 p = GridStructure.s (𝓘 p) := rfl
  by_contra h0
  simp only [nnnorm_eq_zero] at h0
  apply hpp'
  obtain ⟨y, hy⟩ := MeasureTheory.exists_ne_zero_of_integral_ne_zero h0 --6.2.33
  simp only [ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
  -- 6.2.34
  have hdist : dist (𝔠 p) (𝔠 p') < 10*D^(𝔰 p) :=
    calc dist (𝔠 p) (𝔠 p')
      _ ≤ dist (𝔠 p) y + dist y (𝔠 p') := dist_triangle _ _ _
      _ = dist y (𝔠 p) + dist y (𝔠 p') := by rw [dist_comm]
      _ < 5*D^(𝔰 p) + 5*D^(𝔰 p') := add_lt_add (range_support hy.2) (range_support hy.1)
      _ ≤ 5*D^(𝔰 p) + 5*D^(𝔰 p) := add_le_add_left (by gcongr) _
      _ = 10*D^(𝔰 p) := by ring
  -- 6.2.35
  rw [hsp]
  exact subset_trans Grid_subset_ball (ball_subset_ball (by gcongr))

end Tile
