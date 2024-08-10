import Carleson.TileStructure
import Carleson.HardyLittlewood
import Carleson.Psi

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

noncomputable section

open scoped GridStructure ComplexConjugate
open Set Complex MeasureTheory

-- Lemma 6.1.1
lemma E_disjoint {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
     {p p' : 𝔓 X} (hp : p ∈ 𝔄) (hp' : p' ∈ 𝔄) (hE : (E p ∩ E p').Nonempty) : p = p' := by
  set x := hE.some
  have hx := hE.some_mem
  simp only [E, mem_inter_iff, mem_setOf_eq] at hx
  wlog h𝔰 : 𝔰 p ≤ 𝔰 p'
  · have hE' : (E p' ∩ E p).Nonempty := by simp only [inter_comm, hE]
    exact eq_comm.mp (this h𝔄 hp' hp hE' hE'.some_mem (le_of_lt (not_le.mp h𝔰)))
  obtain ⟨⟨hx𝓓p, hxΩp, _⟩ , hx𝓓p', hxΩp', _⟩ := hx
  have h𝓓 : 𝓘 p ≤ 𝓘 p' :=
    (or_iff_left (not_disjoint_iff.mpr ⟨x, hx𝓓p, hx𝓓p'⟩)).mp (le_or_disjoint h𝔰)
  have hΩ : Ω p' ≤ Ω p :=
    (or_iff_right (not_disjoint_iff.mpr ⟨Q x, hxΩp, hxΩp'⟩)).mp (relative_fundamental_dyadic h𝓓)
  have hle : p ≤ p' := ⟨h𝓓, hΩ⟩
  exact IsAntichain.eq h𝔄 hp hp' hle

--variable (K) (σ₁ σ₂) (p : 𝔓 X)

open MeasureTheory Metric
open ENNReal NNReal Real

/-- Constant appearing in Lemma 6.1.2. -/
noncomputable def C_6_1_2 (a : ℕ) : ℕ := 2 ^ (107 * a ^ 3)

lemma C_6_1_2_ne_zero (a : ℕ) : (C_6_1_2 a : ℝ≥0∞) ≠ 0 := by rw [C_6_1_2]; positivity

open MeasureTheory Metric Bornology Set

--TODO: PR
lemma _root_.ENNReal.div_mul (a : ℝ≥0∞) {b c : ℝ≥0∞} (hb0 : b ≠ 0) (hb_top : b ≠ ⊤)
    (hc0 : c ≠ 0) (hc_top : c ≠ ⊤) :
    a / b * c = a / (b / c) := by
  rw [← ENNReal.mul_div_right_comm, ENNReal.div_eq_div_iff (ENNReal.div_ne_zero.mpr ⟨hb0, hc_top⟩)
    _ hb0 hb_top]
  rw [ENNReal.div_eq_inv_mul, mul_comm a, mul_assoc]
  simp only [mul_comm b, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hc_top]
  ring
  · simp only [ne_eq, div_eq_top]
    tauto

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
              (mul_pos (by positivity) (zpow_pos_of_pos (defaultD_pos _) _))))
        rw [mul_div_assoc, ← div_div, div_eq_mul_inv]
        congr
        rw [eq_div_iff_mul_eq (mul_ne_zero (by positivity) hvol), mul_comm, mul_assoc,
          mul_inv_cancel hvol, mul_one]
    _ ≤ 2 ^ a ^ 3 * 2 ^ (5 * a + 100 * a ^ 3) / volume.real (ball x (8 * D ^ 𝔰 p.1)) := by
      apply div_le_div_of_nonneg_left (by positivity)
        (measure_real_ball_pos x (mul_pos (by positivity) (zpow_pos_of_pos (defaultD_pos _) _)))
      · have heq : 2 ^ (100 * a ^ 2) * 2 ^ 5 * (1 / (↑D * 32) * (8 * (D : ℝ) ^ 𝔰 p.1)) =
            (8 * ↑D ^ 𝔰 p.1) := by
          have hD : (D : ℝ) = 2 ^ (100 * a^2) := by simp
          rw [← hD]
          ring_nf
          rw [mul_inv_cancel (ne_of_gt (defaultD_pos _)), one_mul]
        convert (DoublingMeasure.volume_ball_two_le_same_repeat x
          ((1 / ((D : ℝ) * 32)) * (8 * D ^ 𝔰 p.1)) (100*a^2 + 5)) using 1
        · conv_lhs => rw [← heq, ← pow_add]
        · congr 1
          simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat]
          ring
    _ = 2 ^ (5 * a + 101 * a ^ 3) / volume.real (ball x (8 * ↑D ^ 𝔰 p.1)) := by ring_nf

-- Composition of inequalities 6.1.6, 6.1.7
lemma norm_Ks_le'  {x y : X} {𝔄 : Set (𝔓 X)} (p : 𝔄) (hy : Ks (𝔰 p.1) x y ≠ 0)  :
    ‖Ks (𝔰 p.1) x y‖₊ ≤ (2 : ℝ≥0) ^ (5*a + 101*a^3) / volume.nnreal (ball x (8*D ^ 𝔰 p.1)) := by
  have h : ‖Ks (𝔰 p.1) x y‖₊ ≤ (2 : ℝ≥0)^(a^3) / volume.real (ball x (D ^ (𝔰 p.1 - 1)/4)) := by
    apply le_trans (NNReal.coe_le_coe.mpr kernel_bound)
    rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, ← NNReal.val_eq_coe, measureNNReal_val]
    exact div_le_div_of_nonneg_left (pow_nonneg zero_le_two _)
      (measure_ball_pos_real x _ (div_pos (zpow_pos_of_pos (defaultD_pos _) _) zero_lt_four))
      (measureReal_mono (Metric.ball_subset_ball (dist_mem_Icc_of_Ks_ne_zero hy).1)
        (measure_ball_ne_top x (dist x y)))
  apply le_trans h
  rw [zpow_sub₀ (by simp), zpow_one, div_div]
  exact ineq_6_1_7 x p



-- lemma 6.1.2
lemma MaximalBoundAntichain {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
    (ha : 1 ≤ a) {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (x : X) :
    ‖∑ (p ∈ 𝔄), T p f x‖₊ ≤ (C_6_1_2 a) * MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x := by
  by_cases hx : ∃ (p : 𝔄), T p f x ≠ 0
  · obtain ⟨p, hpx⟩ := hx
    have hxE : x ∈ E ↑p := mem_of_indicator_ne_zero hpx
    have hne_p : ∀ b ∈ 𝔄, b ≠ ↑p → T b f x = 0 := by
      intro p' hp' hpp'
      by_contra hp'x
      exact hpp' (E_disjoint h𝔄 hp' p.2 ⟨x, mem_of_indicator_ne_zero hp'x, hxE⟩)
    have hdist_cp : dist x (𝔠 p) ≤ 4*D ^ 𝔰 p.1 := le_of_lt (mem_ball.mp (Grid_subset_ball hxE.1))
    have hdist_y : ∀ {y : X} (hy : Ks (𝔰 p.1) x y ≠ 0),
        dist x y ∈ Icc ((D ^ ((𝔰 p.1) - 1) : ℝ) / 4) (D ^ (𝔰 p.1) / 2) := fun hy ↦
      dist_mem_Icc_of_Ks_ne_zero hy
    have hdist_cpy : ∀ (y : X) (hy : Ks (𝔰 p.1) x y ≠ 0), dist (𝔠 p) y ≤ 8*D ^ 𝔰 p.1 := by
      intro y hy
      calc dist (𝔠 p) y
        ≤ dist (𝔠 p) x + dist x y := dist_triangle (𝔠 p.1) x y
      _ ≤ 4*D ^ 𝔰 p.1 + dist x y := by simp only [add_le_add_iff_right, dist_comm, hdist_cp]
      _ ≤ 4*D ^ 𝔰 p.1 + D ^ 𝔰 p.1 /2 := by
        simp only [add_le_add_iff_left, (mem_Icc.mpr (hdist_y hy)).2]
      _ ≤ 8*D ^ 𝔰 p.1 := by
        rw [div_eq_inv_mul, ← add_mul]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    -- 6.1.6, 6.1.7
    /- have hKs : ∀ (y : X) (hy : Ks (𝔰 p.1) x y ≠ 0), ‖Ks (𝔰 p.1) x y‖₊ ≤
        (2 : ℝ≥0) ^ (5*a + 101*a^3) / volume.real (ball x (8*D ^ 𝔰 p.1)) := fun y hy ↦
      norm_Ks_le' _ hy -/
    have hKs : ∀ (y : X) (hy : Ks (𝔰 p.1) x y ≠ 0), ‖Ks (𝔰 p.1) x y‖₊ ≤
        (2 : ℝ≥0) ^ (5*a + 101*a^3) / volume.nnreal (ball x (8*D ^ 𝔰 p.1)) := fun y hy ↦
      norm_Ks_le' _ hy


    calc (‖∑ (p ∈ 𝔄), T p f x‖₊ : ℝ≥0∞)
      = ↑‖T p f x‖₊:= by rw [Finset.sum_eq_single_of_mem p.1 p.2 hne_p]
    /- _ ≤ ↑‖∫ (y : X), cexp (↑((coeΘ (Q x)) x) - ↑((coeΘ (Q x)) y)) * Ks (𝔰 p.1) x y * f y‖₊ := by
        simp only [T, indicator, if_pos hxE, mul_ite, mul_zero, ENNReal.coe_le_coe,
          ← NNReal.coe_le_coe, coe_nnnorm]
        sorry -/
    _ ≤ ∫⁻ (y : X), ‖cexp (↑((coeΘ (Q x)) x) - ↑((coeΘ (Q x)) y)) * Ks (𝔰 p.1) x y * f y‖₊ := by
        /- simp only [T, indicator, if_pos hxE, mul_ite, mul_zero, ENNReal.coe_le_coe,
          ← NNReal.coe_le_coe, coe_nnnorm] -/
        /- simp only [T, indicator, if_pos hxE]
        apply le_trans (MeasureTheory.ennnorm_integral_le_lintegral_ennnorm _)
        apply MeasureTheory.lintegral_mono
        intro z w -/
        simp only [T, indicator, if_pos hxE]
        apply le_trans (MeasureTheory.ennnorm_integral_le_lintegral_ennnorm _)
        apply MeasureTheory.lintegral_mono
        intro z w
        simp only [nnnorm_mul, coe_mul, some_eq_coe', Nat.cast_pow,
          Nat.cast_ofNat, zpow_neg, mul_ite, mul_zero]
        sorry
    _ ≤ ∫⁻ (y : X), ‖Ks (𝔰 p.1) x y * f y‖₊ := by
      simp only [nnnorm_mul]
      refine lintegral_mono_nnreal ?h
      intro y
      simp only [mul_assoc]
      conv_rhs => rw [← one_mul (‖Ks (𝔰 p.1) x y‖₊ * ‖f y‖₊)]
      apply mul_le_mul_of_nonneg_right _ (zero_le _)
      · sorry
    _ ≤ ∫⁻ (y : X), (((2 : ℝ≥0) ^ (5*a + 101*a^3) / volume.nnreal (ball x (8*D ^ 𝔰 p.1)))
        * ‖f y‖₊ : ℝ≥0) := by
      refine lintegral_mono_nnreal ?_
      intro y
      simp only [nnnorm_mul]
      apply mul_le_mul_of_nonneg_right _ (zero_le _)
      by_cases hy : Ks (𝔰 p.1) x y = 0
      · simp only [hy, nnnorm_zero, zero_le]
      · exact hKs y hy
    _ = ∫⁻ (y : X), (((2 : ℝ≥0) ^ (5*a + 101*a^3) / volume.nnreal (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)))
        * ‖f y‖₊ : ℝ≥0) := by
      congr
      ext y
      congr 3
      simp only [measureNNReal_def]
      rw [ENNReal.toNNReal_eq_toNNReal_iff]
      left

      sorry
    _ = (2 : ℝ≥0)^(5*a + 101*a^3) * ⨍⁻ y, ‖f y‖₊ ∂volume.restrict (ball x (8*D ^ 𝔰 p.1)) := by
      simp only [laverage_eq, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      simp_rw [div_eq_mul_inv, mul_assoc]

      sorry



    _ = (2 : ℝ≥0)^(5*a + 101*a^3) * ⨍⁻ y, ‖f y‖₊ ∂volume.restrict (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)) := by
      congr 2

      --apply MeasureTheory.Measure.restrict_congr_set
      --refine ae_eq_of_subset_of_measure_ge ?_ ?_ ?_ ?_
      --sorry
      sorry
    _ ≤ (C_6_1_2 a) * (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)).indicator (x := x)
        (fun _ ↦ ⨍⁻ y, ‖f y‖₊ ∂volume.restrict (ball (𝔠 p.1) (8*D ^ 𝔰 p.1))) := by
      simp only [coe_ofNat, indicator, mem_ball, mul_ite, mul_zero]
      rw [if_pos]
      apply mul_le_mul_of_nonneg_right _ (zero_le _)
      · rw [C_6_1_2]; norm_cast
        apply pow_le_pow_right one_le_two
        calc
        _ ≤ 5 * a ^ 3 + 101 * a ^ 3 := by
          gcongr; exact le_self_pow (by linarith [four_le_a X]) (by omega)
        _ = 106 * a ^ 3 := by ring
        _ ≤ 107 * a ^ 3 := by gcongr; norm_num
      · exact lt_of_le_of_lt hdist_cp
          (mul_lt_mul_of_nonneg_of_pos (by linarith) (le_refl _) (by linarith)
          (zpow_pos_of_pos (defaultD_pos a) _))
    _ ≤ (C_6_1_2 a) * MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x := by
      rw [mul_le_mul_left _ _, MB, maximalFunction, inv_one, ENNReal.rpow_one, le_iSup_iff]
      simp only [mem_image, Finset.mem_coe, iSup_exists, iSup_le_iff,
        and_imp, forall_apply_eq_imp_iff₂, ENNReal.rpow_one]
      exact (fun _ hc ↦ hc p.1 p.2)
      · exact C_6_1_2_ne_zero a
      · exact coe_ne_top
  · simp only [ne_eq, Subtype.exists, exists_prop, not_exists, not_and, Decidable.not_not] at hx
    have h0 : (∑ (p ∈ 𝔄), T p f x) = (∑ (p ∈ 𝔄), 0) := Finset.sum_congr rfl (fun  p hp ↦ hx p hp)
    simp only [h0, Finset.sum_const_zero, nnnorm_zero, ENNReal.coe_zero, zero_le]

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
noncomputable def C_6_1_3 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2^(111*a^3)*(q-1)⁻¹

namespace ShortVariables

-- q tilde in def. 6.1.9.
scoped notation "q'" => 2*nnq/(nnq + 1)

end ShortVariables

-- lemma 6.1.3, inequality 6.1.10
lemma Dens2Antichain {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X))) (ha : 4 ≤ a)
    {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) {g : X → ℂ} (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (x : X) : ‖∫ x, ((starRingEnd ℂ) (g x)) * ∑ (p ∈ 𝔄), T p f x‖₊ ≤
      (C_6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((q' : ℝ)⁻¹ - 2⁻¹) *
        (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
  have hf1 : f = (F.indicator 1) * f := eq_indicator_one_mul hf
  have hq0 : 0 < nnq := nnq_pos X
  have h1q' : 1 ≤ q' := by -- Better proof?
    rw [one_le_div (add_pos_iff.mpr (Or.inr zero_lt_one)), two_mul, add_le_add_iff_left]
    exact le_of_lt (q_mem_Ioc X).1
  have hqq' : q' ≤ nnq := by -- Better proof?
    rw [add_comm, div_le_iff (add_pos (zero_lt_one) hq0), mul_comm, mul_le_mul_iff_of_pos_left hq0,
      ← one_add_one_eq_two, add_le_add_iff_left]
    exact (nnq_mem_Ioc X).1.le
  have hq'_inv : (q' - 1)⁻¹ ≤ 3 * (nnq - 1)⁻¹ := by
    have : (q' - 1)⁻¹ = (nnq + 1)/(nnq -1) := by
      nth_rewrite 2 [← div_self (a := nnq + 1) (by simp)]
      rw [← NNReal.sub_div, inv_div]
      congr 1
      rw [two_mul, NNReal.sub_def, NNReal.coe_add, NNReal.coe_add, add_sub_add_left_eq_sub]
      rfl
    rw [this, div_eq_mul_inv]
    gcongr
    rw [← two_add_one_eq_three, add_le_add_iff_right]
    exact (nnq_mem_Ioc X).2
  calc ↑‖∫ x, ((starRingEnd ℂ) (g x)) * ∑ (p ∈ 𝔄), T p f x‖₊
    _ ≤ (eLpNorm (∑ (p ∈ 𝔄), T p f) 2 volume) * (eLpNorm g 2 volume) := by
      -- 6.1.18. Use Cauchy-Schwarz
      rw [mul_comm]
      sorry
    _ ≤ 2 ^ (107*a^3) * (eLpNorm (fun x ↦ ((MB volume 𝔄 𝔠 (fun 𝔭 ↦ 8*D ^ 𝔰 𝔭) f x).toNNReal : ℂ))
          2 volume) * (eLpNorm g 2 volume) := by
      -- 6.1.19. Use Lemma 6.1.2.
      apply mul_le_mul_of_nonneg_right _ (zero_le _)
      have h2 : (2 : ℝ≥0∞) ^ (107 * a ^ 3) = ‖(2 : ℝ) ^ (107 * a ^ 3)‖₊ := by
        simp only [nnnorm_pow, nnnorm_two, ENNReal.coe_pow, coe_ofNat]
      rw [h2, ← MeasureTheory.eLpNorm_const_smul]
      apply eLpNorm_mono_nnnorm
      intro z
      have MB_top : MB volume (↑𝔄) 𝔠 (fun 𝔭 ↦ 8 * ↑D ^ 𝔰 𝔭) f z ≠ ⊤ := by
       -- apply ne_top_of_le_ne_top _ (MB_le_eLpNormEssSup)
        --apply ne_of_lt
        --apply eLpNormEssSup_lt_top_of_ae_nnnorm_bound
        sorry
      rw [← ENNReal.coe_le_coe, Finset.sum_apply]
      convert (MaximalBoundAntichain h𝔄 (le_trans (by linarith) ha) hf z)
      · simp only [Pi.smul_apply, real_smul, nnnorm_mul, nnnorm_eq, nnnorm_mul,
         nnnorm_real, nnnorm_pow, nnnorm_two,
        nnnorm_eq, coe_mul, C_6_1_2, ENNReal.coe_toNNReal MB_top]
        norm_cast
    _ ≤ 2 ^ (107*a^3 + 2*a + 2) * (q' - 1)⁻¹ * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((q' : ℝ)⁻¹ - 2⁻¹) *
        (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
      -- 6.1.20. use 6.1.14 and 6.1.16.
      sorry
    _ ≤ (C_6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((q' : ℝ)⁻¹ - 2⁻¹) *
        (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
      -- use 4 ≤ a, hq'_inv.
      have h3 : 3 * ((C_6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((q' : ℝ)⁻¹ - 2⁻¹) *
          (eLpNorm f 2 volume) * (eLpNorm g 2 volume)) =
          (2 : ℝ≥0)^(111*a^3) * (3 * (nnq-1)⁻¹) * (dens₂ (𝔄 : Set (𝔓 X))) ^ ((q' : ℝ)⁻¹ - 2⁻¹) *
          (eLpNorm f 2 volume) * (eLpNorm g 2 volume) := by
        conv_lhs => simp only [C_6_1_3, ENNReal.coe_mul, ← mul_assoc]
        rw [mul_comm 3, mul_assoc _ 3]
        norm_cast
      rw [← ENNReal.mul_le_mul_left (Ne.symm (NeZero.ne' 3)) (ofNat_ne_top 3), h3]
      conv_lhs => simp only [← mul_assoc]
      gcongr
      · norm_cast
        calc 3 * 2 ^ (107 * a ^ 3 + 2 * a + 2)
          _ ≤ 4 * 2 ^ (107 * a ^ 3 + 2 * a + 2) := mul_le_mul_of_nonneg_right (by omega) (zero_le _)
          _ = 2 ^ (107 * a ^ 3 + 2 * a + 4) := by ring
          _ ≤ 2 ^ (107 * a ^ 3) * 2 ^ (4 * a ^ 3) := by
            rw [add_assoc, pow_add]
            apply mul_le_mul_of_nonneg_left _ (zero_le _)
            apply pow_right_mono one_le_two
            apply Nat.add_le_of_le_sub'
            · have h4a3 : 4 * a ^ 3 = 2 * a * (2 * a^2) := by ring
              exact h4a3 ▸ Nat.le_mul_of_pos_right _ (by positivity)
            · apply le_trans ha
              calc a
                _ ≤ a * (4 * a ^ 2 - 2) := by
                  apply Nat.le_mul_of_pos_right _
                  rw [tsub_pos_iff_lt]
                  exact lt_of_lt_of_le (by linarith)
                    (Nat.mul_le_mul_left 4 (pow_le_pow_left zero_le_four ha 2))
                _ = 4 * a ^ 3 - 2 * a := by
                  rw [Nat.mul_sub]
                  ring_nf
          _ = 2 ^ (111 * a ^ 3) := by ring
      · norm_cast -- uses hq'_inv

/-- The constant appearing in Proposition 2.0.3.
Has value `2 ^ (150 * a ^ 3) / (q - 1)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C_2_0_3 (a q : ℝ) : ℝ := 2 ^ (150 * a ^ 3) / (q - 1)

/-- Proposition 2.0.3 -/
theorem antichain_operator {𝔄 : Set (𝔓 X)} {f g : X → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (h𝔄 : IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄)) :
    ‖∫ x, conj (g x) * ∑ᶠ p : 𝔄, T p f x‖ ≤
    C_2_0_3 a q * (dens₁ 𝔄).toReal ^ ((q - 1) / (8 * a ^ 4)) * (dens₂ 𝔄).toReal ^ (q⁻¹ - 2⁻¹) *
    (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := sorry
