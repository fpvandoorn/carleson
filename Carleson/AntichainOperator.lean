import Carleson.GridStructure
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

variable (K) (σ₁ σ₂) (p : 𝔓 X)

open MeasureTheory Metric
open ENNReal NNReal Real

/-- Constant appearing in Lemma 6.1.2. -/
noncomputable def C_6_1_2 (a : ℕ) : ℕ := 2 ^ (107 * a ^ 3)

lemma C_6_1_2_ne_zero (a : ℕ) : C_6_1_2 a ≠ 0 := by rw [C_6_1_2]; positivity

open MeasureTheory Metric Bornology Set

-- lemma 6.1.2
lemma MaximalBoundAntichain {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
    (ha : 1 ≤ a) {F : Set X} {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (x : X) :
    ‖∑ (p ∈ 𝔄), T p f x‖₊ ≤ (C_6_1_2 a) *
      MB volume ((fun (𝔭 : 𝔓 X) ↦ (𝔠 𝔭, 8*D ^ 𝔰 𝔭)) '' (𝔄 : Set (𝔓 X))) f x := by
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
      dist_mem_Icc_of_Ks_ne_zero (range_s_subset (X := X) (mem_range_self (𝓘 p.1))) hy
    have hdist_cpy : ∀ (y : X) (hy : Ks (𝔰 p.1) x y ≠ 0), dist (𝔠 p) y ≤ 8*D ^ 𝔰 p.1 := by
      intro y hy
      calc dist (𝔠 p) y
        ≤ dist (𝔠 p) x + dist x y := dist_triangle (𝔠 p.1) x y
      _ ≤ 4*D ^ 𝔰 p.1 + dist x y := by simp only [add_le_add_iff_right, dist_comm, hdist_cp]
      _ ≤ 4*D ^ 𝔰 p.1 + D ^ 𝔰 p.1 /2 := by
        simp only [add_le_add_iff_left, (mem_Icc.mpr (hdist_y hy)).2]
      _ ≤ 8*D ^ 𝔰 p.1 := by
        rw [div_eq_inv_mul, ← add_mul]
        apply mul_le_mul_of_nonneg_right (by norm_num)
        have := defaultD_pos a
        positivity
    have hKs : ∀ (y : X) (hy : Ks (𝔰 p.1) x y ≠ 0), ‖Ks (𝔰 p.1) x y‖₊ ≤
        (2 : ℝ≥0) ^ (5*a + 101*a^3) / volume (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)) := by
      intro y hy
      /- dist_mem_Icc_of_Ks_ne_zero {s : ℤ} (hs : s ∈ Icc (-S) S) {x y : X}
    (h : Ks s x y ≠ 0) : dist x y ∈ Icc (D ^ (s - 1) / 4) (D ^ s / 2)

      lemma norm_Ks_le {s : ℤ} (hs : s ∈ Icc (-S) S) {x y : X} :
    ‖Ks s x y‖ ≤ C2_1_3 a / volume.real (ball x (D ^ s)) := by-/
      have h : ‖Ks (𝔰 p.1) x y‖₊ ≤ (2 : ℝ≥0)^(a^3) / volume (ball (𝔠 p.1) (D/4 ^ (𝔰 p.1 - 1))) := by
        have hxy : x ≠ y := by
          intro h_eq
          rw [h_eq, Ks_def, ne_eq, mul_eq_zero, not_or, dist_self, mul_zero, psi_zero] at hy
          simp only [Complex.ofReal_zero, not_true_eq_false, and_false] at hy
        apply le_trans (ENNReal.coe_le_coe.mpr (kernel_bound (range_s_subset (X := X)
          (mem_range_self (𝓘 p.1))) hxy))
        rw [coe_ofNat, coe_div]
        sorry
        sorry
      apply le_trans h
      sorry
      /- calc ‖Ks (𝔰 p.1) x y‖₊
        ≤ (2 : ℝ≥0)^(a^3) / volume (ball (𝔠 p.1) (D/4 ^ (𝔰 p.1 - 1))) := by
          done
      _ ≤ (2 : ℝ≥0)^(5*a + 101*a^3) / volume (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)) :=
        sorry -/
    calc ↑‖∑ (p ∈ 𝔄), T p f x‖₊
      = ↑‖T p f x‖₊:= by rw [Finset.sum_eq_single_of_mem p.1 p.2 hne_p]
    _ ≤ ↑‖∫ (y : X), cexp (↑((coeΘ (Q x)) x) - ↑((coeΘ (Q x)) y)) * Ks (𝔰 p.1) x y * f y‖₊ := by
        simp only [T, indicator, if_pos hxE, mul_ite, mul_zero, ENNReal.coe_le_coe]
        simp only [← NNReal.coe_le_coe, coe_nnnorm]
        sorry
    _ ≤ (2 : ℝ≥0)^(5*a + 101*a^3) * ⨍⁻ y, ‖f y‖₊ ∂volume.restrict (ball (𝔠 p.1) (8*D ^ 𝔰 p.1)) := by
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
          (zpow_pos_of_pos (by exact_mod_cast defaultD_pos a) _))
    _ ≤ (C_6_1_2 a) * MB volume ((fun (𝔭 : 𝔓 X) ↦ (𝔠 𝔭, 8*D ^ 𝔰 𝔭)) '' (𝔄 : Set (𝔓 X))) f x := by
      rw [mul_le_mul_left _ _, MB, maximalFunction, inv_one, ENNReal.rpow_one, le_iSup_iff]
      simp only [mem_image, Finset.mem_coe, iSup_exists, iSup_le_iff,
        and_imp, forall_apply_eq_imp_iff₂, ENNReal.rpow_one]
      exact (fun _ hc ↦ hc p.1 p.2)
      · exact_mod_cast C_6_1_2_ne_zero a
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

-- lemma 6.1.3
lemma Dens2Antichain {𝔄 : Finset (𝔓 X)}
    (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X))) {f : X → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) {g : X → ℂ} (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (x : X) :
    ‖∫ x, ((starRingEnd ℂ) (g x)) * ∑ (p ∈ 𝔄), T p f x‖₊ ≤
      (C_6_1_3 a nnq) * (dens₂ (𝔄 : Set (𝔓 X))) * (snorm f 2 volume) * (snorm f 2 volume) := by
  have hf1 : f = (F.indicator 1) * f := eq_indicator_one_mul hf
  set q' := 2*nnq/(1 + nnq) with hq'
  have hq0 : 0 < nnq := nnq_pos X
  have h1q' : 1 ≤ q' := by -- Better proof?
    rw [hq', one_le_div (add_pos_iff.mpr (Or.inl zero_lt_one)), two_mul, add_le_add_iff_right]
    exact le_of_lt (q_mem_Ioc X).1
  have hqq' : q' ≤ nnq := by -- Better proof?
    rw [hq', div_le_iff (add_pos (zero_lt_one) hq0), mul_comm, mul_le_mul_iff_of_pos_left hq0,
      ← one_add_one_eq_two, add_le_add_iff_left]
    exact (nnq_mem_Ioc X).1.le
  sorry

/-- Constant appearing in Proposition 2.0.3. -/
def C_2_0_3 (a q : ℝ) : ℝ := 2 ^ (150 * a ^ 3) / (q - 1)

/-- Proposition 2.0.3 -/
theorem antichain_operator {𝔄 : Set (𝔓 X)} {f g : X → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (h𝔄 : IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄)) :
    ‖∫ x, conj (g x) * ∑ᶠ p : 𝔄, T p f x‖ ≤
    C_2_0_3 a q * (dens₁ 𝔄).toReal ^ ((q - 1) / (8 * a ^ 4)) * (dens₂ 𝔄).toReal ^ (q⁻¹ - 2⁻¹) *
    (snorm f 2 volume).toReal * (snorm g 2 volume).toReal := sorry
