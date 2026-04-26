import Carleson.Antichain.AntichainTileCount
import Carleson.Antichain.TileCorrelation

/-!
# 6. Proof of the Antichain Operator Proposition

This file contains the proofs of Lemma 6.1.4 and Proposition 2.0.3 from the blueprint. Three
versions of the latter are provided.

## Main results
- `dens1_antichain` : Lemma 6.1.4.
- `antichain_operator`: Proposition 2.0.3.
-/
noncomputable section

open scoped ShortVariables ComplexConjugate GridStructure
open Set Complex MeasureTheory Metric NNReal ENNReal

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {𝔄 : Set (𝔓 X)} {f g : X → ℂ}

-- set_option trace.Meta.Tactic.fun_prop true in
open Classical in
lemma dens1_antichain_rearrange (bg : BoundedCompactSupport g) :
    eLpNorm (adjointCarlesonSum 𝔄 g) 2 ^ 2 ≤
      2 * ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p,
        ‖∫ x, adjointCarleson p' g x * conj (adjointCarleson p g x)‖ₑ :=
  calc
    _ = ‖∫ x, ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄,
          adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := by
      rw [eLpNorm_two_eq_enorm_integral_mul_conj (bg.adjointCarlesonSum.memLp 2)]; congr! with x
      unfold adjointCarlesonSum; rw [map_sum, Finset.sum_mul]; congr! with p mp
      rw [Finset.mul_sum]
    _ = ‖∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄,
          ∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := by
      congr 1
      rw [integral_finset_sum]
      · congr! with p mp
        exact integral_finset_sum _ fun p' mp' ↦ by
          -- This smells like a fun_prop bug: removing the `change` makes fun_prop fail to prove
          -- `fails` below, even though it knows about `BoundedCompactSupport.integrable` and
          -- can prove that.
          have : BoundedCompactSupport (fun x ↦ (starRingEnd ℂ) (adjointCarleson p' g x)) volume := by fun_prop
          --have fails : Integrable (fun x ↦ (starRingEnd ℂ) (adjointCarleson p' g x)) volume := by
          --  fun_prop
          change Integrable (adjointCarleson p g * star (adjointCarleson p' g)) volume
          fun_prop
      · exact fun p mp ↦ (BoundedCompactSupport.finset_sum fun p' mp' ↦
          bg.adjointCarleson.mul bg.adjointCarleson.conj).integrable
    _ ≤ ∑ p with p ∈ 𝔄, ‖∑ p' with p' ∈ 𝔄,
          ∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄,
          ‖∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := by
      gcongr; exact enorm_sum_le _ _
    _ = ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p,
          ‖∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ +
            ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄 ∧ 𝔰 p < 𝔰 p',
              ‖∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := by
      conv_lhs =>
        enter [2, p]
        rw [← Finset.sum_filter_add_sum_filter_not (p := fun p' ↦ 𝔰 p' ≤ 𝔰 p)]
      rw [Finset.sum_add_distrib]; congr! 3 with p mp p mp <;> rw [Finset.filter_filter]
      simp only [not_le]
    _ = ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p,
          ‖∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ +
            ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄 ∧ 𝔰 p' < 𝔰 p,
              ‖∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := by
      congr 1
      conv_lhs => enter [2, p]; rw [← Finset.filter_filter, Finset.sum_filter]
      conv_rhs => enter [2, p]; rw [← Finset.filter_filter, Finset.sum_filter]
      rw [Finset.sum_comm]; congr! 3 with p mp p' mp' h
      exact enorm_integral_mul_starRingEnd_comm
    _ ≤ 2 * ∑ p with p ∈ 𝔄, ∑ p' with p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p,
        ‖∫ x, adjointCarleson p g x * conj (adjointCarleson p' g x)‖ₑ := by
      rw [two_mul]; gcongr with p mp; exact fun h ↦ h.le
    _ = _ := by congr! 3 with p mp p' mp'; exact enorm_integral_mul_starRingEnd_comm

open Classical in
/-- `h(p)` in the proof of Lemma 6.1.4 (**d**ens₁ **a**nti**c**hain **h**). -/
def dach (𝔄 : Set (𝔓 X)) (p : 𝔓 X) (g : X → ℂ) : ℝ≥0∞ :=
  (volume (ball (𝔠 p) (14 * D ^ 𝔰 p)))⁻¹ *
  ∫⁻ x, ∑ p' with (p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p) ∧ (𝓘 p' : Set X) ⊆ ball (𝔠 p) (14 * D ^ 𝔰 p),
    (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) * (E p').indicator (‖g ·‖ₑ) x

open Classical in
lemma dens1_antichain_dach (hg : Measurable g) (hgG : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    eLpNorm (adjointCarlesonSum 𝔄 g) 2 ^ 2 ≤
      Tile.C6_1_5 a * 2 ^ (6 * a + 1) * ∑ p with p ∈ 𝔄, dach 𝔄 p g * ∫⁻ y in E p, ‖g y‖ₑ := by
  have bg := bcs_of_measurable_of_le_indicator_g hg hgG
  calc
    _ ≤ _ := dens1_antichain_rearrange bg
    _ = 2 * ∑ p with p ∈ 𝔄,
          ∑ p' with (p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p) ∧ (𝓘 p' : Set X) ⊆ ball (𝔠 p) (14 * D ^ 𝔰 p),
            ‖∫ x, adjointCarleson p' g x * conj (adjointCarleson p g x)‖ₑ := by
      congr! 2 with p mp; nth_rw 2 [← Finset.filter_filter]
      refine (Finset.sum_filter_of_ne fun x mx nx ↦ ?_).symm
      rw [Finset.mem_filter_univ] at mx
      contrapose! nx; exact Tile.correlation_zero_of_ne_subset mx.2 nx
    _ ≤ 2 * ∑ p with p ∈ 𝔄,
        ∑ p' with (p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p) ∧ (𝓘 p' : Set X) ⊆ ball (𝔠 p) (14 * D ^ 𝔰 p),
        Tile.C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) /
        volume (𝓘 p : Set X) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ x in E p, ‖g x‖ₑ := by
      gcongr with p mp p' mp'
      rw [Finset.mem_filter_univ] at mp'
      exact Tile.correlation_le mp'.1.2 hg hgG
    _ = 2 * Tile.C6_1_5 a * ∑ p with p ∈ 𝔄, (∫⁻ x in E p, ‖g x‖ₑ) * (volume (𝓘 p : Set X))⁻¹ *
          ∑ p' with (p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p) ∧ (𝓘 p' : Set X) ⊆ ball (𝔠 p) (14 * D ^ 𝔰 p),
            ∫⁻ y, (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
              (E p').indicator (‖g ·‖ₑ) y := by
      rw [mul_assoc, Finset.mul_sum _ _ (Tile.C6_1_5 a : ℝ≥0∞)]; congr! 2 with p mp
      rw [Finset.mul_sum, Finset.mul_sum]; congr! 1 with p' mp'
      rw [ENNReal.div_eq_inv_mul, lintegral_const_mul _ (hg.enorm.indicator measurableSet_E),
        lintegral_indicator measurableSet_E]
      ring
    _ ≤ 2 * Tile.C6_1_5 a * ∑ p with p ∈ 𝔄,
          (∫⁻ x in E p, ‖g x‖ₑ) * (2 ^ (6 * a) * (volume (ball (𝔠 p) (14 * D ^ 𝔰 p)))⁻¹) *
            ∑ p' with (p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p) ∧ (𝓘 p' : Set X) ⊆ ball (𝔠 p) (14 * D ^ 𝔰 p),
              ∫⁻ y, (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
                (E p').indicator (‖g ·‖ₑ) y := by
      gcongr with p mp
      rw [← ENNReal.inv_le_inv, ENNReal.mul_inv (.inl (by positivity)) (.inl (by finiteness)),
        inv_inv, inv_inv, ← ENNReal.div_eq_inv_mul]
      apply ENNReal.div_le_of_le_mul'
      calc
        _ ≤ volume (ball (𝔠 p) (2 ^ 6 * (D ^ 𝔰 p / 4))) := by rw [← mul_comm_div]; gcongr; norm_num
        _ ≤ defaultA a ^ 6 * volume (ball (𝔠 p) (D ^ 𝔰 p / 4)) :=
          measure_ball_two_le_same_iterate _ _ _
        _ ≤ _ := by
          simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, pow_mul']; gcongr
          exact ball_subset_Grid
    _ = _ := by
      conv_lhs => enter [2, 2, p]; rw [mul_comm _ (_ * _), mul_assoc, mul_assoc]
      rw [← Finset.mul_sum, ← mul_assoc]; congr 1
      · rw [← mul_rotate, ← pow_succ, mul_comm]
      · congr! 1 with p mp; rw [mul_comm (lintegral ..), ← mul_assoc, dach]; congr 2
        exact (lintegral_finset_sum _ fun p' mp' ↦
          (hg.enorm.indicator measurableSet_E).const_mul _).symm

/-- The `maximalFunction` instance that appears in Lemma 6.1.4's proof. -/
def M14 (𝔄 : Set (𝔓 X)) (p : ℝ) (g : X → ℂ) : X → ℝ≥0∞ :=
  maximalFunction volume 𝔄 𝔠 (14 * D ^ 𝔰 ·) p g

lemma eLpNorm_le_M14 {p : 𝔓 X} (mp : p ∈ 𝔄) {x₀ : X} (hx : x₀ ∈ ball (𝔠 p) (14 * D ^ 𝔰 p))
    {r : ℝ} (hr : 0 < r) :
    eLpNorm ((ball (𝔠 p) (14 * D ^ 𝔰 p)).indicator (‖g ·‖ₑ)) (ENNReal.ofReal r) volume ≤
      volume (ball (𝔠 p) (14 * D ^ 𝔰 p)) ^ r⁻¹ * M14 𝔄 r g x₀ := by
  have vpos : 0 < volume (ball (𝔠 p) (14 * D ^ 𝔰 p)) := by
    apply measure_ball_pos; unfold defaultD; positivity
  rw [mul_comm (_ ^ _), ← ENNReal.div_le_iff_le_mul]; rotate_left
  · left
    rw [← inv_ne_top, ← ENNReal.rpow_neg]
    finiteness
  · exact Or.inl <| (by finiteness)
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, mul_comm _ (-1),
    ENNReal.rpow_mul, ENNReal.rpow_neg_one,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa) (by finiteness)]
  simp_rw [ENNReal.toReal_ofReal hr.le, one_div]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), M14, maximalFunction]
  conv_lhs =>
    enter [1, 2, 2, x]
    rw [enorm_eq_self, ← Function.comp_apply (f := (· ^ r)),
      ← indicator_comp_of_zero (g := fun x ↦ x ^ r) (by simpa using hr)]
  rw [lintegral_indicator measurableSet_ball, ← ENNReal.div_eq_inv_mul, ← setLAverage_eq]
  simp only [Function.comp_apply]; refine le_trans ?_ (le_iSup₂ p mp); rw [indicator_of_mem hx]

open Antichain in
/-- Equations (6.1.34) to (6.1.37) in Lemma 6.1.4. -/
lemma dach_bound (h𝔄 : IsAntichain (· ≤ ·) 𝔄) {p : 𝔓 X} (mp : p ∈ 𝔄) (hg : Measurable g)
    (hgG : ∀ x, ‖g x‖ ≤ G.indicator 1 x) {x₀ : X} (hx : x₀ ∈ ball (𝔠 p) (14 * D ^ 𝔰 p)) :
    dach 𝔄 p g ≤ C6_1_6 a * dens₁ 𝔄 ^ (p₆ a : ℝ)⁻¹ * M14 𝔄 (q₆ a) g x₀ := by
  classical
  unfold dach
  set B := ball (𝔠 p) (14 * D ^ 𝔰 p)
  set A : Set (𝔓 X) := {p' | (p' ∈ 𝔄 ∧ 𝔰 p' ≤ 𝔰 p) ∧ (𝓘 p' : Set X) ⊆ B}
  have sA : A ⊆ 𝔄 := fun _ ↦ by simp only [A, mem_setOf_eq, and_imp]; tauto
  calc
    _ = (volume B)⁻¹ * ∫⁻ x, B.indicator (‖g ·‖ₑ) x *
          ∑ p' with p' ∈ A, (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
            (E p').indicator 1 x * G.indicator 1 x := by
      congr! with x; change ∑ p' with p' ∈ A, _ = _
      rw [Finset.mul_sum]
      conv_rhs =>
        enter [2, p']
        rw [← mul_assoc, ← mul_assoc, mul_comm _ (_ ^ _), mul_assoc, mul_assoc]
      congr! 2 with p' mp'
      rw [← mul_assoc, ← inter_indicator_mul]; simp_rw [Pi.one_apply, mul_one]
      simp_rw [A, mem_setOf_eq, Finset.mem_filter_univ] at mp'
      rw [inter_eq_right.mpr (E_subset_𝓘.trans mp'.2)]
      by_cases hx : x ∈ G
      · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      · specialize hgG x; rw [indicator_of_notMem hx, norm_le_zero_iff] at hgG
        have : (E p').indicator (‖g ·‖ₑ) x = 0 := by
          rw [indicator_apply_eq_zero, hgG, enorm_zero]; exact fun _ ↦ rfl
        rw [this, zero_mul]
    _ ≤ (volume B)⁻¹ * eLpNorm (B.indicator (‖g ·‖ₑ)) (ENNReal.ofReal (q₆ a)) *
        eLpNorm (fun x ↦ ∑ p' with p' ∈ A,
          (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
          (E p').indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) := by
      rw [mul_assoc]; gcongr; apply lintegral_mul_le_eLpNorm_mul_eLqNorm
      · exact Real.HolderConjugate.ennrealOfReal (holderConjugate_p₆ (four_le_a X)).symm
      · fun_prop (discharger := measurability)
      · refine Finset.aemeasurable_fun_sum _ fun p' mp' ↦ ?_
        simp_rw [mul_assoc, ← inter_indicator_mul]
        exact (AEMeasurable.indicator (by simp) (measurableSet_E.inter measurableSet_G)).const_mul _
    _ ≤ (volume B)⁻¹ * (volume B ^ (q₆ a)⁻¹ * M14 𝔄 (q₆ a) g x₀) *
        (C6_1_6 a * dens₁ A ^ (p₆ a)⁻¹ * volume (⋃ t ∈ A, (𝓘 t : Set X)) ^ (p₆ a)⁻¹) := by
      gcongr
      · exact eLpNorm_le_M14 mp hx (q₆_pos (four_le_a X))
      · convert tile_count (h𝔄.subset sA) ⟨𝒬 p, range_𝒬 (mem_range_self p)⟩
    _ ≤ (volume B)⁻¹ * (volume B ^ (q₆ a)⁻¹ * M14 𝔄 (q₆ a) g x₀) *
        (C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ * volume B ^ (p₆ a)⁻¹) := by
      have : 0 ≤ (p₆ a)⁻¹ := by rw [Right.inv_nonneg]; exact (p₆_pos (four_le_a X)).le
      gcongr
      · exact dens₁_mono sA
      · refine iUnion₂_subset fun p' mp' ↦ ?_
        simp_rw [A, mem_setOf_eq] at mp'; exact mp'.2
    _ = _ := by
      rw [mul_comm, mul_assoc]; congr 1
      have vpos : 0 < volume B := by apply measure_ball_pos; unfold defaultD; positivity
      rw [← mul_assoc, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ vpos.ne' (by finiteness),
        ← mul_assoc, ← ENNReal.rpow_add _ _ vpos.ne' (by finiteness),
        ← add_rotate, (holderConjugate_p₆ (four_le_a X)).symm.inv_add_inv_eq_one,
        add_neg_cancel, ENNReal.rpow_zero, one_mul]

open Antichain in
lemma M14_bound (hg : MemLp g 2 volume) :
    eLpNorm (M14 𝔄 (q₆ a) g) 2 ≤ 2 ^ (a + 2) * eLpNorm g 2 := by
  have a4 := four_le_a X
  have ha22 : HasStrongType (M14 𝔄 (q₆ a).toNNReal) 2 2 volume volume
      (C2_0_6 (defaultA a) (q₆ a).toNNReal 2) := by
    apply hasStrongType_maximalFunction 𝔄.to_countable
      (Real.toNNReal_pos.mpr <| zero_lt_one.trans (one_lt_q₆ a4))
    simp only [Nat.cast_ofNat, Real.toNNReal_lt_ofNat]
    exact (q₆_le_superparticular a4).trans_lt (by norm_num)
  rw [Real.coe_toNNReal _ (q₆_pos (four_le_a X)).le] at ha22
  apply (ha22 g hg).2.trans; gcongr
  rw [show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← ENNReal.coe_pow, ENNReal.coe_le_coe]
  exact C2_0_6_q₆_le a4

/-- Constant appearing in Lemma 6.1.4.
Has value `2 ^ (117 * a ^ 3)` in the blueprint. -/
irreducible_def C6_1_4 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 5 + 𝕔 / 8) * a ^ 3)

lemma le_C6_1_4 (a4 : 4 ≤ a) :
    Tile.C6_1_5 a * 2 ^ (6 * a + 1) * Antichain.C6_1_6 a * 2 ^ (a + 2) ≤ C6_1_4 a ^ 2 := by
  simp_rw [Tile.C6_1_5, Antichain.C6_1_6, C6_1_4, ← pow_add, ← pow_mul]
  gcongr
  · exact one_le_two
  · have : 𝕔 / 4 ≤ 2 * (𝕔 / 8) + 1 := by lia
    have : (𝕔 / 4) * a ^ 3 ≤ 2 * (𝕔 / 8) * a ^ 3 + a ^ 3 :=
      (mul_le_mul_of_nonneg_right this (Nat.zero_le _)).trans_eq (by ring)
    ring_nf
    linarith [sixteen_times_le_cube a4]

open Classical Antichain in
lemma dens1_antichain_sq (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    (hg : Measurable g) (hgG : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    eLpNorm (adjointCarlesonSum 𝔄 g) 2 ^ 2 ≤
      (C6_1_4 a * dens₁ 𝔄 ^ (8 * a ^ 4 : ℝ)⁻¹ * eLpNorm g 2 volume) ^ 2 := by
  calc
    _ ≤ _ := dens1_antichain_dach hg hgG
    _ ≤ Tile.C6_1_5 a * 2 ^ (6 * a + 1) * ∑ p with p ∈ 𝔄,
        ∫⁻ y in E p, C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ * M14 𝔄 (q₆ a) g y * ‖g y‖ₑ := by
      gcongr with p mp; rw [← lintegral_const_mul _ hg.enorm]
      refine setLIntegral_mono' measurableSet_E fun x mx ↦ mul_le_mul_left ?_ _
      rw [Finset.mem_filter_univ] at mp
      refine dach_bound h𝔄 mp hg hgG <|
        ((E_subset_𝓘.trans Grid_subset_ball).trans (ball_subset_ball ?_)) mx
      change (4 : ℝ) * D ^ 𝔰 p ≤ _; gcongr; norm_num
    _ = Tile.C6_1_5 a * 2 ^ (6 * a + 1) * C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ *
        ∫⁻ y in ⋃ p ∈ 𝔄, E p, M14 𝔄 (q₆ a) g y * ‖g y‖ₑ := by
      rw [mul_assoc _ (C6_1_6 a : ℝ≥0∞), mul_assoc (_ * _), ← lintegral_const_mul'']; swap
      · exact (Measurable.maximalFunction.aemeasurable.mul
          hg.enorm.aemeasurable).restrict
      congr 1; simp_rw [← mul_assoc]
      rw [← lintegral_biUnion_finset _ (fun _ _ ↦ measurableSet_E)]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro p mp p' mp' hn
        simp_rw [Finset.coe_filter, Finset.mem_univ, true_and, setOf_mem_eq] at mp mp'
        exact not_not.mp ((tile_disjointness h𝔄 mp mp').mt hn)
    _ ≤ Tile.C6_1_5 a * 2 ^ (6 * a + 1) * C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ *
        ∫⁻ y, M14 𝔄 (q₆ a) g y * ‖g y‖ₑ := by gcongr; exact Measure.restrict_le_self
    _ ≤ Tile.C6_1_5 a * 2 ^ (6 * a + 1) * C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ *
        (eLpNorm (M14 𝔄 (q₆ a) g) 2 * eLpNorm g 2) := by
      conv_rhs => enter [2, 2]; rw [← eLpNorm_enorm]
      gcongr
      exact ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance
        Measurable.maximalFunction.aemeasurable hg.enorm.aemeasurable
    _ ≤ Tile.C6_1_5 a * 2 ^ (6 * a + 1) * C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ *
        (2 ^ (a + 2) * eLpNorm g 2 ^ 2) := by
      rw [sq, ← mul_assoc (_ ^ _)]
      gcongr
      exact M14_bound ((bcs_of_measurable_of_le_indicator_g hg hgG).memLp _)
    _ ≤ _ := by
      rw [mul_pow, mul_pow]; nth_rw 5 [← ENNReal.rpow_natCast]
      rw [← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) = 2⁻¹⁻¹ by norm_num, ← mul_inv,
        show 8 * a ^ 4 * 2⁻¹ = p₆ a by rw [p₆]; ring, mul_mul_mul_comm, ← mul_assoc]
      gcongr
      simp_rw [show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← ENNReal.coe_pow, ← ENNReal.coe_mul,
        ENNReal.coe_le_coe, le_C6_1_4 (four_le_a X)]

/-- Lemma 6.1.4. -/
lemma dens1_antichain (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (hf : Measurable f)
    (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g) (hgG : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ≤
      C6_1_4 a * dens₁ 𝔄 ^ (8 * a ^ 4 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have bf := bcs_of_measurable_of_le_indicator_f hf hfF
  have bg := bcs_of_measurable_of_le_indicator_g hg hgG
  calc
    _ ≤ ∫⁻ x, ‖adjointCarlesonSum 𝔄 g x‖ₑ * ‖f x‖ₑ := by
      rw [adjointCarlesonSum_adjoint bf bg]
      conv_rhs => enter [2, x]; rw [← RCLike.enorm_conj, ← enorm_mul]
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ eLpNorm (adjointCarlesonSum 𝔄 g) 2 * eLpNorm f 2 := by
      conv_rhs => rw [← eLpNorm_enorm, ← eLpNorm_enorm]
      exact ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance
        bg.adjointCarlesonSum.enorm.aestronglyMeasurable.aemeasurable
        bf.enorm.aestronglyMeasurable.aemeasurable
    _ ≤ _ := by
      rw [← mul_rotate, mul_comm (eLpNorm g 2 volume)]; gcongr
      grw [← ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < (2 : ℕ) by norm_num),
        ENNReal.rpow_natCast, ENNReal.rpow_natCast, dens1_antichain_sq h𝔄 hg hgG]

/-- The constant appearing in Proposition 2.0.3.
Has value `2 ^ (117 * a ^ 3)` in the blueprint. -/
def C2_0_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ ((𝕔 + 5 + 𝕔 / 8) * a ^ 3) / (q - 1)

variable (X) in
omit [TileStructure Q D κ S o] in
private lemma ineq_aux_2_0_3 :
    ((2 ^ ((𝕔 + 5 + 𝕔 / 8 : ℕ) * a ^ 3) : ℝ≥0) : ℝ≥0∞) ^ (q - 1) *
    (((2 ^ ((𝕔 + 3) * a ^ 3) : ℝ≥0) : ℝ≥0∞) * (nnq - 1)⁻¹) ^ (2 - q) ≤
    (2 ^ ((𝕔 + 5 + 𝕔 / 8 : ℕ) * a ^ 3) / (nnq - 1) : ℝ≥0) := by
  have hq1 : 0 ≤ q - 1 := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (nnq_mem_Ioc X).1.le)
  have hq2 : 0 ≤ 2 - q := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (nnq_mem_Ioc X).2)
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  calc
    _ = ((2 ^ ((𝕔 + 5 + 𝕔 / 8 : ℕ) * a ^ 3) : ℝ≥0) : ℝ≥0∞) ^ (q - 1) *
        (((2 ^ ((𝕔 + 3 + 0) * a ^ 3) : ℝ≥0) : ℝ≥0∞)) ^ (2 - q) * (nnq - 1)⁻¹ ^ (2 - q) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq2]; ring
    _ ≤ ((2 ^ ((𝕔 + 5 + 𝕔 / 8 : ℕ) * a ^ 3) : ℝ≥0) : ℝ≥0∞) ^ (q - 1) *
        (((2 ^ ((𝕔 + 5 + 𝕔 / 8 : ℕ) * a ^ 3) : ℝ≥0) : ℝ≥0∞)) ^ (2 - q) * (nnq - 1)⁻¹ := by
      have h11 : (1 + 1 : ℝ≥0) = 2 := by norm_num
      gcongr
      · norm_num
      · norm_num
      · norm_num
      · refine ENNReal.rpow_le_self_of_one_le ?_ (by linarith)
        rw [one_le_coe_iff, one_le_inv₀ (tsub_pos_iff_lt.mpr (nnq_mem_Ioc X).1), tsub_le_iff_right,
          h11]; exact (nnq_mem_Ioc X).2
    _ ≤ _ := by
      rw [div_eq_mul_inv, ENNReal.coe_mul, ← ENNReal.rpow_add_of_nonneg _ _ hq1 hq2,
        sub_add_sub_cancel', h21, ENNReal.rpow_one]

/-- Proposition 2.0.3. -/
theorem antichain_operator (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (hf : Measurable f)
    (hf1 : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ≤
      C2_0_3 a nnq * dens₁ 𝔄 ^ ((q - 1) / (8 * a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
        eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hq : (nnq : ℝ) = q := rfl
  have h21 : (2 : ℝ) - 1 = 1 := by norm_cast
  have h21' : (2 : ℝ≥0) - 1 = 1 := by norm_cast
  -- Eq. 6.1.47
  have heq : (nnqt⁻¹ - 2⁻¹) * (2 - q) = q⁻¹ - 2⁻¹ := by
    have hq0 : q ≠ 0 := by rw [← hq, NNReal.coe_ne_zero]; exact (nnq_pos _).ne'
    simp only [inv_div, NNReal.coe_div, NNReal.coe_add, hq, NNReal.coe_one, NNReal.coe_mul,
      NNReal.coe_ofNat]
    calc
      _ = ((q + 1) / (2 * q) - q / (2 * q)) * (2 - q) := by
        congr; nth_rewrite 1 [inv_eq_one_div, ← one_mul q, mul_div_mul_right 1 2 hq0]; rfl
      _ = q⁻¹ - 2⁻¹ := by ring_nf; simp [hq0]
  push_cast at heq
  by_cases hq2 : q = 2
  · have hnnq2 : nnq = 2 := by simp only [← NNReal.coe_inj, NNReal.coe_ofNat, ← hq2]; rfl
    simp only [hq2, h21, one_div, sub_self, ENNReal.rpow_zero, mul_one]
    apply (dens1_antichain h𝔄 hf hf1 hg hg1).trans
    gcongr
    simp only [C6_1_4, C2_0_3, hnnq2, h21', div_one, le_refl]
  · have hq2' : 0 < 2 - q :=
      sub_pos.mpr (lt_of_le_of_ne (NNReal.coe_le_coe.mpr (nnq_mem_Ioc X).2) hq2)
    -- Take the (2-q)-th power of 6.1.11
    have h2 := dens2_antichain h𝔄 hf1 hf hg1 hg
    rw [← ENNReal.rpow_le_rpow_iff hq2'] at h2
    simp only [mul_assoc] at h2
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq2'.le, ENNReal.mul_rpow_of_nonneg _ _ hq2'.le,
      ← ENNReal.rpow_mul (dens₂ 𝔄), heq] at h2
    -- Take and the (q-1)-th power of 6.1.22
    have h1 := dens1_antichain h𝔄 hf hf1 hg hg1
    have h1q : 0 < q - 1 := sub_pos.mpr (NNReal.coe_lt_coe.mpr (nnq_mem_Ioc X).1)
    rw [← ENNReal.rpow_le_rpow_iff h1q] at h1
    simp only [mul_assoc] at h1
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1q.le, ENNReal.mul_rpow_of_nonneg _ _ h1q.le,
      ← ENNReal.rpow_mul (dens₁ 𝔄)] at h1
    calc
      _ = ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ^ (q - 1) *
          ‖∫ x, conj (g x) * carlesonSum 𝔄 f x‖ₑ ^ (2 - q) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ h1q.le hq2'.le, sub_add_sub_cancel', h21,
          ENNReal.rpow_one]
      _ ≤ (C6_1_4 a ^ (q - 1) * (dens₁ 𝔄 ^ ((8 * ↑a ^ 4)⁻¹ * (q - 1)) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (q - 1))) *
          (C6_1_3 a nnq ^ (2 - q) * (dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (2 - q))) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C6_1_4 a ^ (q - 1) * C6_1_3 a nnq ^ (2 - q)) *
            dens₁ 𝔄 ^ ((8 * ↑a ^ 4)⁻¹ * (q - 1)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
          ((eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (q - 1) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (2 - q)) := by ring
      _ = (C6_1_4 a ^ (q - 1) * C6_1_3 a nnq ^ (2 - q)) *
            dens₁ 𝔄 ^ ((q - 1) / (8 * ↑a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
          eLpNorm f 2 volume * eLpNorm g 2 volume := by
        have hnorm : ((eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (q - 1) *
            (eLpNorm f 2 volume * eLpNorm g 2 volume) ^ (2 - q)) =
            eLpNorm f 2 volume * eLpNorm g 2 volume := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ h1q.le hq2'.le, sub_add_sub_cancel', h21,
            ENNReal.rpow_one]
        rw [div_eq_inv_mul, hnorm]
        ring
      _ ≤ _ := by
        gcongr
        simp only [C6_1_4, C6_1_3, ENNReal.coe_mul, C2_0_3]
        exact ineq_aux_2_0_3 X

/-- Version of the antichain operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function. -/
theorem antichain_operator' {A : Set X} (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    (hf : Measurable f) (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : A ⊆ G) :
    ∫⁻ x in A, ‖carlesonSum 𝔄 f x‖ₑ ≤
    C2_0_3 a nnq * dens₁ 𝔄 ^ ((q - 1) / (8 * a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * volume G ^ (1/2 : ℝ) := by
  have I (x : ℝ) : x / x ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp [hx]
  apply (lintegral_mono_set hA).trans
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  have bf := bcs_of_measurable_of_le_indicator_f hf hfF
  rw [← enorm_integral_starRingEnd_mul_eq_lintegral_enorm bf.carlesonSum.restrict.integrable]
  rw [← integral_indicator measurableSet_G]
  simp_rw [indicator_mul_left, ← Function.comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  apply (antichain_operator h𝔄 hf hfF
    (((measurable_carlesonSum hf).div (measurable_ofReal.comp (measurable_carlesonSum hf).norm)
      ).indicator measurableSet_G)
    (fun _ ↦ by simp [indicator]; split_ifs <;> simp [I])).trans
  gcongr
  calc
  _ ≤ eLpNorm (G.indicator (fun x ↦ 1) : X → ℝ) 2 volume :=
    eLpNorm_mono (fun x ↦ by simp only [indicator]; split_ifs <;> simp [I])
  _ ≤ _ := by
    rw [eLpNorm_indicator_const measurableSet_G (by norm_num) (by norm_num)]
    simp

/-- Version of the antichain operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function, and with the upper bound in terms
of `volume F` and `volume G`. -/
theorem antichain_operator_le_volume {A : Set X} (h𝔄 : IsAntichain (· ≤ ·) 𝔄)
    (hf : Measurable f) (hfF : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : A ⊆ G) :
    ∫⁻ x in A, ‖carlesonSum 𝔄 f x‖ₑ ≤
    C2_0_3 a nnq * dens₁ 𝔄 ^ ((q - 1) / (8 * a ^ 4)) * dens₂ 𝔄 ^ (q⁻¹ - 2⁻¹) *
    volume F ^ (1/2 : ℝ) * volume G ^ (1/2 : ℝ) := by
  apply (antichain_operator' h𝔄 hf hfF hA).trans
  gcongr
  calc
  _ ≤ eLpNorm (F.indicator (fun x ↦ 1) : X → ℝ) 2 volume :=
    eLpNorm_mono (fun x ↦ (hfF x).trans (le_abs_self _))
  _ ≤ _ := by
    rw [eLpNorm_indicator_const measurableSet_F (by norm_num) (by norm_num)]
    simp
