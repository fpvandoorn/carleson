import Carleson.Calculations
import Carleson.ToMathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set Metric Function Topology NNReal ENNReal

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {r : ℝ}
variable {K : X → X → ℂ} {x x' : X} [IsOneSidedKernel a K]

lemma czOperator_bound {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (x : X) :
    ∃ (M : ℝ≥0), ∀ᵐ y ∂(volume.restrict (ball x r)ᶜ), ‖K x y * g y‖ ≤ M := by
  let M0 := (C_K a / volume (ball x r) * eLpNorm g ∞).toNNReal
  use M0
  rw [ae_iff, Measure.restrict_apply₀']
  · let M1 := (C_K a / volume (ball x r)).toNNReal
    let M2 := (eLpNorm g ∞).toNNReal
    have : { y | ¬‖K x y * g y‖ ≤ M0} ⊆ { y | ¬‖K x y‖ ≤ M1 ∨ ¬‖g y‖ ≤ M2} := by
      rw [setOf_subset_setOf]
      intro y
      contrapose!
      intro hy
      rw [norm_mul]
      trans M1 * M2
      · apply mul_le_mul hy.left hy.right
        case b0 | c0 => simp only [norm_nonneg, NNReal.zero_le_coe]

      apply le_of_eq
      norm_cast
      rw [← toNNReal_mul]
    rw [← Measure.restrict_apply₀']
    · apply measure_mono_null_ae this.eventuallyLE
      rw [setOf_or]
      apply measure_union_null
      · rw [← ae_iff]
        apply ae_restrict_of_forall_mem measurableSet_ball.compl
        intro y hy
        simp_rw [M1, ← ENNReal.toReal.eq_1, ← toReal_enorm]
        apply (ENNReal.toReal_le_toReal enorm_lt_top.ne ?_).mpr
        · apply enorm_K_le_ball_complement hy
        · exact (div_lt_top coe_ne_top ((measure_ball_pos volume x hr).ne.symm)).ne
      · simp_rw [← ae_iff, M2, ← ENNReal.toReal.eq_1, ← toReal_enorm,
          (ENNReal.toReal_le_toReal enorm_lt_top.ne (hg.eLpNorm_lt_top).ne), eLpNorm_exponent_top]
        apply ae_restrict_of_ae ae_le_eLpNormEssSup
    · exact measurableSet_ball.compl.nullMeasurableSet
  · exact measurableSet_ball.compl.nullMeasurableSet

omit [IsOneSidedKernel a K] in
@[fun_prop]
lemma czOperator_aestronglyMeasurable' (hK : Measurable (uncurry K))
    {g : X → ℂ} (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun x ↦ czOperator K r g x) := by
  unfold czOperator
  conv => arg 1; intro x; rw [← integral_indicator (by measurability)]
  let f := fun (x,z) ↦ (ball x r)ᶜ.indicator (fun y ↦ K x y * g y) z
  apply AEStronglyMeasurable.integral_prod_right' (f := f)
  unfold f
  apply AEStronglyMeasurable.indicator
  · apply Continuous.comp_aestronglyMeasurable₂ (by fun_prop) hK.aestronglyMeasurable
    exact hg.comp_snd
  · conv => arg 1; change {x : (X × X) | x.2 ∈ (ball x.1 r)ᶜ}
    simp_rw [mem_compl_iff, mem_ball, not_lt]
    apply measurableSet_le <;> fun_prop

@[fun_prop]
lemma czOperator_aestronglyMeasurable
    {g : X → ℂ} (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun x ↦ czOperator K r g x) :=
  czOperator_aestronglyMeasurable' measurable_K hg

/- Next lemma is useful for fun_prop in a context where it can not find the relevant measure to
apply `czOperator_aestronglyMeasurable`.
TODO: investigate -/
@[fun_prop]
lemma czOperator_aestronglyMeasurable_aux {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    AEStronglyMeasurable (fun x ↦ czOperator K r g x) :=
  czOperator_aestronglyMeasurable hg.aestronglyMeasurable

lemma czOperator_welldefined {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (x : X) :
    IntegrableOn (fun y => K x y * g y) (ball x r)ᶜ volume := by
  let Kxg := fun y ↦ K x y * g y
  have mKxg : AEStronglyMeasurable Kxg := by
    have : Measurable (K x) := measurable_K_right x
    fun_prop

  have tmp_Kxg {M : ℝ≥0} : ∀ y, ¬‖Kxg y‖ ≤ M → y ∈ support Kxg := by
    intro y
    contrapose!
    rw [notMem_support]
    intro hy
    rw [hy, norm_zero]
    simp only [NNReal.zero_le_coe]

  have bdd_Kxg : ∃ (M : ℝ), ∀ᵐ y ∂(volume.restrict ((ball x r)ᶜ ∩ support Kxg)), ‖Kxg y‖ ≤ M := by
    obtain ⟨M, hM⟩ := czOperator_bound (K := K) hg hr x
    use M
    rw [ae_iff, Measure.restrict_apply₀']
    · conv =>
        arg 1; arg 2;
        rw [← inter_assoc]
        refine Eq.symm (left_eq_inter.mpr ?_)
        · apply inter_subset_left.trans
          apply setOf_subset.mpr
          apply tmp_Kxg
      rw [← Measure.restrict_apply₀' (by measurability), ← ae_iff]
      exact hM
    · apply NullMeasurableSet.inter
      · exact measurableSet_ball.compl.nullMeasurableSet
      · exact mKxg.nullMeasurableSet_support

  obtain ⟨M, hM⟩ := bdd_Kxg

  apply integrableOn_of_integrableOn_inter_support measurableSet_ball.compl
  apply Measure.integrableOn_of_bounded
  · apply ne_top_of_le_ne_top
    · exact ne_of_lt hg.measure_support_lt
    · apply measure_mono
      trans support Kxg
      · exact inter_subset_right
      · exact support_mul_subset_right (K x) g
  · exact mKxg
  · exact hM

-- This could be adapted to state T_r is a linear operator but maybe it's not worth the effort
lemma czOperator_sub {f g : X → ℂ} (hf : BoundedFiniteSupport f) (hg : BoundedFiniteSupport g) (hr : 0 < r) :
    czOperator K r (f - g) = czOperator K r f - czOperator K r g := by
  ext x
  unfold czOperator
  simp_rw [Pi.sub_apply, mul_sub_left_distrib,
    integral_sub (czOperator_welldefined hf hr x) (czOperator_welldefined hg hr x)]

/-- Lemma 10.1.1 -/
lemma geometric_series_estimate {x : ℝ} (hx : 2 ≤ x) :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-n / x) ≤ 2 ^ x := by
  calc
    _ = ∑' (n : ℕ), ((2 : ℝ≥0∞) ^ (-x⁻¹)) ^ n := by
      congr! 2 with n
      rw [div_eq_mul_inv, neg_mul_comm, mul_comm, ENNReal.rpow_mul, ENNReal.rpow_natCast]
    _ = (1 - 2 ^ (-x⁻¹))⁻¹ := ENNReal.tsum_geometric _
    _ ≤ 2 * (ENNReal.ofReal x⁻¹)⁻¹ := by
      apply near_1_geometric_bound; rw [mem_Icc, inv_nonneg, inv_le_one_iff₀]
      exact ⟨by linarith, .inr (by linarith)⟩
    _ = ENNReal.ofReal (2 * x) := by
      rw [ofReal_inv_of_pos (by linarith), inv_inv, ofReal_mul zero_le_two, ofReal_ofNat]
    _ ≤ ENNReal.ofReal (2 ^ x) := by
      gcongr
      have key := @one_add_mul_self_le_rpow_one_add 1 (by norm_num) (x - 1) (by linarith)
      rw [mul_one, add_sub_cancel, one_add_one_eq_two] at key
      replace key := mul_le_mul_of_nonneg_left key zero_le_two
      rwa [← Real.rpow_one_add' (by linarith) (by linarith), add_sub_cancel] at key
    _ = _ := by rw [← ofReal_rpow_of_pos zero_lt_two, ofReal_ofNat]
