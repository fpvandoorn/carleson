import Carleson.Defs
import Carleson.ToMathlib.BoundedFiniteSupport

open MeasureTheory Set Metric Function Topology NNReal ENNReal

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {r : ℝ}
variable {K : X → X → ℂ} {x x' : X} [IsOneSidedKernel a K]

-- TODO move to ToMathlib, properly generalise
theorem integrableOn_of_integrableOn_inter_support {f : X → ℂ} {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (hf : IntegrableOn f (s ∩ support f) μ) :
    IntegrableOn f s μ := by
  apply IntegrableOn.of_forall_diff_eq_zero hf hs
  simp

-- Is this valuable? Not used right now
lemma memLp_top_K_on_ball_complement (hr : 0 < r) {x : X}:
    MemLp (K x) ∞ (volume.restrict (ball x r)ᶜ) := by
  constructor
  . exact (measurable_K_right x).aestronglyMeasurable
  . simp only [eLpNorm_exponent_top]
    apply eLpNormEssSup_lt_top_of_ae_enorm_bound
    . apply ae_restrict_of_forall_mem
      . measurability
      . intro y hy
        apply enorm_K_le_ball_complement' hr hy

lemma czoperator_welldefined {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (x : X):
    IntegrableOn (fun y => K x y * g y) (ball x r)ᶜ volume := by
  let Kxg := fun y ↦ K x y * g y
  have mKxg : AEStronglyMeasurable Kxg := by
    have : Measurable (K x) := measurable_K_right x
    fun_prop

  have tmp_Kxg {M : ℝ≥0} : ∀ y, ¬‖Kxg y‖ ≤ M → y ∈ support Kxg := by
    intro y
    contrapose!
    rw [nmem_support]
    intro hy
    rw [hy, norm_zero]
    simp only [NNReal.zero_le_coe]

  have bdd_Kxg : ∃ (M : ℝ), ∀ᵐ y ∂(volume.restrict ((ball x r)ᶜ ∩ support Kxg)), ‖Kxg y‖ ≤ M := by
    let M0 := (C_K a / volume (ball x r) * eLpNorm g ∞).toNNReal
    use M0
    rw [ae_iff, Measure.restrict_apply₀']
    . conv =>
        arg 1; arg 2;
        rw [← inter_assoc]
        refine Eq.symm (left_eq_inter.mpr ?_)
        . apply inter_subset_left.trans
          apply setOf_subset.mpr
          apply tmp_Kxg

      let M1 := (C_K a / volume (ball x r)).toNNReal
      let M2 := (eLpNorm g ∞).toNNReal
      have : { y | ¬‖Kxg y‖ ≤ M0} ⊆ { y | ¬‖K x y‖ ≤ M1 ∨ ¬‖g y‖ ≤ M2} := by
        rw [setOf_subset_setOf]
        intro y
        contrapose!
        intro hy
        rw [norm_mul]
        trans M1 * M2
        . apply mul_le_mul hy.left hy.right
          case b0 | c0 => simp only [norm_nonneg, NNReal.zero_le_coe]

        apply le_of_eq
        norm_cast
        rw [← toNNReal_mul]
      rw [← Measure.restrict_apply₀']
      . apply measure_mono_null_ae this.eventuallyLE
        rw [setOf_or]
        apply measure_union_null
        . rw [← ae_iff]
          apply ae_restrict_of_forall_mem measurableSet_ball.compl
          intro y hy
          simp_rw [M1, ← ENNReal.toReal.eq_1, ← toReal_enorm]
          apply (ENNReal.toReal_le_toReal enorm_lt_top.ne ?_).mpr
          . apply enorm_K_le_ball_complement hy
          . exact (div_lt_top coe_ne_top ((measure_ball_pos volume x hr).ne.symm)).ne
        . simp_rw [← ae_iff, M2, ← ENNReal.toReal.eq_1, ← toReal_enorm,
            (ENNReal.toReal_le_toReal enorm_lt_top.ne (hg.eLpNorm_lt_top).ne), eLpNorm_exponent_top]
          apply ae_restrict_of_ae ae_le_eLpNormEssSup
      . exact measurableSet_ball.compl.nullMeasurableSet
    . apply NullMeasurableSet.inter
      . exact measurableSet_ball.compl.nullMeasurableSet
      . exact mKxg.nullMeasurableSet_support

  obtain ⟨M, hM⟩ := bdd_Kxg

  apply integrableOn_of_integrableOn_inter_support measurableSet_ball.compl
  apply Measure.integrableOn_of_bounded
  . apply ne_top_of_le_ne_top
    . exact ne_of_lt hg.measure_support_lt
    . apply measure_mono
      trans support Kxg
      . exact inter_subset_right
      . exact support_mul_subset_right (K x) g
  . exact mKxg
  . exact hM
