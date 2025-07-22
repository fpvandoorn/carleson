import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Carleson.ToMathlib.Misc -- for iSup_rpow

open MeasureTheory Set
open scoped ENNReal

variable {α ε E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε]

namespace MeasureTheory

section MapMeasure

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

theorem eLpNormEssSup_map_measure' [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.enorm hf

theorem eLpNorm_map_measure' [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · aesop
  by_cases hp_top : p = ∞
  · rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure' hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top]
  rw [lintegral_map' (hg.enorm.pow_const p.toReal) hf]
  rfl

theorem eLpNorm_comp_measurePreserving' {ν : Measure β} [MeasurableSpace E]
    [OpensMeasurableSpace E] (hg : AEMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure' (hf.map_eq ▸ hg) hf.aemeasurable

end MapMeasure

section Suprema

theorem eLpNormEssSup_iSup {α : Type*} {ι : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} (f : ι → α → ℝ≥0∞) :
    ⨆ n, eLpNormEssSup (f n) μ = eLpNormEssSup (⨆ n, f n) μ := by
  simp_rw [eLpNormEssSup, essSup_eq_sInf, enorm_eq_self]
  apply le_antisymm
  · refine iSup_le fun i ↦ le_sInf fun b hb ↦ sInf_le ?_
    simp only [iSup_apply, mem_setOf_eq] at hb ⊢
    exact nonpos_iff_eq_zero.mp <|le_of_le_of_eq
        (measure_mono fun ⦃x⦄ h ↦ lt_of_lt_of_le h (le_iSup (fun i ↦ f i x) i)) hb
  · apply sInf_le
    simp only [iSup_apply, mem_setOf_eq]
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ μ (⋃ i, {x | ⨆ n, sInf {a | μ {x | a < f n x} = 0} < f i x}) := by
      refine measure_mono fun x hx ↦ mem_iUnion.mpr ?_
      simp only [mem_setOf_eq] at hx
      exact lt_iSup_iff.mp hx
    _ ≤ _ := measure_iUnion_le _
    _ ≤ ∑' i, μ {x | sInf {a | μ {x | a < f i x} = 0} < f i x} := by
      gcongr with i; apply le_iSup _ i
    _ ≤ ∑' i, μ {x | eLpNormEssSup (f i) μ < ‖f i x‖ₑ} := by
      gcongr with i; rw [eLpNormEssSup, essSup_eq_sInf]; rfl
    _ = ∑' i, 0 := by congr with i; exact meas_eLpNormEssSup_lt
    _ = 0 := by simp

/-- Monotone convergence applied to eLpNorms. AEMeasurable variant.
  Possibly imperfect hypotheses, particularly on `p`. Note that for `p = ∞` the stronger
  statement in `eLpNormEssSup_iSup` holds. -/
theorem eLpNorm_iSup' {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    ⨆ n, eLpNorm (f n) p μ = eLpNorm (⨆ n, f n) p μ := by
  unfold eLpNorm
  split_ifs with hp hp'
  · simp
  · apply eLpNormEssSup_iSup
  · unfold eLpNorm'
    have := ENNReal.toReal_pos hp hp'
    rw [← iSup_rpow (by positivity), ← lintegral_iSup']
    · congr 2 with a; rw [← iSup_rpow (by positivity)]; simp
    · fun_prop
    · filter_upwards [h_mono] with a ha m n hmn
      beta_reduce; gcongr; simp only [enorm_eq_self]; apply ha hmn

end Suprema

end MeasureTheory
