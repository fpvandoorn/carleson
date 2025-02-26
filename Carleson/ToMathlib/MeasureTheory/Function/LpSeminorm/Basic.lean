import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic

open MeasureTheory
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
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure' hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top]
  rw [lintegral_map' (hg.enorm.pow_const p.toReal) hf]
  rfl

theorem eLpNorm_comp_measurePreserving' {ν : Measure β} [MeasurableSpace E]
    [OpensMeasurableSpace E] (hg : AEMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure' (hf.map_eq ▸ hg) hf.aemeasurable

end MapMeasure

end MeasureTheory
