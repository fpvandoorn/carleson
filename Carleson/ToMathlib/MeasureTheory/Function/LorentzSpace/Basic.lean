import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.TriangleInequality

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory


/-- TODO: basic results -/
def Lorentz {α ε : Type*} (p q : ℝ≥0∞) {m0 : MeasurableSpace α} (μ : Measure α) [NoAtoms μ]
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [ContinuousAdd ε] :
    AddSubmonoid (α →ₘ[μ] ε) where
  carrier := {f | eLorentzNorm f p q μ < ⊤}
  zero_mem' := by simp [eLorentzNorm_congr_ae AEEqFun.coeFn_zero, eLorentzNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLorentzNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLorentzNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]

end MeasureTheory
