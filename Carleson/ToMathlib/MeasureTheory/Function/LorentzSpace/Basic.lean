import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.TriangleInequality

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory

def Lorentz {α ε : Type*} (p q : ℝ≥0∞) {m0 : MeasurableSpace α} (μ : Measure α) [NoAtoms μ]
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [ContinuousAdd ε] :
    AddSubmonoid (α → ε) where
  carrier := {f | MemLorentz f p q μ}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    use aestronglyMeasurable_zero
    convert ENNReal.zero_lt_top
    simp
  add_mem' := by
    intro f g hf hg
    apply hf.add hg

end MeasureTheory
