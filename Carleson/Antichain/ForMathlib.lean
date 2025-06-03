import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace MeasureTheory

/- -- [Mathlib.MeasureTheory.Integral.Prod]
theorem setIntegral_prod_swap {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E] [SFinite ν]
    [NormedSpace ℝ E] [SFinite μ] (s : Set α) (t : Set β) (f : α × β → E) :
    ∫ (z : β × α) in t ×ˢ s, f z.swap ∂ν.prod μ = ∫ (z : α × β) in s ×ˢ t, f z ∂μ.prod ν := by
  rw [← Measure.prod_restrict, ← Measure.prod_restrict, integral_prod_swap]

-- [Mathlib.MeasureTheory.Integral.Prod]
theorem IntegrableOn.swap {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E]{μ : Measure α} [SFinite μ] {ν : Measure β} [SFinite ν] {f : α × β → E}
    {s : Set α} {t : Set β} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (f ∘ Prod.swap) (t ×ˢ s) (ν.prod μ) := by
  rw [IntegrableOn, ← Measure.prod_restrict] at hf ⊢
  exact hf.swap -/


end MeasureTheory
