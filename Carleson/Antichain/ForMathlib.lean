import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.SetIntegral


namespace MeasureTheory

theorem setIntegral_prod_swap {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E] [SFinite ν]
    [NormedSpace ℝ E] [SFinite μ] {s : Set α} (hs : MeasurableSet s) {t : Set β}
    (ht : MeasurableSet t) (f : α × β → E) :
    ∫ (z : β × α) in t ×ˢ s, f z.swap ∂ν.prod μ = ∫ (z : α × β) in s ×ˢ t, f z ∂μ.prod ν := by
  have hswap : (t ×ˢ s).indicator (fun z : β × α ↦ f z.swap) =
      (fun z : β × α ↦ ((s ×ˢ t).indicator f) z.swap) := by
    ext z
    simp only [Set.indicator, Set.mem_prod, Prod.fst_swap, Prod.snd_swap]
    aesop
  rw [← integral_indicator (hs.prod ht), ← integral_indicator (ht.prod hs), hswap,
    integral_prod_swap]



/- theorem setIntegral_smul {α : Type u_1} {𝕜 : Type u_4} [NontriviallyNormedField 𝕜] {G : Type u_5} [NormedAddCommGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α} {μ : Measure α} [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G] (c : 𝕜) (f : α → G) :
∫ (a : α), c • f a ∂μ = c • ∫ (a : α), f a ∂μ := sorry -/
/-
theorem setIntegral_mul_left {X L : Type*} [MeasurableSpace X] [RCLike L]
    {s : Set X} {μ : Measure X} (r : L) (f : X → L) :
    ∫ (x : X) in s, r * f x ∂μ = r * ∫ (x : X) in s, f x ∂μ := by
  exact integral_mul_left r f

theorem setIntegral_mul_right {X L : Type*} [MeasurableSpace X] [RCLike L]
    {s : Set X} {μ : Measure X} (r : L) (f : X → L) :
    ∫ (x : X) in s, f x * r ∂μ = (∫ (x : X) in s, f x ∂μ) * r := by
  simp only [mul_comm]; exact setIntegral_mul_left r f -/

theorem IntegrableOn.swap {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E]{μ : Measure α} [SFinite μ] {ν : Measure β} [SFinite ν] {f : α × β → E}
    {s : Set α} {t : Set β} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (f ∘ Prod.swap) (t ×ˢ s) (ν.prod μ) := by
  rw [IntegrableOn, ← Measure.prod_restrict] at hf ⊢
  exact MeasureTheory.Integrable.swap hf

end MeasureTheory
