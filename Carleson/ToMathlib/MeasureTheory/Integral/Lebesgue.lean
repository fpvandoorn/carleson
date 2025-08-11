import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open ENNReal

namespace MeasureTheory

open SimpleFunc

/-- Generalization of `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral` assuming a.e.
measurability of `f` -/
theorem lintegral_eq_iSup_eapprox_lintegral' {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ENNReal} (hf : AEMeasurable f μ) :
    ∫⁻ (a : α), f a ∂μ = ⨆ (n : ℕ), (eapprox (hf.mk f) n).lintegral μ :=
  calc
    _ = ∫⁻ a, hf.mk f a ∂μ                               := lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, ⨆ n, (eapprox (hf.mk f) n : α → ℝ≥0∞) a ∂μ := by
      simp [iSup_eapprox_apply hf.measurable_mk]
    _ = ⨆ n, ∫⁻ a, eapprox (hf.mk f) n a ∂μ              :=
      lintegral_iSup (fun _ ↦ SimpleFunc.measurable _) (fun _ _ h ↦ monotone_eapprox (hf.mk f) h)
    _ = ⨆ n, (eapprox (hf.mk f) n).lintegral μ           := by simp [lintegral_eq_lintegral]

/-- Generalization of `MeasureTheory.lintegral_comp` assuming a.e. measurability of `f` and `g` -/
theorem lintegral_comp' {α : Type*} {β : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace β] {f : β → ENNReal} {g : α → β} (hf : AEMeasurable f (μ.map g))
    (hg : AEMeasurable g μ) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂μ.map g := by
  rw [μ.map_congr hg.ae_eq_mk] at hf ⊢
  calc  ∫⁻ a, (f ∘ g) a ∂μ
    _ = ∫⁻ a, (hf.mk f ∘ hg.mk g) a ∂μ   := by
      rw [lintegral_congr_ae (hg.ae_eq_mk.fun_comp f)]
      exact lintegral_congr_ae (ae_of_ae_map hg.measurable_mk.aemeasurable hf.ae_eq_mk)
    _ = ∫⁻ a, hf.mk f a ∂μ.map (hg.mk g) := lintegral_comp hf.measurable_mk hg.measurable_mk
    _ = ∫⁻ a, f a ∂μ.map (hg.mk g)       := lintegral_congr_ae hf.ae_eq_mk.symm

lemma lintegral_set_mono_fn {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x ∈ s, f x ≤ g x) :
    ∫⁻ (a : α) in s, f a ∂μ ≤ ∫⁻ (a : α) in s, g a ∂μ := by
  rw [← lintegral_indicator hs, ← lintegral_indicator hs]
  apply lintegral_mono
  intro x
  unfold Set.indicator
  split
  · rename_i hxs
    exact hfg x hxs
  · rfl

end MeasureTheory
