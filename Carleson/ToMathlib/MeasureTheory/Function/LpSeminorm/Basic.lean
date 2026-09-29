module

public import Carleson.ToMathlib.Misc

public section -- for iSup_rpow

-- Upstreaming status: lemmas seem useful (mostly minor modifications of mathlib),
-- a lot is ready to go already

open MeasureTheory Set
open scoped ENNReal

variable {α ε E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε]

namespace MeasureTheory

section MapMeasure

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

-- replace the unprimed mathlib version
theorem eLpNormEssSup_map_measure' [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.enorm hf

theorem aestronglyMeasurable_map_iff_of_aemeasurable [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable g (Measure.map f μ) ↔ AEStronglyMeasurable (g ∘ f) μ := by
  refine ⟨fun h ↦ h.comp_aemeasurable hf, fun h ↦ ?_⟩
  obtain ⟨t, ht, hgt⟩ := h.isSeparable_ae_range
  apply AEStronglyMeasurable.comp_aemeasurable (g := id) _ hg
  apply aestronglyMeasurable_id_of_isSeparable ht.closure
  rw [← mem_ae_iff, AEMeasurable.map_map_of_aemeasurable hg hf,
    mem_ae_map_iff (hg.comp_aemeasurable hf) isClosed_closure.measurableSet]
  filter_upwards [hgt] with x hx using subset_closure hx

-- replace the unprimed mathlib version
theorem eLpNorm_map_measure' [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact eLpNorm_map_measure hgm hf
  rw [eLpNorm_of_not_aestronglyMeasurable hgm, eLpNorm_of_not_aestronglyMeasurable
    ((aestronglyMeasurable_map_iff_of_aemeasurable hg hf).not.mp hgm)]

-- replace the unprimed version
theorem eLpNorm_comp_measurePreserving' {ν : Measure β} [MeasurableSpace E]
    [OpensMeasurableSpace E] (hg : AEMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure' (hf.map_eq ▸ hg) hf.aemeasurable

end MapMeasure

section Suprema

theorem eLpNormEssSup_iSup {α : Type*} {ι : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} (f : ι → α → ℝ≥0∞) :
    eLpNormEssSup (fun x => ⨆ n, f n x) μ = ⨆ n, eLpNormEssSup (f n) μ := by
  simp_rw [eLpNormEssSup, essSup_eq_sInf, enorm_eq_self]
  apply le_antisymm
  · apply sInf_le
    simp only [mem_ofPred_eq]
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ μ (⋃ i, {x | ⨆ n, sInf {a | μ {x | a < f n x} = 0} < f i x}) := by
      refine measure_mono fun x hx ↦ mem_iUnion.mpr ?_
      simp only [mem_ofPred_eq] at hx
      exact lt_iSup_iff.mp hx
    _ ≤ _ := measure_iUnion_le _
    _ ≤ ∑' i, μ {x | sInf {a | μ {x | a < f i x} = 0} < f i x} := by
      gcongr with i; apply le_iSup _ i
    _ ≤ ∑' i, μ {x | eLpNormEssSup (f i) μ < ‖f i x‖ₑ} := by
      gcongr with i
      · rw [eLpNormEssSup, essSup_eq_sInf]; rfl
      · simp
    _ = ∑' i, 0 := by congr with i; exact meas_eLpNormEssSup_lt
    _ = 0 := by simp
  · refine iSup_le fun i ↦ le_sInf fun b hb ↦ sInf_le ?_
    simp only [mem_ofPred_eq] at hb ⊢
    exact nonpos_iff_eq_zero.mp <|le_of_le_of_eq
        (measure_mono fun ⦃x⦄ h ↦ lt_of_lt_of_le h (le_iSup (fun i ↦ f i x) i)) hb

-- XXX: why does the lemma before assume a countable indexing type and this work with ℕ?
-- make consistent!
/-- Monotone convergence applied to eLpNorms. AEMeasurable variant.
  Possibly imperfect hypotheses, particularly on `p`. Note that for `p = ∞` the stronger
  statement in `eLpNormEssSup_iSup` holds. -/
theorem eLpNorm_iSup' {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    eLpNorm (fun x => ⨆ n, f n x) p μ = ⨆ n, eLpNorm (f n) p μ := by
  have hf' : ∀ n, AEStronglyMeasurable (f n) μ := fun n ↦ (hf n).aestronglyMeasurable
  have hsup : AEStronglyMeasurable (fun x => ⨆ n, f n x) μ :=
    (AEMeasurable.iSup hf).aestronglyMeasurable
  by_cases hp : p = 0
  · simp [hp, eLpNorm_exponent_zero hsup, eLpNorm_exponent_zero (hf' _)]
  by_cases hp' : p = ∞
  · simp_rw [hp', eLpNorm_exponent_top hsup, eLpNorm_exponent_top (hf' _), eLpNormEssSup_iSup f]
  · have hp0 := ENNReal.toReal_pos hp hp'
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hsup,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' (hf' _), enorm_eq_self, iSup_rpow hp0,
      lintegral_iSup' (fun n ↦ (hf n).pow_const _) (h_mono.mono fun x hx m n hmn ↦ ENNReal.rpow_le_rpow (hx hmn) hp0.le),
      iSup_rpow (one_div_pos.2 hp0)]

end Suprema

section Indicator

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {c : ε} {s : Set α}
  {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']

--complements the mathlib lemma eLpNormEssSup_indicator_const_eq
lemma eLpNormEssSup_indicator_const_eq' {s : Set α} {c : ε} (hμs : μ s = 0) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ = 0 := by
  rw [eLpNormEssSup_congr_ae (indicator_meas_zero hμs), eLpNormEssSup_zero]

end Indicator

section ENormSMulClass

open Filter

variable {𝕜 : Type*} --[NormedRing 𝕜]
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMul NNReal ε] [ENorm 𝕜]
  [ENormSMulClass NNReal ε]
  {c : NNReal} {f : α → ε}

theorem eLpNorm'_const_smul_le'' (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ ↦ le_of_eq (enorm_smul ..)) hq

theorem eLpNormEssSup_const_smul_le'' : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])

theorem MemLp.const_smul'' [ContinuousConstSMul NNReal ε] (hf : MemLp f p μ) :
    MemLp (c • f) p μ :=
  hf.of_enorm_le_mul (hf.aestronglyMeasurable.const_smul c) (.of_forall fun _ ↦ (enorm_smul ..).le)

theorem MemLp.const_mul'' [ContinuousConstSMul NNReal ε] (hf : MemLp f p μ) :
    MemLp (fun x => c • f x) p μ :=
  hf.const_smul''

end ENormSMulClass

section Lp

variable {ε : Type*} [TopologicalSpace ε] [ENorm ε]

lemma MemLp.eLpNormEssSup_lt_top {f : α → ε} (hu : MemLp f ⊤ μ) :
    eLpNormEssSup f μ < ⊤ :=
  eLpNormEssSup_le_eLpNorm_top.trans_lt hu

end Lp

end MeasureTheory
