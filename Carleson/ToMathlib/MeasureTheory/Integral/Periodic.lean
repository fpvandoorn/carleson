import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Analysis.Convolution
import Carleson.ToMathlib.Topology.Instances.AddCircle

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

open scoped Convolution

namespace AddCircle

variable {B : Type*}

section AE

variable {p a : ℝ} [hp : Fact (0 < p)] (f : ℝ → B)

instance noAtoms_volume : NoAtoms (volume : Measure (AddCircle p)) where
  measure_singleton x := by simpa [hp.out.le] using AddCircle.volume_closedBall p (x := x) 0

theorem liftIoc_eq_liftIco_of_ne {x : AddCircle p} (x_ne_a : x ≠ a) :
    liftIoc p a f x = liftIco p a f x := by
  let b := QuotientAddGroup.equivIcoMod hp.out a x
  have x_eq_b : x = ↑b := (QuotientAddGroup.equivIcoMod hp.out a).apply_eq_iff_eq_symm_apply.mp rfl
  have hb := mem_Ico.mp (Subtype.coe_prop b)
  rw [x_eq_b, liftIco_coe_apply (Subtype.coe_prop b)]
  exact liftIoc_coe_apply ⟨lt_of_le_of_ne hb.1 (x_ne_a <| · ▸ x_eq_b), hb.2.le⟩

theorem liftIoc_ae_eq_liftIco : liftIoc p a f =ᶠ[ae volume] liftIco p a f :=
  Filter.Eventually.mono (by simp [Filter.Eventually, ae]) (fun _ ↦ liftIoc_eq_liftIco_of_ne f)

end AE

section Measurability

variable (p a : ℝ) [hp : Fact (0 < p)] {f : ℝ → B}

theorem liftIoc_aestronglyMeasurable [TopologicalSpace B] (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (liftIoc p a f) := by
  have h : Measurable (equivIoc p a) := (AddCircle.measurableEquivIoc p a).measurable_toFun
  refine AEStronglyMeasurable.comp_measurable ?_ measurable_subtype_coe |>.comp_measurable h
  convert hf.restrict (s := Ioc a (a + p))
  rw [← (AddCircle.measurePreserving_mk p a).map_eq]
  rw [Measure.map_map measurable_subtype_coe h, Measure.map_map (measurable_subtype_coe.comp h)]
  · exact (Measure.map_congr <| Filter.Eventually.mono (self_mem_ae_restrict measurableSet_Ioc) <|
      fun x hx ↦ AddCircle.liftIoc_coe_apply hx).trans Measure.map_id
  · exact fun _ ↦ id

theorem liftIco_aestronglyMeasurable [TopologicalSpace B] (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (liftIco p a f) :=
  (liftIoc_aestronglyMeasurable p a hf).congr (liftIoc_ae_eq_liftIco f)

theorem liftIoc_aemeasurable [MeasurableSpace B] (hf : AEMeasurable f) :
    AEMeasurable (liftIoc p a f) := by
  have h : Measurable (equivIoc p a) := (AddCircle.measurableEquivIoc p a).measurable_toFun
  refine AEMeasurable.comp_measurable ?_ measurable_subtype_coe |>.comp_measurable h
  convert hf.restrict (s := Ioc a (a + p))
  rw [← (AddCircle.measurePreserving_mk p a).map_eq]
  rw [Measure.map_map measurable_subtype_coe h, Measure.map_map (measurable_subtype_coe.comp h)]
  · exact (Measure.map_congr <| Filter.Eventually.mono (self_mem_ae_restrict measurableSet_Ioc) <|
      fun x hx ↦ AddCircle.liftIoc_coe_apply (f := id (α := ℝ)) hx).trans Measure.map_id
  · exact fun _ ↦ id

theorem liftIco_aemeasurable [MeasurableSpace B] (hf : AEMeasurable f) :
    AEMeasurable (liftIco p a f) :=
  (liftIoc_aemeasurable p a hf).congr (liftIoc_ae_eq_liftIco f)

end Measurability

section Convolution

variable {𝕜 : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F] (L : E →L[𝕜] E' →L[𝕜] F)
  {f : ℝ → E} {g : ℝ → E'}

variable {T : ℝ} [hT : Fact (0 < T)] (a : ℝ)

theorem convolution_liftIco (hf : f.Periodic T) (hg : g.Periodic T) :
    liftIco T a f ⋆[L] liftIco T a g = liftIco T a fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y)) := by
  refine funext (fun q ↦ QuotientAddGroup.induction_on q (fun x ↦ ?_))
  have : Periodic (fun x ↦ ∫ y in a..a+T, L (f y) (g (x-y))) T := by
    intro; refine integral_congr (fun _ _ ↦ ?_); rw [add_sub_right_comm, hg]
  rw [convolution, ← AddCircle.intervalIntegral_preimage T a, liftIco_coe_apply_of_periodic a this]
  refine integral_congr (fun y _ ↦ ?_)
  rw [AddCircle.liftIco_coe_apply_of_periodic a hf, ← AddCircle.liftIco_coe_apply_of_periodic a hg]
  rfl

theorem convolution_liftIoc (hf : f.Periodic T) (hg : g.Periodic T) :
    liftIoc T a f ⋆[L] liftIoc T a g = liftIoc T a fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y)) := by
  have : Periodic (fun x ↦ ∫ y in a..a+T, L (f y) (g (x-y))) T := by
    intro; refine integral_congr (fun _ _ ↦ ?_); rw [add_sub_right_comm, hg]
  rw [← liftIco_eq_liftIoc a a hf, ← liftIco_eq_liftIoc a a hg, ← liftIco_eq_liftIoc a a this]
  exact convolution_liftIco L a hf hg

end Convolution

section eLpNorm

variable {𝕜 B : Type*} [NormedAddCommGroup B]

variable (T : ℝ) [hT : Fact (0 < T)] (a a' : ℝ) {f : ℝ → B} (hf : AEStronglyMeasurable f)
include hf

/-- The norm of the lift of a function `f` is equal to the norm of `f` on that period. -/
theorem eLpNorm_liftIoc (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIoc T a f) p = eLpNorm ((Set.Ioc a (a + T)).indicator f) p := by
  set I := Ioc a (a + T)
  have : I.indicator f = I.indicator (liftIoc T a f ∘ QuotientAddGroup.mk) := by
    ext x
    by_cases hx : x ∈ I
    · simpa [hx] using (liftIoc_coe_apply hx).symm
    · simp [hx]
  rw [this, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc]
  refine (eLpNorm_comp_measurePreserving (liftIoc_aestronglyMeasurable T a hf) ?_).symm
  exact AddCircle.measurePreserving_mk T a

/-- The norm of the lift of a function `f` is equal to the norm of `f` on that period. -/
theorem eLpNorm_liftIco (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIco T a f) p = eLpNorm ((Set.Ico a (a + T)).indicator f) p := by
  rw [eLpNorm_congr_ae (liftIoc_ae_eq_liftIco f).symm, eLpNorm_liftIoc T a hf,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ico,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc, restrict_Ico_eq_restrict_Ioc]

/-- The norm of the lift of a periodic function `f` is equal to the norm of `f` on any period. -/
theorem eLpNorm_liftIoc_of_periodic (hfT : Periodic f T) (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIoc T a f) p = eLpNorm ((Set.Ioc a' (a' + T)).indicator f) p := by
  rw [liftIoc_eq_liftIoc a a' hfT, eLpNorm_liftIoc T a' hf p]

/-- The norm of the lift of a periodic function `f` is equal to the norm of `f` on any period. -/
theorem eLpNorm_liftIco_of_periodic (hfT : Periodic f T) (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIco T a f) p = eLpNorm ((Set.Ico a' (a' + T)).indicator f) p := by
  rw [liftIco_eq_liftIco a a' hfT, eLpNorm_liftIco T a' hf p]

end eLpNorm

end AddCircle
