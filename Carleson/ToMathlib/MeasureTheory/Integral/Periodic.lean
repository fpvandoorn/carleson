import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Analysis.Convolution
import Carleson.ToMathlib.Topology.Instances.AddCircle

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

open scoped Convolution


section AE

variable {B : Type*} {p a : ℝ} [hp : Fact (0 < p)] (f : ℝ → B)

instance AddCircle.noAtoms_volume : NoAtoms (volume : Measure (AddCircle p)) where
  measure_singleton x := by simpa [hp.out.le] using AddCircle.volume_closedBall p (x := x) 0

theorem AddCircle.liftIoc_ae_eq_liftIco : liftIoc p a f =ᶠ[ae volume] liftIco p a f :=
  Filter.Eventually.mono (by simp [Filter.Eventually, ae]) (fun _ ↦ liftIoc_eq_liftIco_of_ne f)

end AE


section Measurability

variable {E : Type*} (p a : ℝ) [hp : Fact (0 < p)] {f : ℝ → E}

lemma AddCircle.map_subtypeVal_map_equivIoc :
    (volume.map (equivIoc p a)).map Subtype.val = volume.restrict (Ioc a (a + p)) := by
  have h : Measurable (equivIoc p a) := (AddCircle.measurableEquivIoc p a).measurable_toFun
  rw [← (AddCircle.measurePreserving_mk p a).map_eq]
  rw [Measure.map_map measurable_subtype_coe h, Measure.map_map (measurable_subtype_coe.comp h)]
  · exact (Measure.map_congr <| Filter.Eventually.mono (self_mem_ae_restrict measurableSet_Ioc) <|
      fun x hx ↦ AddCircle.liftIoc_coe_apply hx).trans Measure.map_id
  · exact fun _ ↦ id

namespace MeasureTheory

open AddCircle

variable {E : Type*} (p a : ℝ) [hp : Fact (0 < p)] {f : ℝ → E}

protected theorem AEStronglyMeasurable.liftIoc [TopologicalSpace E]
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (liftIoc p a f) :=
  (map_subtypeVal_map_equivIoc p a ▸ hf.restrict).comp_measurable
    measurable_subtype_coe |>.comp_measurable (AddCircle.measurableEquivIoc p a).measurable_toFun

protected theorem AEStronglyMeasurable.liftIco [TopologicalSpace E]
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (liftIco p a f) :=
  (hf.liftIoc p a).congr (liftIoc_ae_eq_liftIco f)

protected theorem AEMeasurable.liftIoc [MeasurableSpace E] (hf : AEMeasurable f) :
    AEMeasurable (liftIoc p a f) :=
  (map_subtypeVal_map_equivIoc p a ▸ hf.restrict).comp_measurable
    measurable_subtype_coe |>.comp_measurable (AddCircle.measurableEquivIoc p a).measurable_toFun

protected theorem AEMeasurable.liftIco [MeasurableSpace E] (hf : AEMeasurable f) :
    AEMeasurable (liftIco p a f) :=
  (hf.liftIoc p a).congr (liftIoc_ae_eq_liftIco f)

end MeasureTheory

end Measurability


namespace AddCircle

section Convolution

variable {𝕜 : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F] (L : E →L[𝕜] E' →L[𝕜] F)
  {f : ℝ → E} {g : ℝ → E'}

variable {T : ℝ} [hT : Fact (0 < T)] (a : ℝ)

theorem liftIco_convolution_liftIco (hf : f.Periodic T) (hg : g.Periodic T) :
    liftIco T a f ⋆[L] liftIco T a g = liftIco T a fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y)) := by
  refine funext (fun q ↦ QuotientAddGroup.induction_on q (fun x ↦ ?_))
  have : Periodic (fun x ↦ ∫ y in a..a+T, L (f y) (g (x-y))) T := by
    intro; refine integral_congr (fun _ _ ↦ ?_); rw [add_sub_right_comm, hg]
  rw [convolution, ← AddCircle.intervalIntegral_preimage T a, liftIco_coe_apply_of_periodic a this]
  refine integral_congr (fun y _ ↦ ?_)
  rw [AddCircle.liftIco_coe_apply_of_periodic a hf, ← AddCircle.liftIco_coe_apply_of_periodic a hg]
  rfl

theorem liftIoc_convolution_liftIoc (hf : f.Periodic T) (hg : g.Periodic T) :
    liftIoc T a f ⋆[L] liftIoc T a g = liftIoc T a fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y)) := by
  have : Periodic (fun x ↦ ∫ y in a..a+T, L (f y) (g (x-y))) T := by
    intro; refine integral_congr (fun _ _ ↦ ?_); rw [add_sub_right_comm, hg]
  rw [← liftIco_eq_liftIoc a a hf, ← liftIco_eq_liftIoc a a hg, ← liftIco_eq_liftIoc a a this]
  exact liftIco_convolution_liftIco L a hf hg

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
  exact (eLpNorm_comp_measurePreserving (hf.liftIoc T a) (AddCircle.measurePreserving_mk T a)).symm

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
