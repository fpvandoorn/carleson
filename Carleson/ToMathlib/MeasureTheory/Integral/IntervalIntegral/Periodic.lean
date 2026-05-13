module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

public section

namespace Function

namespace Periodic

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {E ε : Type*} [NormedAddCommGroup E] [TopologicalSpace ε] [ENormedAddMonoid ε]

variable [NormedSpace ℝ E]

variable {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ} {T : ℝ}

--TODO: use this in the proof of `intervalIntegral_add_eq` in mathlib?
/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
theorem setIntegral_Ioc_add_eq (hf : Periodic f T) (t s : ℝ) :
    ∫ x in Ioc t (t + T), f x = ∫ x in Ioc s (s + T), f x := by
  wlog! hT : 0 < T
  · rw [Ioc_eq_empty (by simpa), Ioc_eq_empty (by simpa)]
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]

theorem setLIntegral_Ioc_add_eq {f : ℝ → ℝ≥0∞} (hf : Periodic f T) (t s : ℝ) :
    ∫⁻ x in Ioc t (t + T), f x = ∫⁻ x in Ioc s (s + T), f x := by
  wlog! hT : 0 < T
  · rw [Ioc_eq_empty (by simpa), Ioc_eq_empty (by simpa)]
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setLIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s,
    (hf.comp enorm).map_vadd_zmultiples]

--TODO: the assumption `p ≠ ⊤` is not necessary; this case should be proved as well
theorem eLpNorm {T : ℝ} {s t : ℝ} {f : ℝ → ℂ}
  (periodic_f : f.Periodic T)
  {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    eLpNorm f p (volume.restrict (Ioc t (t + T))) = eLpNorm f p (volume.restrict (Ioc s (s + T))) := by
  unfold MeasureTheory.eLpNorm
  split_ifs with p_zero --p_top
  · rfl
  --· sorry
  · rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm, ]
    congr 1
    apply setLIntegral_Ioc_add_eq
    intro x
    simp only
    congr 2
    apply periodic_f

theorem aestronglyMeasurable {t T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
  (periodic_f : f.Periodic T) (hf : AEStronglyMeasurable f (volume.restrict (Ioc t (t + T)))) :
    AEStronglyMeasurable f := by
  rw [← Measure.restrict_univ (μ := volume), ← iUnion_Ioc_add_zsmul hT.out t]
  apply AEStronglyMeasurable.iUnion
  intro n
  have : AEStronglyMeasurable (f ∘ (fun x ↦ x - n • T))
      (volume.restrict (Ioc (t + n • T) (t + (n + 1) • T))) := by
    apply hf.comp_measurePreserving
    have : (Ioc (t + n • T) (t + (n + 1) • T)) = (fun x ↦ x - n • T) ⁻¹' (Ioc t (t + T)) := by
      rw [preimage_sub_const_Ioc, add_smul]
      ring_nf
    rw [this]
    apply MeasurePreserving.restrict_preimage (measurePreserving_sub_right _ _) measurableSet_Ioc
  convert this
  ext x
  simp only [comp_apply]
  rw [periodic_f.sub_zsmul_eq]

/-
theorem locallyIntegrable_of {T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
  (periodic_f : f.Periodic T) (hf : IntegrableOn f (Ioc 0 T)) :
    LocallyIntegrable f := by
  rw [← Measure.restrict_univ (μ := volume), ← iUnion_Ioc_zsmul hT.out]
  #check locallyIntegrableOn_iff_locallyIntegrable_restrict
  apply LocallyIntegrableOn.iUnion
  intro n
  have : AEStronglyMeasurable (f ∘ (fun x ↦ x - n • T))
      (volume.restrict (Ioc (n • T) ((n + 1) • T))) := by
    apply hf.comp_measurePreserving
    have : (Ioc (n • T) ((n + 1) • T)) = (fun x ↦ x - n • T) ⁻¹' (Ioc 0 T) := by
      rw [preimage_sub_const_Ioc, add_smul]
      ring_nf
    rw [this]
    apply MeasurePreserving.restrict_preimage (measurePreserving_sub_right _ _) measurableSet_Ioc
  convert this
  ext x
  simp only [comp_apply]
  rw [periodic_f.sub_zsmul_eq]
-/

end Periodic

end Function

open Set ENNReal

-- Analogous to `MeasureTheory.MemLp.memLp_liftIoc`
theorem MeasureTheory.eLpNorm_eq_eLpNorm_liftIoc {T : ℝ} [hT : Fact (0 < T)] {t : ℝ} {f : ℝ → ℂ}
  {p : ℝ≥0∞} (hf : AEStronglyMeasurable f (volume.restrict (Ioc t (t + T)))) :
    eLpNorm f p (volume.restrict (Ioc t (t + T))) = eLpNorm (AddCircle.liftIoc T t f) p volume := by
  simp only [AddCircle.liftIoc, Set.restrict_def, Function.comp_def]
  rw [← Function.comp_def, eLpNorm_comp_measurePreserving (g := f) (p := p) hf]
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T
