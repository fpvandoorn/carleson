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

theorem setLIntegral_Ioc_add_eq {f : ℝ → ε} (hf : Periodic f T) (t s : ℝ) :
    ∫⁻ x in Ioc t (t + T), ‖f x‖ₑ = ∫⁻ x in Ioc s (s + T), ‖f x‖ₑ := by
  wlog! hT : 0 < T
  · rw [Ioc_eq_empty (by simpa), Ioc_eq_empty (by simpa)]
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setLIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s,
    (hf.comp enorm).map_vadd_zmultiples]


end Periodic

end Function

open Set ENNReal

#check AddCircle.measurePreserving_mk


-- Analogous to `MeasureTheory.MemLp.memLp_liftIoc`
theorem MeasureTheory.eLpNorm_eq_eLpNorm_liftIoc {T : ℝ} [hT : Fact (0 < T)] {t : ℝ} {f : ℝ → ℂ}
  {p : ℝ≥0∞} (hf : AEStronglyMeasurable f (volume.restrict (Ioc t (t + T)))) :
    eLpNorm f p (volume.restrict (Ioc t (t + T))) = eLpNorm (AddCircle.liftIoc T t f) p volume := by
  simp only [AddCircle.liftIoc, Set.restrict_def, Function.comp_def]
  rw [← Function.comp_def, eLpNorm_comp_measurePreserving (g := f) (p := p) hf]
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T
