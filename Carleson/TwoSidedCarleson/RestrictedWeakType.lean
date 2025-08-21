import Carleson.ToMathlib.RealInterpolation.LorentzInterpolation
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.TwoSidedCarleson.MainTheorem

/-! This file contains a reformulation of Theorem 10.0.1.
It is not officially part of the blueprint. -/


open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Reformulations of Theorem 10.0.1 -/

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_restricted_weak_type (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2)
  (hqq' : q.HolderConjugate q')
  (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
      HasRestrictedWeakType (carlesonOperator K) q q' volume volume (C10_0_1 a q) := by
  unfold HasRestrictedWeakType
  intro F G hF F_finite hG G_finite
  constructor
  · sorry --TODO: hopefully, this is already done somewhere
    -- or check if maybe this can be removed from the definition of HasRestrictedWeakType
  rw [eLpNorm_one_eq_lintegral_enorm, mul_assoc, mul_comm (volume _ ^ _), ← mul_assoc]
  simp_rw [enorm_eq_self]
  simp only [toReal_inv, coe_toReal]
  apply two_sided_metric_carleson ha hq hqq' hF hG hT
  · exact (measurable_indicator_const_iff 1).mpr hF
  · intro x
    unfold indicator
    split_ifs <;> simp

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_strong_type (ha : 4 ≤ a) (hq : q ∈ Ioo 1 2)
    (hqq' : q.HolderConjugate q')
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
      HasStrongType (carlesonOperator K) q q volume volume
        ((C_LorentzInterpolation q q q q q (4 * C10_0_1 a q  / q) (4 * C10_0_1 a q  / q) 1 q)) := by
  --TODO: change parameters of constant to something reasonable
  have : HasLorentzType (carlesonOperator K) q 1 q ⊤ volume volume (4 * (C10_0_1 a q) / q) := by
    apply (two_sided_metric_carleson_restricted_weak_type ha (mem_Ioc_of_Ioo hq) hqq' hT).hasLorentzType
    · simpa
    · intro f g x hf hg
      simp only [enorm_eq_self]
      --TODO: write some lemma carlesonOperator_add
      sorry
    · intro a f x
      simp only [enorm_eq_self]
      apply le_of_eq
      --TODO: write lemma carlesonOperator_const_smul (')
      --convert carlesonOperator_const_smul K f a
      sorry
    · intro f fs f_locInt h_meas h_lim G
      rename_i m d kernel cf cancel
      calc _
        _ ≤ eLpNorm (fun x ↦ Filter.liminf (fun n ↦ carlesonOperator K (fs n) x) Filter.atTop) 1 (volume.restrict G) := by
          apply eLpNorm_mono_enorm
          intro x
          simp only [enorm_eq_self]
          have : IsOneSidedKernel a K := by infer_instance
          set kpd : KernelProofData a K := KernelProofData.mk d ha cf this
          apply carlesonOperator_le_liminf_carlesonOperator_of_tendsto (norm ∘ f) h_meas _ f_locInt.norm h_lim
          -- !! TODO: add this as an assumption at the appropriate place !!
          sorry
        _ ≤ Filter.liminf (fun n ↦ eLpNorm (carlesonOperator K (fs n)) 1 (volume.restrict G)) Filter.atTop := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          simp_rw [eLpNorm_one_eq_lintegral_enorm, enorm_eq_self]
          apply lintegral_liminf_le'
          intro n
          apply AEMeasurable.restrict
          sorry --TODO: find / show lemma about measurability of the Carleson operator
      apply Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
  /- Apply `exists_hasLorentzType_real_interpolation` and `MemLorentz_nested` here,
  or just directly write another version of real interpolation that directly gives strong type.
  -/
  have helper : (4 * (C10_0_1 a q) / q) = ENNReal.ofNNReal (4 * (C10_0_1 a q) / q) := by
    sorry
  rw [helper] at this
  --norm_cast at this
  rw [hasStrongType_iff_hasLorentzType]
  convert exists_hasLorentzType_real_interpolation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ this _ _ _

end
