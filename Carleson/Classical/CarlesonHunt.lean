module

public import Carleson.Classical.ClassicalCarleson
public import Carleson.ToMathlib.Dynamics.Ergodic.MeasurePreserving

/-! This file contains the Carleson-Hunt theorem, a generalization of `classical_carleson`. -/

public section

open MeasureTheory Real

noncomputable section

local notation "S_" => partialFourierSum

theorem carleson_hunt_two_pi [hT : Fact (0 < 2 * π)] {f : AddCircle (2 * π) → ℂ} {p : ENNReal}
  (hp : 1 < p) (hf : MemLp f p) :
    ∀ᵐ x, Filter.Tendsto (partialFourierSum' · f x) Filter.atTop (nhds (f x)) := by
  wlog meas_f : Measurable f generalizing f
  · rcases hf.1 with ⟨g, meas_g, hfg⟩
    have hg : MemLp g p volume := by
      rwa [memLp_congr_ae hfg.symm]
    have := this hg meas_g.measurable
    filter_upwards [hfg, this]
    intro x hx
    rw [hx]
    intro h
    convert h using 2 with N
    unfold partialFourierSum'
    congr with n x
    congr 2
    have hfg' : f =ᶠ[ae AddCircle.haarAddCircle] g := by
      convert hfg using 1
      exact (Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_ne_zero_iff.mpr Real.two_pi_pos)
        AddCircle.haarAddCircle).symm
    rw [fourierCoeff_congr_ae hfg']
  set g := fun (x : ℝ) ↦ f x
  have periodic_g : g.Periodic (2 * π) := by
    unfold g
    intro x
    simp
  have hg : MemLp g p (volume.restrict (Set.Ioc 0 (2 * π))) := by
    unfold g
    nth_rw 2 [← zero_add (2 * π)]
    constructor
    · apply (hf.1.comp_measurePreserving (AddCircle.measurePreserving_mk _ _))
    · rw [eLpNorm_eq_eLpNorm_liftIoc' hf.1]
      exact hf.2
  apply ae_tendsto_zero_of_distribution_le
  intro δ δpos ε εpos
  rcases exceptional_set_carleson periodic_g hp hg δpos εpos with ⟨N₀, hN₀⟩
  use N₀
  apply hN₀.trans'
  unfold distribution
  rw [Measure.restrict_apply' measurableSet_Ioc,
    ← AddCircle.volume_preimage_equivIoc (by exact (measurableSet_superlevelSet (by fun_prop)))]
  apply measure_mono
  intro x
  simp only [gt_iff_lt, enorm_eq_self, Set.mem_setOf_eq]
  intro hx
  simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq]
  convert hx using 5 with N hN
  unfold g
  simp only [AddCircle.coe_equivIoc, sub_right_inj]
  rw [← partialFourierSum'_eq_partialFourierSum_apply N _]
  · simp only [AddCircle.coe_equivIoc]
  · nth_rw 1 [← zero_add (2 * π)]
    apply Subtype.mem

/- Version of carleson_hunt with `volume` instead of `haarAddMeasure` in the assumption.-/
--TODO: decide whether we really want to keep the other (equivalent) version
theorem carleson_hunt' {T : ℝ} [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ENNReal} (hp : 1 < p)
  (hf : MemLp f p) :
    ∀ᵐ x, Filter.Tendsto (partialFourierSum' · f x) Filter.atTop (nhds (f x)) := by
  have : Fact (0 < 2 * π) := fact_iff.mpr Real.two_pi_pos
  set g := fun (x : AddCircle (2 * π)) ↦
    f (AddCircle.equivAddCircle (2 * π) T Real.two_pi_pos.ne' hT.out.ne' x)
  have hg : MemLp g p := by
    unfold g
    rw [← memLp_haarAddCircle_iff] at *
    apply hf.comp_measurePreserving AddCircle.measurePreserving_equivAddCircle
  have h := carleson_hunt_two_pi hp hg
  rw [AddCircle.volume_eq_smul_haarAddCircle] at *
  rw [Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_ne_zero_iff.mpr this.out)] at h
  apply Measure.ae_smul_measure
  convert AddCircle.measurePreserving_equivAddCircle.ae_comp h using 4 with x N
  · exact partialFourierSum'_comp_equivAddCircle.symm
  · unfold g
    congr
    exact (AddEquiv.symm_apply_eq
      (AddCircle.equivAddCircle (2 * π) T (two_pi_pos.ne') (hT.out.ne'))).mp rfl

/-- Classical theorem of Carleson and Hunt asserting a.e. convergence of the partial Fourier sums
for `L^p` functions for `p > 1`. This is a strengthening of `classical_carleson`, and not officially
part of the blueprint. -/
theorem carleson_hunt {T : ℝ} [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ENNReal} (hp : 1 < p)
  (hf : MemLp f p AddCircle.haarAddCircle) :
    ∀ᵐ x, Filter.Tendsto (partialFourierSum' · f x) Filter.atTop (nhds (f x)) :=
  carleson_hunt' hp hf.of_haarAddCircle

end
