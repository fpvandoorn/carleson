module

public import Carleson.Classical.Approximation
public import Carleson.Classical.CarlesonHuntBasic
public import Carleson.Classical.ControlApproximationEffect

/-! This file contains the Carleson-Hunt theorem, a generalization of `classical_carleson`. -/

open MeasureTheory Real ENNReal Filter Topology

public noncomputable section

local notation "S_" => partialFourierSum

section Real

section TwoPiPos

local instance : Fact (0 < 2 * π) where
  out := two_pi_pos

/- Theorem 1.1 (Classical Carleson) -/
theorem exceptional_set_carleson {f : ℝ → ℂ} (periodic_f : f.Periodic (2 * π))
  {q : ℝ≥0∞} (hq : 1 < q) (hf : MemLp f q (volume.restrict (Set.Ioc 0 (2 * π))))
  {δ ε : NNReal} (δpos : 0 < δ) (εpos : 0 < ε) :
    ∃ N₀, distribution (fun x ↦ ⨆ N > N₀, ‖f x - S_ N f x‖ₑ) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  set p := (min (3 / 2) q).toNNReal with p_def
  have : min (3 / 2) q ≠ ⊤ := by
    apply ne_of_lt
    rw [min_lt_iff]
    left
    refine div_lt_top (by simp) (by simp)
  have hp : p ∈ Set.Ioo 1 2 := by
    rw [p_def]
    simp only [Set.mem_Ioo]
    constructor
    · rw [← coe_lt_iff_lt_toNNReal this, lt_min_iff]
      simp only [ENNReal.coe_one]
      symm
      use hq
      exact (ENNReal.lt_div_iff_mul_lt (by simp) (by simp)).mpr (by simp; norm_num)
    · apply toNNReal_lt_of_lt_coe
      simp only [coe_ofNat, inf_lt_iff]
      left
      refine div_lt_of_lt_mul ?_
      norm_num
  have hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
    apply MemLp.mono_exponent hf
    rw [p_def, coe_toNNReal this]
    exact min_le_right _ _
  have meas_f : AEStronglyMeasurable f :=
    periodic_f.aestronglyMeasurable (t := 0) (by simp [hf.1])
  have one_lt_p : (1 : ENNReal) < p := by simp [hp.1]
  have δ2pos : 0 < δ / 2 := by positivity
  have δ4pos : 0 < δ / 4 := by positivity
  have ε2pos : 0 < ε / 2 := by positivity
  have ε4pos : 0 < ε / 4 := by positivity
  /- Approximate f by a smooth f₀. -/
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ :=
    close_smooth_approx_periodic_Lp one_lt_p.le (by simp) hf
      (lt_min (C_distribution_le_of_eLpNorm_le_pos (p := p) δ4pos ε2pos)
        (C_control_approximation_effect_pos (p := p) δ2pos ε2pos))
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀
    ((contDiff_infty.mp (contDiff_f₀)) 2) δ4pos
  /- This is a classical "epsilon third" argument. -/
  use N₀
  have : ∀ᶠx in (ae (volume.restrict (Set.Ioc 0 (2 * π)))), ⨆ N > N₀, ‖f x - S_ N f x‖ₑ
      ≤ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    apply iSup_le
    intro N
    apply iSup_le
    intro hN
    calc ‖f x - S_ N f x‖ₑ
      _ = ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x) + (S_ N f₀ x - S_ N f x)‖ₑ := by ring_nf
      _ ≤ ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x)‖ₑ + ‖S_ N f₀ x - S_ N f x‖ₑ := enorm_add_le ..
      _ ≤ ‖f x - f₀ x‖ₑ + ‖f₀ x - S_ N f₀ x‖ₑ + ‖S_ N f₀ x - S_ N f x‖ₑ :=
        add_le_add_left (enorm_add_le ..) _
      _ ≤ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ := by
        gcongr
        · exact le_iSup₂_of_le N hN (le_of_eq rfl)
        · apply le_iSup_of_le N
          rw [partialFourierSum_sub (contDiff_f₀.continuous.intervalIntegrable _ _)]
          · rfl
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
          apply hf.integrable (by simp [hp.1.le])
  calc _
    _ ≤ distribution
        (fun x ↦ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ)
        ((δ / 4) + (δ / 4) + (δ / 2)) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_mono
      · filter_upwards [this] with x hx
        simp [hx]
      · norm_cast
        ring_nf
        rfl
    _ ≤ distribution (fun x ↦ ‖f x - f₀ x‖ₑ) (δ / 4) (volume.restrict (Set.Ioc 0 (2 * π)))
        + distribution (fun x ↦ ⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) (δ / 4) (volume.restrict (Set.Ioc 0 (2 * π)))
        + distribution (fun x ↦ ⨆ N, ‖S_ N (f₀ - f) x‖ₑ) (δ / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_add_le.trans
      gcongr
      exact distribution_add_le
    _ ≤ ε / 2 + 0 + ε / 2 := by
      gcongr
      · norm_cast
        apply distribution_le_of_eLpNorm_le (p := p) (by positivity) (by positivity [hp.1])
          (meas_f.sub contDiff_f₀.continuous.aestronglyMeasurable).enorm.aestronglyMeasurable.restrict
        simp only [eLpNorm_enorm]
        apply hf₀.trans
        simp
      · simp only [gt_iff_lt, nonpos_iff_eq_zero]
        rw [distribution_eq_zero_iff]
        apply essSup_le_of_ae_le _
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with x hx
        simp only [enorm_eq_self, iSup_le_iff]
        intro N hN
        rw [enorm_eq_nnnorm, ← nnnorm_norm]
        norm_cast
        calc _
          _ ≤ ‖((δ / 4) : ℝ)‖₊ := by
            apply nnnorm_le_nnnorm (by simp)
            exact hN₀ N hN x (Set.Ioc_subset_Icc_self hx)
          _ = δ / 4 := by simp
      · norm_cast
        apply control_approximation_effect (ε := ε / 2) δ2pos
          (contDiff_f₀.continuous.aestronglyMeasurable.sub meas_f) (periodic_f₀.sub periodic_f) hp
        rw [eLpNorm_sub_comm]
        apply hf₀.trans
        simp
    _ = ε := by simp

end TwoPiPos

theorem carleson_hunt_interval {f : ℝ → ℂ} (periodic_f : f.Periodic (2 * π))
  {p : ℝ≥0∞} (hp : 1 < p) (hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π)))) :
    ∀ᵐ x ∂volume.restrict (Set.Ioc 0 (2 * π)),
      Tendsto (S_ · f x) atTop (𝓝 (f x)) := by
  apply ae_tendsto_zero_of_distribution_le
  intro δ δpos ε εpos
  exact exceptional_set_carleson periodic_f hp hf δpos εpos

/- **Carleson's theorem** asserting a.e. point-wise convergence of the partial Fourier sums for
periodic L^p functions, p > 1. -/
theorem carleson_hunt_real {f : ℝ → ℂ} (periodic_f : f.Periodic (2 * π))
  {p : ℝ≥0∞} (hp : 1 < p) (hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π)))) :
    ∀ᵐ x, Tendsto (S_ · f x) atTop (𝓝 (f x)) := by
  -- Reduce to a.e. convergence on [0,2π]
  apply @Function.Periodic.ae_of_ae_restrict _ two_pi_pos 0
  · rw [Function.Periodic]
    intro x
    conv => pattern S_ _ _ _; rw [partialFourierSum_periodic]
    conv => pattern f _; rw [periodic_f]
  apply ae_restrict_of_ae_eq_of_ae_restrict Ico_ae_eq_Icc.symm
  rw [zero_add]
  -- Show a.e. convergence on [0,2π]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  exact carleson_hunt_interval periodic_f hp hf

/- Proves that the old, weak version of classical Carleson is implied by the L^p version. -/
theorem classical_carleson_from_carleson_hunt_real : ClassicalCarleson := by
  unfold ClassicalCarleson
  intro f continuous_f periodic_f
  apply carleson_hunt_real (p := ⊤) periodic_f (by simp)
  rcases continuous_bounded continuous_f.continuousOn with ⟨C, hC⟩
  apply memLp_top_of_bound (C := C) continuous_f.measurable.aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with x hx
  apply hC _ (Set.Ioc_subset_Icc_self hx)

end Real

section AddCircle

section TwoPiPos

local instance : Fact (0 < 2 * π) where
  out := two_pi_pos

theorem carleson_hunt_two_pi {f : AddCircle (2 * π) → ℂ} {p : ℝ≥0∞} (hp : 1 < p) (hf : MemLp f p) :
    ∀ᵐ x, Tendsto (partialFourierSum' · f x) atTop (𝓝 (f x)) := by
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
      exact (Measure.ae_ennreal_smul_measure_eq (ofReal_ne_zero_iff.mpr two_pi_pos)
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
  simp only [AddCircle.coe_equivIoc]
  rw [← partialFourierSum'_eq_partialFourierSum_apply N _]
  · simp only [AddCircle.coe_equivIoc]
  · nth_rw 1 [← zero_add (2 * π)]
    apply Subtype.mem

/- Version of carleson_hunt with `volume` instead of `haarAddMeasure` in the assumption.-/
--TODO: decide whether we really want to keep the other (equivalent) version
theorem carleson_hunt' {T : ℝ} [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ℝ≥0∞} (hp : 1 < p)
  (hf : MemLp f p) :
    ∀ᵐ x, Tendsto (partialFourierSum' · f x) atTop (𝓝 (f x)) := by
  set g := fun (x : AddCircle (2 * π)) ↦
    f (AddCircle.equivAddCircle (2 * π) T two_pi_pos.ne' hT.out.ne' x)
  have hg : MemLp g p := by
    unfold g
    rw [← memLp_haarAddCircle_iff] at *
    apply hf.comp_measurePreserving AddCircle.measurePreserving_equivAddCircle
  have h := carleson_hunt_two_pi hp hg
  rw [AddCircle.volume_eq_smul_haarAddCircle] at *
  rw [Measure.ae_ennreal_smul_measure_eq (ofReal_ne_zero_iff.mpr two_pi_pos)] at h
  apply Measure.ae_smul_measure
  convert AddCircle.measurePreserving_equivAddCircle.quasiMeasurePreserving.ae h using 4 with x N
  · exact partialFourierSum'_comp_equivAddCircle.symm
  · unfold g
    congr
    exact (AddEquiv.symm_apply_eq
      (AddCircle.equivAddCircle (2 * π) T (two_pi_pos.ne') (hT.out.ne'))).mp rfl

end TwoPiPos

/-- Classical theorem of Carleson and Hunt asserting a.e. convergence of the partial Fourier sums
for `L^p` functions for `p > 1`. This is a strengthening of `classical_carleson`, and not officially
part of the blueprint. -/
theorem carleson_hunt {T : ℝ} [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ℝ≥0∞} (hp : 1 < p)
  (hf : MemLp f p AddCircle.haarAddCircle) :
    ∀ᵐ x, Tendsto (partialFourierSum' · f x) atTop (𝓝 (f x)) :=
  carleson_hunt' hp hf.of_haarAddCircle

end AddCircle

end
