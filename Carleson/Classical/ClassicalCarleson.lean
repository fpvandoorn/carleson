module

public import Carleson.Classical.Approximation
public import Carleson.Classical.CarlesonHuntBasic
public import Carleson.Classical.ControlApproximationEffectContinuous

public section

/- This file contains the proof of the classical Carleson theorem from Section 11.1.

   TODO: This file can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends
   on `sorryAx`
-/

open MeasureTheory Real NNReal ENNReal Topology Filter

noncomputable section

local notation "S_" => partialFourierSum

section TwoPiPos

local instance : Fact (0 < 2 * π) where
  out := two_pi_pos

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
/- Theorem 1.1 (Classical Carleson) -/
theorem exceptional_set_carleson' {f : ℝ → ℂ} (cont_f : Continuous f)
  (periodic_f : f.Periodic (2 * π)) {δ ε : NNReal} (δpos : 0 < δ) (εpos : 0 < ε) :
    ∃ N₀, distribution (fun x ↦ ⨆ N > N₀, ‖f x - S_ N f x‖ₑ) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  have δ2pos : 0 < δ / 2 := by positivity
  have δ4pos : 0 < δ / 4 := by positivity
  have ε2pos : 0 < ε / 2 := by positivity
  have ε4pos : 0 < ε / 4 := by positivity
  have unicont_f : UniformContinuous f := periodic_f.uniformContinuous_of_continuous
    Real.two_pi_pos cont_f.continuousOn
  /- Approximate f by a smooth f₀. -/
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ :=
    close_smooth_approx_periodic unicont_f periodic_f
      (lt_min δ4pos (C_control_approximation_effect'_pos δ2pos ε2pos))
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
        · refine le_iSup₂_of_le N hN ?_
          rfl
        · apply le_iSup_of_le N
          rw [partialFourierSum_sub (contDiff_f₀.continuous.intervalIntegrable 0 (2 * π))
            (cont_f.intervalIntegrable 0 (2 * π))]
          · rfl
  calc _
    _ ≤ distribution
        (fun x ↦ ‖f x - f₀ x‖ₑ + (⨆ N > N₀, ‖f₀ x - S_ N f₀ x‖ₑ) + ⨆ N, ‖S_ N (f₀ - f) x‖ₑ)
        ((δ / 4) + (δ / 4) + (δ / 2)) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_mono
      · filter_upwards [this] with x hx
        simp only [gt_iff_lt, enorm_eq_self, hx]
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
        convert! zero_le (α := ℝ≥0∞)
        rw [distribution_eq_zero_iff]
        apply eLpNormEssSup_le_of_ae_enorm_bound
        filter_upwards with x
        simp only [enorm_eq_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, coe_div, coe_ofNat]
        have : ENNReal.ofNNReal δ / 4 = ↑(δ / 4) := by norm_num
        rw [this, enorm_le_coe]
        rw [← nnnorm_norm]
        calc _
          _ ≤ ‖((δ / 4) : ℝ)‖₊ := nnnorm_le_nnnorm (by simp) ((hf₀ x).trans (min_le_left _ _))
          _ = δ / 4 := by simp
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
          _ ≤ ‖((δ / 4) : ℝ)‖₊ :=
            nnnorm_le_nnnorm (by simp) (hN₀ N hN x (Set.Ioc_subset_Icc_self hx))
          _ = δ / 4 := by simp
      · norm_cast
        apply control_approximation_effect' (ε := ε / 2) δ2pos ε2pos
          (contDiff_f₀.continuous.sub cont_f).measurable
            (periodic_f₀.sub periodic_f)
        intro x
        rw [Pi.sub_apply, norm_sub_rev]
        apply (hf₀ x).trans (min_le_right _ _)
    _ = ε := by simp

end TwoPiPos

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
theorem carleson_interval' {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
    ∀ᵐ x ∂volume.restrict (Set.Ioc 0 (2 * π)),
      Tendsto (S_ · f x) atTop (𝓝 (f x)) := by
  apply ae_tendsto_zero_of_distribution_le
  intro δ δpos ε εpos
  exact exceptional_set_carleson' cont_f periodic_f δpos εpos

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
/- **Carleson's theorem** asserting a.e. point-wise convergence of the partial Fourier sums for
periodic continuous functions. -/
theorem classical_carleson {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
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
  exact carleson_interval' cont_f periodic_f

theorem classical_carleson_check : ClassicalCarleson := classical_carleson

end
