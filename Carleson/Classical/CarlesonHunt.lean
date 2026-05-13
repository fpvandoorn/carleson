module

public import Carleson.Classical.ClassicalCarleson

/-! This file contains the Carleson-Hunt theorem, a generalization of `classical_carleson`. -/

public section

open MeasureTheory Real

noncomputable section

local notation "S_" => partialFourierSum


--TODO: find better name, generalize and move
lemma helper' {T : ℝ} [hT : Fact (0 < T)] {s : Set ℝ} (hs : MeasurableSet s) :
    volume (s ∩ Set.Ioc 0 T) = volume ((fun x ↦ (AddCircle.equivIoc T 0 x : ℝ)) ⁻¹' s) := by
  rw [← lintegral_indicator_one (hs.inter measurableSet_Ioc),
    ← lintegral_indicator_one ((Measurable.subtype_val (AddCircle.measurable_equivIoc T 0)) hs)]
  rw [← AddCircle.lintegral_preimage (t := 0) (T := T), Set.inter_comm, ← Set.indicator_indicator,
    lintegral_indicator measurableSet_Ioc]
  simp_rw [zero_add]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro x hx
  unfold Set.indicator
  simp only [Pi.one_apply, Set.mem_preimage]
  congr 1
  simp only [eq_iff_iff]
  simp only [Set.mem_preimage]
  rw [AddCircle.equivIoc_coe_eq]
  simpa

theorem carleson_hunt_two_pi [hT : Fact (0 < 2 * π)] {f : AddCircle (2 * π) → ℂ} {p : ENNReal} (hp : 1 < p)
  (hf : MemLp f p AddCircle.haarAddCircle) :
    ∀ᵐ x, Filter.Tendsto (partialFourierSum' · f x) Filter.atTop (nhds (f x)) := by
  wlog meas_f : Measurable f
  · sorry
  have hf' : MemLp f p volume := by
    sorry
  set g := fun (x : ℝ) ↦ f x
  have periodic_g : g.Periodic (2 * π) := by
    unfold g
    intro x
    simp
  have hg : MemLp g p (volume.restrict (Set.Ioc 0 (2 * π))) := by
    unfold g
    constructor
    · sorry
    · sorry
      --rw [hf'.memLp_liftIoc]
  apply ae_tendsto_zero_of_distribution_le
  intro δ δpos ε εpos
  rcases exceptional_set_carleson periodic_g hp hg δpos εpos with ⟨N₀, hN₀⟩
  use N₀
  apply hN₀.trans'
  unfold distribution
  rw [Measure.restrict_apply' measurableSet_Ioc,
    helper' (by exact (measurableSet_superlevelSet (by fun_prop)))]
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

/-- Classical theorem of Carleson and Hunt asserting a.e. convergence of the partial Fourier sums
for `L^p` functions for `p > 1`. This is a strengthening of `classical_carleson`, and not officially
part of the blueprint. -/
theorem carleson_hunt {T : ℝ} [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ENNReal} (hp : 1 < p)
  (hf : MemLp f p AddCircle.haarAddCircle) :
    ∀ᵐ x, Filter.Tendsto (partialFourierSum' · f x) Filter.atTop (nhds (f x)) := by
  sorry


end
