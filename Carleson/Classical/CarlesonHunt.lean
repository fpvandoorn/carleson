module

public import Carleson.Classical.ClassicalCarleson

/-! This file contains the Carleson-Hunt theorem, a generalization of `classical_carleson`. -/

public section

open MeasureTheory Real

noncomputable section

local notation "S_" => partialFourierSum


--TODO: find better name, generalize and move
lemma helper {T : ℝ} [hT : Fact (0 < T)] {s : Set ℝ} (hs : MeasurableSet s) :
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
    helper (by exact (measurableSet_superlevelSet (by fun_prop)))]
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

--TODO: move, generalize?
lemma AddCircle.equivAddCircle_eq {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)] :
    equivAddCircle p q hp.out.ne' hq.out.ne'
      = fun x ↦ ((equivIco p 0 x).val * (p⁻¹ * q) : AddCircle q) := by
  ext x
  have : ↑↑((equivIco p 0) x) = x := coe_equivIco
  nth_rw 1 [← this, equivAddCircle_apply_mk]

--TODO: move, generalize?
lemma AddCircle.continuous_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)]
  [hq : Fact (0 < q)] :
    Continuous (⇑(AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne')) :=
  (homeomorphAddCircle _ _ _ _).2

--TODO: move, generalize?
lemma AddCircle.measurePreserving_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)]
  [hq : Fact (0 < q)] :
    MeasurePreserving (⇑(AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne'))
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  AddMonoidHom.measurePreserving continuous_equivAddCircle
    (equivAddCircle p q (hp.out.ne') (hq.out.ne')).surjective (by simp)

--TODO: find better name, move?
lemma helper' {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)] {P : (x : AddCircle p) → Prop}
  (h : ∀ᵐ (x : AddCircle p), P x) :
    ∀ᵐ (x : AddCircle q), P (AddCircle.equivAddCircle _ _ hq.out.ne' hp.out.ne' x) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle] at *
  apply Measure.ae_smul_measure
  rw [Measure.ae_ennreal_smul_measure_eq (by simp [hp.out])] at h
  rw [ae_iff] at *
  rw [← Set.preimage_setOf_eq (p := fun x ↦ ¬ P x), ← h]
  exact MeasurePreserving.measure_preimage AddCircle.measurePreserving_equivAddCircle
    (NullMeasurableSet.of_null h)

theorem fourier_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {x : AddCircle p} {n : ℤ} :
    (fourier n) x = (fourier n) ((AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne') x) := by
  simp only [fourier_apply, SetLike.coe_eq_coe]
  rw [AddCircle.toCircle_zsmul, AddCircle.toCircle_zsmul]
  congr 1
  rw [AddCircle.equivAddCircle_eq]
  have : ↑↑((AddCircle.equivIco p 0) x) = x := AddCircle.coe_equivIco
  nth_rw 1 [← this]
  rw [AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk]
  congr 1
  field [hq.out.ne']

--TODO: move
theorem fourierCoeff_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {f : AddCircle q → ℂ} {n : ℤ} :
    fourierCoeff f n
      = fourierCoeff (fun x ↦ f ((AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne') x)) n := by
  unfold fourierCoeff
  symm
  simp only [smul_eq_mul]
  simp_rw [@fourier_comp_equivAddCircle p q, ← Pi.mul_apply]
  apply AddCircle.measurePreserving_equivAddCircle.integral_comp
    (AddCircle.homeomorphAddCircle _ _ _ _).measurableEmbedding

--TODO: move
theorem partialFourierSum'_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {f : AddCircle q → ℂ} {N : ℕ} {x : AddCircle q} :
    partialFourierSum' N f x
      = partialFourierSum' N (fun x ↦ f ((AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne') x))
          ((AddCircle.equivAddCircle q p hq.out.ne' hp.out.ne') x) := by
  unfold partialFourierSum'
  simp only [Int.ofNat_eq_natCast, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr with n
  congr 1
  · apply fourierCoeff_comp_equivAddCircle
  · apply fourier_comp_equivAddCircle

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
  convert helper' (carleson_hunt_two_pi hp hg) using 4 with x N
  · apply partialFourierSum'_comp_equivAddCircle
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
