module

public import Carleson.ToMathlib.MeasureTheory.Function.EssSup
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Defs
public import Carleson.ToMathlib.RealInterpolation.Misc

public section
public import Carleson.ToMathlib.Topology.ContinuousOn
public import Carleson.ToMathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Carleson.ToMathlib.Analysis.SpecialFunctions.Integrals.Basic

/- Upstreaming status: still needs some cleanup, and more analogues to mathlib lemmas about eLpNorm
could be added -/

noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α} {p q : ℝ≥0∞} {μ : Measure α} [ENorm ε]
  [ENorm ε']

namespace MeasureTheory

lemma eLorentzNorm'_mono_enorm_ae {f : α → ε'} {g : α → ε} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm' f p q μ ≤ eLorentzNorm' g p q μ := by
  unfold eLorentzNorm'
  gcongr
  apply eLpNorm_mono_enorm
  intro x
  simp only [ENNReal.toReal_inv, enorm_eq_self]
  gcongr

lemma eLorentzNorm_mono_enorm_ae {f : α → ε'} {g : α → ε} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  unfold eLorentzNorm
  split_ifs
  · trivial
  · trivial
  · exact essSup_mono_ae h
  · gcongr
    exact essSup_mono_ae h
  · exact eLorentzNorm'_mono_enorm_ae h

--Proof analogous to eLpNorm_congr_enorm_ae
theorem eLorentzNorm_congr_enorm_ae {f : α → ε'} {g : α → ε} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  le_antisymm (eLorentzNorm_mono_enorm_ae <| Filter.EventuallyEq.le hfg)
    (eLorentzNorm_mono_enorm_ae <| (Filter.EventuallyEq.symm hfg).le)

--Proof analogous to eLpNorm_congr_ae
theorem eLorentzNorm_congr_ae {f g : α → ε'} (hfg : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  eLorentzNorm_congr_enorm_ae <| hfg.mono fun _x hx => hx ▸ rfl

@[simp]
theorem eLorentzNorm_enorm (f : α → ε) : eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_enorm_ae <| Eventually.of_forall fun _ => enorm_enorm _

variable {ε : Type*} [TopologicalSpace ε]

lemma eLorentzNorm'_eq_zero_of_ae_enorm_zero [ESeminormedAddMonoid ε] {f : α → ε}
  (h : enorm ∘ f =ᵐ[μ] 0) (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) :
    eLorentzNorm' f p q μ = 0 := by
  unfold eLorentzNorm'
  conv in ↑t * distribution f _ μ ^ p⁻¹.toReal =>
    rw [distribution_eq_zero_of_ae_zero_enorm h,
    ENNReal.zero_rpow_of_pos (by simp only [ENNReal.toReal_inv, inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top),
    mul_zero]
  simp

lemma eLorentzNorm_eq_zero_of_ae_enorm_zero [ESeminormedAddMonoid ε] {f : α → ε} (h : enorm ∘ f =ᵐ[μ] 0) :
    eLorentzNorm f p q μ = 0 := by
  simp only [eLorentzNorm, ite_eq_left_iff]
  intro p_ne_zero
  rw [← eLpNorm_exponent_top, eLpNorm_zero_of_ae_zero' h]
  simp only [mul_zero, ite_self, ite_eq_left_iff]
  intro p_ne_top
  exact eLorentzNorm'_eq_zero_of_ae_enorm_zero h p_ne_zero p_ne_top

lemma eLorentzNorm'_eq_zero_of_ae_zero [ESeminormedAddMonoid ε] {f : α → ε}
    (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) (h : f =ᵐ[μ] 0) :
    eLorentzNorm' f p q μ = 0 := by
  apply eLorentzNorm'_eq_zero_of_ae_enorm_zero _ p_ne_zero p_ne_top
  filter_upwards [h]
  simp +contextual

lemma eLorentzNorm_eq_zero_of_ae_zero [ESeminormedAddMonoid ε] {f : α → ε} (h : f =ᵐ[μ] 0) :
    eLorentzNorm f p q μ = 0 := by
  apply eLorentzNorm_eq_zero_of_ae_enorm_zero
  filter_upwards [h]
  simp +contextual

section ENormedAddMonoid -- TODO: do all of these results require positive definiteness?

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

theorem ae_eq_zero_of_eLorentzNorm'_eq_zero {f : α → ε} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  (q_ne_zero : q ≠ 0) (h : eLorentzNorm' f p q μ = 0) :
    f =ᵐ[μ] 0 := by
  rw [eLorentzNorm', mul_eq_zero, eLpNorm_eq_zero_iff (by fun_prop) q_ne_zero] at h
  contrapose! h
  constructor
  · simp [p_ne_zero]
  rw [withDensity_ae_eq (by fun_prop) (by simp)]
  simp_rw [← Measure.measure_support_eq_zero_iff]
  simp only [ENNReal.toReal_inv, Function.support_mul, Function.support_ofNNReal]
  rw [Function.support_rpow_of_pos (by rw [inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top)]
  have : (fun (x : ℝ≥0) ↦ distribution f x μ) = (fun x ↦ distribution f x μ) ∘ ENNReal.ofNNReal := by
    ext x
    simp
  rw [this, Function.support_comp_eq_preimage, support_distribution, ENNReal.ofNNReal_preimage,
      Set.diff_singleton_eq_self (by simp), ENNReal.toNNReal_Iio]
  split_ifs with h'
  · simp only [Set.inter_univ, ne_eq]
    rw [NNReal.volume_Ioi]
    simp
  · rw [Set.Ioi_inter_Iio, NNReal.volume_Ioo]
    simp only [ENNReal.coe_zero, tsub_zero, ENNReal.coe_eq_zero, ne_eq]
    rw [ENNReal.toNNReal_eq_zero_iff]
    simp only [eLpNormEssSup_eq_zero_iff, not_or]
    use h

theorem eLorentzNorm'_eq_zero_iff {f : α → ε}
  (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) (q_ne_zero : q ≠ 0) :
    eLorentzNorm' f p q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_eLorentzNorm'_eq_zero p_ne_zero p_ne_top q_ne_zero,
    eLorentzNorm'_eq_zero_of_ae_zero p_ne_zero p_ne_top⟩

theorem eLorentzNorm_eq_zero_iff {f : α → ε}
  (p_ne_zero : p ≠ 0) (q_ne_zero : q ≠ 0) :
    eLorentzNorm f p q μ = 0 ↔ f =ᵐ[μ] 0 := by
  unfold eLorentzNorm
  split_ifs with p_zero p_top q_zero
  · contradiction
  · exact eLpNormEssSup_eq_zero_iff
  · simp
  · exact eLorentzNorm'_eq_zero_iff p_ne_zero p_top q_ne_zero

end ENormedAddMonoid


variable [ESeminormedAddMonoid ε]

@[simp]
lemma eLorentzNorm_zero : eLorentzNorm (0 : α → ε) p q μ = 0 := by
  apply eLorentzNorm_eq_zero_of_ae_enorm_zero
  simp

@[simp]
lemma eLorentzNorm_zero' : eLorentzNorm (fun _ : α ↦  (0 : ε)) p q μ = 0 := eLorentzNorm_zero

lemma eLorentzNorm_eq_eLpNorm {f : α → ε} (hf : AEStronglyMeasurable f μ) :
  eLorentzNorm f p p μ = eLpNorm f p μ := by
  by_cases p_zero : p = 0
  · simp [p_zero]
  by_cases p_eq_top : p = ∞
  · simp [p_eq_top]
  have p_eq : p = .ofReal p.toReal := by simp [p_eq_top]
  simp only [eLorentzNorm, eLorentzNorm', p_zero, ↓reduceIte, p_eq_top]
  calc _
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal t ^ (p.toReal - 1) ) ^ p⁻¹.toReal := by
        rw [← p_eq, eLpNorm_eq_eLpNorm' p_zero p_eq_top, eLpNorm'_eq_lintegral_enorm,
          ENNReal.mul_rpow_of_nonneg, lintegral_withDensity_eq_lintegral_mul_non_measurable]
        · simp only [ENNReal.toReal_inv, enorm_eq_self, one_div]
          congr 2
          simp only [Pi.mul_apply]
          rw [lintegral_nnreal_eq_lintegral_Ioi_ofReal
            (f := fun x ↦ x⁻¹ * (x * distribution f x μ ^ p.toReal⁻¹)^ p.toReal)]
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht
          simp only
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← mul_assoc, ← ENNReal.rpow_neg_one,
              ← ENNReal.rpow_add _ _ (by simpa) (by simp), mul_comm]
          congr 2
          · rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨p_zero, p_eq_top⟩),
              ENNReal.rpow_one]
          · exact neg_add_eq_sub 1 p.toReal
        · exact Measurable.inv measurable_coe_nnreal_ennreal
        · rw[Filter.eventually_iff_exists_mem]
          use {x | x ≠ 0}
          constructor
          · simp [mem_ae_iff]
          · intro x hx
            rw [ENNReal.inv_lt_top, ENNReal.coe_pos]
            exact pos_of_ne_zero hx
        · simp
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal (t ^ (p.toReal - 1)) ) ^ p.toReal⁻¹ := by
        rw [ENNReal.toReal_inv]
        congr 2
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [ENNReal.ofReal_rpow_of_pos ht]
    _ = eLpNorm f (.ofReal p.toReal) μ := (eLpNorm_eq_distribution hf (ENNReal.toReal_pos p_zero p_eq_top)).symm
    _ = eLpNorm f p μ := by congr; exact p_eq.symm

lemma eLorentzNorm'_eq_wnorm (p_ne_top : p ≠ ∞) {f : α → ε} {μ : Measure α} :
    eLorentzNorm' f p ∞ μ = wnorm f p μ := by
  rw [wnorm_ne_top p_ne_top]
  unfold eLorentzNorm' wnorm'
  simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, ENNReal.toReal_inv,
    eLpNorm_exponent_top, one_mul]
  rw [eLpNormEssSup_withDensity (by fun_prop) (by simp)]
  apply eLpNormEssSup_nnreal_eq_iSup_nnreal (f := fun t ↦ t * distribution f t μ ^ p.toReal⁻¹)
  intro a x ha
  apply ContinuousWithinAt.ennreal_mul continuous_id'.continuousWithinAt
    ((continuousWithinAt_distribution _).ennrpow_const _)
  · rw [or_iff_not_imp_left]
    push Not
    intro h
    exfalso
    rw [h] at ha
    simp at ha
  · right
    simp

lemma eLorentzNorm_eq_wnorm (p_ne_zero : p ≠ 0) {f : α → ε} {μ : Measure α} :
    eLorentzNorm f p ∞ μ = wnorm f p μ := by
  by_cases p_ne_top : p = ⊤
  · rw [p_ne_top]
    simp
  rw [eLorentzNorm_eq_eLorentzNorm' p_ne_zero p_ne_top, eLorentzNorm'_eq_wnorm p_ne_top]

--Theorem 6.6 in https://doi.org/10.1007/978-3-319-30034-4
lemma eLorentzNorm'_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  by_cases q_zero : q = 0
  · rw [q_zero]
    simp
  by_cases q_top : q = ⊤
  · rw [q_top, eLorentzNorm'_eq_wnorm p_ne_top,
      wnorm_eq_iSup_rpow_mul_rearrangement p_nonzero p_ne_top]
    simp only [ENNReal.toReal_inv, eLpNorm_exponent_top]
    symm
    rw [eLpNormEssSup_withDensity (by fun_prop) (by simp)]
    apply eLpNormEssSup_nnreal_eq_iSup_nnreal (f := fun t ↦ t ^ p.toReal⁻¹ * rearrangement f t μ)
    intro a x ha
    apply ContinuousWithinAt.ennreal_mul
    · fun_prop
    · apply continuousWithinAt_rearrangement.congr_mono (Set.eqOn_refl _ _)
      · simp
      · simp
    · rw [or_iff_not_imp_left]
      push Not
      intro h
      exfalso
      rw [h] at ha
      simp at ha
    · right
      simp
  unfold eLorentzNorm'
  rw [← eLpNorm_const_smul'' (by simp; aesop), eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top,
      lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  congr 1
  simp only [ENNReal.toReal_inv, Pi.smul_apply, smul_eq_mul, enorm_eq_self]
  conv =>
    lhs
    congr
    rfl
    intro t
    simp
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp),
        ENNReal.rpow_inv_rpow (ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩),
        ENNReal.mul_rpow_of_nonneg _ _ (by simp),
        ← mul_assoc, ← mul_assoc, mul_comm _ p, mul_assoc p, ← ENNReal.rpow_neg_one]
  conv =>
    rhs
    congr
    rfl
    intro t
    simp
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_neg_one, ← mul_assoc]
  symm
  calc _
    _ = ∫⁻ t, t ^ ((q / p).toReal - 1) * rearrangement f t μ ^ q.toReal := by
      rw [lintegral_nnreal_eq_lintegral_Ioi_ofReal
            (f := fun t => t ^ (-1) * t ^ (p.toReal⁻¹ * q.toReal) * rearrangement f t μ ^ q.toReal),
          lintegral_ennreal_eq_lintegral_Ioi_ofReal
            (f := fun t => t ^ ((q / p).toReal - 1) * rearrangement f t μ ^ q.toReal)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [ENNReal.toReal_div]
      congr
      rw [inv_mul_eq_div, ← ENNReal.toReal_div, ← ENNReal.rpow_add _ _ (by simpa) (by simp)]
      ring_nf
    _ = ∫⁻ t, t ^ ((q / p).toReal - 1)
          * (∫⁻ l in Set.Iio (rearrangement f t μ), q * l ^ (q.toReal - 1)) := by
      congr with t
      congr
      rw [lintegral_const_mul _ (by fun_prop)]
      rw [setLIntegral_Iio_rpow, sub_add_cancel, ENNReal.ofReal_toReal q_top,
        ENNReal.mul_div_cancel q_zero q_top]
      simp only [neg_lt_sub_iff_lt_add, lt_add_iff_pos_right]
      exact ENNReal.toReal_pos q_zero q_top
    _ = ∫⁻ t, (∫⁻ l, t ^ ((q / p).toReal - 1)
          * (Set.Iio (rearrangement f t μ)).indicator (fun l ↦ q * l ^ (q.toReal - 1)) l) := by
      congr with t
      rw [← lintegral_indicator measurableSet_Iio,
          ← lintegral_const_mul _ (Measurable.indicator (by fun_prop) measurableSet_Iio)]
    _ = ∫⁻ l, (∫⁻ t, t ^ ((q / p).toReal - 1)
          * (Set.Iio (rearrangement f t μ)).indicator (fun l ↦ q * l ^ (q.toReal - 1)) l) := by
      rw [lintegral_lintegral_swap]
      apply Measurable.aemeasurable
      apply Measurable.mul (by fun_prop)
      apply Measurable.indicator (by fun_prop)
      change MeasurableSet {(a : ℝ≥0∞ × ℝ≥0∞) | a.2 ∈ Set.Iio (rearrangement f a.1 μ)}
      have : {(a : ℝ≥0∞ × ℝ≥0∞) | a.2 ∈ Set.Iio (rearrangement f a.1 μ)} = ((fun a ↦ (⟨rearrangement f a.1 μ, a.2⟩ : ℝ≥0∞ × ℝ≥0∞)) ⁻¹' ({t | t.2 < t.1})) := by
        ext a
        simp
      rw [this]
      measurability
    _ = ∫⁻ l, (∫⁻ t, t ^ ((q / p).toReal - 1)
          * (Set.Iio (distribution f l μ)).indicator 1 t * (q * l ^ (q.toReal - 1))) := by
      congr with l
      congr with t
      rw [mul_assoc (_ ^ _)]
      congr
      rw [← Set.indicator_mul_const]
      simp only [Pi.one_apply, one_mul]
      apply Set.indicator_const_eq_indicator_const
      simp only [Set.mem_Iio]
      apply lt_rearrangement_iff_lt_distribution
    _ = ∫⁻ l, (∫⁻ t in Set.Iio (distribution f l μ), t ^ ((q / p).toReal - 1)) * (q * l ^ (q.toReal - 1)) := by
      congr with l
      rw [← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]
      congr with t
      rw [Set.indicator_mul_right, mul_assoc, ← Set.indicator_mul_const]
      simp
    _ = ∫⁻ l, (distribution f l μ ^ (q / p).toReal / (q / p)) * (q * l ^ (q.toReal - 1)) := by
      congr with l
      rw [setLIntegral_Iio_rpow, sub_add_cancel,
        ENNReal.ofReal_toReal (ENNReal.div_ne_top q_top p_nonzero)]
      simp only [ENNReal.toReal_div, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right]
      exact div_pos (ENNReal.toReal_pos q_zero q_top) (ENNReal.toReal_pos p_nonzero p_ne_top)
    _ = ∫⁻ l, p * l ^ (q.toReal - 1) * distribution f l μ ^ (q / p).toReal := by
      congr with l
      rw [← ENNReal.div_mul _ (by left; assumption) (by left; assumption), ENNReal.div_eq_inv_mul,
        mul_comm, mul_comm q, mul_assoc, ← mul_assoc q, ← mul_assoc q,
        ENNReal.mul_inv_cancel q_zero q_top]
      ring
    _ = ∫⁻ (l : ℝ≥0), p * (↑l ^ (-1 : ℝ) * ↑l ^ q.toReal) * (distribution f (↑l) μ ^ p.toReal⁻¹) ^ q.toReal := by
      rw [lintegral_ennreal_eq_lintegral_Ioi_ofReal
            (f := fun l => p * l ^ (q.toReal - 1) * distribution f l μ ^ (q / p).toReal),
          lintegral_nnreal_eq_lintegral_Ioi_ofReal
            (f := fun l => p * (l ^ (-1 : ℝ) * l ^ q.toReal) * (distribution f l μ ^ p.toReal⁻¹) ^ q.toReal)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro l hl
      simp only [ENNReal.toReal_div]
      rw [← ENNReal.rpow_mul, inv_mul_eq_div, ← ENNReal.rpow_add _ _ (by simpa) (by simp)]
      ring_nf

lemma eLorentzNorm'_eq' (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) q := by
  by_cases q_zero : q = 0
  · rw [q_zero]
    simp
  rw [eLorentzNorm'_eq p_nonzero p_ne_top]
  by_cases q_top : q = ⊤
  · rw [q_top]
    simp only [ENNReal.toReal_inv, eLpNorm_exponent_top, ENNReal.inv_top, ENNReal.toReal_zero,
      sub_zero]
    apply eLpNormEssSup_withDensity (by fun_prop) (by simp)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top, eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top,
      lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne volume 0]
  intro t ht
  simp only [ENNReal.toReal_inv, enorm_eq_self, Pi.mul_apply]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ENNReal.mul_rpow_of_nonneg _ _ (by simp),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc, sub_mul,
      inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩)]
  congr
  rw [ENNReal.rpow_sub _ _ (by simpa) (by simp), ENNReal.rpow_one, ENNReal.div_eq_inv_mul]

--TODO: remove this?
lemma eLorentzNorm_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} :
  eLorentzNorm f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  unfold eLorentzNorm
  split_ifs with hp0
  · contradiction
  exact eLorentzNorm'_eq p_nonzero p_ne_top

lemma eLorentzNorm'_indicator_const {a : ε} (ha : ‖a‖ₑ ≠ ⊤)
  {s : Set α} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) :
    eLorentzNorm' (s.indicator (Function.const α a)) p 1 μ = p * (‖a‖ₑ * μ s ^ p⁻¹.toReal) := by
  rw [eLorentzNorm'_eq_integral_distribution_rpow]
  congr
  simp_rw [distribution_indicator_const (ε := ε) (μ := μ) (s := s) (a := a)]
  unfold Set.indicator
  simp only [ENNReal.toReal_inv, ite_pow]
  symm
  calc ‖a‖ₑ * μ s ^ p.toReal⁻¹
    _ = (∫⁻ (t : ℝ≥0), (Set.Iio ‖a‖ₑ.toNNReal).indicator (fun x ↦ μ s ^ p.toReal⁻¹) t) := by
      rw [lintegral_indicator_const measurableSet_Iio, mul_comm]
      congr 1
      rw [NNReal.volume_Iio, ENNReal.coe_toNNReal ha]
  congr with t
  unfold Set.indicator
  rw [ENNReal.zero_rpow_of_pos (by simp only [inv_pos]; exact ENNReal.toReal_pos p_ne_zero p_ne_top)]
  congr 1
  simp only [Set.mem_Iio, eq_iff_iff]
  exact (ENNReal.coe_lt_iff_lt_toNNReal ha).symm

lemma eLorentzNorm'_indicator_const' {a : ε} {s : Set α} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) :
    eLorentzNorm' (s.indicator (Function.const α a)) p q μ
      = (p / q) ^ q.toReal⁻¹ * μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  rw [eLorentzNorm'_eq p_ne_zero p_ne_top]
  simp_rw [rearrangement_indicator_const]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal q_ne_zero q_ne_top]
  simp only [ENNReal.toReal_inv, enorm_eq_self, one_div]
  conv in (_ * _) ^ _ => rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    Set.comp_indicator (fun t ↦ t ^ q.toReal),
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos q_ne_zero q_ne_top),
    Function.comp_const, Function.const_zero, Set.piecewise_eq_indicator,
    ← Set.indicator_mul_right _ (fun t ↦ (t ^ p.toReal⁻¹) ^ q.toReal) _,
    ← Set.indicator_comp_right]
  rw [lintegral_indicator (by measurability)]
  simp only [Function.const_apply, Function.comp_apply]
  rw [lintegral_mul_const _ (by fun_prop),
    ENNReal.mul_rpow_of_nonneg _ _ (by simp),
    ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨q_ne_zero, q_ne_top⟩)]
  congr
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop) (by measurability)]
  simp only [Pi.mul_apply]
  simp_rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul]
  rw [← lintegral_indicator (by measurability), lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  simp_rw [← Set.indicator_comp_right]
  rw [setLIntegral_indicator (by measurability)]
  have : ENNReal.ofNNReal ∘ Real.toNNReal = ENNReal.ofReal := rfl
  rw [← Set.preimage_comp, this]
  simp only [Function.comp_apply]
  have : ((μ s ^ p.toReal⁻¹) ^ q.toReal) ^ q.toReal⁻¹ = μ s ^ p.toReal⁻¹:= by
    apply ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨q_ne_zero, q_ne_top⟩)
  rw [← this, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← ENNReal.rpow_mul]
  congr
  calc _
    _ = ∫⁻ (a : ℝ) in ENNReal.ofReal ⁻¹' Set.Iio (μ s) ∩ Set.Ioi 0,
          ENNReal.ofReal (a ^ (p.toReal⁻¹ * q.toReal - 1)) := by
      apply setLIntegral_congr_fun (by measurability)
      intro x hx
      simp only
      rw [← ENNReal.rpow_add _ _
        (by simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]; exact hx.2)
        (by simp)]
      ring_nf
      rw [← ENNReal.ofReal_rpow_of_pos hx.2]
      congr
  rw [ENNReal.ofReal_Iio_eq]
  have hpq : 0 < p.toReal⁻¹ * q.toReal := by
    apply mul_pos
    · rw [inv_pos]
      exact ENNReal.toReal_pos p_ne_zero p_ne_top
    · exact ENNReal.toReal_pos q_ne_zero q_ne_top
  split_ifs with h h
  · simp only [Set.empty_inter, Measure.restrict_empty, lintegral_zero_measure, zero_eq_mul,
    ENNReal.div_eq_zero_iff, ENNReal.rpow_eq_zero_iff]
    right
    left
    use h, hpq
  · rw [Set.univ_inter]
    rw [lintegral_rpow_Ioi_top]
    rw [h, ENNReal.top_rpow_of_pos hpq, ENNReal.mul_top]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    use p_ne_zero, q_ne_top
  · rw [Set.Iio_inter_Ioi, lintegral_rpow_of_gt ENNReal.toReal_nonneg (by simpa)]
    simp only [sub_add_cancel]
    rw [ENNReal.ofReal_div_of_pos hpq, ENNReal.ofReal_mul (by simp),
        ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos p_ne_zero p_ne_top),
        ENNReal.ofReal_toReal p_ne_top, ENNReal.ofReal_toReal q_ne_top, ← ENNReal.div_eq_inv_mul,
        ← ENNReal.div_mul _ (by left; assumption) (by left; assumption), ENNReal.mul_comm_div,
        mul_comm, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
        ENNReal.ofReal_toReal h]

@[simp]
lemma eLorentzNorm_indicator_const {a : ε} {s : Set α} :
  eLorentzNorm (s.indicator (Function.const α a)) p q μ
    = if p = 0 then 0
      else if q = 0 then 0
      else if p = ∞ then
        (if μ s = 0 then 0 else if q = ∞ then ‖a‖ₑ else ∞ * ‖a‖ₑ)
      else if q = ∞ then
        μ s ^ p.toReal⁻¹ * ‖a‖ₑ
      else
        (p / q) ^ q.toReal⁻¹ * μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  unfold eLorentzNorm
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  all_goals try rfl
  · exact eLpNormEssSup_indicator_const_eq' h₄
  · unfold Function.const
    rw [eLpNormEssSup_indicator_const_eq s a h₄]
  · unfold Function.const
    rw [eLpNormEssSup_indicator_const_eq' h₅]
    exact CommMonoidWithZero.mul_zero ⊤
  · congr
    exact eLpNormEssSup_indicator_const_eq s a h₅
  · simp [h₆]
  · rw [← eLorentzNorm_eq_eLorentzNorm' h₀ h₁, h₇, eLorentzNorm_eq_wnorm h₀]
    rw [wnorm_indicator_const h₀ h₁]
  · exact eLorentzNorm'_indicator_const' h₀ h₁ h₆ h₇

lemma MemLorentz_iff_MemLp {f : α → ε} :
    MemLorentz f p p μ ↔ MemLp f p μ := by
  unfold MemLorentz MemLp
  constructor
  · intro h
    rwa [← eLorentzNorm_eq_eLpNorm h.1]
  · intro h
    rwa [eLorentzNorm_eq_eLpNorm h.1]

-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_of_MemLorentz_ge {r₁ r₂ : ℝ≥0∞} (r₁_pos : 0 < r₁) (r₁_le_r₂ : r₁ ≤ r₂) {f : α → ε}
  (hf : MemLorentz f p r₁ μ) :
    MemLorentz f p r₂ μ := by
  unfold MemLorentz at *
  rcases hf with ⟨meas_f, norm_f⟩
  use meas_f
  unfold eLorentzNorm at *
  split_ifs at * with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exfalso
    exact r₁_pos.ne h₆.symm
  · exact norm_f
  · rw [ENNReal.top_mul'] at norm_f
    split_ifs at norm_f with h
    · rwa [h]
    · exfalso
      exact (lt_self_iff_false ⊤).mp norm_f
  · exfalso
    exact r₁_pos.ne h₈.symm
  · exfalso
    rw [h₉, top_le_iff] at r₁_le_r₂
    exact h₅ r₁_le_r₂
  · exact norm_f
  · by_cases r₁_top : r₁ = ∞
    · convert norm_f
      rw [r₁_top, top_le_iff] at r₁_le_r₂
      rw [r₁_top, r₁_le_r₂]
    --Now the only interesting case
    have measurable_mul_distribution_rpow : Measurable fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal := by measurability
    unfold eLorentzNorm' at norm_f
    rw [ENNReal.mul_lt_top_iff] at norm_f
    rcases norm_f with ⟨_, norm_lt_top⟩ | p_zero | norm_zero
    · wlog r₂_top : r₂ = ⊤ generalizing r₂
      · have memLp_r₁: MemLp (fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal) r₁
                        (volume.withDensity fun t ↦ (↑t)⁻¹) := by
          constructor
          · exact (aeMeasurable_withDensity_inv measurable_mul_distribution_rpow.aemeasurable).aestronglyMeasurable
          exact norm_lt_top
        have memLp_top : MemLp (fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal) ⊤
                          (volume.withDensity fun t ↦ (↑t)⁻¹) := by
          constructor
          · exact (aeMeasurable_withDensity_inv measurable_mul_distribution_rpow.aemeasurable).aestronglyMeasurable
          have := this le_top rfl
          unfold eLorentzNorm' at this
          rw [ENNReal.mul_lt_top_iff] at this
          rcases this with ⟨_, norm_lt_top⟩ | p_zero | norm_zero
          · exact norm_lt_top
          · --TODO: duplicate from below
            exfalso
            rw [ENNReal.rpow_eq_zero_iff] at p_zero
            rcases p_zero with ⟨p_zero, _⟩ | ⟨p_top, _⟩
            · exact h₀ p_zero
            · exact h₁ p_top
          · rw [norm_zero]
            exact ENNReal.zero_lt_top
        unfold eLorentzNorm'
        rw [ENNReal.mul_lt_top_iff]
        left
        use ENNReal.rpow_lt_top_of_nonneg (by simp) h₁
        exact (MeasureTheory.memLp_of_memLp_le_of_memLp_ge r₁_pos ⟨r₁_le_r₂, le_top⟩ memLp_r₁ memLp_top).2
      /- Hardest part -/
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal r₁_pos.ne' r₁_top,
          lintegral_withDensity_eq_lintegral_mul₀ (by measurability) (measurable_mul_distribution_rpow.aestronglyMeasurable.enorm.pow_const r₁.toReal),
          lintegral_nnreal_eq_lintegral_toNNReal_Ioi] at norm_lt_top
      simp only [ENNReal.toReal_inv, enorm_eq_self, Pi.mul_apply, one_div] at norm_lt_top
      rw [r₂_top, ← eLorentzNorm_eq_eLorentzNorm' h₀ h₁, eLorentzNorm_eq_wnorm h₀, wnorm_ne_top h₁, wnorm']
      rw [iSup_lt_iff]
      have toReal_r₁_pos := ENNReal.toReal_pos r₁_pos.ne' r₁_top
      have : r₁ ^ r₁.toReal⁻¹ < ∞ := ENNReal.rpow_lt_top_of_nonneg (by simp) r₁_top
      have norm_lt_top' := ENNReal.mul_lt_top norm_lt_top this
      exists _, norm_lt_top'
      intro s
      rw [← ENNReal.div_le_iff_le_mul (by left; apply (ENNReal.rpow_pos r₁_pos r₁_top).ne') (by left; exact this.ne)] --TODO: improve this
      calc _
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (↑s / r₁ ^ r₁.toReal⁻¹) := by
          rw [mul_comm, mul_div_assoc]
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          rw [ENNReal.div_rpow_of_nonneg,
              ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne', r₁_top⟩)]
          simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          congr 1
          · rw [ENNReal.rpow_mul, ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne', r₁_top⟩)]
          --·
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, ENNReal.ofReal (x ^ (r₁.toReal - 1))) ^ r₁.toReal⁻¹:= by
          congr
          rw [lintegral_rpow_of_gt NNReal.zero_le_coe (by linarith), ENNReal.ofReal_div_of_pos (by simpa),
              ← ENNReal.ofReal_rpow_of_nonneg NNReal.zero_le_coe (by linarith)]
          ring_nf
          rw [ENNReal.ofReal_toReal r₁_top, ENNReal.ofReal, Real.toNNReal_coe]
        _ = (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal ^ r₁.toReal * distribution f s μ ^ (p.toReal⁻¹ * r₁.toReal))) ^ r₁.toReal⁻¹ := by
          rw [← ENNReal.mul_rpow_of_nonneg, ← lintegral_const_mul]
          · congr 1
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro x hx
            simp only
            rw [mul_comm, ← mul_assoc]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_pos hx.1, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ (by simp [hx.1]) (by simp), neg_add_eq_sub]
            congr
          · measurability
          · simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal * distribution f s μ ^ p.toReal⁻¹) ^ r₁.toReal) ^ r₁.toReal⁻¹ := by
          congr with x
          rw [ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul]
          exact ENNReal.toReal_nonneg
        _ ≤ (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal * distribution f (↑x.toNNReal) μ ^ p.toReal⁻¹) ^ r₁.toReal) ^ r₁.toReal⁻¹ := by
          apply ENNReal.rpow_le_rpow _ (by simp only [inv_nonneg, ENNReal.toReal_nonneg])
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ht
          gcongr
          exact Real.toNNReal_le_iff_le_coe.mpr ht.2.le
        _ ≤ (∫⁻ (x : ℝ) in Set.Ioi 0, (↑x.toNNReal)⁻¹ * (↑x.toNNReal * distribution f (↑x.toNNReal) μ ^ p.toReal⁻¹) ^ r₁.toReal) ^
            r₁.toReal⁻¹ := by
          gcongr
          exact Set.Ioo_subset_Ioi_self
    · exfalso
      rw [ENNReal.rpow_eq_zero_iff] at p_zero
      rcases p_zero with ⟨p_zero, _⟩ | ⟨p_top, _⟩
      · exact h₀ p_zero
      · exact h₁ p_top
    · unfold eLorentzNorm'
      rw [ENNReal.mul_lt_top_iff]
      right; right
      rw [eLpNorm_eq_zero_iff measurable_mul_distribution_rpow.aestronglyMeasurable r₁_pos.ne'] at norm_zero
      rwa [eLpNorm_eq_zero_iff measurable_mul_distribution_rpow.aestronglyMeasurable (r₁_pos.trans_le r₁_le_r₂).ne']

lemma MemLorentz.memLp {f : α → ε} (hf : MemLorentz f p q μ) (h : q ∈ Set.Ioc 0 p) :
    MemLp f p μ := by
  rw [← MemLorentz_iff_MemLp]
  apply MemLorentz_of_MemLorentz_ge h.1 h.2 hf

end MeasureTheory
