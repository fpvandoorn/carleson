module

public import Carleson.ToMathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Defs
public import Carleson.ToMathlib.MeasureTheory.Integral.Layercake
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.MeasureTheory.Function.LpNorm.Misc
public import Carleson.ToMathlib.Topology.ContinuousOn

/- Upstreaming status: still needs some cleanup, and more analogues to mathlib lemmas about eLpNorm
could be added -/

public section

noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α} {p q : ℝ≥0∞} {μ : Measure α} [ENorm ε]
  [ENorm ε']

namespace MeasureTheory

--Proof analogous to eLpNorm_congr_enorm_ae
theorem eLorentzNorm_congr_enorm_ae [TopologicalSpace ε] [TopologicalSpace ε'] {f : α → ε'}
    {g : α → ε} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  le_antisymm (eLorentzNorm_mono_enorm_ae hf <| Filter.EventuallyEq.le hfg)
    (eLorentzNorm_mono_enorm_ae hg <| (Filter.EventuallyEq.symm hfg).le)

--Proof analogous to eLpNorm_congr_ae
theorem eLorentzNorm_congr_ae [TopologicalSpace ε'] {f g : α → ε'} (hfg : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_enorm_ae hf (hf.congr hfg) <| hfg.mono fun _x hx => hx ▸ rfl
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf,
      eLorentzNorm_of_not_aestronglyMeasurable ((aestronglyMeasurable_congr hfg).not.mp hf)]

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] in
@[simp]
theorem eLorentzNorm_enorm {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_enorm_ae hf.enorm.aestronglyMeasurable hf <|
    Eventually.of_forall fun _ => enorm_enorm _

lemma eLorentzNorm'_eq_zero_of_ae_enorm_zero {f : α → ε}
  (h : enorm ∘ f =ᵐ[μ] 0) (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) :
    eLorentzNorm' f p q μ = 0 := by
  unfold eLorentzNorm'
  conv in ↑t * distribution f _ μ ^ p⁻¹.toReal =>
    rw [distribution_eq_zero_of_ae_zero_enorm h,
    ENNReal.zero_rpow_of_pos (by simp only [ENNReal.toReal_inv, inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top),
    mul_zero]
  simp

section

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

lemma eLorentzNorm_eq_zero_of_ae_enorm_zero {f : α → ε} (hf : AEStronglyMeasurable f μ)
    (h : enorm ∘ f =ᵐ[μ] 0) :
    eLorentzNorm f p q μ = 0 := by
  simp only [eLorentzNorm, hf, ↓reduceIte, ite_eq_left_iff]
  intro p_ne_zero
  rw [show eLpNormEssSup f μ = 0 from ENNReal.essSup_eq_zero_iff.mpr h]
  simp only [mul_zero, ite_self, ite_eq_left_iff]
  intro p_ne_top
  exact eLorentzNorm'_eq_zero_of_ae_enorm_zero h p_ne_zero p_ne_top

lemma eLorentzNorm'_eq_zero_of_ae_zero {f : α → ε}
    (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) (h : f =ᵐ[μ] 0) :
    eLorentzNorm' f p q μ = 0 := by
  apply eLorentzNorm'_eq_zero_of_ae_enorm_zero _ p_ne_zero p_ne_top
  filter_upwards [h]
  simp +contextual

lemma eLorentzNorm_eq_zero_of_ae_zero {f : α → ε} (h : f =ᵐ[μ] 0) :
    eLorentzNorm f p q μ = 0 := by
  apply eLorentzNorm_eq_zero_of_ae_enorm_zero (aestronglyMeasurable_zero.congr h.symm)
  filter_upwards [h]
  simp +contextual

@[simp]
lemma eLorentzNorm_zero : eLorentzNorm (0 : α → ε) p q μ = 0 := by
  apply eLorentzNorm_eq_zero_of_ae_enorm_zero aestronglyMeasurable_zero
  simp

@[simp]
lemma eLorentzNorm_zero' : eLorentzNorm (fun _ : α ↦  (0 : ε)) p q μ = 0 := eLorentzNorm_zero

end

section ENormedAddMonoid -- TODO: do all of these results require positive definiteness?

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

theorem ae_eq_zero_of_eLorentzNorm'_eq_zero {f : α → ε} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
    (q_ne_zero : q ≠ 0) (h : eLorentzNorm' f p q μ = 0) :
    f =ᵐ[μ] 0 := by
  rw [eLorentzNorm', mul_eq_zero, eLpNorm_eq_zero_iff q_ne_zero] at h
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
      Set.sdiff_singleton_eq_self (by simp), ENNReal.toNNReal_Iio]
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
  refine ⟨fun h ↦ ?_, eLorentzNorm_eq_zero_of_ae_zero⟩
  have hf := aestronglyMeasurable_of_eLorentzNorm_ne_top (h ▸ ENNReal.zero_ne_top)
  simp only [eLorentzNorm, hf, p_ne_zero, q_ne_zero, ↓reduceIte] at h
  split_ifs at h with p_top
  · exact eLpNormEssSup_eq_zero_iff.mp h
  · simpa using h
  · exact ae_eq_zero_of_eLorentzNorm'_eq_zero p_ne_zero p_top q_ne_zero h

end ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] in
lemma eLorentzNorm_eq_eLpNorm {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  by_cases p_zero : p = 0
  · simp [p_zero, hf]
  by_cases p_eq_top : p = ∞
  · simp [p_eq_top, hf]
  have p_eq : p = .ofReal p.toReal := by simp [p_eq_top]
  simp only [eLorentzNorm, eLorentzNorm', hf, p_zero, ↓reduceIte, p_eq_top]
  calc _
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal t ^ (p.toReal - 1) ) ^ p⁻¹.toReal := by
        rw [← p_eq, eLpNorm_eq_eLpNorm' p_zero p_eq_top (by fun_prop), eLpNorm'_eq_lintegral_enorm,
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

variable {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε'] in
lemma MemLorentz_iff_MemLp {f : α → ε'} : MemLorentz f p p μ ↔ MemLp f p μ :=
    ⟨fun h ↦ (eLorentzNorm_eq_eLpNorm h.aestronglyMeasurable).symm.trans_lt h,
    fun h ↦ (eLorentzNorm_eq_eLpNorm h.aestronglyMeasurable).trans_lt h⟩

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

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
  have hp : 0 < p.toReal := ENNReal.toReal_pos p_ne_zero p_ne_top
  have hq : 0 < q.toReal := ENNReal.toReal_pos q_ne_zero q_ne_top
  set S : Set ℝ≥0 := ENNReal.ofNNReal ⁻¹' Set.Iio ‖a‖ₑ
  have hS : MeasurableSet S := measurable_coe_nnreal_ennreal measurableSet_Iio
  have h_eq : (fun t : ℝ≥0 ↦
      (t : ℝ≥0∞) * distribution (s.indicator (Function.const α a)) t μ ^ p⁻¹.toReal)
      = μ s ^ p.toReal⁻¹ • S.indicator (fun t ↦ (t : ℝ≥0∞)) := by
    ext t
    by_cases ht : (t : ℝ≥0∞) < ‖a‖ₑ
    · simp [distribution_indicator_const, ht, S, mul_comm]
    · simp [distribution_indicator_const, ht, S, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)]
  have h_int : ∫⁻ t : ℝ≥0, S.indicator (fun t ↦ (t : ℝ≥0∞)) t ^ q.toReal
      ∂(volume.withDensity (fun t : ℝ≥0 ↦ (t : ℝ≥0∞)⁻¹)) = ‖a‖ₑ ^ q.toReal / q := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
    calc _
      _ = ∫⁻ t in S, (t : ℝ≥0∞) ^ (q.toReal - 1) := by
        rw [← lintegral_indicator hS]
        apply lintegral_congr_ae
        filter_upwards [Measure.ae_ne volume 0] with t ht
        by_cases htS : t ∈ S
        · simp only [Pi.mul_apply, Set.indicator_of_mem htS]
          rw [ENNReal.rpow_sub _ _ (by simpa) (by simp), ENNReal.rpow_one, ENNReal.div_eq_inv_mul]
        · simp [Set.indicator_of_notMem htS, ENNReal.zero_rpow_of_pos hq]
      _ = ∫⁻ t in Set.Iio ‖a‖ₑ, t ^ (q.toReal - 1) :=
        (setLIntegral_ennreal_eq_setLintegral_of_nnreal
          (f := fun t ↦ t ^ (q.toReal - 1)) measurableSet_Iio).symm
      _ = _ := by
        rw [setLIntegral_Iio_rpow (by linarith), sub_add_cancel, ENNReal.ofReal_toReal q_ne_top]
  rw [eLorentzNorm', h_eq, eLpNorm_const_smul''' (by fun_prop),
    eLpNorm_eq_lintegral_rpow_enorm_toReal q_ne_zero q_ne_top (by fun_prop)]
  simp only [enorm_eq_self]
  rw [h_int, ENNReal.div_rpow_of_nonneg _ _ (by positivity), one_div,
    ENNReal.rpow_rpow_inv hq.ne', ENNReal.div_rpow_of_nonneg _ _ (by positivity),
    ENNReal.toReal_inv]
  simp only [div_eq_mul_inv]
  ring

lemma eLorentzNorm_indicator_const₀ {a : ε} {s : Set α} (hs : NullMeasurableSet s μ) :
  eLorentzNorm (s.indicator (Function.const α a)) p q μ
    = if p = 0 then 0
      else if q = 0 then 0
      else if p = ∞ then
        (if μ s = 0 then 0 else if q = ∞ then ‖a‖ₑ else ∞ * ‖a‖ₑ)
      else if q = ∞ then
        μ s ^ p.toReal⁻¹ * ‖a‖ₑ
      else
        (p / q) ^ q.toReal⁻¹ * μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  have hf : AEStronglyMeasurable (s.indicator (Function.const α a)) μ :=
    aestronglyMeasurable_const.indicator₀ hs
  rw [eLorentzNorm, ite_eq_left hf]
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
  · have hp : 0 < p.toReal⁻¹ := by positivity [ENNReal.toReal_pos h₀ h₁]
    rw [h₇, eLorentzNorm'_exponent_top, mul_comm]
    calc _
      _ = ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ‖a‖ₑ), t * μ s ^ p.toReal⁻¹ := by
        refine iSup_congr fun t ↦ ?_
        by_cases ht : (t : ℝ≥0∞) < ‖a‖ₑ <;> simp [distribution_indicator_const, ht, hp]
      _ = ‖a‖ₑ * μ s ^ p.toReal⁻¹ := by
        simp_rw [← ENNReal.iSup_mul]
        congr
        exact le_antisymm (iSup₂_le fun t ht ↦ ht.le)
          (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ le_iSup₂_of_le r hr le_rfl)
  · exact eLorentzNorm'_indicator_const' h₀ h₁ h₆ h₇

lemma eLorentzNorm_indicator_const {a : ε} {s : Set α} (hs : MeasurableSet s) :
  eLorentzNorm (s.indicator (Function.const α a)) p q μ
    = if p = 0 then 0
      else if q = 0 then 0
      else if p = ∞ then
        (if μ s = 0 then 0 else if q = ∞ then ‖a‖ₑ else ∞ * ‖a‖ₑ)
      else if q = ∞ then
        μ s ^ p.toReal⁻¹ * ‖a‖ₑ
      else
        (p / q) ^ q.toReal⁻¹ * μ s ^ p.toReal⁻¹ * ‖a‖ₑ :=
    eLorentzNorm_indicator_const₀ hs.nullMeasurableSet

end MeasureTheory
