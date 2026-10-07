module

public import Carleson.ToMathlib.Rearrangement
public import Carleson.ToMathlib.MeasureTheory.Function.LpNorm.Misc
public import Carleson.ToMathlib.Topology.ContinuousOn

-- Upstreaming status: mostly ready but things should be more closely aligned with mathlib Lp spaces

/-!
# Lorentz space

This file describes properties of almost everywhere strongly measurable functions with finite
`(p,q)`-seminorm, denoted by `eLorentzNorm f p q μ`.

The Prop-valued `MemLorentz f p q μ` states that a function `f : α → ε` has finite `(p,q)`-seminorm
and is almost everywhere strongly measurable.

## Main definitions
* TODO

-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α} {p q : ℝ≥0∞} [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lorentz

/-- The Lorentz seminorm of a function, for `0 < p < ∞` -/
def eLorentzNorm' (f : α → ε) (p : ℝ≥0∞) (q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  p ^ q⁻¹.toReal * eLpNorm (fun (t : ℝ≥0) ↦ t * distribution f t μ ^ p⁻¹.toReal) q
    (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

@[simp]
lemma eLorentzNorm'_exponent_zero' {f : α → ε} {μ : Measure α} : eLorentzNorm' f p 0 μ = 0 := by
  simp [eLorentzNorm']

lemma eLorentzNorm'_eq_integral_distribution_rpow {_ : MeasurableSpace α} {f : α → ε}
  {μ : Measure α} :
    eLorentzNorm' f p 1 μ = p * ∫⁻ (t : ℝ≥0), distribution f t μ ^ p.toReal⁻¹ := by
  unfold eLorentzNorm'
  simp only [inv_one, ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.toReal_inv]
  congr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [lintegral_withDensity_eq_lintegral_mul₀' (by measurability)
    (by apply aeMeasurable_withDensity_inv; apply AEMeasurable.pow_const; apply AEStronglyMeasurable.enorm; apply
      aestronglyMeasurable_iff_aemeasurable.mpr; apply Measurable.aemeasurable; measurability)]
  simp only [enorm_eq_self, ENNReal.toReal_one, ENNReal.rpow_one, Pi.mul_apply, ne_eq, one_ne_zero,
    not_false_eq_true, div_self]
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi, lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only
  rw [← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · rw [ENNReal.coe_ne_zero]
    symm
    apply ne_of_lt
    rw [Real.toNNReal_pos]
    exact hx
  · exact ENNReal.coe_ne_top

lemma eLorentzNorm'_exponent_top {f : α → ε} {μ : Measure α} :
    eLorentzNorm' f p ∞ μ = ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹ := by
  unfold eLorentzNorm'
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

theorem iSup_mul_distribution_rpow_eq_iSup_rpow_mul_rearrangement {p : ℝ} (hp : 0 < p)
    {f : α → ε} {μ : Measure α} :
    ⨆ t : ℝ≥0, t * distribution f t μ ^ p⁻¹ = ⨆ t : ℝ≥0, t ^ p⁻¹ * rearrangement f t μ := by
  have hp' : 0 < p⁻¹ := by simpa
  calc _
    _ = ⨆ t, t * distribution f t μ ^ p⁻¹ := by
      rw [ENNReal.iSup_ennreal]
      simp only [distibution_top, left_eq_sup]
      rw [ENNReal.zero_rpow_of_pos hp', mul_zero]
      exact zero_le
  symm
  calc _
    _ = ⨆ t, t ^ p⁻¹ * rearrangement f t μ := by
      rw [ENNReal.iSup_ennreal]
      simp
  symm
  apply le_antisymm
  · apply iSup_le
    intro t
    apply le_of_forall_lt
    intro a ha
    by_cases! a_ne_zero : a = 0
    · rw [a_ne_zero]
      rw [a_ne_zero] at ha
      rw [lt_iSup_iff]
      contrapose! ha
      simp only [nonpos_iff_eq_zero, mul_eq_zero] at *
      simp_rw [ENNReal.rpow_eq_zero_iff_of_pos hp'] at *
      by_cases ht : t = 0
      · left
        assumption
      · right
        rw [← nonpos_iff_eq_zero]
        apply _root_.le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add, ← rearrangement_le_iff_distribution_le]
        rcases ha ε with h | h
        · order
        rw [h]
        exact zero_le
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use (a / t) ^ p
    rw [ENNReal.rpow_rpow_inv hp.ne']
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul, lt_rearrangement_iff_lt_distribution]
    apply (ENNReal.lt_rpow_inv_iff hp).mp
    rwa [ENNReal.div_lt_iff (by right; assumption) (by right; assumption), mul_comm]
  · apply iSup_le
    intro t
    apply le_of_forall_lt
    intro a ha
    by_cases! a_ne_zero : a = 0
    · rw [a_ne_zero]
      rw [a_ne_zero] at ha
      rw [lt_iSup_iff]
      contrapose! ha
      simp only [nonpos_iff_eq_zero, mul_eq_zero] at *
      simp_rw [ENNReal.rpow_eq_zero_iff_of_pos hp'] at *
      by_cases ht : t = 0
      · left
        assumption
      · right
        rw [← nonpos_iff_eq_zero]
        apply _root_.le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add, rearrangement_le_iff_distribution_le]
        rcases ha ε with h | h
        · order
        rw [h]
        exact zero_le
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use a / t ^ p⁻¹
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul]
    gcongr
    rw [← lt_rearrangement_iff_lt_distribution]
    rwa [ENNReal.div_lt_iff (by right; assumption) (by right; assumption), mul_comm]

lemma eLorentzNorm'_mono_enorm_ae {f : α → ε'} {g : α → ε} {μ : Measure α}
  (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm' f p q μ ≤ eLorentzNorm' g p q μ := by
  unfold eLorentzNorm'
  gcongr
  apply eLpNorm_mono_enorm
  intro x
  simp only [ENNReal.toReal_inv, enorm_eq_self]
  gcongr

/-- The Lorentz seminorm of a function -/
def eLorentzNorm [TopologicalSpace ε] (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  open scoped Classical in
  if AEStronglyMeasurable f μ then
  if p = 0 then 0 else if p = ∞ then
    (if q = 0 then 0 else if q = ∞ then eLpNormEssSup f μ else ∞ * eLpNormEssSup f μ)
  else eLorentzNorm' f p q μ
  else ∞

variable {μ : Measure α}

theorem eLorentzNorm_of_not_aestronglyMeasurable [TopologicalSpace ε]
    {f : α → ε} {p q : ℝ≥0∞} (h : ¬ AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ = ∞ := by
  simp [eLorentzNorm, h]

theorem aestronglyMeasurable_of_eLorentzNorm_ne_top [TopologicalSpace ε]
    {f : α → ε} {p q : ℝ≥0∞} (h : eLorentzNorm f p q μ ≠ ∞) : AEStronglyMeasurable f μ := by
  contrapose h
  exact eLorentzNorm_of_not_aestronglyMeasurable h

theorem eLorentzNorm_eq_eLorentzNorm' [TopologicalSpace ε]
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ = eLorentzNorm' f p q μ := by
  simp [eLorentzNorm, hp_ne_zero, hp_ne_top, hf]

@[simp]
lemma eLorentzNorm_exponent_zero [TopologicalSpace ε] {f : α → ε} (hf : AEStronglyMeasurable f μ) :
  eLorentzNorm f 0 q μ = 0 := by simpa [eLorentzNorm]

@[simp]
lemma eLorentzNorm_exponent_zero' [TopologicalSpace ε] {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p 0 μ = 0 := by
  simpa [eLorentzNorm, eLorentzNorm']

@[simp]
lemma eLorentzNorm_exponent_top_top [TopologicalSpace ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f ∞ ∞ μ = eLpNormEssSup f μ := by
  simp [eLorentzNorm, hf]

lemma eLorentzNorm_exponent_top' [TopologicalSpace ε] {f : α → ε} (q_ne_zero : q ≠ 0)
  (q_ne_top : q ≠ ⊤) (hf : eLpNormEssSup f μ ≠ 0) :
    eLorentzNorm f ∞ q μ = ∞ := by
  simp only [eLorentzNorm, ENNReal.top_ne_zero, ↓reduceIte, ite_eq_right_iff]
  rw [ite_eq_right_of_eq_false _ _ (by simpa), ite_eq_right_of_eq_false _ _ (by simpa),
    ENNReal.top_mul hf]
  simp

lemma eLorentzNorm_exponent_top {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) (hf : ¬ f =ᶠ[ae μ] 0) :
    eLorentzNorm f ∞ q μ = ∞ := by
  apply eLorentzNorm_exponent_top' q_ne_zero q_ne_top
  contrapose! hf
  exact eLpNormEssSup_eq_zero_iff.mp hf

lemma eLorentzNorm_mono_enorm_ae [TopologicalSpace ε] [TopologicalSpace ε'] {f : α → ε} {g : α → ε'}
  (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  unfold eLorentzNorm
  simp only [hf, ↓reduceIte]
  split_ifs
  · trivial
  · trivial
  · trivial
  · trivial
  · exact essSup_mono_ae h
  · apply le_top
  · gcongr
    exact essSup_mono_ae h
  · apply le_top
  · exact eLorentzNorm'_mono_enorm_ae h
  · apply le_top

/-- A function is in the Lorentz space `L^{p,q}` if it is (strongly a.e.)-measurable and
  has finite Lorentz seminorm. -/
def MemLorentz [TopologicalSpace ε] (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  eLorentzNorm f p r μ < ∞

lemma memLorentz_iff [TopologicalSpace ε] {f : α → ε} :
    MemLorentz f p q μ ↔ eLorentzNorm f p q μ < ∞ := Iff.rfl

theorem MemLorentz.aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞}
  (h : MemLorentz f p q μ) :
    AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_eLorentzNorm_ne_top h.ne

lemma MemLorentz.aemeasurable [MeasurableSpace ε] [TopologicalSpace ε]
    [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]
    {f : α → ε} {p : ℝ≥0∞} (hf : MemLorentz f p q μ) :
    AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

end Lorentz

end MeasureTheory
