import Carleson.ToMathlib.MeasureTheory.Measure.AEMeasurable
import Carleson.ToMathlib.Rearrangement

-- Upstreaming status: NOT READY yet (mostly); this file is being actively worked on.
-- Needs significant clean-up (refactoring, code style, extracting lemmas etc.) first.


/-!
# Lorentz space

This file describes properties of almost everywhere strongly measurable functions with finite
`(p,q)`-seminorm, denoted by `eLorentzNorm f p q μ`.

The Prop-valued `MemLorentz f p q μ` states that a function `f : α → ε` has finite `(p,q)`-seminorm
and is almost everywhere strongly measurable.

## Main definitions
* TODO

-/

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

lemma eLorentzNorm'_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  sorry

--TODO: probably need some assumptions on q here
lemma eLorentzNorm'_eq' (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) q := by
  sorry --should be an easy consequence of eLorentzNorm'_eq

lemma eLorentzNorm'_eq_integral_distribution_rpow {_ : MeasurableSpace α} {f : α → ε}
  {μ : Measure α} :
    eLorentzNorm' f p 1 μ = p * ∫⁻ (t : ℝ≥0), distribution f t μ ^ p.toReal⁻¹ := by
  unfold eLorentzNorm'
  simp only [inv_one, ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.toReal_inv]
  congr
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
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

/-- The Lorentz seminorm of a function -/
def eLorentzNorm (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then
    (if q = 0 then 0 else if q = ∞ then eLpNormEssSup f μ else ∞ * eLpNormEssSup f μ)
  else eLorentzNorm' f p q μ

variable {μ : Measure α}

lemma eLorentzNorm_eq_eLorentzNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} :
    eLorentzNorm f p q μ = eLorentzNorm' f p q μ := by
  unfold eLorentzNorm
  simp [hp_ne_zero, hp_ne_top]

--TODO: remove this?
lemma eLorentzNorm_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} :
  eLorentzNorm f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  unfold eLorentzNorm
  split_ifs with hp0
  · contradiction
  exact eLorentzNorm'_eq p_nonzero p_ne_top


@[simp]
lemma eLorentzNorm_exponent_zero {f : α → ε} : eLorentzNorm f 0 q μ = 0 := by simp [eLorentzNorm]

@[simp]
lemma eLorentzNorm_exponent_zero' {f : α → ε} : eLorentzNorm f p 0 μ = 0 := by
  simp [eLorentzNorm, eLorentzNorm']

@[simp]
lemma eLorentzNorm_exponent_top_top {f : α → ε} : eLorentzNorm f ∞ ∞ μ = eLpNormEssSup f μ := by
  simp [eLorentzNorm]

lemma eLorentzNorm_exponent_top' {f : α → ε} (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) (hf : eLpNormEssSup f μ ≠ 0) :
    eLorentzNorm f ∞ q μ = ∞ := by
  simp only [eLorentzNorm, ENNReal.top_ne_zero, ↓reduceIte]
  rw [ite_cond_eq_false, ite_cond_eq_false, ENNReal.top_mul hf] <;> simpa

lemma eLorentzNorm_exponent_top {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) (hf : ¬ f =ᶠ[ae μ] 0) :
    eLorentzNorm f ∞ q μ = ∞ := by
  apply eLorentzNorm_exponent_top' q_ne_zero q_ne_top
  contrapose! hf
  exact eLpNormEssSup_eq_zero_iff.mp hf

/-- A function is in the Lorentz space `L^{p,q}` if it is (strongly a.e.)-measurable and
  has finite Lorentz seminorm. -/
def MemLorentz [TopologicalSpace ε] (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ eLorentzNorm f p r μ < ∞

theorem MemLorentz.aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞}
  (h : MemLorentz f p q μ) :
    AEStronglyMeasurable f μ :=
  h.1

lemma MemLorentz.aemeasurable [MeasurableSpace ε] [TopologicalSpace ε]
    [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]
    {f : α → ε} {p : ℝ≥0∞} (hf : MemLorentz f p q μ) :
    AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

end Lorentz

end MeasureTheory
