module

public import Carleson.ToMathlib.WeakType

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
