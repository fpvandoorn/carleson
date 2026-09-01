module

public import Carleson.ToMathlib.Data.ENNReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

public section

-- Upstreaming status: can be upstreamed/being worked on
-- Many remaining declarations require PRing a new enorm class to mathlib first,
-- i.e. are not a good first target.

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ : Type*}

@[simp] lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← ofReal_norm, ofReal_toReal_le]

@[simp] lemma enorm_NNReal {x : ℝ≥0} : ‖x‖ₑ = x := by rfl

-- TODO appropriate generality (ENormedDivisionSemiring?), for ℝ≥0 it is already there
-- @[simp] lemma enorm_inv'' {a : ℝ≥0} (ha : a ≠ 0): ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹ := by
--   simp_rw [enorm_NNReal, coe_inv ha]

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommSubMonoid (E : Type*) [TopologicalSpace E] extends ENormedAddCommMonoid E, Sub E where
  sub_add_cancel_of_enorm_le : ∀ ⦃x y : E⦄, ‖y‖ₑ ≤ ‖x‖ₑ → x - y + y = x
  add_right_cancel_of_enorm_lt_top : ∀ ⦃x : E⦄, ‖x‖ₑ < ⊤ → ∀ {y z : E}, y + x = z + x → y = z
  esub_self : ∀ x : E, x - x = 0

/-
The generalization of `NormedSpace` to `ENorm` is
`[ENormedAddCommMonoid E] [Module ℝ≥0 E] [ENormSMulClass ℝ≥0 E]`.
This could be its own class `ENormedSpace`, but this seems not worth it.
-/

export ENormedAddCommSubMonoid
  (sub_add_cancel_of_enorm_le add_right_cancel_of_enorm_lt_top esub_self)

attribute [simp] enorm_smul

#guard_msgs (drop info) in
#synth ENormedAddCommMonoid ℝ≥0∞
#guard_msgs (drop info) in
#synth Module ℝ≥0 ℝ≥0∞

instance : ENormSMulClass ℝ≥0∞ ℝ≥0∞ where
  enorm_smul := by simp

instance : ContinuousConstSMul ℝ≥0 ℝ≥0∞ where
  continuous_const_smul t := ENNReal.continuous_const_mul (by simp)

-- TODO: the generated instance name has suffix `_carleson`, not 100% sure why
@[nolint defsWithUnderscore]
instance : ContinuousENorm ℝ≥0 where
  continuous_enorm := by change Continuous ofNNReal; fun_prop

-- TODO: the generated instance name has suffix `_carleson`, not 100% sure why
@[nolint defsWithUnderscore]
instance : ENormedAddCommMonoid ℝ≥0 where
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := by fun_prop

#guard_msgs (drop info) in
#synth Module ℝ≥0 ℝ≥0

instance : ENormSMulClass ℝ≥0 ℝ≥0∞ where
  enorm_smul := by simp [ENNReal.smul_def]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormSMulClass ℝ≥0 E where
  enorm_smul := by
    simp_rw [enorm_eq_nnnorm, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory

lemma esub_zero [TopologicalSpace E] [ENormedAddCommSubMonoid E] {x : E} : x - 0 = x := by
  rw [← add_zero (x - 0)]
  apply sub_add_cancel_of_enorm_le
  simp_rw [enorm_zero, zero_le]

section

-- TODO: find better place for this?
theorem _root_.ENNReal.toNNReal_smul {α : Type*} {c : ℝ≥0∞} (hc : c ≠ ⊤) {f : α → ℝ≥0∞} :
    c.toNNReal • f = c • f := by
  ext x
  simp [ENNReal.smul_def, hc]

end

section ENormedSpace

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMul ℝ≥0 ε] [ENormSMulClass ℝ≥0 ε]
  {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε'] [Module ℝ≥0 ε'] [ENormSMulClass ℝ≥0 ε']

open MeasureTheory

-- TODO: put next to MeasureTheory.eLpNorm_const_smul_le (which perhaps can stay)
theorem eLpNorm_const_nnreal_smul_le
    {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
    {μ : Measure α} {c : ℝ≥0} {f : α → ε} : eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (p := p) ?_
  filter_upwards with x using le_of_eq (by simp [enorm_smul])

-- TODO: put next to eLpNorm_const_smul
theorem eLpNorm_const_smul' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
    {μ : Measure α} {c : ℝ≥0} {f : α → ε'} :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm eLpNorm_const_nnreal_smul_le <| ENNReal.mul_le_of_le_div' ?_
  simpa [ENNReal.div_eq_inv_mul, hc] using eLpNorm_const_nnreal_smul_le (c := c⁻¹) (f := c • f)

set_option backward.isDefEq.respectTransparency false in
theorem eLpNorm_top_smul
    {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ) : eLpNorm (∞ • f) p μ = ⊤ * eLpNorm f p μ := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases h : f =ᶠ[ae μ] 0
  · rw [eLpNorm_eq_zero_of_ae_zero h, mul_zero]
    apply eLpNorm_eq_zero_of_ae_zero
    filter_upwards [h] with x hx
    simpa
  · have : ¬ eLpNorm f p μ = 0 := by
      rwa [eLpNorm_eq_zero_iff hf hp]
    by_cases h' : eLpNorm f p μ = ⊤
    · simp only [h', ne_eq, top_ne_zero, not_false_eq_true, mul_top]
      rw [eq_top_iff] at *
      apply h'.trans
      apply eLpNorm_mono_enorm
      intro x
      simp only [enorm_eq_self, Pi.smul_apply, smul_eq_mul]
      exact ENNReal.le_mul_top_self
    rw [top_mul this]
    apply eq_top_of_forall_nnreal_le
    intro r
    calc _
      _ = r / eLpNorm f p μ * eLpNorm f p μ := by
        rw [mul_comm, ENNReal.mul_div_cancel this h']
      _ = eLpNorm ((r / eLpNorm f p μ).toNNReal • f) p μ := by
        rw [eLpNorm_const_smul' (ε' := ℝ≥0∞)]
        congr
        simp only [toNNReal_div, toNNReal_coe, enorm_NNReal]
        rw [ENNReal.coe_div (by apply toNNReal_ne_zero.mpr; use this, h')]
        congr
        exact Eq.symm (coe_toNNReal h')
      _ ≤ eLpNorm (∞ • f) p μ := by
        apply eLpNorm_mono_enorm
        intro x
        simp only [toNNReal_div, toNNReal_coe, Pi.smul_apply, enorm_smul, enorm_eq_self,
          smul_eq_mul, enorm_NNReal]
        gcongr
        exact le_top

-- TODO: put next to eLpNorm_const_smul
set_option backward.isDefEq.respectTransparency false in
theorem eLpNorm_const_smul'' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
  {μ : Measure α} {c : ℝ≥0∞} (hc : c ≠ ⊤) {f : α → ℝ≥0∞} :
    eLpNorm (c • f) p μ = c * eLpNorm f p μ := by
  rw [← ENNReal.toNNReal_smul hc, eLpNorm_const_smul' (ε' := ℝ≥0∞)]
  congr
  simp [hc]

-- TODO: put next to eLpNorm_const_smul
theorem eLpNorm_const_smul''' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
  {μ : Measure α} {c : ℝ≥0∞} {f : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (c • f) p μ = c * eLpNorm f p μ := by
  by_cases hc : c = ⊤
  · simp only [hc]
    exact MeasureTheory.eLpNorm_top_smul hf
  exact eLpNorm_const_smul'' hc

-- TODO: put next to the unprimed version; perhaps both should stay
lemma eLpNormEssSup_const_nnreal_smul_le {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {c : ℝ≥0} {f : α → ε} : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ := by
  have (x : α) : ‖(c • f) x‖ₑ ≤ ↑c * ‖f x‖ₑ := by simp [enorm_smul]
  apply eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
  filter_upwards with x using this x

end ENormedSpace

end MeasureTheory
