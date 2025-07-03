import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ : Type*}

@[simp] lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← ofReal_norm, ofReal_toReal_le]

@[simp] lemma enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
  simp [hx, ← ofReal_norm_eq_enorm]

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

/-- An enormed space is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedSpace (E : Type*) [TopologicalSpace E] extends ENormedAddCommMonoid E, Module ℝ≥0 E where
  enorm_smul_eq_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export ENormedAddCommSubMonoid
  (sub_add_cancel_of_enorm_le add_right_cancel_of_enorm_lt_top esub_self)
export ENormedSpace (enorm_smul_eq_smul)

-- mathlib has this (in the _root_ namespace), in a less general setting
attribute [simp] ENormedSpace.enorm_smul_eq_smul

instance : ENormedSpace ℝ≥0∞ where
  enorm := id
  enorm_eq_zero := by simp
  -- enorm_neg := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := continuous_id
  enorm_smul_eq_smul := by simp
  add_smul := fun _ _ _ ↦ Module.add_smul ..
  zero_smul := by simp

instance : ENormedSpace ℝ≥0 where
  enorm := ofNNReal
  add_smul r s x := by
    simp only [smul_eq_mul]
    ring
  zero_smul := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := by fun_prop
  enorm_smul_eq_smul c x := by simp [ENNReal.smul_def]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
  enorm_smul_eq_smul := by
    simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory

section ContinuousENorm
variable {α E : Type*} {m : MeasurableSpace α} [TopologicalSpace E] [ContinuousENorm E] {μ : Measure α}

variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ContinuousENorm ε']

end ContinuousENorm

lemma esub_zero [TopologicalSpace E] [ENormedAddCommSubMonoid E] {x : E} : x - 0 = x := by
  rw [← add_zero (x - 0)]
  apply sub_add_cancel_of_enorm_le
  simp_rw [enorm_zero, zero_le]

section ENormedSpace

variable {ε : Type*} [TopologicalSpace ε] [ENormedSpace ε]

-- TODO: this lemma and Mathlib's `enorm_smul` could be unified using a `ENormedDivisionSemiring`
-- typeclass
-- (which includes ENNReal and normed fields like ℝ and ℂ), i.e. assuming 𝕜 is a normed semifield.
-- Investigate if this is worthwhile when upstreaming this to mathlib.
lemma enorm_smul_eq_mul {c : ℝ≥0} (z : ε) : ‖c • z‖ₑ = ‖c‖ₑ * ‖z‖ₑ :=
  ENormedSpace.enorm_smul_eq_smul _ _

instance : ContinuousConstSMul ℝ≥0 ℝ≥0∞ where
  continuous_const_smul t := ENNReal.continuous_const_mul (by simp)

open MeasureTheory

-- TODO: put next to MeasureTheory.eLpNorm_const_smul_le (which perhaps can stay)
theorem eLpNorm_const_smul_le' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
  {μ : Measure α} {c : ℝ≥0} {f : α → ε}: eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (p := p) ?_
  filter_upwards with x using by simp [ENNReal.smul_def]

-- TODO: put next to eLpNorm_const_smul
theorem eLpNorm_const_smul' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
  {μ : Measure α} {c : ℝ≥0} {f : α → ε}:
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm eLpNorm_const_smul_le' <| ENNReal.mul_le_of_le_div' ?_
  simpa [ENNReal.div_eq_inv_mul, hc] using eLpNorm_const_smul_le' (c := c⁻¹) (f := c • f)

-- TODO: put next to the unprimed version; perhaps both should stay
lemma eLpNormEssSup_const_smul_le' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {c : ℝ≥0} {f : α → ε} : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ := by
  have (x : α) : ‖(c • f) x‖ₑ ≤ ↑c * ‖f x‖ₑ := by simp [ENNReal.smul_def]
  apply eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
  filter_upwards with x using this x

end ENormedSpace

end MeasureTheory
