import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

@[simp] lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← ofReal_norm, ofReal_toReal_le]

@[simp] lemma enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
  simp [hx, ← ofReal_norm_eq_enorm]

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommSubMonoid (E : Type*) [TopologicalSpace E] extends ENormedAddCommMonoid E, Sub E where
  sub_add_cancel_of_enorm_le : ∀ ⦃x y : E⦄, ‖y‖ₑ ≤ ‖x‖ₑ → x - y + y = x
  add_right_cancel_of_enorm_lt_top : ∀ ⦃x : E⦄, ‖x‖ₑ < ⊤ → ∀ {y z : E}, y + x = z + x → y = z
  esub_self : ∀ x : E, x - x = 0

/-- An enormed space is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedSpace (E : Type*) [TopologicalSpace E] extends ENormedAddCommMonoid E, Module ℝ≥0 E where
  enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export ENormedAddCommSubMonoid
  (sub_add_cancel_of_enorm_le add_right_cancel_of_enorm_lt_top esub_self)
export ENormedSpace (enorm_smul)

-- mathlib has this (in the _root_ namespace), in a less general setting
attribute [simp] ENormedSpace.enorm_smul

instance : ENormedSpace ℝ≥0∞ where
  enorm := id
  enorm_eq_zero := by simp
  -- enorm_neg := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := continuous_id
  enorm_smul := by simp

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
  enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory

-- PRed in #22798
section ContinuousENorm
variable {α E : Type*} {m : MeasurableSpace α} [TopologicalSpace E] [ContinuousENorm E] {μ : Measure α}

@[fun_prop]
theorem measurable_enorm [MeasurableSpace E] [OpensMeasurableSpace E] :
    Measurable (fun a : E => (‖a‖ₑ)) :=
  continuous_enorm.measurable

@[fun_prop]
protected theorem AEMeasurable.enorm [MeasurableSpace E] [OpensMeasurableSpace E] {f : α → E}
    (hf : AEMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
  measurable_enorm.comp_aemeasurable hf

-- TODO: when updating mathlib, replace this by the unprimed version
-- (in mathlib, which is generalised in PR 22798)
@[fun_prop]
protected theorem AEStronglyMeasurable.enorm' {f : α → E}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
  continuous_enorm.comp_aestronglyMeasurable hf |>.aemeasurable

end ContinuousENorm

lemma esub_zero [TopologicalSpace E] [ENormedAddCommSubMonoid E] {x : E} : x - 0 = x := by
  rw [← add_zero (x - 0)]
  apply sub_add_cancel_of_enorm_le
  simp_rw [enorm_zero, zero_le]

end MeasureTheory
