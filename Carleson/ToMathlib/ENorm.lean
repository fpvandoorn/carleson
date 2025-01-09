import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

lemma ENNReal.ofReal_norm [SeminormedAddGroup E] (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by
  simp_rw [enorm_eq_nnnorm, ofReal_norm_eq_coe_nnnorm]

lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← ofReal_norm, ofReal_toReal_le]

/-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`.
Note: do we want to unbundle this (at least separate out `TopologicalSpace E`?)
Note: not sure if this is the "right" class to add to Mathlib. -/
class ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
  continuous_enorm : Continuous enorm
  -- the topology is somehow defined by the enorm.

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddMonoid (E : Type*) extends ContinuousENorm E, AddMonoid E where
  enorm_zero : ∀ x : E, enorm x = 0 ↔ x = 0
  enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
  enorm_triangle : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommMonoid (E : Type*) extends ENormedAddMonoid E, AddCommMonoid E where



instance : ENormedAddCommMonoid ℝ≥0∞ where
  enorm := id
  enorm_zero := by simp
  enorm_neg := by simp
  enorm_triangle := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := continuous_id

instance [SeminormedAddGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm

instance [NormedAddGroup E] : ENormedAddMonoid E where
  enorm_zero := by simp [enorm_eq_nnnorm]
  enorm_neg := by
    simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
  enorm_triangle := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]

instance [NormedAddCommGroup E] : ENormedAddCommMonoid E where
  add_comm := by simp [add_comm]

namespace MeasureTheory
section ContinuousENorm
variable {α E : Type*} {m : MeasurableSpace α} [ContinuousENorm E] {μ : Measure α}

export ContinuousENorm (continuous_enorm)

protected theorem Continuous.enorm {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) : Continuous (fun x => (‖f x‖ₑ)) :=
  continuous_enorm.comp hf

protected theorem AEStronglyMeasurable.enorm {f : α → E}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
  continuous_enorm.comp_aestronglyMeasurable hf |>.aemeasurable

end ContinuousENorm

end MeasureTheory
