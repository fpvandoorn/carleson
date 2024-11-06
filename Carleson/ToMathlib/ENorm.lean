import Mathlib.Analysis.NormedSpace.IndicatorFunction
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section

open ENNReal NNReal MeasureTheory Function Set

/-- Auxiliary class, endowing a type `α` with a function `enorm : α → ℝ≥0∞` with notation `‖x‖ₑ`. -/
@[notation_class]
class ENorm (E : Type*) where
  /-- the `ℝ≥0∞`-valued norm function. -/
  enorm : E → ℝ≥0∞

export ENorm (enorm)

@[inherit_doc]
notation "‖" e "‖ₑ" => enorm e

#check EMetricSpace
/-- An enormed monoid is an additive monoid endowed with an enorm. -/
class ENormedAddMonoid (E : Type*) extends ENorm E, AddMonoid E, TopologicalSpace E where
  enorm_zero : ∀ x : E, enorm x = 0 ↔ x = 0
  enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
  enorm_triangle : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ
  -- the topology is somehow defined by the enorm.

/-- An enormed monoid is an additive monoid endowed with an enorm. -/
class ENormedAddCommMonoid (E : Type*) extends ENormedAddMonoid E, AddCommMonoid E where
  -- the topology is somehow defined by the enorm.

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

instance : ENormedAddCommMonoid ℝ≥0∞ where
  enorm := id
  enorm_zero := by simp
  enorm_neg := by simp
  enorm_triangle := by simp
  add_comm := by simp [add_comm]

instance [NNNorm E] : ENorm E where
  enorm := (‖·‖₊ : E → ℝ≥0∞)

lemma enorm_eq_nnnorm [NNNorm E] {x : E} : ‖x‖ₑ = ‖x‖₊ := rfl

instance [NormedAddGroup E] : ENormedAddMonoid E where
  enorm_zero := by simp [enorm_eq_nnnorm]
  enorm_neg := by
    simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
  enorm_triangle := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]

instance [NormedAddCommGroup E] : ENormedAddCommMonoid E where
  add_comm := by simp [add_comm]

namespace MeasureTheory

/-- `(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def eLpNorm' {_ : MeasurableSpace α} (f : α → F) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`. -/
def eLpNormEssSup {_ : MeasurableSpace α} (f : α → F) (μ : Measure α) :=
  essSup (fun x => ‖f x‖ₑ) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`essSup ‖f‖ μ` for `p = ∞`. -/
def eLpNorm {_ : MeasurableSpace α}
    (f : α → F) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

def Memℒp [TopologicalSpace E] [ENorm E] {_ : MeasurableSpace α} (f : α → E) (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞

variable [MeasurableSpace α] [MeasurableSpace α']

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution [ENorm E] (f : α → E) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' [ENorm E] (f : α → E) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

/-- The weak L^p norm of a function. -/
def wnorm [ENorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWℒp [TopologicalSpace E] [ENorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

variable [ENorm E₁] [ENorm E₂] [TopologicalSpace E₁] [TopologicalSpace E₂]

/-- An operator has weak type `(p, q)` if it is bounded as a map from L^p to weak-L^q.
`HasWeakType T p p' μ ν c` means that `T` has weak type `(p, p')` w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasWeakType (T : (α → E₁) → (α' → E₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0) : Prop :=
  ∀ f : α → E₁, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- An operator has strong type `(p, q)` if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type `(p, p')` w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-
1. Prove that for a function into `ENNReal`, if it is `MemWℒp` then it is almost everywhere
not infinity (this should be relatively easy from unfolding the definitions).
-/

/- If a function into `ENNReal` is `MemWℒp`, then its norm almost everywhere not infinity.-/
lemma MemWℒp.ae_ne_top [TopologicalSpace E] [ENorm E] {f : α → E} {p : ℝ≥0∞} {μ : Measure α}
    (hf : MemWℒp f p μ) : ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
  by_cases hp : p = ∞
  · rw [hp] at hf
    simp_rw [← lt_top_iff_ne_top]
    exact ae_lt_of_essSup_lt hf.2
  · set A := { x | ‖f x‖ₑ = ∞ } with hA
    unfold MemWℒp wnorm wnorm' at hf
    simp [hp] at hf
    rw [Filter.eventually_iff, mem_ae_iff]
    simp [compl_def, ← hA]
    by_contra h
    have h1 (t : ℝ≥0) : μ A ≤ distribution f t μ := by
      refine μ.mono ?_
      simp_all only [setOf_subset_setOf, coe_lt_top, implies_true, A]
    set C := ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹ with hC
    have h2 : C < ∞ := by aesop
    -- maybe separate the case C = 0?
    have h3' (t : ℝ≥0) : t * distribution f t μ ^ p.toReal⁻¹ ≤ C := le_iSup_iff.mpr fun b a ↦ a t
    have h3 (t : ℝ≥0) (ht : t ≠ 0) : distribution f t μ ≤ (C / t) ^ p.toReal := by
      sorry
    have h4 (t : ℝ≥0) (ht : t ≠ 0) : μ A ≤ (C / t) ^ p.toReal := (h1 t).trans (h3 t ht)
    have h5 : μ A ≤ μ A / 2 := by
      convert h4 (C * (2 / μ A) ^ p.toReal⁻¹).toNNReal ?_
      swap
      · sorry
      refine ?_
      rw [ENNReal.coe_toNNReal]
      swap
      · refine mul_ne_top h2.ne_top (rpow_ne_top_of_nonneg (inv_nonneg.mpr toReal_nonneg) ?_)
        simp [div_eq_top, h]
      refine ?_
      nth_rw 1 [← mul_one C]
      rw [ENNReal.mul_div_mul_left]
      rotate_left
      · sorry
      · exact h2.ne_top
      -- simp  [toNNReal_mul, toNNReal_rpow, toNNReal_div, coe_mul]
      refine ?_
      sorry -- use t = (C * (2 / μ A) ^ p.toReal⁻¹)
    -- Find a way to make a contradiction from h5, it is mathematically clear, we need a lemma from
    -- Mathlib that says that h5 → μ A = 0, then the contradiction comes from h
    have h6 : μ A = 0 := by sorry
    exact h h6

/-
2. Prove a variant `HasWeakType.MB_one` but for the function `MB` that
has codomain `ENNReal`.
-/

end MeasureTheory