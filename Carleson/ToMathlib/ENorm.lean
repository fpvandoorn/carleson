import Mathlib.Analysis.NormedSpace.IndicatorFunction
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

-- these imports are only needed in the `tmp` section
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.MeasureTheory.Covering.Vitali

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

/-- The property that `f : α → E` is a.e. strongly measurable and `(∫ ‖f a‖^p ∂μ)^(1/p)` is finite
if `p < ∞`, or `essSup f < ∞` if `p = ∞`. -/
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

lemma wnorm'_zero [ENorm E] (f : α → E) (μ : Measure α) : wnorm' f 0 μ = ∞ := by
  simp only [wnorm, zero_ne_top, ↓reduceIte, wnorm', zero_toReal, GroupWithZero.inv_zero,
    ENNReal.rpow_zero, mul_one, iSup_eq_top]
  refine fun b hb ↦ ⟨b.toNNReal + 1, ?_⟩
  rw [coe_add, ENNReal.coe_one, coe_toNNReal hb.ne_top]
  exact lt_add_right hb.ne_top one_ne_zero

lemma wnorm_zero [ENorm E] (f : α → E) (μ : Measure α) : wnorm f 0 μ = ∞ := by
  simp [wnorm, wnorm'_zero]

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWℒp [TopologicalSpace E] [ENorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma MemWℒp_zero [TopologicalSpace E] [ENorm E] (f : α → E) (μ : Measure α) : ¬ MemWℒp f 0 μ := by
  simp [MemWℒp, wnorm_zero]

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

/- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/18704. -/
lemma _root_.ENNReal.inv_div {a b : ℝ≥0∞} (h1 : b ≠ ∞ ∨ a ≠ ∞) (h2 : b ≠ 0 ∨ a ≠ 0) :
    (a / b)⁻¹ = b / a := by
  rw [← ENNReal.inv_ne_zero] at h1
  rw [← ENNReal.inv_ne_top] at h2
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv h1 h2, mul_comm, inv_inv]

/-- If a function `f : α → ENNReal` is `MemWℒp`, then its norm is almost everywhere finite.-/
theorem MemWℒp.ae_ne_top [TopologicalSpace E] [ENorm E] {f : α → E} {p : ℝ≥0∞} {μ : Measure α}
    (hf : MemWℒp f p μ) : ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
  by_cases hp_inf : p = ∞
  · rw [hp_inf] at hf
    simp_rw [← lt_top_iff_ne_top]
    exact ae_lt_of_essSup_lt hf.2
  by_cases hp_zero : p = 0
  · exact (MemWℒp_zero _ _ <| hp_zero ▸ hf).elim
  set A := {x | ‖f x‖ₑ = ∞} with hA
  unfold MemWℒp wnorm wnorm' at hf
  simp only [hp_inf] at hf
  rw [Filter.eventually_iff, mem_ae_iff]
  simp only [ne_eq, compl_def, mem_setOf_eq, Decidable.not_not, ← hA]
  have hp_toReal_zero := toReal_ne_zero.mpr ⟨hp_zero, hp_inf⟩
  have h1 (t : ℝ≥0) : μ A ≤ distribution f t μ := by
    refine μ.mono ?_
    simp_all only [setOf_subset_setOf, coe_lt_top, implies_true, A]
  set C := ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹
  by_cases hC_zero : C = 0
  · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
    specialize hC_zero 1
    simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_lt, and_false, or_false,
      false_or] at hC_zero
    exact measure_mono_null (setOf_subset_setOf.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
  by_contra h
  have h2 : C < ∞ := by aesop
  have h3 (t : ℝ≥0) : distribution f t μ ≤ (C / t) ^ p.toReal := by
    rw [← rpow_inv_rpow hp_toReal_zero (distribution ..)]
    refine rpow_le_rpow ?_ toReal_nonneg
    rw [ENNReal.le_div_iff_mul_le (Or.inr hC_zero) (Or.inl coe_ne_top), mul_comm]
    exact le_iSup_iff.mpr fun _ a ↦ a t
  have h4 (t : ℝ≥0) : μ A ≤ (C / t) ^ p.toReal := (h1 t).trans (h3 t)
  have h5 : μ A ≤ μ A / 2 := by
    convert h4 (C * (2 / μ A) ^ p.toReal⁻¹).toNNReal
    rw [coe_toNNReal ?_]
    swap
    · refine mul_ne_top h2.ne_top (rpow_ne_top_of_nonneg (inv_nonneg.mpr toReal_nonneg) ?_)
      simp [div_eq_top, h]
    nth_rw 1 [← mul_one C]
    rw [ENNReal.mul_div_mul_left _ _ hC_zero h2.ne_top, div_rpow_of_nonneg _ _ toReal_nonneg,
      ENNReal.rpow_inv_rpow hp_toReal_zero, ENNReal.one_rpow, one_div,
        ENNReal.inv_div (Or.inr two_ne_top) (Or.inr (NeZero.ne' 2).symm)]
  have h6 : μ A = 0 := by
    convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top (rpow_ne_top_of_nonneg
      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt h5.not_lt
    tauto
  exact h h6

-- Maybe this statement is not needed, we can just use the previous one.
/-- If a function `f : α → ENNReal` is `MemWℒp`, then it is almost everywhere finite.-/
theorem MemWℒp.ae_ne_top' {f : α → ENNReal} {p : ℝ≥0∞} {μ : Measure α}
    (hf : MemWℒp f p μ) : ∀ᵐ x ∂μ, f x ≠ ∞ := hf.ae_ne_top

/- Add temporary section. -/
section tmp

/- Copy-pasted all this code here temporarily to be able to prove `HasWeakType.MB_one'` while avoiding the import conflicts, the problem is that this file redefines some objects that are imported in the files that define `IsDoubling`, `MB` ecc. When these definitions will replace the old ones this can be fixed
-/

open Metric Vitali MeasureTheory Measure

/-- A doubling measure is a measure on a metric space with the condition doubling
the radius of a ball only increases the volume by a constant factor, independent of the ball. -/
class Measure.IsDoubling {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (A : outParam ℝ≥0) : Prop where
  measure_ball_two_le_same : ∀ (x : X) r, μ (ball x (2 * r)) ≤ A * μ (ball x r)

variable {X E : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsDoubling A] [NormedAddCommGroup E]
  {f : X → E} {x : X} {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ}

section laverage

variable (μ : Measure α)

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`, denoted `⨍⁻ x, f x ∂μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def laverage (f : α → ℝ≥0∞) := ∫⁻ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => laverage μ r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ s)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `s` has infinite measure. If `s`
has measure `1`, then the average of any function is equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => laverage (Measure.restrict μ s) r

theorem laverage_eq' (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ := rfl

theorem laverage_eq (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ := by
  rw [laverage_eq', lintegral_smul_measure, ENNReal.div_eq_inv_mul]

theorem setLaverage_eq (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s := by rw [laverage_eq, restrict_apply_univ]

end laverage

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑.
M_{𝓑, p} in the blueprint. -/
def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ)
  (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
  fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖u y‖₊ ^ p ∂μ) ^ p⁻¹

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑 with exponent 1.
M_𝓑 in the blueprint. -/
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ 𝓑 c r 1 u x

-- todo: move
-- slightly more general than the Mathlib version
-- the extra conclusion says that if there is a nonnegative radius, then we can choose `r b` to be
-- larger than `r a` (up to a constant)
theorem exists_disjoint_subfamily_covering_enlargement_closedBall' {α} [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) ∧
        (∀ u ∈ t, 0 ≤ r u → r a ≤ (τ - 1) / 2 * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases ht : ∀ a ∈ t, r a < 0
  · refine ⟨t, .rfl, fun a ha b _ _ ↦ by
      simp only [Function.onFun, closedBall_eq_empty.2 (ht a ha), empty_disjoint],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset],
      fun u hut hu ↦ (ht u hut).not_le hu |>.elim⟩⟩
  push_neg at ht
  let t' := { a ∈ t | 0 ≤ r a }
  have h2τ : 1 < (τ - 1) / 2 := by linarith
  rcases exists_disjoint_subfamily_covering_enlargment (fun a => closedBall (x a) (r a)) t' r
      ((τ - 1) / 2) h2τ (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closedBall_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) ∧
    ∀ u ∈ t, 0 ≤ r u → r a ≤ (τ - 1) / 2 * r b := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) ≤ r a + r b := dist_le_add_of_nonempty_closedBall_inter_closedBall hb
    exact ⟨closedBall_subset_closedBall' <| by linarith, fun _ _ _ ↦ rb⟩
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases le_or_lt 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _, hc⟩
    refine ⟨c, cu, by simp only [closedBall_eq_empty.2 h'a, empty_subset], fun _ _ _ ↦ ?_⟩
    have : 0 ≤ r c := nonneg_of_mul_nonneg_right (rb.2.trans <| hc b rb.1 rb.2) (by positivity)
    exact h'a.le.trans <| by positivity

-- move to Vitali
theorem Vitali.exists_disjoint_subfamily_covering_enlargement_ball {α} [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => ball (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
  obtain ⟨σ, hσ, hστ⟩ := exists_between hτ
  obtain ⟨u, hut, hux, hu⟩ :=
    exists_disjoint_subfamily_covering_enlargement_closedBall' t x r R hr σ hσ
  refine ⟨u, hut, fun i hi j hj hij ↦ ?_, fun a ha => ?_⟩
  · exact (hux hi hj hij).mono ball_subset_closedBall ball_subset_closedBall
  obtain ⟨b, hbu, hb⟩ := hu a ha
  refine ⟨b, hbu, ?_⟩
  obtain h2a|h2a := le_or_lt (r a) 0
  · simp_rw [ball_eq_empty.mpr h2a, empty_subset]
  refine ball_subset_closedBall.trans hb.1 |>.trans <| closedBall_subset_ball ?_
  gcongr
  apply pos_of_mul_pos_right <| h2a.trans_le <| hb.2 a ha h2a.le
  linarith

/- NOTE: This was changed to use `ℝ≥0∞` rather than `ℝ≥0` because that was more convenient for the
proof of `first_exception'` in ExceptionalSet.lean. But everything involved there is finite, so
you can prove this with `ℝ≥0` and deal with casting between `ℝ≥0` and `ℝ≥0∞` there, if that turns
out to be easier. -/
theorem _root_.Set.Countable.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (h𝓑 : 𝓑.Countable)
    (l : ℝ≥0∞) (u : X → ℝ≥0∞) (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  obtain ⟨B, hB𝓑, hB, h2B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    𝓑 c r R hR (2 ^ 2) (by norm_num)
  have : Countable B := h𝓑.mono hB𝓑
  have disj := fun i j hij ↦
    hB (Subtype.coe_prop i) (Subtype.coe_prop j) (Subtype.coe_ne_coe.mpr hij)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
          refine l.mul_left_mono (μ.mono fun x hx ↦ ?_)
          simp only [mem_iUnion, mem_ball, exists_prop] at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑
          refine mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) :=
          l.mul_left_mono <| measure_biUnion_le μ (h𝓑.mono hB𝓑) fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
          refine l.mul_left_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
          rw [sq, sq, mul_assoc, mul_assoc]
          apply (Measure.IsDoubling.measure_ball_two_le_same (c i) (2 * r i)).trans
          exact ENNReal.mul_left_mono (Measure.IsDoubling.measure_ball_two_le_same (c i) (r i))
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc, mul_comm l]
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := by
          gcongr; exact h2u _ (hB𝓑 (Subtype.coe_prop _))
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := by
          congr; simpa using (lintegral_iUnion (fun i ↦ measurableSet_ball) disj u).symm
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := by
          gcongr; exact setLIntegral_le_lintegral (⋃ i ∈ B, ball (c i) (r i)) u

protected theorem AEStronglyMeasurable.maximalFunction [BorelSpace X] {p : ℝ}
    {u : X → E} (h𝓑 : 𝓑.Countable) : AEStronglyMeasurable (maximalFunction μ 𝓑 c r p u) μ :=
  (AEMeasurable.biSup 𝓑 h𝓑 fun _ _ ↦ aemeasurable_const.indicator measurableSet_ball).pow
    aemeasurable_const |>.aestronglyMeasurable

protected theorem HasWeakType.MB_one' [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    HasWeakType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) 1 1 μ μ (A ^ 2) := by
  intro f _
  use AEStronglyMeasurable.maximalFunction h𝓑
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖₊ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, wnorm', one_toReal, inv_one, ENNReal.rpow_one, reduceIte,
    ENNReal.coe_pow, eLpNorm, one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self,
    iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hBₗ : (Bₗ t).Countable := h𝓑.mono (fun i hi ↦ mem_of_mem_inter_left hi)
  refine le_trans ?_ (hBₗ.measure_biUnion_le_lintegral (c := c) (r := r) (l := t)
    (u := fun x ↦ ‖f x‖₊) (R := R) ?_ ?_)
  · refine mul_left_mono <| μ.mono (fun x hx ↦ mem_iUnion₂.mpr ?_)
    -- We need a ball in `Bₗ t` containing `x`. Since `MB μ 𝓑 c r f x` is large, such a ball exists
    simp only [mem_setOf_eq] at hx
    -- replace hx := lt_of_lt_of_le hx coe_toNNReal_le_self
    simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one] at hx
    obtain ⟨i, ht⟩ := lt_iSup_iff.mp hx
    replace hx : x ∈ ball (c i) (r i) :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    refine ⟨i, ?_, hx⟩
    -- It remains only to confirm that the chosen ball is actually in `Bₗ t`
    simp only [ge_iff_le, mem_setOf_eq, Bₗ]
    have hi : i ∈ 𝓑 :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    exact ⟨hi, mul_le_of_le_div <| le_of_lt (by simpa [setLaverage_eq, hi, hx] using ht)⟩
  · exact fun i hi ↦ hR i (mem_of_mem_inter_left hi)
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

end tmp

end MeasureTheory
