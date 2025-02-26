import Carleson.Defs
import Carleson.ToMathlib.HardyLittlewood

open MeasureTheory Set Bornology Function ENNReal Metric Filter Topology
open Classical
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]
variable {f : X → ℂ} {α : ℝ≥0∞}

/-! ## Section 10.2 and Lemma 10.0.3

Question: -/

/-- The constant used in `nontangential_from_simple`.
I(F) think the constant needs to be fixed in the blueprint. -/
irreducible_def C10_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (4 * a)

/-- Lemma 10.2.1, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem maximal_theorem (ha : 4 ≤ a) :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  apply HasWeakType.hasBoundedWeakType
  have : C10_2_1 a = (defaultA a) ^ 4 := by
    simp_rw [C10_2_1_def, defaultA, pow_mul', Nat.cast_pow, Nat.cast_ofNat]
  rw [this]
  rw [← hasWeakType_toReal_iff sorry /- remove if we remove the `toReal` from
    `hasWeakType_globalMaximalFunction`. -/]
  -- for some reason `exact` goes on a wild goose chase on the next line
  apply hasWeakType_globalMaximalFunction le_rfl le_rfl


/-- Lemma 10.2.2.
Should be an easy consequence of `VitaliFamily.ae_tendsto_average`. -/
theorem lebesgue_differentiation
    {f : X → ℂ} (hmf : Measurable f) (hf : eLpNorm f ∞ < ∞) (h2f : volume (support f) < ∞) :
    ∀ᵐ x ∂volume, ∃ (c : ℕ → X) (r : ℕ → ℝ),
    Tendsto (fun i ↦ ⨍ y in ball (c i) (r i), f y ∂volume) atTop (𝓝 (f x)) ∧
    Tendsto r atTop (𝓝[>] 0) ∧
    ∀ i, x ∈ ball (c i) (r i) := by
  sorry


/-! Lemma 10.2.3 is in Mathlib: `Pairwise.countable_of_isOpen_disjoint`. -/

/-- Lemma 10.2.4
This is very similar to `Vitali.exists_disjoint_subfamily_covering_enlargement`.
Can we use that (or adapt it so that we can use it)?  -/
theorem ball_covering {O : Set X} (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ closedBall (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, ¬ Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, Cardinal.mk { i | x ∈ ball (c i) (3 * r i)} ≤ (2 ^ (6 * a) : ℕ) := by
  sorry

/-! ### Remarks about Lemma 10.2.5

Lemma 10.2.5 has an annoying case distinction between the case `E_α ≠ X` (general case) and
`E_α = X` (finite case). It isn't easy to get rid of this case distinction.

In the formalization we state most properties of Lemma 10.2.5 twice, once for each case
(in some cases the condition is vacuous in the finite case, and then we omit it)

We could have tried harder to uniformize the cases, but in the finite case there is really only set
`B*_j`, and in the general case it is convenient to index `B*_j` by the natural numbers.
-/

/-- An auxillary definition bundling the properties of Lemma 10.2.5
so that we don't have to write this every time.
Slightly weaker than `BoundedCompactSupport`. -/
def BoundedFiniteSupport (f : X → ℂ) : Prop :=
  Measurable f ∧ eLpNorm f ∞ < ∞ ∧ volume (support f) < ∞

/-- The property specifying whether we are in the "general case". -/
def GeneralCase (f : X → ℂ) (α : ℝ≥0∞) : Prop :=
  ∃ x, α < globalMaximalFunction (X := X) volume 1 f x

/-- In the finite case, the volume of `X` is finite. -/
lemma volume_lt_of_not_GeneralCase (h : ¬ GeneralCase f α) : volume (univ : Set X) < ∞ :=
  sorry -- Use Lemma 10.2.1

/- Use `lowerSemiContinuous_globalMaximalFunction` for part 1. -/
lemma isOpen_MB_preimage_Ioi (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α) ∧
    globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ := by
  sorry

/-- The center of B_j in the proof of Lemma 10.2.5 (general case). -/
def czCenter (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : X :=
  ball_covering (isOpen_MB_preimage_Ioi hf hX) |>.choose i

/-- The radius of B_j in the proof of Lemma 10.2.5 (general case). -/
def czRadius (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : ℝ :=
  ball_covering (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose i

/-- The ball B_j in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hf hX i) (czRadius hf hX i)

/-- The ball B_j' introduced below Lemma 10.2.5 (general case). -/
abbrev czBall2 (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hf hX i) (2 * czRadius hf hX i)

/-- The ball B_j* in Lemma 10.2.5 (general case). -/
abbrev czBall3 (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hf hX i) (3 * czRadius hf hX i)

/-- The ball B_j** in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall7 (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hf hX i) (7 * czRadius hf hX i)

lemma czBall_pairwiseDisjoint {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ closedBall (czCenter hf hX i) (czRadius hf hX i) :=
  ball_covering (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.1

lemma iUnion_czBall3 {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    ⋃ i, czBall3 hf hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  ball_covering (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_czBall7 {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {i : ℕ} :
    ¬ Disjoint (czBall7 hf hX i) (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ :=
  ball_covering (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.2.2.1 i

/-- Part of Lemma 10.2.5 (general case). -/
lemma cardinalMk_czBall3_le {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    Cardinal.mk { i | y ∈ czBall3 hf hX i} ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.2.2.2 y hy

lemma mem_czBall3_finite {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    { i | y ∈ czBall3 hf hX i}.Finite :=
  sorry

/-- `Q_i` in the proof of Lemma 10.2.5 (general case). -/
def czPartition (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  czBall3 hf hX i \ ((⋃ j < i, czPartition hf hX j) ∪ ⋃ j > i, czBall hf hX i)

lemma czBall_subset_czPartition {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {i : ℕ} :
    czBall hf hX i ⊆ czPartition hf hX i := by
  sorry

lemma czPartition_subset_czBall3 {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {i : ℕ} :
    czPartition hf hX i ⊆ czBall3 hf hX i := by
  rw [czPartition]; exact diff_subset

lemma czPartition_pairwiseDisjoint {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ czPartition hf hX i :=
  sorry

lemma czPartition_pairwiseDisjoint' {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {x : X} {i j : ℕ} (hi : x ∈ czPartition hf hX i) (hj : x ∈ czPartition hf hX j) :
    i = j :=
  sorry

lemma iUnion_czPartition {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    ⋃ i, czPartition hf hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  sorry

/-- The function `g` in Lemma 10.2.5. (both cases) -/
def czApproximation (hf : BoundedFiniteSupport f) (α : ℝ≥0∞) (x : X) : ℂ :=
  if hX : GeneralCase f α then
    if hx : ∃ j, x ∈ czPartition hf hX j then ⨍ y in czPartition hf hX hx.choose, f y else f x
  else ⨍ y, f y

lemma czApproximation_def_of_mem {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {x : X}
    {i : ℕ} (hx : x ∈ czPartition hf hX i) :
    czApproximation hf α x = ⨍ y in czPartition hf hX i, f y := by
  have : ∃ i, x ∈ czPartition hf hX i := ⟨i, hx⟩
  simp [czApproximation, hX, this, czPartition_pairwiseDisjoint' this.choose_spec hx]

lemma czApproximation_def_of_nmem {hf : BoundedFiniteSupport f} {x : X} (hX : GeneralCase f α)
    (hx : x ∉ globalMaximalFunction volume 1 f ⁻¹' Ioi α) :
    czApproximation hf α x = f x := by
  rw [← iUnion_czPartition (hf := hf) (hX := hX), mem_iUnion, not_exists] at hx
  simp only [czApproximation, hX, ↓reduceDIte, hx, exists_const]

lemma czApproximation_def_of_volume_lt {hf : BoundedFiniteSupport f} {x : X}
    (hX : ¬ GeneralCase f α) : czApproximation hf α x = ⨍ y, f y := by
  simp [czApproximation, hX]

/-- The function `b_i` in Lemma 10.2.5 (general case). -/
def czRemainder' (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) (x : X) : ℂ :=
  (czPartition hf hX i).indicator (f - czApproximation hf α) x

/-- The function `b = ∑ⱼ bⱼ` introduced below Lemma 10.2.5.
In the finite case, we also use this as the function `b = b₁` in Lemma 10.2.5.
We choose a more convenient definition, but prove in `tsum_czRemainder'` that this is the same. -/
def czRemainder (hf : BoundedFiniteSupport f) (α : ℝ≥0∞) (x : X) : ℂ :=
  f x - czApproximation hf α x

/-- Part of Lemma 10.2.5, this is essentially (10.2.16) (both cases). -/
def tsum_czRemainder' (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (x : X) :
      ∑ᶠ i, czRemainder' hf hX i x = czRemainder hf α x := by
    sorry

/-- Part of Lemma 10.2.5 (both cases). -/
lemma measurable_czApproximation {hf : BoundedFiniteSupport f} :
    Measurable (czApproximation hf α) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.16) (both cases).
This is true by definition, the work lies in `tsum_czRemainder'` -/
lemma czApproximation_add_czRemainder {hf : BoundedFiniteSupport f} {x : X} :
    czApproximation hf α x + czRemainder hf α x = f x := by
  simp [czApproximation, czRemainder]

/-- Part of Lemma 10.2.5, equation (10.2.17) (both cases). -/
lemma norm_czApproximation_le {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    ∀ᵐ x, ‖czApproximation hf α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  sorry

/-- Equation (10.2.17) specialized to the general case. -/
lemma norm_czApproximation_le_infinite {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∀ᵐ x, ‖czApproximation hf α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.18) (both cases). -/
lemma eLpNorm_czApproximation_le {hf : BoundedFiniteSupport f} (hα : 0 < α) :
    eLpNorm (czApproximation hf α) 1 volume ≤ eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.19) (general case). -/
lemma support_czRemainder'_subset {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} (hα : 0 < α)
    {i : ℕ} :
    support (czRemainder' hf hX i) ⊆ czBall3 hf hX i := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.20) (general case). -/
lemma integral_czRemainder' {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} (hα : 0 < α)
    {i : ℕ} :
    ∫ x, czRemainder' hf hX i x = 0 := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.20) (finite case). -/
lemma integral_czRemainder {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    ∫ x, czRemainder hf α x = 0 := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.21) (general case). -/
lemma eLpNorm_czRemainder'_le {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} (hα : 0 < α)
    {i : ℕ} :
    eLpNorm (czRemainder' hf hX i) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 hf hX i) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.21) (finite case). -/
lemma eLpNorm_czRemainder_le {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    eLpNorm (czRemainder hf α) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.22) (general case). -/
lemma tsum_volume_czBall3_le {hf : BoundedFiniteSupport f} (hX : GeneralCase f α) (hα : 0 < α) :
    ∑' i, volume (czBall3 hf hX i) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.22) (finite case). -/
lemma volume_univ_le {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    volume (univ : Set X) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.23) (general case). -/
lemma tsum_eLpNorm_czRemainder'_le {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∑' i, eLpNorm (czRemainder' hf hX i) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.23) (finite case). -/
lemma tsum_eLpNorm_czRemainder_le {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    eLpNorm (czRemainder hf α) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  sorry

/- ### Lemmas 10.2.6 - 10.2.9 -/

/-- The constant `c` introduced below Lemma 10.2.5. -/
irreducible_def c10_0_3 (a : ℕ) : ℝ≥0 := (2 ^ (a ^ 3 + 12 * a + 4))⁻¹

/-- The set `Ω` introduced below Lemma 10.2.5. -/
def Ω (hf : BoundedFiniteSupport f) (α : ℝ≥0∞) : Set X :=
  if hX : GeneralCase f α then ⋃ i, czBall2 hf hX i else univ

/-- The constant used in `estimate_good`. -/
irreducible_def C10_2_6 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a ^ 3 + 3 * a + 2) * c10_0_3 a

/-- Lemma 10.2.6 -/
lemma estimate_good {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) :
    distribution (czOperator K r (czApproximation hf α)) (α / 2) volume ≤
    C10_2_6 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `czOperatorBound`. -/
irreducible_def C10_2_7 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1) * c10_0_3 a

/-- The function `F` defined in Lemma 10.2.7. -/
def czOperatorBound (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * ∑' i, ((czRadius hf hX i).toNNReal / nndist x (czCenter hf hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 hf hX i) / volume (ball x (dist x (czCenter hf hX i)))

/-- Lemma 10.2.7.
Note that `hx` implies `hX`, but we keep the superfluous hypothesis to shorten the statement. -/
lemma estimate_bad_partial {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hx : x ∈ (Ω hf α)ᶜ) (hX : GeneralCase f α) :
    ‖czOperator K r (czRemainder hf α) x‖ₑ ≤ 3 * czOperatorBound hf hX x + α / 8 := by
  sorry

/-- The constant used in `distribution_czOperatorBound`. -/
irreducible_def C10_2_8 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.8 -/
lemma distribution_czOperatorBound {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    volume ((Ω hf α)ᶜ ∩ czOperatorBound hf hX ⁻¹' Ioi (α / 8)) ≤
    C10_2_8 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `estimate_bad`. -/
irreducible_def C10_2_9 (a : ℕ) : ℝ≥0 := 2 ^ (5 * a) / c10_0_3 a + 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.9 -/
-- In the proof, case on `GeneralCase f α`, noting in the finite case that `Ω = univ`
lemma estimate_bad {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    distribution (czOperator K r (czRemainder hf α)) (α / 2) volume ≤
    C10_2_9 a / α * eLpNorm f 1 volume := by
  sorry


/- ### Lemmas 10.0.3 -/

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
-- in proof: do cases on `α ≤ ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a`.
-- If true, use the argument directly below (10.2.37)
theorem czoperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
