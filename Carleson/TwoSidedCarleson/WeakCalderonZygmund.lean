import Carleson.Defs
import Carleson.ToMathlib.HardyLittlewood

open MeasureTheory Set Bornology Function ENNReal Metric Filter Topology
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

/-- An auxillary definition so that we don't have to write this every time.
Can we use `BoundedCompactSupport` for this? -/
def BdMeasurable (f : X → ℂ) (α : ℝ≥0∞) : Prop :=
  Measurable f ∧ eLpNorm f ∞ < ∞ ∧ volume (support f) < ∞ ∧
  globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ

/- Use `lowerSemiContinuous_globalMaximalFunction` -/
lemma isOpen_MB_preimage_Ioi (hf : BdMeasurable f α) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α) ∧
    globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ := by
  sorry

/-- The center of B_j in the proof of Lemma 10.2.5. -/
def czCenter (hf : BdMeasurable f α) (i : ℕ) : X :=
  ball_covering (isOpen_MB_preimage_Ioi hf) |>.choose i

/-- The radius of B_j in the proof of Lemma 10.2.5. -/
def czRadius (hf : BdMeasurable f α) (i : ℕ) : ℝ :=
  ball_covering (isOpen_MB_preimage_Ioi hf) |>.choose_spec.choose i

/-- The ball B_j in the proof of Lemma 10.2.5. -/
abbrev czBall (hf : BdMeasurable f α) (i : ℕ) : Set X :=
  ball (czCenter hf i) (czRadius hf i)

/-- The ball B_j* in Lemma 10.2.5. -/
abbrev czBall3 (hf : BdMeasurable f α) (i : ℕ) : Set X :=
  ball (czCenter hf i) (3 * czRadius hf i)

/-- The ball B_j** in the proof of Lemma 10.2.5. -/
abbrev czBall7 (hf : BdMeasurable f α) (i : ℕ) : Set X :=
  ball (czCenter hf i) (7 * czRadius hf i)

lemma czBall_pairwiseDisjoint {hf : BdMeasurable f α} :
    univ.PairwiseDisjoint fun i ↦ closedBall (czCenter hf i) (czRadius hf i) :=
  ball_covering (isOpen_MB_preimage_Ioi hf) |>.choose_spec.choose_spec.1

lemma iUnion_czBall3 {hf : BdMeasurable f α} :
    ⋃ i, czBall3 hf i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  ball_covering (isOpen_MB_preimage_Ioi hf) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_czBall7 {hf : BdMeasurable f α} {i : ℕ} :
    ¬ Disjoint (czBall7 hf i) (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ :=
  ball_covering (isOpen_MB_preimage_Ioi hf) |>.choose_spec.choose_spec.2.2.1 i

lemma cardinalMk_czBall3_le {hf : BdMeasurable f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    Cardinal.mk { i | y ∈ czBall3 hf i} ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering (isOpen_MB_preimage_Ioi hf) |>.choose_spec.choose_spec.2.2.2 y hy

/-- `Q_i` in the proof of Lemma 10.2.5. -/
def czPartition (hf : BdMeasurable f α) (i : ℕ) : Set X :=
  czBall3 hf i \ ((⋃ j < i, czPartition hf j) ∪ ⋃ j > i, czBall hf i)

lemma czBall_subset_czPartition {hf : BdMeasurable f α} {i : ℕ} :
    czBall hf i ⊆ czPartition hf i := by
  sorry

lemma czPartition_subset_czBall3 {hf : BdMeasurable f α} {i : ℕ} :
    czPartition hf i ⊆ czBall3 hf i := by
  rw [czPartition]; exact diff_subset

lemma czPartition_pairwiseDisjoint {hf : BdMeasurable f α} :
    univ.PairwiseDisjoint fun i ↦ czPartition hf i :=
  sorry

lemma iUnion_czPartition {hf : BdMeasurable f α} :
    ⋃ i, czPartition hf i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  sorry

open Classical in
/-- The function `g` in Lemma 10.2.5. -/
def czApproximation (hf : BdMeasurable f α) (x : X) : ℂ :=
  if hx : ∃ j, x ∈ czPartition hf j then ⨍ y in czPartition hf hx.choose, f y else f x
  -- alternative definition:
  -- (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ.indicator f x +
  -- ∑' i, (czPartition hf i).indicator (fun _ ↦ ⨍ y in czPartition hf i, f y) x

lemma czApproximation_def_of_mem {hf : BdMeasurable f α} {x : X} {i : ℕ}
    (hx : x ∈ czPartition hf i) :
    czApproximation hf x = ⨍ y in czPartition hf i, f y := by
  sorry

lemma czApproximation_def_of_nmem {hf : BdMeasurable f α} {x : X} {i : ℕ}
    (hx : x ∉ globalMaximalFunction volume 1 f ⁻¹' Ioi α) :
    czApproximation hf x = f x := by
  sorry

/-- The function `b_i` in Lemma 10.2.5 -/
def czRemainder (hf : BdMeasurable f α) (i : ℕ) (x : X) : ℂ :=
  (czPartition hf i).indicator (f - czApproximation hf) x

/-- Lemma 10.2.5. -/
theorem calderon_zygmund_decomposition
    {f : X → ℂ} (hmf : Measurable f) (hf : eLpNorm f ∞ < ∞) (h2f : volume (support f) < ∞)
    {α : ℝ≥0} (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    -- do we need the special case B₁ = X?
    -- b j x = b_j(x)
    ∃ (g : X → ℂ) (hg : Measurable g) (s : Set X) (r : X → ℝ) (b : X → X → ℂ),
    s.Countable ∧
    (∀ x, Cardinal.mk { j ∈ s | x ∈ ball j (3 * r j)} ≤ (2 ^ (6 * a) : ℕ)) ∧
    (∀ x, f x = g x + tsum (s.indicator (b · x))) ∧
    eLpNorm g ∞ volume ≤ 2 ^ (3 * a) * α ∧
    ∫⁻ x, ‖g x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∧
    (∀ j ∈ s, support (b j) ⊆ ball j (r j)) ∧
    (∀ j ∈ s, ∫ x, b j x = 0) ∧
    (∀ j ∈ s, eLpNorm (b j) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (ball j (r j))) ∧
    (tsum (s.indicator (fun j ↦ volume (ball j (r j)))) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume) ∧
    (tsum (s.indicator (fun j ↦ eLpNorm (b j) 1 volume)) ≤ 2 * eLpNorm f 1) := by
  sorry

/-- Lemma 10.2.5.
To check: are we using `volume univ < ∞`? -/
theorem calderon_zygmund_decomposition
    {f : X → ℂ} (hmf : Measurable f) (hf : eLpNorm f ∞ < ∞) (h2f : volume (support f) < ∞)
    {α : ℝ≥0} (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    -- do we need the special case B₁ = X?
    -- b j x = b_j(x)
    ∃ (g : X → ℂ) (hg : Measurable g) (s : Set X) (r : X → ℝ) (b : X → X → ℂ),
    s.Countable ∧
    (∀ x, Cardinal.mk { j ∈ s | x ∈ ball j (3 * r j)} ≤ (2 ^ (6 * a) : ℕ)) ∧
    (∀ x, f x = g x + tsum (s.indicator (b · x))) ∧
    eLpNorm g ∞ volume ≤ 2 ^ (3 * a) * α ∧
    ∫⁻ x, ‖g x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∧
    (∀ j ∈ s, support (b j) ⊆ ball j (r j)) ∧
    (∀ j ∈ s, ∫ x, b j x = 0) ∧
    (∀ j ∈ s, eLpNorm (b j) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (ball j (r j))) ∧
    (tsum (s.indicator (fun j ↦ volume (ball j (r j)))) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume) ∧
    (tsum (s.indicator (fun j ↦ eLpNorm (b j) 1 volume)) ≤ 2 * eLpNorm f 1) := by
  sorry

/-- The constant `c` introduced below Lemma 10.2.5. -/
irreducible_def c10_0_3 (a : ℕ) : ℝ := (2 ^ (a ^ 3 + 12 * a + 4))⁻¹

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem czoperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (CZOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
