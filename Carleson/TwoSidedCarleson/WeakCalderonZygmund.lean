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
variable {f : X → ℂ}

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
theorem ball_covering {O : Set X} (hO : IsOpen O) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ closedBall (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, ¬ Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, Cardinal.mk { i | x ∈ ball (c i) (3 * r i)} ≤ (2 ^ (6 * a) : ℕ) := by
  sorry

/-- An auxillary definition so that we don't have to write this every time.
Can we use `BoundedCompactSupport` for this? -/
def BdMeasurable (f : X → ℂ) : Prop :=
  Measurable f ∧ eLpNorm f ∞ < ∞ ∧ volume (support f) < ∞

/- Use `lowerSemiContinuous_globalMaximalFunction` -/
lemma isOpen_MB_preimage_Ioi (hf : BdMeasurable f) (x : ℝ≥0∞) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi x) := by
  sorry

/-- The center of B_j in the proof of 10.2.5. -/
def czCenter (hf : BdMeasurable f) (x : ℝ≥0∞) (i : ℕ) : X :=
  ball_covering (isOpen_MB_preimage_Ioi hf x) |>.choose i

/-- The radius of B_j in the proof of 10.2.5. -/
def czRadius (hf : BdMeasurable f) (x : ℝ≥0∞) (i : ℕ) : ℝ :=
  ball_covering (isOpen_MB_preimage_Ioi hf x) |>.choose_spec.choose i

lemma cz_pairwiseDisjoint {hf : BdMeasurable f} {x : ℝ≥0∞} :
    univ.PairwiseDisjoint fun i ↦ closedBall (czCenter hf x i) (czRadius hf x i) :=
  ball_covering (isOpen_MB_preimage_Ioi hf x) |>.choose_spec.choose_spec.1

lemma biUnion_cz {hf : BdMeasurable f} {x : ℝ≥0∞} :
    ⋃ i, ball (czCenter hf x i) (3 * czRadius hf x i) =
    globalMaximalFunction volume 1 f ⁻¹' Ioi x :=
  ball_covering (isOpen_MB_preimage_Ioi hf x) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_cz {hf : BdMeasurable f} {x : ℝ≥0∞} {i : ℕ} :
    ¬ Disjoint (ball (czCenter hf x i) (7 * czRadius hf x i))
    (globalMaximalFunction volume 1 f ⁻¹' Ioi x)ᶜ :=
  ball_covering (isOpen_MB_preimage_Ioi hf x) |>.choose_spec.choose_spec.2.2.1 i

lemma cardinalMk_cz_le {hf : BdMeasurable f} {x : ℝ≥0∞} {y : X}
    (hy : x < globalMaximalFunction volume 1 f y) :
    Cardinal.mk { i | y ∈ ball (czCenter hf x i) (3 * czRadius hf x i)} ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering (isOpen_MB_preimage_Ioi hf x) |>.choose_spec.choose_spec.2.2.2 y hy


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




/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem czoperator_weak_1_1 (ha : 4 ≤ a)
    (hT : ∃ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (CZOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
