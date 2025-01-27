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

/-! ## Section 10.2 and Lemma 10.0.3 -/

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
    Tendsto (fun i => ⨍ y in ball (c i) (r i), f y ∂volume) atTop (𝓝 (f x)) ∧
    Tendsto r atTop (𝓝[>] 0) ∧
    ∀ i, x ∈ ball (c i) (r i) := by
  sorry


/-! Lemma 10.2.3 is in Mathlib: `Pairwise.countable_of_isOpen_disjoint`. -/

/-- Lemma 10.2.4
Can we use `Vitali.exists_disjoint_subfamily_covering_enlargement` (or adapt it so that we
can use it)?  -/
theorem ball_covering {O : Set X} (hO : IsOpen O) :
    ∃ (s : Set X) (r : X → ℝ), s.Countable ∧ (s.PairwiseDisjoint fun a => closedBall a (r a)) ∧
      ⋃ x ∈ s, ball x (3 * r x) = O ∧ (∀ x ∈ s, ¬ Disjoint (ball x (7 * r x)) Oᶜ) ∧
      ∀ x ∈ O, Cardinal.mk { y ∈ s | x ∈ ball y (3 * r y)} ≤ (2 ^ (6 * a) : ℕ) := by
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
