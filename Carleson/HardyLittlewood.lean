import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Covering.VitaliFamily

open MeasureTheory Metric Bornology Set
open scoped NNReal ENNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

-- #check VitaliFamily

variable {X E} [MetricSpace X] [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure X} {f : X → E} {x : X} {𝓑 : Finset (X × ℝ)}

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑. -/
def maximalFunction (μ : Measure X) (𝓑 : Set (X × ℝ)) (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ z ∈ 𝓑, (ball z.1 z.2).indicator (x := x)
  fun _ ↦ ⨍⁻ y, ‖u y‖₊ ∂μ.restrict (ball z.1 z.2)) ^ p⁻¹

abbrev MB (μ : Measure X) (𝓑 : Set (X × ℝ)) (u : X → E) (x : X) := maximalFunction μ 𝓑 1 u x

-- old
-- /-- Hardy-Littlewood maximal function -/
-- def maximalFunction (μ : Measure X) (f : X → E) (x : X) : ℝ :=
--   ⨆ (x' : X) (δ : ℝ) (_hx : x ∈ ball x' δ),
--   ⨍⁻ y, ‖f y‖₊ ∂μ.restrict (ball x' δ) |>.toReal

/-! The following results probably require a doubling measure,
and maybe some properties from `ProofData`.
They are the statements from the blueprint.
We probably want a more general version first. -/

theorem measure_biUnion_le_lintegral {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l)
    {u : X → ℝ≥0} (hu : AEStronglyMeasurable u μ)
    (h2u : ∀ z ∈ 𝓑, l * μ (ball z.1 z.2) ≤ ∫⁻ x in ball z.1 z.2, u x ∂μ)
    :
    l * μ (⋃ z ∈ 𝓑, ball z.1 z.2) ≤ 2 ^ (2 * a) * ∫⁻ x, u x ∂μ  := by
  sorry

theorem maximalFunction_lt_top {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l) {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : Memℒp u p₂ μ) {x : X} :
    maximalFunction μ 𝓑 p₁ u x < ∞ := by
  sorry

theorem snorm_maximalFunction {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l) {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : AEStronglyMeasurable u μ) :
    snorm (maximalFunction μ 𝓑 p₁ u · |>.toReal) p₂ μ ≤
    2 ^ (2 * a) * p₂ / (p₂ - p₁) * snorm u p₂ μ := by
  sorry

theorem Memℒp.maximalFunction {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l) {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : Memℒp u p₂ μ) :
    Memℒp (maximalFunction μ 𝓑 p₁ u · |>.toReal) p₂ μ := by
  sorry

/-- The transformation M characterized in Proposition 2.0.6. -/
def M (u : X → ℂ) (x : X) : ℝ≥0∞ := sorry

theorem M_lt_top {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l) {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {x : X} : M u x < ∞ := by
  sorry

theorem laverage_le_M {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} :
     ⨍⁻ y, ‖u y‖₊ ∂μ.restrict (ball z r) ≤ M u x := by
  sorry

theorem snorm_M_le {a : ℝ} (ha : 4 ≤ a) {l : ℝ≥0} (hl : 0 < l){p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} :
    snorm (fun x ↦ (M (fun x ↦ u x ^ (p₁ : ℂ)) x).toReal ^ (p₁⁻¹ : ℝ)) p₂ μ ≤
    2 ^ (4 * a)  * p₂ / (p₂ - p₁) * snorm u p₂ μ := by
  sorry
