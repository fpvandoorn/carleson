import Carleson.DoublingMeasure
import Carleson.WeakType

open MeasureTheory Metric Bornology Set
open scoped NNReal ENNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

-- #check VitaliFamily
-- Note: Lemma 9.0.2 is roughly Vitali.exists_disjoint_covering_ae

section General



end General

variable {X E} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [DoublingMeasure X A]
  {μ : Measure X} {f : X → E} {x : X} {𝓑 : Finset (X × ℝ)}
  -- feel free to assume `A ≥ 16` or similar

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑. -/
def maximalFunction (μ : Measure X) (𝓑 : Set (X × ℝ)) (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ z ∈ 𝓑, (ball z.1 z.2).indicator (x := x)
  fun _ ↦ ⨍⁻ y, ‖u y‖₊ ^ p ∂μ.restrict (ball z.1 z.2)) ^ p⁻¹

abbrev MB (μ : Measure X) (𝓑 : Set (X × ℝ)) (u : X → E) (x : X) := maximalFunction μ 𝓑 1 u x

/-! Maybe we can generalize some of the hypotheses? (e.g. remove `DoublingMeasure`)? -/

/- NOTE: This was changed to use `ℝ≥0∞` rather than `ℝ≥0` because that was more convenient for the
proof of `first_exception` in DiscreteCarleson.lean. But everything involved there is finite, so
you can prove this with `ℝ≥0` and deal with casting between `ℝ≥0` and `ℝ≥0∞` there, if that turns
out to be easier. -/
theorem measure_biUnion_le_lintegral {l : ℝ≥0∞} (hl : 0 < l)
    {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (h2u : ∀ z ∈ 𝓑, l * μ (ball z.1 z.2) ≤ ∫⁻ x in ball z.1 z.2, u x ∂μ)
    :
    l * μ (⋃ z ∈ 𝓑, ball z.1 z.2) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  sorry

theorem maximalFunction_le_snorm {p : ℝ≥0}
    (hp₁ : 1 ≤ p) {u : X → E} (hu : AEStronglyMeasurable u μ) {x : X} :
    maximalFunction μ 𝓑 p u x ≤ snorm u p μ := by
  sorry

theorem hasStrongType_maximalFunction {l : ℝ≥0} (hl : 0 < l) {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : AEStronglyMeasurable u μ) :
    HasStrongType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 p₁ u x |>.toReal)
      p₂ p₂ μ μ (A ^ 2 * p₂ / (p₂ - p₁)) := by
  sorry

/-- The transformation M characterized in Proposition 2.0.6. -/
def M (u : X → ℂ) (x : X) : ℝ≥0∞ := sorry

theorem M_lt_top {l : ℝ≥0} (hl : 0 < l) {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {x : X} : M u x < ∞ := by
  sorry

theorem laverage_le_M {l : ℝ≥0} (hl : 0 < l)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} :
     ⨍⁻ y, ‖u y‖₊ ∂μ.restrict (ball z r) ≤ M u x := by
  sorry

theorem snorm_M_le {l : ℝ≥0} (hl : 0 < l){p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} :
    snorm (fun x ↦ (M (fun x ↦ u x ^ (p₁ : ℂ)) x).toReal ^ (p₁⁻¹ : ℝ)) p₂ μ ≤
    A ^ 4  * p₂ / (p₂ - p₁) * snorm u p₂ μ := by
  sorry
