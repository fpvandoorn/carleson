import Carleson.Carleson
import Mathlib.Analysis.Fourier.AddCircle

/-! The classical version of Carleson's theorem.

For this we take `X = ℝ`, `K x y := 1 / (x - y)` and `Θ = {linear functions}`.
-/

open MeasureTheory Measure NNReal Metric Complex Set TileStructure Function BigOperators Filter
open AddCircle Topology
open scoped ENNReal
noncomputable section

variable {T : ℝ} {f : AddCircle T → ℂ} {ε : ℝ} [Fact (0 < T)]


def partialFourierSum (f : AddCircle T → ℂ) (n : ℤ) (x : AddCircle T) : ℂ :=
  ∑ i in Finset.Icc (- n) n, fourierCoeff f i * fourier i x

theorem classical_carleson (hf : UniformContinuous f) (h2f : ∀ x, ‖f x‖ ≤ 1)
    (hε : 0 < ε) :
    ∃ (E : Set (AddCircle T)) (N₀ : ℕ), MeasurableSet E ∧ haarAddCircle E ≤ .ofReal ε ∧
    ∀ N x, N₀ ≤ N → x ∉ E → ‖f x - partialFourierSum f N x‖ < ε := by
  sorry


theorem classical_carleson_pointwise (hf : UniformContinuous f) (h2f : ∀ x, ‖f x‖ ≤ 1) :
    ∃ (E : Set (AddCircle T)) (N₀ : ℕ), MeasurableSet E ∧ haarAddCircle E = 0 ∧
    ∀ x, x ∉ E → Tendsto (partialFourierSum f · x) atTop (𝓝 (f x)) := by
  sorry
