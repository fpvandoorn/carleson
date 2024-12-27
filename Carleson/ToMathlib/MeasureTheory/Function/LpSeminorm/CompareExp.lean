import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open scoped ENNReal
open MeasureTheory

/- The next ones should be put just after `Memℒp.smul`. -/
variable {α : Type*} [MeasurableSpace α] {𝕜 : Type*} [NormedRing 𝕜] {μ : Measure α}
  {p q r : ℝ≥0∞} {f : α → 𝕜} {φ : α → 𝕜}

theorem Memℒp.mul (hf : Memℒp f r μ) (hφ : Memℒp φ q μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    Memℒp (φ * f) p μ :=
  Memℒp.smul hf hφ hpqr

theorem Memℒp.mul' (hf : Memℒp f r μ) (hφ : Memℒp φ q μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    Memℒp (fun x ↦ φ x * f x) p μ :=
  Memℒp.smul hf hφ hpqr

theorem Memℒp.mul_of_top_right (hf : Memℒp f p μ) (hφ : Memℒp φ ∞ μ) : Memℒp (φ * f) p μ :=
  Memℒp.smul_of_top_right hf hφ

theorem Memℒp.mul_of_top_right' (hf : Memℒp f p μ) (hφ : Memℒp φ ∞ μ) :
    Memℒp (fun x ↦ φ x * f x) p μ :=
  Memℒp.smul_of_top_right hf hφ

theorem Memℒp.mul_of_top_left (hf : Memℒp f ∞ μ) (hφ : Memℒp φ p μ) : Memℒp (φ * f) p μ :=
  Memℒp.smul_of_top_left hf hφ

theorem Memℒp.mul_of_top_left' (hf : Memℒp f ∞ μ) (hφ : Memℒp φ p μ) :
    Memℒp (fun x ↦ φ x * f x) p μ :=
  Memℒp.smul_of_top_left hf hφ
