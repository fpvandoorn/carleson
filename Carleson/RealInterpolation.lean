import Carleson.WeakType

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)
  {f g : α → E} {t : ℝ} {s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}


namespace MeasureTheory

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

lemma aestronglyMeasurable_trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := sorry

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (MeasureTheory.trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

/-- The operator is subadditive on functions satisfying `P` with constant `A`. -/
def SubadditiveOn (T : (α → E₁) → α' → E₂) (P : (α → E₁) → Prop) (A : ℝ) : Prop :=
  ∀ (f g : α → E₁) (x : α'), P f → P g → ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

/-- The operator is sublinear on functions satisfying `P` with constant `A`. -/
def SublinearOn (T : (α → E₁) → α' → E₂) (P : (α → E₁) → Prop) (A : ℝ) : Prop :=
  SubadditiveOn T P A ∧ ∀ (f : α → E₁) (c : ℝ), P f → T (c • f) = c • T f

/-- The constant occurring in the real interpolation theorem. -/
-- todo: remove unused variables
def C_realInterpolation (p₀ p₁ q₀ q₁ p q : ℝ≥0∞) (C₀ C₁ t A : ℝ≥0) : ℝ≥0 := sorry

-- todo: add necessary hypotheses
lemma C_realInterpolation_pos (p₀ p₁ q₀ q₁ p q : ℝ≥0∞) (C₀ C₁ t A : ℝ≥0) :
    0 < C_realInterpolation p₀ p₁ q₀ q₁ p q C₀ C₁ t := sorry

/-- Marcinkiewicz real interpolation theorem. -/
-- feel free to assume that T also respect a.e.-equality if needed.
/- For the proof, see
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.4, theorem 6.28.
You want to use `trunc f A` when the book uses `h_A`.
Minkowski's inequality is `ENNReal.lintegral_Lp_add_le` -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t A : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hmT : ∀ f, Memℒp f p₀ μ ∨ Memℒp f p₁ μ → AEStronglyMeasurable (T f) ν)
    (hT : SublinearOn T (fun f ↦ Memℒp f p₀ μ ∨ Memℒp f p₁ μ) A)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁) :
    HasStrongType T p p μ ν (C_realInterpolation p₀ p₁ q₀ q₁ p q C₀ C₁ t A) := sorry

/- State and prove Remark 1.2.7 -/

end MeasureTheory
