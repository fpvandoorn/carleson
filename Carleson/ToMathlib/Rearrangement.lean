import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.WeakType

noncomputable section

-- Upstreaming status: NOT READY yet (mostly); this file is being actively worked on.
-- Needs significant clean-up (refactoring, code style, extracting lemmas etc.) first.

open scoped NNReal ENNReal

variable {α ε ε' : Type*} {m : MeasurableSpace α}

namespace MeasureTheory


section rearrangement
variable [ENorm ε] [ENorm ε']


/-! # Decreasing rearrangements `f^#` -/
/- many lemma statements were initially taken from
https://github.com/fpvandoorn/BonnAnalysis/blob/master/BonnAnalysis/LorentzSpace.lean -/

/-- The decreasing rearrangement function `f^#`. It equals `μ univ` for `t = 0`.
Note that unlike the notes, we also define this for `t = ∞`. -/
def rearrangement (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  sInf {σ | distribution f σ μ ≤ t}


variable {f : α → ε} {g : α → ε'} {μ : Measure α} {x y : ℝ≥0∞}

lemma distribution_decreasing_rearrangement :
  distribution f x μ = distribution (rearrangement f · μ) x volume := sorry

@[gcongr] lemma rearrangement_mono_right (h : x ≤ y) :
    rearrangement f y μ ≤ rearrangement f x μ := sorry

@[gcongr] lemma rearrangement_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    rearrangement f x μ ≤ rearrangement g x μ := sorry

/-
lemma rearrangement_antitone {f : α → ε} {μ : Measure α} :
    Antitone (rearrangement f · μ) := sorry
-/

@[gcongr] lemma rearrangement_mono (h1 : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h2 : x ≤ y) :
    rearrangement f y μ ≤ rearrangement g x μ := sorry

/-
lemma rearrangement_smul_left (c : 𝕜) :
    rearrangement (c • f) x μ = ‖c‖ₑ * rearrangement f x μ := sorry
-/

-- this should also hold if `distribution f t μ = ∞`.
lemma rearrangement_distribution_le : rearrangement f (distribution f x μ) μ ≤ x := sorry

-- this should also hold if `rearrangement f x μ = ∞`.
lemma distribution_rearrangement_le : distribution f (rearrangement f x μ) μ ≤ x := sorry

lemma rearrangement_add_le [TopologicalSpace ε] [ENormedAddMonoid ε] {f g : α → ε} :
    rearrangement (f + g) (x + y) μ ≤ rearrangement f x μ + rearrangement g y μ := sorry

/-
lemma _root_.ContinuousLinearMap.rearrangement_le {f : α → E₁} {g : α → E₂} :
    rearrangement (fun x ↦ L (f x) (g x)) (‖L‖₊ * x * y) μ ≤
    rearrangement f x μ + rearrangement g y μ := sorry
-/

-- Lemma 1.1.22 of [Ian Tice]
lemma lt_rearrangement_iff [MeasurableSpace ε] (hf : Measurable f) :
    y < rearrangement f x μ ↔ x < distribution f y μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma continuousWithinAt_rearrangement [MeasurableSpace ε] (hf : Measurable f) (x : ℝ≥0∞) :
    ContinuousWithinAt (rearrangement f · μ) (Set.Ici x) x := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma volume_lt_rearrangement [MeasurableSpace ε] (hf : Measurable f) (s : ℝ≥0∞) :
    volume { x | s < rearrangement f (.ofReal x) μ } = distribution f s μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma lintegral_rearrangement_pow [MeasurableSpace ε] (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ t, (rearrangement f (.ofReal t) μ) ^ p = ∫⁻ x, ‖f x‖ₑ ∂μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma sSup_rearrangement [MeasurableSpace ε] (hf : Measurable f) :
    ⨆ t > 0, rearrangement f t μ = rearrangement f 0 μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma essSup_nnnorm_eq_rearrangement_zero [MeasurableSpace ε] (hf : Measurable f) :
    essSup (‖f ·‖ₑ) μ = rearrangement f 0 μ  := sorry


open Filter Topology

-- Lemma 1.1.23 of [Ian Tice]
lemma tendsto_rearrangement [TopologicalSpace ε] [MeasurableSpace ε] {s : ℕ → α → ε} (hs : ∀ᶠ i in atTop, Measurable (s i))
    (hf : Measurable f) (h2s : ∀ᵐ x ∂μ, Monotone (fun n ↦ ‖s n x‖ₑ))
    (h : ∀ᵐ x ∂μ, Tendsto (‖s · x‖ₑ) atTop (𝓝 ‖f x‖ₑ)) :
    Tendsto s atTop (𝓝 f) := sorry

-- Lemma 1.1.23 of [Ian Tice]
lemma liminf_rearrangement [MeasurableSpace ε] {s : ℕ → α → ε} (hs : ∀ᶠ i in atTop, Measurable (s i))
    (hf : Measurable f) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ liminf (‖s · x‖ₑ) atTop) :
    rearrangement f x μ ≤ liminf (fun i ↦ rearrangement (s i) x μ) atTop := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_distribution [MeasurableSpace ε] [Zero ε] {f : α → ε} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ distribution f t μ := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_measure [MeasurableSpace ε] [Zero ε] {f : α → ε} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ μ X := sorry

/- The interval `[0, a) ⊆ ℝ` for `a : ℝ≥0∞`, if useful. -/
protected def _root_.ENNReal.Ico (a : ℝ≥0∞) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ ENNReal.ofReal x < a}

/- to do: some computation rules for this set. -/

/-- Version of `rearrangement_indicator_le` for `t : ℝ≥0∞` -/
lemma rearrangement_indicator_le' [MeasurableSpace ε] [Zero ε] {f : α → ε} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    rearrangement (X.indicator f) t μ ≤
    Set.indicator (Set.Iio (μ X)) (rearrangement f · μ) t := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma rearrangement_indicator_le [MeasurableSpace ε] [Zero ε] {f : α → ε} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (t : ℝ) (μ : Measure α) :
    rearrangement (X.indicator f) (.ofReal t) μ ≤
    Set.indicator (μ X).Ico (fun x ↦ rearrangement f (.ofReal x) μ) t := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma integral_norm_le_integral_rearrangement [MeasurableSpace ε] {f : α → ε} (hf : Measurable f)
    {X : Set α} (hX : MeasurableSet X) (μ : Measure α) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤
    ∫⁻ t in (μ X).Ico, rearrangement f (ENNReal.ofReal t) μ := sorry

/-

-- todo: Hardy-Littlewood rearrangement inequality for functions into `ℝ≥0∞`.

/-- The Hardy-Littlewood rearrangement inequality, for functions into `𝕜` -/
theorem lintegral_norm_mul_le_lintegral_rearrangement_mul {f g : α → 𝕜} :
    ∫⁻ x, ‖f x * g x‖₊ ∂μ ≤
    ∫⁻ t, rearrangement f (.ofReal t) μ * rearrangement g (.ofReal t) μ := by
  sorry

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`. -/
def lnorm' (f : α → E) (p : ℝ≥0∞) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, (ENNReal.ofReal (t ^ (p⁻¹).toReal) *
  rearrangement f (.ofReal t) μ) ^ q⁻¹ / (ENNReal.ofReal t)

/- to do: state and prove lemmas about `lnorm'`. -/

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`. -/
def lnorm (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if q = ∞ then
    ⨆ t > 0, ENNReal.ofReal (t ^ (p⁻¹).toReal) * rearrangement f (.ofReal t) μ
  else
    lnorm' f p q.toReal μ

/- to do: double check definition for `p = ∞`
to do: state and prove lemmas about `lnorm`. -/

/-- the Lorentz space `L^{p,q}` -/
def Lorentz {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p q : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lnorm f p q μ < ∞ }
  zero_mem' := by sorry
  add_mem' {f g} hf hg := by sorry
  neg_mem' {f} hf := by sorry

-/


end rearrangement

end MeasureTheory
