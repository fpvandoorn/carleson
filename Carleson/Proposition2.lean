import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A]
variable [Inhabited X] {𝓠 : Set C(X, ℂ)} {D : ℝ} {C : ℝ≥0} (T : TileStructure 𝓠 D C)

def C2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ≥0 := sorry

lemma C2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : C2_2 A τ q C > 0 := sorry

def ε2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ := sorry

lemma ε2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ε2_2 A τ q C > 0 := sorry

/- Not sure how to interpret the LHS. -/
theorem prop2_2
    {τ q : ℝ} (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2)
    {F : Set X} (hF : MeasurableSet F)
    {t : ℝ≥0} (ht : t ∈ Ioc 0 1)
    {𝔄 : Set (𝔓 X)} (hA : IsAntichain (·≤·) (toTileLike '' 𝔄))
    (h2A : 𝔄 ⊆ boundedTiles F t) (h3A : 𝔄.Finite) :
    sorry /-‖∑ᶠ i, _‖₊-/ ≤ C2_2 A τ q C * (density G Q' 𝔄) ^ ε2_2 A τ q C * t ^ (1 / q - 1 / 2) := sorry
