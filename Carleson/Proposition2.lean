import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A]
variable [Inhabited X] {𝓠 : Set C(X, ℂ)} {ι : Type*} {𝔓 : Type*}
    {D : ℝ} {C : ℝ≥0} (T : TileStructure 𝓠 ι 𝔓 D C)

def C2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ≥0 := sorry

lemma C2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : C2_2 A τ q C > 0 := sorry

theorem prop2_2
    {τ q : ℝ} (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2)
    {F : Set X} (hF : MeasurableSet F)
    {t : ℝ≥0} (ht : t ∈ Ioc 0 1)
    {𝔄 : Set 𝔓} (hA : IsAntichain (·≤·) (toTileLike T '' 𝔄))
    (h2A : 𝔄 ⊆ boundedTiles T F t) : sorry := sorry

/- TODO: state Propositions 2.2 -/
