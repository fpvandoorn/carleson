import Carleson.Defs
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X]
variable {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}
variable {f : X → ℂ}

variable [CompatibleFunctions ℝ X (defaultA a)]
    (ha : 4 ≤ a)
    {x : X} {θ : Θ X} {R₁ R₂ : ℝ}

namespace MetricΘ
scoped instance : PseudoMetricSpace (Θ X) :=
  inferInstanceAs <| PseudoMetricSpace <| WithFunctionDistance o 1

lemma dist_eq_cdist {f g : Θ X} : dist f g = dist_{o, 1} f g := rfl


/- Use le_cdist_iterate & cdist_le_iterate to prove the next two results
(feel free to change the constant). -/

lemma dist_le_cdist {f g : Θ X} {x : X} {r : ℝ≥0} :
    dist f g ≤ As (nndist x o + r) a * dist_{x, r} f g :=
  sorry

lemma cdist_le_dist {f g : Θ X} {x : X} {r : ℝ≥0} :
    dist_{x, r} f g ≤ As (nndist x o + r⁻¹) a * dist f g :=
  sorry

-- why do we know this?
instance : SecondCountableTopology (Θ X) := sorry

end MetricΘ

open MetricΘ

variable
    [DoublingMeasure X (defaultA a : ℕ)]
    [IsCancellative X (defaultτ a)]
    [IsOneSidedKernel a K]


lemma continuous_carlesonOperatorIntegrand (hf : ∀ x, ‖f x‖ ≤ 1) :
    Continuous (carlesonOperatorIntegrand K · R₁ R₂ f x) := by
  sorry

lemma rightContinuous_carlesonOperatorIntegrand (hf : ∀ x, ‖f x‖ ≤ 1) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ · R₂ f x) (Ici R₁) R₁ := by
  sorry

lemma leftContinuous_carlesonOperatorIntegrand (hf : ∀ x, ‖f x‖ ≤ 1) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ R₁ · f x) (Iic R₂) R₂ := by
  sorry

lemma measurable_carlesonOperatorIntegrand (hf : ∀ x, ‖f x‖ ≤ 1) :
    Measurable (carlesonOperatorIntegrand K θ R₁ R₂ f) := by
  sorry

/-- The constant used in the proof of `int-continuous`. -/
irreducible_def C3_0_1 (a : ℕ) (R₁ R₂ : ℝ≥0) : ℝ≥0 := 2 ^ ((a : ℝ) ^ 3) * (2 * R₂ / R₁) ^ a

-- not sure if this is the best phrasing
lemma isBounded_carlesonOperatorIntegrand {R₁ R₂ : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖carlesonOperatorIntegrand K θ R₁ R₂ f x‖₊ ≤ C3_0_1 a R₁ R₂ := by
  sorry
