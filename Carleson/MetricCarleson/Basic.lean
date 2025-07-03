import Carleson.Defs
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {K : X → X → ℂ}

namespace MetricΘ

variable [CompatibleFunctions ℝ X (defaultA a)]

/-- We choose as metric space instance on `Θ` one given by an arbitrary ball.
The metric given by all other balls are equivalent. -/
scoped instance : PseudoMetricSpace (Θ X) :=
  inferInstanceAs <| PseudoMetricSpace <| WithFunctionDistance o 1

lemma dist_eq_cdist {f g : Θ X} : dist f g = dist_{o, 1} f g := rfl

/-!
The following two lemmas state that the distance could be equivalently given by any other cdist.
-/

lemma dist_le_cdist {f g : Θ X} {x : X} {r : ℝ} (hr : 0 < r) :
    dist f g ≤ As (defaultA a) ((1 + dist o x) / r) * dist_{x, r} f g :=
  cdist_le_mul_cdist hr (by norm_num) f g

lemma cdist_le_dist {f g : Θ X} {x : X} {r : ℝ} (hr : 0 < r) :
    dist_{x, r} f g ≤ As (defaultA a) (r + dist o x) * dist f g := by
  rw [← div_one (_ + _), dist_comm o]
  exact cdist_le_mul_cdist (by norm_num) hr f g

instance : SecondCountableTopology (Θ X) :=
  CompatibleFunctions.allBallsCoverBalls.secondCountableTopology one_lt_two

end MetricΘ

open MetricΘ

variable [KernelProofData a K] {θ : Θ X} {Q : SimpleFunc X (Θ X)} {R₁ R₂ : ℝ} {f : X → ℂ} {x : X}
-- [IsCancellative X (defaultτ a)]

lemma measurable_carlesonOperatorIntegrand (mf : Measurable f) :
    Measurable (fun x ↦ carlesonOperatorIntegrand K (Q x) R₁ R₂ f x) := by
  unfold carlesonOperatorIntegrand
  rw [← stronglyMeasurable_iff_measurable]
  conv => enter [1, x]; rw [← integral_indicator Annulus.measurableSet_oo]
  apply StronglyMeasurable.integral_prod_right
  rw [stronglyMeasurable_iff_measurable]
  refine Measurable.indicator ?_ (measurable_dist.comp measurable_id measurableSet_Ioo)
  apply (measurable_K.mul (mf.comp measurable_snd)).mul
  exact ((Complex.measurable_ofReal.comp measurable_Q₂).const_mul I).cexp

lemma rightContinuous_carlesonOperatorIntegrand (mf : Measurable f) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ · R₂ f x) (Ici R₁) R₁ := by
  sorry

lemma leftContinuous_carlesonOperatorIntegrand (mf : Measurable f) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ R₁ · f x) (Iic R₂) R₂ := by
  sorry

lemma continuous_carlesonOperatorIntegrand (nf : (‖f ·‖) ≤ 1) :
    Continuous (carlesonOperatorIntegrand K · R₁ R₂ f x) := by
  sorry

/-- The constant used in the proof of `int-continuous`. -/
irreducible_def C3_0_1 (a : ℕ) (R₁ R₂ : ℝ≥0) : ℝ≥0 :=
  2 ^ (a ^ 3) * (2 * R₂ / R₁) ^ a

-- not sure if this is the best phrasing
lemma isBounded_carlesonOperatorIntegrand {R₁ R₂ : ℝ≥0} (nf : (‖f ·‖) ≤ 1) :
    ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ₑ ≤ C3_0_1 a R₁ R₂ := by
  sorry
