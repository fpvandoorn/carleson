import Carleson.Defs

open MeasureTheory Set

noncomputable section

/-- The constant used in `metric_carleson`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C1_0_2 (a : ℕ) (q : ℝ) : ℝ := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

lemma C1_0_2_pos {a : ℕ} {q : ℝ} (hq : 1 < q) : 0 < C1_0_2 a q := by
  rw [C1_0_2]
  apply div_pos
  · positivity
  · apply pow_pos
    linarith [hq]

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ q q' : ℝ} {C : ℝ}
variable {F G : Set X}
variable {K : X → X → ℂ}

/- Theorem 1.0.2 -/
theorem metric_carleson [CompatibleFunctions ℝ X (defaultA a)]
  [IsCancellative X (defaultτ a)] [IsOneSidedKernel a K]
    (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : HasBoundedStrongType (nontangentialOperator K · · |>.toReal) 2 2 volume volume (C_Ts a))
    (f : X → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    ENNReal.ofReal (C1_0_2 a q) * (volume G) ^ q'⁻¹ * (volume F) ^ q⁻¹ := by
  sorry

/- maybe investigate: making `volume` implicit in both `hg` and `h3g` of `metric_carleson` causes slow
elaboration. -/

end
