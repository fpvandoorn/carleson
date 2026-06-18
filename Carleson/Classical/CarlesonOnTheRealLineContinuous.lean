module

public import Carleson.Classical.CarlesonOnTheRealLineBasic
public import Carleson.TwoSidedCarleson.MainTheorem

/-
This file contains the proof of Lemma 11.1.4 (real Carleson), from section 11.7.
-/

public noncomputable section

open MeasureTheory Function Metric Bornology Real NNReal

local notation "T" => carlesonOperatorReal K

/- Version of Lemma 11.1.5 for general exponents -/
lemma rcarleson_general {q q' : ℝ≥0} (hq : q ∈ Set.Ioc 1 2) (hqq' : q.HolderConjugate q')
    {F G : Set ℝ} (hF : MeasurableSet F) (hG : MeasurableSet G)
    (f : ℝ → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, T f x ≤ C10_0_1 4 q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  calc ∫⁻ x in G, T f x
    _ ≤ ∫⁻ x in G, carlesonOperator K f x :=
      lintegral_mono (carlesonOperatorReal_le_carlesonOperator _)
    _ ≤ C10_0_1 4 q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ :=
      two_sided_metric_carleson (a := 4) (by norm_num) hq hqq' hF hG
        Hilbert_strong_2_2 hmf hf

/- Lemma 11.1.5 -/
lemma rcarleson {F G : Set ℝ} (hF : MeasurableSet F) (hG : MeasurableSet G)
    (f : ℝ → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, T f x ≤ C10_0_1 4 2 * (volume G) ^ (2 : ℝ)⁻¹ * (volume F) ^ (2 : ℝ)⁻¹ := by
  have conj_exponents : NNReal.HolderConjugate 2 2 := by
    rw [NNReal.holderConjugate_iff_eq_conjExponent]
    · ext; norm_num
    norm_num
  exact rcarleson_general (by simp) conj_exponents hF hG f hmf hf

end
