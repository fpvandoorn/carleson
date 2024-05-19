/- This file contains the proof of Lemma 10.4, from section 10.7-/

import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic

--import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals


noncomputable section

section

open ENNReal

local notation "θ" => integer_linear

local notation "Θ" => {(θ n) | n : ℤ}

#check theorem1_2C


-- copied from HomogeneousType
-- anyway, providing a proof would be good and is actually partly part of section 10.7
--instance helper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
--    IsSpaceOfHomogeneousType E (2 ^ FiniteDimensional.finrank ℝ E) := by sorry

/- lemmas 10.22 to 10.26 are for this -/

instance IsSpaceOfHomogeneousTypeR2: IsSpaceOfHomogeneousType ℝ 2 := by
  have : IsSpaceOfHomogeneousType ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := by infer_instance
  --simpa
  exact {volume_ball_two_le_same := sorry}

lemma h1 : 2 ∈ Set.Ioc 1 (2 : ℝ) := by simp
lemma h2 : Real.IsConjExponent 2 2 := by rw [Real.isConjExponent_iff_eq_conjExponent] <;> norm_num


--mainly have to work for the following lemmas

/-Stronger version of oscillation_control from the paper-/
lemma localOscillation_of_integer_linear {x R : ℝ}  : ∀ n m : ℤ, localOscillation (Metric.ball x R) (θ n) (θ m) = 2 * R * |(n : ℝ) - m| := by
  --TODO : readd (Rpos : R > 0) or (better) add a case distinction
  intro n m
  /- Rewrite to a more convenient form for the following steps. -/
  calc localOscillation (Metric.ball x R) (θ n) (θ m)
    _ = ⨆ z ∈ (Metric.ball x R) ×ˢ (Metric.ball x R), ‖(n - m) * (z.1 - x) - (n - m) * (z.2 - x)‖ := by
      --TODO : shorten the following
      rw [localOscillation]
      congr
      ext z
      rw [←Complex.norm_real]
      congr
      ext h
      congr
      rw [integer_linear, integer_linear]
      simp
      ring
  /- Show inequalities in both directions. -/
  apply le_antisymm
  . calc ⨆ z ∈ (Metric.ball x R) ×ˢ (Metric.ball x R), ‖(n - m) * (z.1 - x) - (n - m) * (z.2 - x)‖
      _ ≤ 2 * R * |↑n - ↑m| := by
        apply Real.iSup_le
        --TODO: investigate strange (delaborator) behavior - why is there still a sup?
        intro z
        apply Real.iSup_le
        . intro hz
          simp at hz
          rw [Real.dist_eq, Real.dist_eq] at hz
          rw [Real.norm_eq_abs]
          calc |(n - m) * (z.1 - x) - (n - m) * (z.2 - x)|
          _ ≤ |(n - m) * (z.1 - x)| + |(n - m) * (z.2 - x)| := by apply abs_sub
          _ = |↑n - ↑m| * |z.1 - x| + |↑n - ↑m| * |z.2 - x| := by congr <;> apply abs_mul
          _ ≤ |↑n - ↑m| * R + |↑n - ↑m| * R := by gcongr; linarith [hz.1]; linarith [hz.2]
          _ = 2 * R * |↑n - ↑m| := by ring
        --TODO: fix this
        repeat
          apply mul_nonneg
          linarith
          apply abs_nonneg
        sorry
        sorry
  . apply le_of_forall_le
    intro c hc
    let R' := c / (2 * |(n : ℝ) - m|)
    --TODO: seems like we do not use the right theorem here...
    --apply le_iSup
    --apply le_iSup_iff.2
    apply (Real.le_sSup_iff _ _).mpr
    . intro ε εpos
      use |c|
      simp
      --rw [exists_exists]
      constructor
      . use (x + R'), (x - R')
        simp
        apply le_antisymm
        . apply Real.iSup_le
          . intro h
            calc |(↑n - ↑m) * R' + (↑n - ↑m) * R'|
            _ ≤ |(↑n - ↑m) * R'| + |(↑n - ↑m) * R'| := by apply abs_add
            _ = |↑n - ↑m| * |R'| + |↑n - ↑m| * |R'| := by congr <;> apply abs_mul
            _ = 2 * |↑n - ↑m| * |c / (2 * |↑n - ↑m|)| := by ring
            _ = 2 * |↑n - ↑m| * (|c| / |(2 * |↑n - ↑m|)|) := by congr; apply abs_div
            _ = 2 * |↑n - ↑m| * (|c| / (2 * |↑n - ↑m|)) := by congr; apply abs_of_nonneg; apply mul_nonneg; linarith; apply abs_nonneg
            _ = |c| := by
              ring_nf
              apply mul_div_cancel_left₀
              --TODO : extra case
              sorry
          . apply abs_nonneg
        . sorry
        --rw [Real.iSup_]
      linarith [le_abs_self c]
    . sorry
    . sorry
  --have : localOscillation (Metric.ball x R) (θ n) (θ m) =


/- to HomogeneousType -/
@[reducible]
def isSpaceOfHomogeneousType_with_increased_constant {X : Type} {a b : ℝ} [MetricSpace X] [IsSpaceOfHomogeneousType X a] (aleb : a ≤ b) : IsSpaceOfHomogeneousType X b where
  volume_ball_two_le_same := by
    intro x r
    calc MeasureTheory.volume.real (Metric.ball x (2 * r))
    _ ≤ a * MeasureTheory.volume.real (Metric.ball x r) := by apply volume_ball_two_le_same
    _ ≤ b * MeasureTheory.volume.real (Metric.ball x r) := by gcongr

--#lint
--TODO : decide whether to move this up so that all the above lemmas are directly proven with the right doubling constant
instance badR: IsSpaceOfHomogeneousType ℝ 4 := by
  have : IsSpaceOfHomogeneousType ℝ 2 := by infer_instance
  simp at this
  exact isSpaceOfHomogeneousType_with_increased_constant (by linarith)

--lemma frequency_ball_doubling {x R : ℝ} (Rpos : 0 < R) :

instance h4 : IsCompatible Θ where
  /- Lemma frequency_ball_doubling from the paper. -/
  localOscillation_two_mul_le := by
    intro x₁ x₂ R f g hf hg _
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg]
    rw [localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    sorry

  /- Lemma frequency_ball_growth from the paper. -/
  localOscillation_le_of_subset := by
    intro x₁ x₂ R f g hf hg _ _
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg]
    rw [localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    sorry
    --trivial

  /- Lemma integer_ball_cover from the paper. -/
  ballsCoverBalls := by
    intro x R R' f hf
    obtain ⟨n, hθnf⟩ := hf
    rw [←hθnf]
    let m₁ := Nat.floor (n - R' / 2)
    let m₂ := n
    let m₃ := Nat.ceil (n + R' / 2)
    rw [coveredByBalls_iff]
    let (a : Finset ℕ) := {1, 2, 3}
    /- The following is necessary for withLocalOscillation to be defined. -/
    --have ball_bounded := fact_isCompact_ball x R
    classical
    set balls : Finset (C(ℝ, ℂ)) := {θ m₁, θ m₂, θ m₃} with balls_def
    use balls
    constructor
    . rw [balls_def]
      apply Nat.le_floor
      norm_cast
      apply le_trans Finset.card_le_three
      norm_num
    intro φ hφ
    simp at hφ
    obtain ⟨n', hn'⟩ := hφ.2
    /- m₁, m₂, m₃ each correspond to one case. -/
    by_cases h : n' ≤ n - R' / 2
    . sorry
    push_neg at h
    by_cases h' : n' < n + R' / 2
    . sorry
    push_neg at h'
    sorry



--TODO : What is Lemma 10.34 (frequency ball growth) needed for?

--TODO : possibly issues with a different "doubling constant" than in the paper (4 instead of 2)
instance h5 : IsCancellative 2 Θ where
  /- Lemma 10.36 (real van der Corput) from the paper. -/
  norm_integral_exp_le := by sorry




--TODO : add some Real.vol lemma

instance h6 : IsCZKernel 4 K where
  /- uses Hilbert_kernel_bound -/
  norm_le_vol_inv := by
    intro x y
    rw [Complex.norm_eq_abs, Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
    calc Complex.abs (K x y)
    _ ≤ 2 ^ (4 : ℝ) / (2 * |x - y|) := by apply Hilbert_kernel_bound
    _ ≤ 2 ^ (4 : ℝ) ^ 3 / (2 * |x - y|) := by gcongr <;> norm_num
  /- uses Hilbert_kernel_regularity -/
  norm_sub_le := by
    intro x y y' h
    rw [Real.dist_eq, Real.dist_eq] at *
    calc ‖K x y - K x y'‖
    _ ≤ 2 ^ 10 * (1 / |x - y|) * (|y - y'| / |x - y|) := by
      apply Hilbert_kernel_regularity
      linarith [abs_nonneg (x-y)]
    _ ≤ (|y - y'| / |x - y|) ^ (4 : ℝ)⁻¹ * (2 ^ (4 : ℝ) ^ 3 / Real.vol x y) := by
      rw [Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
      ring_nf
      rw [pow_two, mul_assoc |x - y|⁻¹]
      gcongr
      . conv =>
          lhs
          rw [← Real.rpow_one (|x - y|⁻¹ * |y - y'|)]
        apply Real.rpow_le_rpow_of_exponent_ge'
        . field_simp
          apply div_nonneg (abs_nonneg (y - y')) (abs_nonneg (x - y))
        . field_simp
          apply div_le_one_of_le <;> linarith [abs_nonneg (x - y)]
        . norm_num
        . norm_num
      . norm_num
  /- Lemma ?-/
  measurable_right := by
    intro y
    --apply measurable_div
    --rw [K]
    sorry
  /- Lemma ?-/
  measurable := by sorry

/- Lemma ?-/
lemma h3 : NormBoundedBy (ANCZOperatorLp 2 K) 1 := sorry



#check @theorem1_2C
--#check theorem1_2C K (by simp) h1 h2 _ _ h3



local notation "T" => CarlesonOperatorReal K

/-Not sure whether this is actually true. Probably we only have "le" (which should suffice). -/
--TODO : change name to reflect that this only holds for a specific instance of CarlesonOperaterReal?
lemma CarlesonOperatorReal_eq_CarlesonOperator : T = CarlesonOperator K Θ := by
  sorry

/- Lemma 10.4 -/
--TODO : directly write out constant (2^(2^40)) ?
lemma rcarleson {F G : Set ℝ}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (h2F : MeasureTheory.volume F ∈ Set.Ioo 0 ∞) (h2G : MeasureTheory.volume G ∈ Set.Ioo 0 ∞)
    (f : ℝ → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    :
    ‖∫ x in G, T f x‖ ≤
    C1_2 4 2 * (MeasureTheory.volume.real G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real F) ^ (2 : ℝ)⁻¹ := by
  rw [CarlesonOperatorReal_eq_CarlesonOperator]
  --WARNING : theorem1_2C does not yet require all necessary implicit parameters since no proof using them has been provided yet.
  convert theorem1_2C K (by simp) h1 h2 hF hG h3 f hf <;> sorry


end section
