/- This file contains the proof of Lemma 10.4, from section 10.7-/

import Carleson.Carleson
import Carleson.HomogeneousType

--import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals


noncomputable section
--local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

section

open ENNReal

def k (x : ℝ) : ℂ := max (1 - |x|) 0 / (1 - Complex.exp (Complex.I * x))

lemma k_of_neg_eq_conj_k {x : ℝ} : k (-x) = (starRingEnd ℂ) (k x) := by
  sorry

/- Little helper lemmas. -/
lemma k_of_abs_le_one {x : ℝ} (abs_le_one : |x| ≤ 1) : k x = (1 - |x|) / (1 - Complex.exp (Complex.I * x)) := by
  sorry
lemma k_of_one_le_abs {x : ℝ} (abs_le_one : 1 ≤ |x|) : k x = 0 := by
  sorry


def K (x y : ℝ) : ℂ := k (x-y)

--TODO : call constructor in a better way?
def integer_linear (n : ℤ) : C(ℝ, ℂ) := ⟨fun (x : ℝ) ↦ (n * x : ℂ), by continuity⟩

local notation "θ" => integer_linear

--lemma θcont {n : ℤ} : Continuous (θ n) := sorry

local notation "Θ" => {(θ n) | n : ℤ}

local notation "T_" => (CarlesonOperator K Θ)


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

/-Cf. section below lemma 10.26-/
lemma localOscillation_of_integer_linear {x R: ℝ}  : ∀ n m : ℤ, localOscillation (Metric.ball x R) (θ n) (θ m) = 2 * R * |(n : ℝ) - m| := by
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

instance h4 : IsCompatible Θ where
  /- Lemma 10.32 (real line doubling) from the paper. -/
  localOscillation_two_mul_le := by
    intro x₁ x₂ R f g hf hg _
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg]
    rw [localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    sorry
    --gcongr

  /- Lemma 10.33 (frequency ball doubling) from the paper. -/
  localOscillation_le_of_subset := by
    intro x₁ x₂ R f g hf hg _ _
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg]
    rw [localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    sorry
    --trivial
  /- Lemma 10.35 (frequency ball cover) from the paper. -/
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
    have ball_bounded := fact_isCompact_ball x R
    classical
    --TODO: fix problems with Finset

    set balls : Finset (C(ℝ, ℂ)) := {θ m₁, θ m₂, θ m₃} with balls_def
    use balls
    constructor
    . rw [balls_def]
      --simp
      sorry
      --apply Finset.card_le_three
    . sorry



--TODO : What is Lemma 10.34 (frequency ball growth) needed for?

--TODO : possibly issues with a different "doubling constant" than in the paper (4 instead of 2)
instance h5 : IsCancellative 2 Θ where
  /- Lemma 10.36 (real van der Corput) from the paper. -/
  norm_integral_exp_le := by sorry

/- Lemma 10.9 (lower secant bound) from the paper. -/
lemma lower_secant_bound {η : ℝ} (ηpos : η > 0) {x : ℝ} (xIcc : x ∈ Set.Icc (-2 * Real.pi + η) (2 * Real.pi - η)) (xAbs : η ≤ |x|) :
    η / 8 ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
  sorry

--open ComplexConjugate

/- Lemma 10.37 (Hilbert kernel bound) -/
lemma Hilbert_kernel_bound {x y : ℝ} : Complex.abs (K x y) ≤ 2 ^ (4 : ℝ) / (2 * |x - y|) := by
  by_cases h : 0 < |x - y| ∧ |x - y| < 1
  . calc Complex.abs (K x y)
      _ ≤ 1 / Complex.abs (1 - Complex.exp (Complex.I * ↑(x - y))) := by
        rw [K, k, Complex.abs.isAbsoluteValue.abv_div] --TODO: check whether the last lemma also has a better name
        gcongr
        rw [Complex.abs_ofReal, abs_of_nonneg]
        . apply max_le
          linarith [abs_nonneg (x-y)]
          linarith
        . apply le_max_right
      _ ≤ 1 / (|x - y| / 8) := by
        gcongr
        . linarith
        . apply lower_secant_bound
          . exact h.1
          . rw [Set.mem_Icc]
            --TODO : improve calculations
            constructor
            . simp
              calc |x - y|
                _ ≤ 1 := h.2.le
                _ ≤ 2 * Real.pi - 1 := by
                  rw [le_sub_iff_add_le]
                  linarith [Real.two_le_pi]
                _ ≤ 2 * Real.pi + (x - y) := by
                  rw [sub_eq_add_neg]
                  gcongr
                  exact (abs_le.mp h.2.le).1
            . calc x - y
                _ ≤ |x - y| := le_abs_self (x - y)
                _ ≤ 1 := h.2.le
                _ ≤ 2 * Real.pi - 1 := by
                  rw [le_sub_iff_add_le]
                  linarith [Real.two_le_pi]
                _ ≤ 2 * Real.pi - |x - y| := by
                  gcongr
                  exact h.2.le
          . trivial
      _ = 8 / |x - y| := by
        field_simp
      _ = 2 ^ (4 : ℝ) / (2 * |x - y|) := by
        rw [div_mul_eq_div_div]
        congr
        norm_num
  . push_neg at h
    have : Complex.abs (K x y) = 0 := by
      rw [Complex.abs.isAbsoluteValue.abv_eq_zero, K, k, _root_.div_eq_zero_iff]
      by_cases xeqy : x = y
      . right
        simp [xeqy]
      . left
        simp
        apply h (abs_pos.mpr (sub_ne_zero.mpr xeqy))
    rw [this]
    apply div_nonneg
    . norm_num
    . linarith [abs_nonneg (x-y)]

/- Lemma 10.38 (Hilbert kernel regularity) -/
lemma Hilbert_kernel_regularity {x y y' : ℝ} (hxy : x ≠ y) :
    2 * |y - y'| ≤ |x - y| → ‖K x y - K x y'‖ ≤ 2 ^ 10 * (1 / |x - y|) * (|y - y'| / |x - y|)  := by
  rw [K, K]
  wlog x_eq_zero : x = 0 generalizing x y y'
  . intro h
    set! x_ := (0 : ℝ) with x_def
    set y_ := y - x with y_def
    set y'_ := y' - x with y'_def
    have hxy_ : x_ ≠ y_ := by
      rw [x_def, y_def]
      exact (sub_ne_zero_of_ne hxy.symm).symm
    have h_ : 2 * |y_ - y'_| ≤ |x_ - y_| := by
      rw [x_def, y_def, y'_def]
      simpa
    have := this hxy_ x_def h_
    rw [x_def, y_def, y'_def] at this
    simpa
  rw [x_eq_zero]
  intro h
  simp at h
  simp only [zero_sub, abs_neg] --, one_div
  wlog yy'nonneg : 0 ≤ y ∧ 0 ≤ y' generalizing y y'
  . --TODO : improve case distinction to avoid nesting
    --rcases (not_and_or.mp yy'_nonneg) with
    by_cases yge0 : 0 ≤ y
    . push_neg at yy'nonneg
      exfalso
      rw [abs_of_nonneg yge0, abs_of_nonneg] at h <;> linarith [yy'nonneg yge0]
    --rcases ltTrichotomy
    . push_neg at yge0
      by_cases y'ge0 : 0 ≤ y'
      . exfalso
        rw [abs_of_neg yge0, abs_of_neg] at h <;> linarith
      . -- This is the only interesting case.
        push_neg at y'ge0
        set! y_ := -y with y_def
        set! y'_ := -y' with y'_def
        have h_ : 2 * |y_ - y'_| ≤ |y_| := by
          rw [y_def, y'_def, ← abs_neg]
          simpa [neg_add_eq_sub]
        have y_y'_nonneg : 0 ≤ y_ ∧ 0 ≤ y'_ := by constructor <;> linarith
        have hxy_ : x ≠ y_ := by
          rw [x_eq_zero] at hxy
          sorry

        have := this hxy_ h_ y_y'_nonneg
        rw [y_def, y'_def] at this
        simp only [neg_neg, abs_neg, sub_neg_eq_add, neg_add_eq_sub] at this
        rw [← IsROrC.norm_conj, map_sub, ← k_of_neg_eq_conj_k, ← k_of_neg_eq_conj_k, ←abs_neg (y' - y)] at this
        simpa
  -- Beginning of the main proof.
  have y2ley' : y / 2 ≤ y' := by
    rw [div_le_iff two_pos]
    calc y
      _ = 2 * (y - y') - y + 2 * y' := by ring
      _ ≤ 2 * |y - y'| - y + 2 * y' := by
        gcongr
        apply le_abs_self
      _ ≤ y - y + 2 * y' := by
        gcongr
        rw [abs_eq_self.mpr yy'nonneg.1] at h
        exact h
      _ = y' * 2 := by ring
  /- Distinguish four cases. -/
  rcases le_or_gt y 1, le_or_gt y' 1 with ⟨hy | hy, hy' | hy'⟩
  . rw [k_of_abs_le_one, k_of_abs_le_one]
    . simp only [abs_neg, Complex.ofReal_neg, mul_neg, ge_iff_le]
      rw [abs_of_nonneg yy'nonneg.1, abs_of_nonneg yy'nonneg.2]
      let κ : ℝ → ℂ := fun t ↦ (1 - t) / (1 - Complex.exp (-(Complex.I * t)))
      let κ' : ℝ → ℂ := fun t ↦ (-1 + Complex.exp (-Complex.I * t) + Complex.I * (1 - t) * Complex.exp (Complex.I * t)) / (1 - Complex.exp (-(Complex.I * t)))^2
      calc ‖(1 - y) / (1 - Complex.exp (-(Complex.I * y))) - (1 - y') / (1 - Complex.exp (-(Complex.I * y')))‖
      _ = ‖κ y - κ y'‖ := by simp
      _ = ‖∫ (t : ℝ) in y'..y, κ' t‖ := by
        congr 1
        rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt]
        . intro t ht
          sorry
        . sorry
      _ ≤ 2 ^ 10 * (1 / y) * (|y - y'| / y) := by sorry
    . rw [abs_neg, abs_of_nonneg yy'nonneg.2]
      assumption
    . rw [abs_neg, abs_of_nonneg yy'nonneg.1]
      assumption
  . sorry
  . sorry
  . sorry


#check intervalIntegral.integral_eq_sub_of_hasDerivAt

--TODO : add some Real.vol lemma

instance h6 : IsCZKernel 4 K where
  /- Lemma 10.37 (Hilbert kernel bound) from the paper. -/
  norm_le_vol_inv := by
    intro x y
    rw [Complex.norm_eq_abs, Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
    calc Complex.abs (K x y)
    _ ≤ 2 ^ (4 : ℝ) / (2 * |x - y|) := by apply Hilbert_kernel_bound
    _ ≤ 2 ^ (4 : ℝ) ^ 3 / (2 * |x - y|) := by gcongr <;> norm_num
  /- uses Lemma 10.38 (Hilbert kernel regularity) -/
  norm_sub_le := by sorry
  /- Lemma ?-/
  measurable_right := by sorry
  /- Lemma ?-/
  measurable := by sorry

/- Lemma ?-/
lemma h3 : NormBoundedBy (ANCZOperatorLp 2 K) 1 := sorry



#check @theorem1_2C
--#check theorem1_2C K (by simp) h1 h2 _ _ h3

/- Lemma 10.4 -/
--TODO : directly write out constant (2^(2^40)) ?
lemma rcarleson {F G : Set ℝ}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (h2F : MeasureTheory.volume F ∈ Set.Ioo 0 ∞) (h2G : MeasureTheory.volume G ∈ Set.Ioo 0 ∞)
    (f : ℝ → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    :
    ‖∫ x in G, T_ f x‖ ≤
    C1_2 4 2 * (MeasureTheory.volume.real G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real F) ^ (2 : ℝ)⁻¹ := by
  have hF' :  @MeasurableSet ℝ (@MeasureTheory.MeasureSpace.toMeasurableSpace ℝ IsSpaceOfHomogeneousType.toMeasureSpace) F := by sorry
  have hG' :  @MeasurableSet ℝ (@MeasureTheory.MeasureSpace.toMeasurableSpace ℝ IsSpaceOfHomogeneousType.toMeasureSpace) G := by sorry
  --WARNING : theorem1_2C does not yet require all necessary implicit parameters since no proof using them has been provided yet.
  convert theorem1_2C K (by simp) h1 h2 hF' hG' h3 f hf <;> sorry


end section
