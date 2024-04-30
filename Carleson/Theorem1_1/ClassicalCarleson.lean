import Carleson.Carleson
import Carleson.HomogeneousType

--import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic

--TODO: add local notation for f₀


noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

--def K : ℝ → ℝ → ℂ := fun x y ↦ 1 / (x - y)




#check Complex.abs

#check Finset.range

#check AddCircle (2 * Real.pi)

--variable [IsSpaceOfHomogeneousType ℝ 2] (μ : MeasureTheory.Measure ℝ)

open BigOperators
open Finset

#check fourier
--def stdCircle : AddCircle (2 * Real.pi)

#check Finset.Icc

section
open Metric
variable {α : Type} {β : Type}
--might be generalized
--TODO : choose better name
lemma uniformContinuous_iff_bounded [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} {b : ℝ} (bpos : b > 0):
  UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, δ < b ∧ ∀ {x y : α}, dist x y < δ → dist (f x) (f y) < ε := by
  rw [Metric.uniformContinuous_iff]
  constructor
  . intro h ε εpos
    obtain ⟨δ', δ'pos, hδ'⟩ := h ε εpos
    use min δ' (b / 2)
    constructor
    . exact (lt_min δ'pos (by linarith)).gt
    constructor
    . apply min_lt_of_right_lt
      linarith
    . intro x y hxy
      exact hδ' (lt_of_lt_of_le hxy (min_le_left δ' (b / 2)))
  . intro h ε εpos
    obtain ⟨δ, δpos, _, hδ⟩ := h ε εpos
    use δ
end section


def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
#check partialFourierSum

variable {f : ℝ → ℂ} {N : ℕ}

--TODO : add reasonable notation
--local notation "S_" => partialFourierSum f

--TODO : seems like theorem1_1 is actually Theorem 1.2 from the paper
theorem classical_carleson --{f : ℝ → ℂ}
  (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
  {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
  --need condition E ⊆ Set.Icc 0 (2 * Real.pi) to ensure the E has finite volume
  ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
  ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
  Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
    --Choose some δ.
    --TODO : use some scaled ε for the choose
    obtain ⟨δ, δpos, δltpi, hδ⟩ := (uniformContinuous_iff_bounded Real.pi_pos).mp unicontf (ε / 2) (by linarith)
    --definitions from section 10.1 depending on the choice of δ
    set K := Nat.floor ((2 * Real.pi) / δ) + 1 with Kdef
    have Kgt2 : (2 : ℝ) < K := by
      rw [Kdef]
      have : 2 < 2 * Real.pi / δ := (lt_div_iff δpos).mpr ((mul_lt_mul_left (by norm_num)).mpr δltpi)
      convert this.trans (Nat.lt_floor_add_one ((2 * Real.pi) / δ))
      simp
    let f₀ : ℝ → ℂ := fun x ↦ f ((2 * Real.pi * Int.floor ((K * x) / (2 * Real.pi))) / K)
    let E₁ : Set ℝ := ⋃ k ∈ range (K + 1), Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))
    --added helper lemma
    have E₁measurable : MeasurableSet E₁ := by
      apply measurableSet_biUnion
      intro k hk
      exact measurableSet_Icc
    have E₁volume : MeasureTheory.volume.real E₁ ≤ (ε / 2) := by
      calc MeasureTheory.volume.real E₁
      _ ≤ ∑ k in range (K + 1), MeasureTheory.volume.real (Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))) := by
        apply MeasureTheory.measureReal_biUnion_finset_le
      _ = ∑ k in range (K + 1), ε / (4 * K) := by
        apply sum_congr
        . trivial
        intro k hk
        have : 2 * Real.pi / K * (k + ε / (16 * Real.pi)) - 2 * Real.pi / K * (k - ε / (16 * Real.pi)) = ε / (4 * K) := by
          field_simp
          ring
        rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
        . exact this
        . rw [this]
          apply div_nonneg_iff.mpr
          left
          use hε.1.le
          linarith
      _ ≤ (K + 1) * (ε / (4 * K)) := by
        rw [Finset.sum_const]
        simp
      _ = ε / 2 * ((K + 1)/(2 * K)) := by ring
      _ ≤ ε / 2 := by
        rewrite (config := {occs := .pos [2]}) [← mul_one (ε / 2)]
        gcongr
        linarith
        rw [div_le_iff (by linarith)]
        linarith
    --TODO : correct size of N₀
    let N₀ := Nat.ceil (K^2 / ε^3)
    --Lemma 10.2 from the paper
    --changed interval to Icc to match the interval in the theorem
    have piecePartialFourierSumApprox {N : ℕ} (hN : N > N₀) :
      ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₁, Complex.abs (f₀ x - partialFourierSum f₀ N x) ≤ ε / 4:= by
      -- use has_pointwise_sum_fourier_series_of_summable or hasSum_fourier_series_L2 from mathlib?
      -- search for more convergence theorems
      sorry
    --Lemma 10.3 from the paper
    --TODO : review measurability assumption
    --added subset assumption
    --changed interval to match the interval in the theorem
    /-
    have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      sSup {Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) | N : ℕ} ≤ ε / 4 := by
      sorry
    -/
    --simplified statement so that we do not have to worry about a sSup
    have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      ∀ N, Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) ≤ ε / 4 := by
      sorry
    obtain ⟨E₂, E₂subset, E₂measurable, E₂volume, hE₂⟩ := diffPartialFourierSums


    --TODO : change definition of E₁ to be able to prove this
    have E₁subset : E₁ ⊆ Set.Icc 0 (2 * Real.pi) := by
      rw [Set.iUnion_subset_iff]
      simp
      intro k klt x
      simp
      intro lex xle
      sorry

    --set E := E₁ ∪ E₂

    -- Definition of E, slightly changed compared to the paper
    /-
    use (E₁ ∪ E₂) ∩ Set.Icc 0 (2 * Real.pi)
    --use Set.union_subset E₁subset E₂subset
    constructor
    . apply Set.inter_subset_right
    use (E₁measurable.union E₂measurable).inter measurableSet_Icc
    constructor
    . calc MeasureTheory.volume.real ((E₁ ∪ E₂) ∩ Set.Icc 0 (2 * Real.pi))
      _ ≤ MeasureTheory.volume.real (E₁ ∪ E₂) := by
        apply MeasureTheory.measureReal_mono (Set.inter_subset_left (E₁ ∪ E₂) (Set.Icc 0 (2 * Real.pi))) _
        finiteness
      _ ≤ MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := by apply MeasureTheory.measureReal_union_le
      _ ≤ ε / 2 + ε / 2 := by
          apply add_le_add E₁volume E₂volume
      _ = ε := by simp
    -/
    --Definition of E
    use E₁ ∪ E₂
    use Set.union_subset E₁subset E₂subset
    use E₁measurable.union E₂measurable
    constructor
    . calc MeasureTheory.volume.real (E₁ ∪ E₂)
      _ ≤ MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := by apply MeasureTheory.measureReal_union_le
      _ ≤ ε / 2 + ε / 2 := by
          apply add_le_add E₁volume E₂volume
      _ = ε := by simp
    . use N₀
      intro x hx N NgtN₀
      --use "telescope" sum
      calc Complex.abs (f x - partialFourierSum f N x)
      _ = Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x) + (partialFourierSum f₀ N x - partialFourierSum f N x)) := by congr; ring
      _ ≤ Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x)) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
        apply AbsoluteValue.add_le
      _ ≤ Complex.abs (f x - f₀ x) + Complex.abs (f₀ x - partialFourierSum f₀ N x) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
        apply add_le_add_right
        apply AbsoluteValue.add_le
      _ ≤ (ε / 2) + (ε / 4) + (ε/4) := by
        gcongr
        . -- here, we use the definitions of δ, K and f₀
          apply le_of_lt
          apply hδ
          rw [Real.dist_eq]
          calc |x - 2 * Real.pi * ⌊K * x / (2 * Real.pi)⌋ / K|
          _ = |2 * Real.pi * (K * x / (2 * Real.pi)) / K - 2 * Real.pi * ⌊K * x / (2 * Real.pi)⌋ / K| := by congr; field_simp; ring
          _ = |2 * Real.pi * (K * x / (2 * Real.pi) - ⌊K * x / (2 * Real.pi)⌋) / K| := by
            ring_nf
          _ = 2 * Real.pi * |K * x / (2 * Real.pi) - ⌊K * x / (2 * Real.pi)⌋| / K := by
            rw [abs_div, abs_mul, abs_eq_self.mpr Real.two_pi_pos.le, abs_eq_self.mpr ((zero_lt_two).trans Kgt2).le]
          _ ≤ 2 * Real.pi * 1 / K := by
            apply (div_le_div_right ((zero_lt_two).trans Kgt2)).mpr
            apply (mul_le_mul_left Real.two_pi_pos).mpr
            rw [abs_eq_self.mpr]
            apply le_of_lt
            rw [sub_lt_iff_lt_add, add_comm]
            apply Int.lt_floor_add_one
            rw [le_sub_iff_add_le, zero_add]
            apply Int.floor_le
          _ < δ := by
            rw [div_lt_iff, mul_one, ← div_lt_iff' δpos]
            . push_cast
              apply Nat.lt_floor_add_one
            exact (zero_lt_two).trans Kgt2
        . have : x ∈ Set.Icc 0 (2 * Real.pi) \ E₁ := ⟨hx.1, fun xE₁ ↦ hx.2 (Set.mem_union_left E₂ xE₁)⟩
          apply piecePartialFourierSumApprox NgtN₀ x this
        . have : x ∈ Set.Icc 0 (2 * Real.pi) \ E₂ := ⟨hx.1, fun xE₂ ↦ hx.2 (Set.mem_union_right E₁ xE₂)⟩
          apply hE₂ x this N
      _ ≤ ε := by linarith


#check classical_carleson



section

open ENNReal

def k (x : ℝ) : ℂ := max (1 - |x|) 0 / (1 - Complex.exp (Complex.I * x))
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
instance helper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    IsSpaceOfHomogeneousType E (2 ^ FiniteDimensional.finrank ℝ E) := by sorry

/- lemmas 10.22 to 10.26 are for this -/
instance IsSpaceOfHomogeneousTypeR2: IsSpaceOfHomogeneousType ℝ 2 := by
  have : IsSpaceOfHomogeneousType ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := by apply helper
  simpa

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
lemma isSpaceOfHomogeneousType_with_increased_constant {X : Type} {a b : ℝ} [MetricSpace X] [IsSpaceOfHomogeneousType X a] (aleb : a ≤ b) : IsSpaceOfHomogeneousType X b where
  volume_ball_two_le_same := by
    intro x r
    calc MeasureTheory.volume.real (Metric.ball x (2 * r))
    _ ≤ a * MeasureTheory.volume.real (Metric.ball x r) := by apply volume_ball_two_le_same
    _ ≤ b * MeasureTheory.volume.real (Metric.ball x r) := by gcongr

--TODO : decide whether to move this up so that all the above lemmas are directly proven with the right doubling constant
instance badR: IsSpaceOfHomogeneousType ℝ 4 := by
  have : IsSpaceOfHomogeneousType ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := by apply helper
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
    sorry
    --TODO: fix problems with Finset
    /-
    let balls : Finset (C(ℝ, ℂ)) := {θ m₁, θ m₂, θ m₃} --with balls_def
    use balls
    constructor
    . rw [balls_def]
      apply card_le_three
    -/


--TODO : What is Lemma 10.34 (frequency ball growth) needed for?

--TODO : possibly issues with a different "doubling constant" than in the paper (4 instead of 2)
instance h5 : IsCancellative 2 Θ where
  /- Lemma 10.36 (real van der Corput) from the paper. -/
  norm_integral_exp_le := by sorry

/- Lemma 10.9 (lower secant bound) from the paper. -/
lemma lower_secant_bound {η : ℝ} (ηpos : η > 0) {x : ℝ} (xIcc : x ∈ Set.Icc (-2 * Real.pi + η) (2 * Real.pi - η)) (xAbs : η ≤ |x|) :
    η / 8 ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
  sorry

/- Lemma 10.38 (Hilbert kernel regularity) -/
lemma Hilbert_kernel_regularity {x y y' : ℝ} :
    2 * |y - y'| ≤ |x - y| → ‖K x y - K x y'‖ ≤ 2 ^ 10 * (1 / |x - y|) * (|y - y'| / |x - y|)  := by
  sorry

--TODO : add some Real.vol lemma

instance h6 : IsCZKernel 4 K where
  /- Lemma 10.37 (Hilbert kernel bound) from the paper. -/
  norm_le_vol_inv := by
    intro x y
    by_cases h : 0 < |x - y| ∧ |x - y| < 1
    . calc ‖K x y‖
        _ ≤ 1 / ‖1 - Complex.exp (Complex.I * ↑(x - y))‖ := by
          rw [K, k, norm_div]
          gcongr
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
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
        _ ≤ (2 : ℝ) ^ (4 : ℝ) ^ 3 / Real.vol x y := by
          rw [Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal]
          . ring_nf
            gcongr
            norm_num
          . linarith
        _ = (2 : ℝ) ^ (4 : ℝ) ^ 3 / @Real.vol ℝ Real.pseudoMetricSpace IsSpaceOfHomogeneousType.toMeasureSpace x y := by
          congr
          --TODO : Identify Real.measureSpace = IsSpaceOfHomogeneousType.toMeasureSpace
          --rw [IsSpaceOfHomogeneousType.toMeasureSpace, badR]
          sorry
    . push_neg at h
      have : ‖K x y‖ = 0 := by
        rw [norm_eq_zero, K, k, _root_.div_eq_zero_iff]
        by_cases xeqy : x = y
        . right
          simp [xeqy]
        . left
          simp
          apply h (abs_pos.mpr (sub_ne_zero.mpr xeqy))
      rw [this]
      apply div_nonneg
      . norm_num
      . exact MeasureTheory.measureReal_nonneg
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
