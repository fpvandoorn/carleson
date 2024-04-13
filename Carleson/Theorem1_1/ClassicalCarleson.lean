import Carleson.Carleson
import Carleson.HomogeneousType

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic


noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

#check theorem1_1C
/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

def K : ℝ → ℝ → ℂ := fun x y ↦ 1 / (x - y)

instance : IsSpaceOfHomogeneousType ℝ 2 := by
  have : IsSpaceOfHomogeneousType ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := inferInstance
  simpa

#check theorem1_1C K (by norm_num)

#check Complex.abs

#check Finset.range

#check AddCircle (2 * Real.pi)

variable [IsSpaceOfHomogeneousType ℝ 2] (μ : MeasureTheory.Measure ℝ)

open BigOperators
open Finset

#check fourier
--def stdCircle : AddCircle (2 * Real.pi)

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in range (2 * N + 1), fourierCoeffOn Real.two_pi_pos f (n - N) * fourier (n - N) (x : AddCircle (2 * Real.pi))
#check partialFourierSum

--let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume

--TODO : seems like theorem1_1 is actually Theorem 1.2 from the paper
--TODO : check and compare to version in mathlib has_pointwise_sum_fourier_series_of_summable and similar
theorem classical_carleson {f : ℝ → ℂ}
  (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
  {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
  --TODO: readd condition E ⊆ Set.Icc 0 (2 * Real.pi) ?
  ∃ E : Set ℝ, MeasurableSet E ∧ MeasureTheory.volume E ≤ ε.toNNReal ∧
  ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
  Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
    --TODO : use some scaled ε for the choose
    --TODO : ensure that we choose δ < Real.pi
    choose δ δpos hδ using Metric.uniformContinuous_iff.mp unicontf ε hε.1
    have δltpi : δ < Real.pi := sorry

    --definitions from section 10.1 depending on the choice of δ
    set K := Nat.floor ((2 * Real.pi) / δ) + 1 with Kdef
    have Kgt2 : (2 : ℝ) < K := by
      rw [Kdef]
      have : 2 < 2 * Real.pi / δ := (lt_div_iff δpos).mpr ((mul_lt_mul_left (by norm_num)).mpr δltpi)
      convert this.trans (Nat.lt_floor_add_one ((2 * Real.pi) / δ))
      simp
    let f₀ : ℝ → ℂ := fun x ↦ f ((2 * Real.pi * Int.floor ((K * x) / (2 * δ))) / K)
    let E₁ : Set ℝ := ⋃ k ∈ range (K + 1), Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))
    --added helper lemma
    have E₁measurable : MeasurableSet E₁ := by
      --rw [E₁def]
      apply measurableSet_biUnion
      intro k hk
      exact measurableSet_Icc
    have E₁volume : MeasureTheory.volume E₁ ≤ (ε / 2).toNNReal := by
      calc MeasureTheory.volume E₁
      _ ≤ ∑ k in range (K + 1), MeasureTheory.volume (Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))) := by
        apply MeasureTheory.measure_biUnion_finset_le
      _ = ∑ k in range (K + 1), ↑(ε / (4 * K)).toNNReal := by
        apply sum_congr
        . trivial
        intro k hk
        rw [Real.volume_Icc]
        congr
        field_simp
        ring
      _ ≤ (K + 1) * ↑(ε / (4 * K)).toNNReal := by
        rw [Finset.sum_const]
        simp
      _ = (ε / 2 * ((K + 1)/(2 * K))).toNNReal := by
        sorry
      _ ≤ (ε / 2).toNNReal := by sorry

    --TODO : correct size of N₀
    let N₀ := Nat.ceil (K^2 / ε^3)
    --Lemma 10.2 from the paper
    have piecePartialFourierSumApprox {N : ℕ} (hN : N > N₀) :
      ∀ x ∈ Set.Ico 0 (2 * Real.pi) \ E₁, Complex.abs (f₀ x - partialFourierSum f₀ N x) ≤ ε / 4:= by
      sorry
    --Lemma 10.3 from the paper
    --TODO : review measurability assumption
    have diffPartialFourierSums : ∃ E₂, MeasurableSet E₂ ∧ MeasureTheory.volume E₂ ≤ (ε / 2).toNNReal ∧ ∀ x ∈ (Set.Ico 0 1) \ E₂,
      sSup {Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) | N : ℕ} ≤ ε / 4 := by
      sorry
    obtain ⟨E₂, E₂measurable, E₂volume, hE₂⟩ := diffPartialFourierSums

    --set E := E₁ ∪ E₂
    use E₁ ∪ E₂
    use E₁measurable.union E₂measurable
    constructor
    . calc MeasureTheory.volume (E₁ ∪ E₂)
      _ ≤ MeasureTheory.volume E₁ + MeasureTheory.volume E₂ := by apply MeasureTheory.measure_union_le
      _ ≤ (ε / 2).toNNReal + (ε / 2).toNNReal := by
        apply add_le_add E₁volume E₂volume
      _ = ε.toNNReal := by sorry
        --rw [←coe_add]
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
        apply add_le_add
        . apply add_le_add
          . sorry --obtain this from hδ somehow
          . apply piecePartialFourierSumApprox NgtN₀ x
            simp
            constructor
            . sorry
            . have := hx.2
              simp at this
              push_neg at this
              exact this.1
        . sorry --apply hE₂ x
      _ ≤ ε := by field_simp; ring_nf; trivial





#check classical_carleson
