/- This file contains the proof of Lemma 10.4, from section 10.7-/

import Carleson.MetricCarleson
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Hilbert_kernel
import Carleson.Theorem1_1.CarlesonOperatorReal
import Carleson.Theorem1_1.Van_der_Corput

--import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open MeasureTheory Function Metric Bornology

--#lint

section
@[reducible]
def DoublingMeasureR2 : DoublingMeasure ℝ 2 where
  --rwa [FiniteDimensional.finrank_self, pow_one] at this
  volume_ball_two_le_same := by
    have : DoublingMeasure ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := by infer_instance
    intro x r
    have := this.volume_ball_two_le_same x r
    simp only [FiniteDimensional.finrank_self, pow_one] at this
    --rw [FiniteDimensional.finrank_self, pow_one] at this

    calc MeasureTheory.volume.real (Metric.ball x (2 * r))
      _ ≤ 2 * MeasureTheory.volume.real (Metric.ball x r) := by
        by_cases r_nonneg : r < 0
        . rw [ball_eq_empty.mpr, ball_eq_empty.mpr]
          simp
          all_goals linarith
        rw [measureReal_def, measureReal_def, Real.volume_ball, Real.volume_ball, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
        <;> linarith

instance DoublingMeasureR4 : DoublingMeasure ℝ (2 ^ 4 : ℕ) :=
  DoublingMeasureR2.mono (by norm_num)
end

lemma h1 : 2 ∈ Set.Ioc 1 (2 : ℝ) := by simp
lemma h2 : Real.IsConjExponent 2 2 := by rw [Real.isConjExponent_iff_eq_conjExponent] <;> norm_num

lemma localOscillation_on_emptyset {X : Type} [PseudoMetricSpace X] {f g : C(X, ℝ)} :
    localOscillation ∅ f g = 0 := by simp [localOscillation]

lemma localOscillation_on_empty_ball {X : Type} [PseudoMetricSpace X] {x : X} {f g : C(X, ℝ)} {R : ℝ} (R_nonpos : R ≤ 0):
    localOscillation (Metric.ball x R) f g = 0 := by
  rw [Metric.ball_eq_empty.mpr R_nonpos, localOscillation_on_emptyset]

lemma ConditionallyCompleteLattice.le_biSup {α : Type} [ConditionallyCompleteLinearOrder α] {ι : Type} [Nonempty ι]
    {f : ι → α} {s : Set ι} {a : α} (hfs : BddAbove (f '' s)) (ha : ∃ i ∈ s, f i = a) :
    a ≤ ⨆ i ∈ s, f i := by
  apply ConditionallyCompleteLattice.le_csSup
  · --TODO: improve this
    rw [bddAbove_def] at *
    rcases hfs with ⟨x, hx⟩
    use (max x (sSup ∅))
    intro y hy
    simp at hy
    rcases hy with ⟨z, hz⟩
    rw [iSup] at hz
    by_cases h : z ∈ s
    · have : (@Set.range α (z ∈ s) fun _ ↦ f z) = {f z} := by
        rw [Set.eq_singleton_iff_unique_mem]
        constructor
        · simpa
        · exact fun x hx => hx.2.symm
      rw [this] at hz
      have : sSup {f z} = f z := csSup_singleton _
      rw [this] at hz
      simp at hx
      have : f z ≤ x := hx z h
      rw [hz] at this
      exact le_max_of_le_left this
    have : (@Set.range α (z ∈ s) fun _ ↦ f z) = ∅ := by simpa
    rw [this] at hz
    exact hz ▸ le_max_right x y
  rw [Set.mem_range]
  rcases ha with ⟨i, hi, fia⟩
  use i
  rw [iSup]
  convert csSup_singleton _
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simp
    use hi, fia
  · intro x hx
    simp at hx
    rwa [hx.2] at fia

--mainly have to work for the following lemmas

section

open ENNReal

section
local notation "θ" => integer_linear

local notation "Θ" => {(θ n) | n : ℤ}

theorem localOscillation_of_same  {X : Type} [PseudoMetricSpace X] {E : Set X} {f : C(X, ℝ)} :
    localOscillation E f f = 0 := by simp [localOscillation]

/-Stronger version of oscillation_control from the paper-/
/-Based on earlier version of the paper. -/
lemma localOscillation_of_integer_linear {x R : ℝ} (R_nonneg : 0 ≤ R) : ∀ n m : ℤ, localOscillation (Metric.ball x R) (θ n) (θ m) = 2 * R * |(n : ℝ) - m| := by
  intro n m
  by_cases n_ne_m : n = m
  · simp [n_ne_m, sub_self, abs_zero, mul_zero, localOscillation_of_same]
  push_neg at n_ne_m
  have norm_n_sub_m_pos : 0 < |(n : ℝ) - m| := by
    simp only [abs_pos, ne_eq]
    rwa [sub_eq_zero, Int.cast_inj]
  /- Rewrite to a more convenient form for the following steps. -/
  have norm_integer_linear_eq {n m : ℤ} {z : ℝ × ℝ} : ‖(θ n) z.1 - (θ m) z.1 - (θ n) z.2 + (θ m) z.2‖ = ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
    simp only [integer_linear, ContinuousMap.coe_mk, Real.norm_eq_abs]
    ring_nf
  have localOscillation_eq : localOscillation (Metric.ball x R) (θ n) (θ m) = ⨆ z ∈ (Metric.ball x R) ×ˢ (Metric.ball x R), ‖(n - m) * (z.1 - x) - (n - m) * (z.2 - x)‖ := by
      rw [localOscillation]
      congr with z
      rw [norm_integer_linear_eq]
  rw [localOscillation_eq]
  /- Show inequalities in both directions. -/
  apply le_antisymm
  · calc ⨆ z ∈ (Metric.ball x R) ×ˢ (Metric.ball x R), ‖(n - m) * (z.1 - x) - (n - m) * (z.2 - x)‖
      _ ≤ 2 * R * |↑n - ↑m| := by
        apply Real.iSup_le
        --TODO: investigate strange (delaborator) behavior - why is there still a sup?
        intro z
        apply Real.iSup_le
        · intro hz
          simp at hz
          rw [Real.dist_eq, Real.dist_eq] at hz
          rw [Real.norm_eq_abs]
          calc |(n - m) * (z.1 - x) - (n - m) * (z.2 - x)|
          _ ≤ |(n - m) * (z.1 - x)| + |(n - m) * (z.2 - x)| := abs_sub _ _
          _ = |↑n - ↑m| * |z.1 - x| + |↑n - ↑m| * |z.2 - x| := by congr <;> apply abs_mul
          _ ≤ |↑n - ↑m| * R + |↑n - ↑m| * R := by gcongr; linarith [hz.1]; linarith [hz.2]
          _ = 2 * R * |↑n - ↑m| := by ring
        repeat
          apply mul_nonneg
          linarith
          apply abs_nonneg
  · apply le_of_forall_lt
    intro c hc
    have := fact_isCompact_ball x R
    by_cases c_nonneg : 0 > c
    · calc c
        _ < 0 := c_nonneg
        _ ≤ @dist (withLocalOscillation ℝ (Metric.ball x R)) PseudoMetricSpace.toDist (θ n) (θ m) := dist_nonneg
        _ = localOscillation (Metric.ball x R) (θ n) (θ m) := rfl
        _ = ⨆ z ∈ Metric.ball x R ×ˢ Metric.ball x R, ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
          rw [localOscillation]
          congr with z
          rw [norm_integer_linear_eq]
    push_neg at c_nonneg
    set R' := (c + 2 * R * |(n : ℝ) - m|) / (4 * |(n : ℝ) - m|) with R'def
    have hR' : 0 ≤ R' ∧ R' < R := by
      rw [R'def]
      constructor
      · positivity
      calc (c + 2 * R * |↑n - ↑m|) / (4 * |↑n - ↑m|)
        _ < (2 * R * |↑n - ↑m| + 2 * R * |↑n - ↑m|) / (4 * |↑n - ↑m|) := by gcongr
        _ = R := by
          ring_nf
          rw [mul_assoc, mul_inv_cancel norm_n_sub_m_pos.ne.symm, mul_one]
    let y := (x - R', x + R')
    calc c
      _ = c / 2 + c / 2 := by ring
      _ < c / 2 + (2 * R * |↑n - ↑m|) / 2 := by gcongr
      _ = 2 * R' * |↑n - ↑m| := by
        rw [R'def]
        ring_nf
        rw [pow_two, ←mul_assoc, mul_assoc c, mul_inv_cancel norm_n_sub_m_pos.ne.symm,
          mul_assoc (R * _), mul_inv_cancel norm_n_sub_m_pos.ne.symm]
        ring
      _ ≤ ‖(↑n - ↑m) * (y.1 - x) - (↑n - ↑m) * (y.2 - x)‖ := by
        simp only [mul_assoc, sub_sub_cancel_left, mul_neg, add_sub_cancel_left,
          sub_eq_add_neg (-((n - m) * R')), ← two_mul, norm_neg, norm_mul, RCLike.norm_ofNat,
          Real.norm_eq_abs, mul_comm |(n : ℝ) - m|, gt_iff_lt, Nat.ofNat_pos,
          _root_.mul_le_mul_left]
        gcongr
        exact le_abs_self _
      _ ≤ ⨆ z ∈ Metric.ball x R ×ˢ Metric.ball x R, ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
        apply ConditionallyCompleteLattice.le_biSup
        · convert bddAbove_localOscillation (Metric.ball x R) (θ n) (θ m) using 2
          exact norm_integer_linear_eq.symm
        · use y
          simp [abs_of_nonneg, hR'.1, hR'.2]

--TODO: probably not needed any more
lemma bciSup_of_emptyset  {α : Type} [ConditionallyCompleteLattice α] {ι : Type} [Nonempty ι] {f : ι → α} :
    ⨆ i ∈ (∅ : Set ι), f i = sSup ∅ := by
  rw [iSup]
  convert csSup_singleton _
  have : ∀ i : ι, IsEmpty (i ∈ (∅ : Set ι)) := by tauto
  have : (fun (i : ι) ↦ ⨆ (_ : i ∈ (∅ : Set ι)), f i) = fun i ↦ sSup ∅ := by
    ext i
    --rw [csSup_empty]
    rw [iSup]
    congr
    rw [Set.range_eq_empty_iff]
    exact this i
  rw [this]
  exact Set.range_const

end
--lemma frequency_ball_doubling {x R : ℝ} (Rpos : 0 < R) :

instance : FunctionDistances ℝ ℝ where
  Θ := ℤ
  coeΘ := integer_linear
  coeΘ_injective {n m} hnm := by simpa [integer_linear] using hnm 1
  metric := fun _ R ↦ {
      dist := fun n m ↦ 2 * max R 0 * |n - m|
      dist_self := by simp
      dist_comm := by
        simp only [Int.cast_abs, Int.cast_sub, mul_eq_mul_left_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or]
        intro x y
        left
        norm_cast
        apply abs_sub_comm
      dist_triangle := by
        simp only [Int.cast_abs, Int.cast_sub]
        intro x y z
        rw [← mul_add]
        gcongr
        norm_cast
        apply abs_sub_le
      --next field will get default in mathlib and is left out here
      --TODO: remove when that is the case
      edist_dist := fun x y ↦ rfl
  }

--TODO: add lemma to avoid unfolds.
--lemma dist_eq_ww

lemma coeΘ_R (n : Θ ℝ) (x : ℝ) : n x = n * x := rfl
lemma coeΘ_R_C (n : Θ ℝ) (x : ℝ) : (n x : ℂ) = n * x := by norm_cast

instance h4 : CompatibleFunctions ℝ ℝ (2 ^ 4) where
  eq_zero := by
    use 0
    intro f
    rw [coeΘ_R, mul_zero]
  localOscillation_le_cdist := by
    intro x r f g
    by_cases r_pos : r ≤ 0
    . rw [ball_eq_empty.mpr r_pos]
      unfold localOscillation
      simp [dist_nonneg]
    push_neg at r_pos
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
      localOscillation integer_linear
    dsimp
    calc ⨆ z ∈ ball x r ×ˢ ball x r, |↑f * z.1 - ↑g * z.1 - ↑f * z.2 + ↑g * z.2|
      _ = ⨆ z ∈ ball x r ×ˢ ball x r, ‖(f - g) * (z.1 - x) - (f - g) * (z.2 - x)‖ := by
        congr
        ext z
        congr
        ext h
        rw [Real.norm_eq_abs]
        congr 1
        ring
      _ ≤ 2 * r * |↑f - ↑g| := by
        apply Real.iSup_le
        --TODO: investigate strange (delaborator) behavior - why is there still a sup?
        intro z
        apply Real.iSup_le
        . intro hz
          simp at hz
          rw [Real.dist_eq, Real.dist_eq] at hz
          rw [Real.norm_eq_abs]
          calc |(f - g) * (z.1 - x) - (f - g) * (z.2 - x)|
          _ ≤ |(f - g) * (z.1 - x)| + |(f - g) * (z.2 - x)| := by apply abs_sub
          _ = |↑f - ↑g| * |z.1 - x| + |↑f - ↑g| * |z.2 - x| := by congr <;> apply abs_mul
          _ ≤ |↑f - ↑g| * r + |↑f - ↑g| * r := by gcongr; linarith [hz.1]; linarith [hz.2]
          _ = 2 * r * |↑f - ↑g| := by ring
        all_goals
        repeat
          apply mul_nonneg
          linarith
          apply abs_nonneg
      _ ≤ 2 * max r 0 * |↑f - ↑g| := by
        gcongr
        apply le_max_left
    norm_cast
  cdist_mono := by
    intro x₁ x₂ r R f g h
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    by_cases r_pos : r ≤ 0
    . rw [ball_eq_empty.mpr r_pos] at h
      rw [max_eq_right r_pos]
      gcongr
      apply le_max_right
    push_neg at r_pos
    gcongr
    rw [Real.ball_eq_Ioo, Real.ball_eq_Ioo, Set.Ioo_subset_Ioo_iff (by linarith)] at h
    linarith [h.1, h.2]
  cdist_le := by
    intro x₁ x₂ r f g
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal Real.pseudoMetricSpace
    dsimp
    intro _
    by_cases r_nonneg : r ≥ 0
    . rw [max_eq_left, max_eq_left]
      ring_nf
      gcongr
      norm_num
      all_goals linarith [r_nonneg]
    . rw [max_eq_right, max_eq_right]
      simp
      all_goals linarith [r_nonneg]
  le_cdist := by
    intro x₁ x₂ r f g _
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    by_cases r_nonneg : r ≥ 0
    . rw [max_eq_left, max_eq_left]
      ring_nf
      gcongr
      norm_num
      all_goals linarith [r_nonneg]
    . rw [max_eq_right, max_eq_right]
      simp
      all_goals linarith [r_nonneg]
  ballsCoverBalls := by
    intro x R R' f
    unfold WithFunctionDistance at f
    rw [coveredByBalls_iff]
    by_cases R'pos : 0 ≥ R'
    · --trivial case
      use {f}
      constructor
      . norm_num
      simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
      rw [Metric.ball_eq_empty.mpr R'pos, Set.subset_empty_iff, Metric.ball_eq_empty]
      linarith
    push_neg at R'pos
    by_cases Rpos : 0 ≥ R
    · --trivial case
      use {f}
      constructor
      . norm_num
      simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
      convert Set.subset_univ _
      ext g
      constructor
      . simp
      simp only [Set.mem_univ, mem_ball, true_implies]
      unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
      dsimp
      convert R'pos
      simp
      left
      exact Rpos
    push_neg at Rpos
    set m₁ := Int.floor (f - R' / (2 * R)) with m₁def
    set! m₂ := f with m₂def
    set m₃ := Int.ceil (f + R' / (2 * R)) with m₃def

    /- The following is necessary for withLocalOscillation to be defined. -/
    classical
    set balls : Finset ((WithFunctionDistance x R)) := {m₁, m₂, m₃} with balls_def
    use balls
    constructor
    · rw [balls_def]
      apply le_trans Finset.card_le_three
      norm_num
    intro φ hφ
    unfold WithFunctionDistance at φ
    --rw [←hn'] at hφ
    rw [mem_ball] at hφ
    rw [dist_comm] at hφ
    /- m₁, m₂, m₃ each correspond to one case. -/
    --rw [←hn']
    simp only [Set.mem_iUnion, mem_ball, exists_prop]
    by_cases h : φ ≤ f - R' / (2 * R)
    . use m₁
      constructor
      · rw [balls_def]
        simp
      unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
      dsimp
      calc 2 * max R 0 * |↑φ - m₁|
        _ = 2 * R * |↑φ - m₁| := by
          congr
          rw [max_eq_left_iff]
          exact Rpos.le
        _ = 2 * R * (m₁ - ↑φ) := by
          rw [abs_of_nonpos]
          simp only [neg_sub]
          norm_cast
          simp only [tsub_le_iff_right, zero_add, Int.cast_le]
          rwa [m₁def, Int.le_floor]
        _ = 2 * R * (m₁ - f) + 2 * R * (f - φ) := by ring
        _ < - R' + 2 * R' := by
          apply add_lt_add_of_le_of_lt
          . rw [m₁def]
            calc 2 * R * (⌊f - R' / (2 * R)⌋ - f)
              _ ≤ 2 * R * (f - R' / (2 * R) - f) := by
                gcongr
                apply Int.floor_le
              _ = -R' := by
                ring_nf
                rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
          . calc 2 * R * (↑f - ↑φ)
              _ ≤ 2 * R * |↑f - ↑φ| := by
                gcongr
                apply le_abs_self
              _ < 2 * R' := by
                convert hφ
                unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
                dsimp
                norm_cast
                congr
                symm
                rw [max_eq_left_iff]
                exact Rpos.le
        _ = R' := by ring
    push_neg at h
    by_cases h' : φ < f + R' / (2 * R)
    . use m₂
      constructor
      · rw [balls_def]
        simp
      rw [m₂def, dist_comm]
      unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
      dsimp
      push_cast
      calc 2 * max R 0 * |↑f - ↑φ|
        _ = 2 * R * |↑f - ↑φ| := by
          congr
          rw [max_eq_left_iff]
          exact Rpos.le
        _ < 2 * R * (R' / (2 * R)) := by
          gcongr
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        _ = R' := by field_simp
    push_neg at h'
    use m₃
    constructor
    . simp [balls_def]
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    push_cast
    calc 2 * max R 0 * |↑φ - ↑m₃|
      _ = 2 * R * (↑φ - ↑m₃) := by
        rw [abs_of_nonneg]
        congr
        rw [max_eq_left_iff]
        exact Rpos.le
        simp only [sub_nonneg, Int.cast_le]
        rwa [m₃def, Int.ceil_le]
      _ = 2 * R * (φ - f) + 2 * R * (f - m₃) := by ring
      _ < 2 * R' - R' := by
        apply add_lt_add_of_lt_of_le
        . calc 2 * R * (↑φ - ↑f)
            _ ≤ 2 * R * |↑φ - ↑f| := by
              gcongr
              exact le_abs_self _
            _ = 2 * R * |↑f - ↑φ| := by
              congr 1
              exact abs_sub_comm _ _
            _ < 2 * R' := by
              convert hφ
              unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
              dsimp
              norm_cast
              congr
              symm
              rw [max_eq_left_iff]
              exact Rpos.le
        . rw [m₃def]
          calc 2 * R * (f - ⌈f + R' / (2 * R)⌉)
            _ ≤ 2 * R * (f - (f + R' / (2 * R))) := by
              gcongr
              exact Int.le_ceil _
            _ = -R' := by
              ring_nf
              rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
      _ = R' := by ring


--TODO : What is Lemma 10.34 (frequency ball growth) needed for?

--set_option profiler true in
instance h5 : IsCancellative ℝ (1 / (4 : ℕ)) where
  /- Lemma 10.36 (real van der Corput) from the paper. -/
  norm_integral_exp_le := by
    intro x r ϕ K hK _ f g
    by_cases r_pos : 0 ≥ r
    . rw [ball_eq_empty.mpr r_pos]
      simp
    push_neg at r_pos
    rw [measureReal_def, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [r_pos]), Real.ball_eq_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [r_pos])]
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric CompatibleFunctions.toFunctionDistances h4
    dsimp only
    unfold instFunctionDistancesReal
    dsimp only
    rw [max_eq_left r_pos.le]
    set L : NNReal := ⟨⨆ (x : ℝ) (y : ℝ) (_ : x ≠ y), ‖ϕ x - ϕ y‖ / dist x y, by
            apply Real.iSup_nonneg
            intro x
            apply Real.iSup_nonneg
            intro y
            apply Real.iSup_nonneg
            intro _
            apply div_nonneg (norm_nonneg _) dist_nonneg⟩  with Ldef
    set B : NNReal := ⟨⨆ y ∈ ball x r, ‖ϕ y‖, by
            apply Real.iSup_nonneg
            intro i
            apply Real.iSup_nonneg
            intro _
            apply norm_nonneg⟩  with Bdef
    calc ‖∫ (x : ℝ) in x - r..x + r, (Complex.I * (↑(f x) - ↑(g x))).exp * ϕ x‖
      _ = ‖∫ (x : ℝ) in x - r..x + r, (Complex.I * ((↑f - ↑g) : ℤ) * x).exp * ϕ x‖ := by
        congr
        ext x
        rw [mul_assoc]
        congr
        push_cast
        rw [_root_.sub_mul]
        norm_cast
      _ ≤ 2 * Real.pi * ((x + r) - (x - r)) * (B + L * ((x + r) - (x - r)) / 2) * (1 + |((↑f - ↑g) : ℤ)| * ((x + r) - (x - r)))⁻¹ := by
        apply van_der_Corput (by linarith)
        . rw [lipschitzWith_iff_dist_le_mul]
          intro x y
          --TODO: The following could be externalised as a lemma.
          by_cases hxy : x = y
          . rw [hxy]
            simp
          rw [dist_eq_norm, ← div_le_iff (dist_pos.mpr hxy), Ldef, NNReal.coe_mk]
          --apply ConditionallyCompleteLattice.le_csSup
          apply le_ciSup_of_le _ x
          apply le_ciSup_of_le _ y
          apply le_ciSup_of_le _ hxy
          rfl
          . use K
            rw [upperBounds]
            simp only [ne_eq, Set.mem_range, exists_prop, and_imp,
              forall_apply_eq_imp_iff, Set.mem_setOf_eq]
            intro h
            rw [div_le_iff (dist_pos.mpr h), dist_eq_norm]
            apply LipschitzWith.norm_sub_le hK
          . use K
            rw [upperBounds]
            simp only [ne_eq, Set.mem_range, forall_exists_index,
              forall_apply_eq_imp_iff, Set.mem_setOf_eq]
            intro y
            apply Real.iSup_le _ NNReal.zero_le_coe
            intro h
            rw [div_le_iff (dist_pos.mpr h), dist_eq_norm]
            apply LipschitzWith.norm_sub_le hK
          . use K
            rw [upperBounds]
            simp only [ne_eq, Set.mem_range, forall_exists_index,
              forall_apply_eq_imp_iff, Set.mem_setOf_eq]
            intro x
            apply Real.iSup_le _ NNReal.zero_le_coe
            intro y
            apply Real.iSup_le _ NNReal.zero_le_coe
            intro h
            rw [div_le_iff (dist_pos.mpr h), dist_eq_norm]
            apply LipschitzWith.norm_sub_le hK
        . --prove main property of B
          intro y hy
          apply ConditionallyCompleteLattice.le_biSup
          . --TODO: externalize as lemma LipschitzWithOn.BddAbove or something like that?
            rw [Real.ball_eq_Ioo]
            apply BddAbove.mono (Set.image_mono Set.Ioo_subset_Icc_self)
            exact isCompact_Icc.bddAbove_image (continuous_norm.comp hK.continuous).continuousOn
          use y
          rw [Real.ball_eq_Ioo]
          use hy
      _ = 2 * Real.pi * (2 * r) * (B + r * L) * (1 + 2 * r * |((↑f - ↑g) : ℤ)|)⁻¹ := by
        ring
      _ ≤ (2 ^ 4 : ℕ) * (2 * r) * iLipNorm ϕ x r * (1 + 2 * r * ↑|(↑f - ↑g : ℤ)|) ^ (- (1 / (4 : ℝ))) := by
        gcongr
        . apply mul_nonneg
          apply mul_nonneg (by norm_num) (by linarith)
          apply iLipNorm_nonneg r_pos.le
        . norm_num
          linarith [Real.pi_le_four]
        . unfold iLipNorm
          gcongr
          apply le_of_eq Bdef
          apply le_of_eq Ldef
        . rw [← Real.rpow_neg_one]
          apply Real.rpow_le_rpow_of_exponent_le _ (by norm_num)
          simp only [Int.cast_abs, Int.cast_sub, le_add_iff_nonneg_right]
          apply mul_nonneg (by linarith)
          apply abs_nonneg


--TODO : add some Real.vol lemma

instance h6 : IsOneSidedKernel 4 K where
  /- uses Hilbert_kernel_bound -/
  norm_K_le_vol_inv := by
    intro x y
    rw [Complex.norm_eq_abs, Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
    calc Complex.abs (K x y)
    _ ≤ 2 ^ (2 : ℝ) / (2 * |x - y|) := Hilbert_kernel_bound
    _ ≤ 2 ^ (4 : ℝ) ^ 3 / (2 * |x - y|) := by gcongr <;> norm_num
  /- uses Hilbert_kernel_regularity -/
  norm_K_sub_le := by
    intro x y y' h
    rw [Real.dist_eq, Real.dist_eq] at *
    calc ‖K x y - K x y'‖
    _ ≤ 2 ^ 8 * (1 / |x - y|) * (|y - y'| / |x - y|) := by
      apply Hilbert_kernel_regularity
      linarith [abs_nonneg (x-y)]
    _ ≤ (|y - y'| / |x - y|) ^ (4 : ℝ)⁻¹ * (2 ^ (4 : ℝ) ^ 3 / Real.vol x y) := by
      rw [Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
      ring_nf
      rw [pow_two, mul_assoc |x - y|⁻¹]
      gcongr
      · conv =>
          lhs
          rw [← Real.rpow_one (|x - y|⁻¹ * |y - y'|)]
        apply Real.rpow_le_rpow_of_exponent_ge'
        · field_simp
          exact div_nonneg (abs_nonneg (y - y')) (abs_nonneg (x - y))
        · field_simp
          apply div_le_one_of_le <;> linarith [abs_nonneg (x - y)]
        · norm_num
        · norm_num
      · norm_num
  /- Lemma ?-/
  measurable_K_left := fun y ↦ Measurable.of_uncurry_right Hilbert_kernel_measurable
  /- Lemma ?-/
  measurable_K_right := Hilbert_kernel_measurable

/- Lemma ?-/
lemma h3 : HasBoundedStrongType (ANCZOperator K) 2 2 volume volume (C_Ts 4) := sorry



-- #check @metric_carleson
--#check metric_carleson K (by simp) h1 h2 _ _ h3

local notation "T" => CarlesonOperatorReal K

--TODO : change name to reflect that this only holds for a specific instance of CarlesonOperaterReal?
lemma CarlesonOperatorReal_le_CarlesonOperator : T ≤ CarlesonOperator K := by
  intro f x
  rw [CarlesonOperator, CarlesonOperatorReal]
  apply iSup_le
  intro n
  apply iSup_le
  intro r
  apply iSup_le
  intro rpos
  apply iSup_le
  intro rle1
  apply le_iSup_of_le n _
  apply le_iSup₂_of_le r 1 _
  apply (le_iSup₂_of_le rpos rle1 (le_of_eq _))
  congr with y
  rw [coeΘ_R_C]
  ring_nf

/- Lemma 10.4 (ENNReal version) -/
lemma rcarleson {F G : Set ℝ}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    --(h2F : MeasureTheory.volume F ≠ ∞) (h2G : MeasureTheory.volume G ≠ ∞)
    (f : ℝ → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    :
    ∫⁻ x in G, T f x ≤
    ENNReal.ofReal (C1_2 4 2) * (MeasureTheory.volume G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ := by
  calc ∫⁻ x in G, T f x
    _ ≤ ∫⁻ x in G, CarlesonOperator K f x :=
      MeasureTheory.lintegral_mono (CarlesonOperatorReal_le_CarlesonOperator _)
    _ ≤ ENNReal.ofReal (C1_2 4 2) * (MeasureTheory.volume G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ := metric_carleson (a := 4) K (by norm_num) h1 h2 hF hG h3 f hf

end section
