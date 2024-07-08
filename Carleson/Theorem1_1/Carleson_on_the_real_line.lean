/- This file contains the proof of Lemma 10.4, from section 10.7-/

import Carleson.MetricCarleson
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Hilbert_kernel
import Carleson.Theorem1_1.CarlesonOperatorReal

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
        --convert this
        sorry
        --exact this.volume_ball_two_le_same x r

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
          _ ≤ |(n - m) * (z.1 - x)| + |(n - m) * (z.2 - x)| := by apply abs_sub
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
  metric := fun x R ↦ sorry

lemma coeΘ_R (n : Θ ℝ) (x : ℝ) : n x = n * x := rfl
lemma coeΘ_R_C (n : Θ ℝ) (x : ℝ) : (n x : ℂ) = n * x := by norm_cast

instance h4 : CompatibleFunctions ℝ ℝ (2 ^ 4 : ℕ) where
  eq_zero := sorry
  localOscillation_le_cdist := sorry
  cdist_mono := sorry
  cdist_le := sorry
  le_cdist := sorry
  ballsCoverBalls := sorry
/-
  /- Lemma frequency_ball_doubling from the paper. -/
  localOscillation_two_mul_le := by
    intro x₁ x₂ R f g hf hg _
    /-TODO: move case split to standard definition? -/
    by_cases Rpos : 0 ≥ R
    · rw [localOscillation_on_empty_ball (by linarith), localOscillation_on_empty_ball Rpos]
      simp
    push_neg at Rpos
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg, localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    gcongr
    norm_num
    exact Rpos.le
    linarith
  /- Lemma frequency_ball_growth from the paper. -/
  localOscillation_le_of_subset := by
    intro x₁ x₂ R f g hf hg _ _
    by_cases Rpos : 0 ≥ R
    · rw [localOscillation_on_empty_ball Rpos, localOscillation_on_empty_ball (by linarith)]
      simp
    push_neg at Rpos
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg]
    rw [localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    gcongr
    norm_num
    linarith
    exact Rpos.le
  /- Lemma integer_ball_cover from the paper. -/
  ballsCoverBalls := by
    intro x R R' f hf
    rw [coveredByBalls_iff]
    by_cases R'pos : 0 ≥ R'
    · --trivial case
      use {f}
      constructor
      · simp
      simp
      rw [Metric.ball_eq_empty.mpr R'pos, Set.subset_empty_iff]
      convert Set.empty_inter _
      rw [Metric.ball_eq_empty]
      linarith
    push_neg at R'pos
    by_cases Rpos : 0 ≥ R
    · --trivial case
      use {f}
      constructor
      · simp

      convert Set.subset_univ _
      ext g
      constructor
      · simp
      simp
      calc localOscillation (Metric.ball x R) g f
        _ = 0 := by
          apply localOscillation_on_empty_ball Rpos.le
        _ < R' := R'pos
    push_neg at Rpos
    obtain ⟨n, hθnf⟩ := hf
    rw [←hθnf]
    set m₁ := Int.floor (n - R' / (2 * R)) with m₁def
    set! m₂ := n with m₂def
    set m₃ := Int.ceil (n + R' / (2 * R)) with m₃def

    /- The following is necessary for withLocalOscillation to be defined. -/
    classical
    set balls : Finset (C(ℝ, ℂ)) := {θ m₁, θ m₂, θ m₃} with balls_def
    use balls
    constructor
    · rw [balls_def]
      apply Nat.le_floor
      norm_cast
      apply le_trans Finset.card_le_three
      norm_num
    intro φ ⟨hφ, φ_memΘ⟩
    obtain ⟨n', hn'⟩ := φ_memΘ
    rw [←hn'] at hφ
    simp at hφ
    rw [dist_comm] at hφ
    /- m₁, m₂, m₃ each correspond to one case. -/
    rw [←hn']
    simp
    by_cases h : n' ≤ n - R' / (2 * R)
    · use θ m₁
      constructor
      · rw [balls_def]
        simp
      calc localOscillation (Metric.ball x R) (θ n') (θ m₁)
        _ = 2 * R * |(n' : ℝ) - m₁| := localOscillation_of_integer_linear Rpos.le _ _
        _ = 2 * R * (m₁ - n') := by
          rw [abs_of_nonpos]
          simp only [neg_sub]
          simp only [tsub_le_iff_right, zero_add, Int.cast_le]
          rwa [m₁def, Int.le_floor]
        _ = 2 * R * (m₁ - n) + 2 * R * (n - n') := by ring
        _ < - R' + 2 * R' := by
          apply add_lt_add_of_le_of_lt
          · rw [m₁def]
            calc 2 * R * (⌊n - R' / (2 * R)⌋ - n)
              _ ≤ 2 * R * (n - R' / (2 * R) - n) := by
                gcongr
                apply Int.floor_le
              _ = -R' := by
                ring_nf
                rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
          · calc 2 * R * (↑n - ↑n')
              _ ≤ 2 * R * |↑n - ↑n'| := by
                gcongr
                apply le_abs_self
              _ = localOscillation (Metric.ball x R) (θ n) (θ n') := by
                symm
                apply localOscillation_of_integer_linear Rpos.le
              _ < 2 * R' := hφ
        _ = R' := by ring
    push_neg at h
    by_cases h' : n' < n + R' / (2 * R)
    · use θ m₂
      constructor
      · rw [balls_def]
        simp
      rw [m₂def, dist_comm]
      calc localOscillation (Metric.ball x R) (θ n) (θ n')
        _ = 2 * R * |(n : ℝ) - n'| := localOscillation_of_integer_linear Rpos.le _ _
        _ < 2 * R * (R' / (2 * R)) := by
          gcongr
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        _ = R' := by field_simp
    push_neg at h'
    use θ m₃
    constructor
    · simp [balls_def]
    calc localOscillation (Metric.ball x R) (θ n') (θ m₃)
      _ = 2 * R * |(n' : ℝ) - m₃| := by
        apply localOscillation_of_integer_linear Rpos.le
      _ = 2 * R * (n' - m₃) := by
        rw [abs_of_nonneg]
        simp
        rwa [m₃def, Int.ceil_le]
      _ = 2 * R * (n' - n) + 2 * R * (n - m₃) := by ring
      _ < 2 * R' - R' := by
        apply add_lt_add_of_lt_of_le
        · calc 2 * R * (↑n' - ↑n)
            _ ≤ 2 * R * |↑n' - ↑n| := by
              gcongr
              exact le_abs_self _
            _ = 2 * R * |↑n - ↑n'| := by
              congr 1
              exact abs_sub_comm _ _
            _ = localOscillation (Metric.ball x R) (θ n) (θ n') := by
              symm
              exact localOscillation_of_integer_linear Rpos.le _ _
            _ < 2 * R' := by exact hφ
        · rw [m₃def]
          calc 2 * R * (n - ⌈n + R' / (2 * R)⌉)
            _ ≤ 2 * R * (n - (n + R' / (2 * R))) := by
              gcongr
              exact Int.le_ceil _
            _ = -R' := by
              ring_nf
              rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
      _ = R' := by ring -/



--TODO : What is Lemma 10.34 (frequency ball growth) needed for?

--TODO : possibly issues with a different "doubling constant" than in the paper (4 instead of 2)
instance h5 : IsCancellative ℝ (2 ^ (4 : ℕ)) where
  /- Lemma 10.36 (real van der Corput) from the paper. -/
  norm_integral_exp_le := by sorry

--TODO : add some Real.vol lemma

instance h6 : IsCZKernel 4 K where
  /- uses Hilbert_kernel_bound -/
  norm_le_vol_inv := by
    intro x y
    rw [Complex.norm_eq_abs, Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
    calc Complex.abs (K x y)
    _ ≤ 2 ^ (2 : ℝ) / (2 * |x - y|) := Hilbert_kernel_bound
    _ ≤ 2 ^ (4 : ℝ) ^ 3 / (2 * |x - y|) := by gcongr <;> norm_num
  /- uses Hilbert_kernel_regularity -/
  norm_sub_le := by
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
  measurable_right := by
    apply Measurable.of_uncurry_right
    exact Hilbert_kernel_measurable
  /- Lemma ?-/
  measurable := Hilbert_kernel_measurable

/- Lemma ?-/
lemma h3 : HasBoundedStrongType (ANCZOperator K) 2 2 volume volume (C_Ts 4) := sorry



-- #check @metric_carleson
--#check metric_carleson K (by simp) h1 h2 _ _ h3

local notation "T" => CarlesonOperatorReal K
local notation "T'" => CarlesonOperatorReal' K

/-Not sure whether this is actually true. Probably we only have "le" (which should suffice). -/
--TODO : change name to reflect that this only holds for a specific instance of CarlesonOperaterReal?
lemma CarlesonOperatorReal'_le_CarlesonOperator : T' ≤ CarlesonOperator K := by
  intro f x
  rw [CarlesonOperator, CarlesonOperatorReal']
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
lemma rcarleson' {F G : Set ℝ}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    --(h2F : MeasureTheory.volume F ≠ ∞) (h2G : MeasureTheory.volume G ≠ ∞)
    (f : ℝ → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    :
    ∫⁻ x in G, T' f x ≤
    ENNReal.ofReal (C1_2 4 2) * (MeasureTheory.volume G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ := by
  --rw [CarlesonOperatorReal_eq_CarlesonOperator]
  calc ∫⁻ x in G, T' f x
    _ ≤ ∫⁻ x in G, CarlesonOperator K f x :=
      MeasureTheory.lintegral_mono (CarlesonOperatorReal'_le_CarlesonOperator _)
    _ ≤ ENNReal.ofReal (C1_2 4 2) * (MeasureTheory.volume G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ := metric_carleson (a := 4) K (by norm_num) h1 h2 hF hG h3 f hf

end section
