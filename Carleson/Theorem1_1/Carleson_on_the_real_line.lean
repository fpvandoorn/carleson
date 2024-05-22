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

lemma localOscillation_on_emptyset {X : Type} [PseudoMetricSpace X] {f g : C(X, ℂ)} : localOscillation ∅ f g = 0 := by
  rw [localOscillation]
  simp

lemma localOscillation_on_empty_ball {X : Type} [PseudoMetricSpace X] {x : X} {f g : C(X, ℂ)} {R : ℝ} (R_nonpos : R ≤ 0):
    localOscillation (Metric.ball x R) f g = 0 := by
  convert localOscillation_on_emptyset
  exact Metric.ball_eq_empty.mpr R_nonpos

lemma ConditionallyCompleteLattice.le_biSup {α : Type} [ConditionallyCompleteLinearOrder α] {ι : Type} [Nonempty ι]
    {f : ι → α} {s : Set ι} {a : α} (hfs : BddAbove (f '' s)) (ha : ∃ i ∈ s, f i = a) :
    a ≤ ⨆ i ∈ s, f i := by
  apply ConditionallyCompleteLattice.le_csSup
  . --TODO: improve this
    rw [bddAbove_def] at *
    rcases hfs with ⟨x, hx⟩
    use (max x (sSup ∅))
    intro y hy
    simp at hy
    rcases hy with ⟨z, hz⟩
    rw [iSup] at hz
    by_cases h : z ∈ s
    . have : (@Set.range α (z ∈ s) fun _ ↦ f z) = {f z} := by
        rw [Set.eq_singleton_iff_unique_mem]
        constructor
        . simpa
        . intro x hx
          simp at hx
          exact hx.2.symm
      rw [this] at hz
      have : sSup {f z} = f z := by apply csSup_singleton
      rw [this] at hz
      simp at hx
      have : f z ≤ x := hx z h
      rw [hz] at this
      apply le_max_of_le_left this
    have : (@Set.range α (z ∈ s) fun _ ↦ f z) = ∅ := by
      simpa
    rw [this] at hz
    rw [hz]
    exact le_max_right x y
  rw [Set.mem_range]
  rcases ha with ⟨i, hi, fia⟩
  use i
  rw [iSup]
  convert csSup_singleton _
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  . simp
    use hi, fia
  . intro x hx
    simp at hx
    rwa [hx.2] at fia


--mainly have to work for the following lemmas

/-Stronger version of oscillation_control from the paper-/
/-Based on earlier version of the paper. -/
lemma localOscillation_of_integer_linear {x R : ℝ} (R_nonneg : 0 ≤ R) : ∀ n m : ℤ, localOscillation (Metric.ball x R) (θ n) (θ m) = 2 * R * |(n : ℝ) - m| := by
  intro n m
  by_cases n_ne_m : n = m
  . sorry
  push_neg at n_ne_m
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
  . apply le_of_forall_lt
    intro c hc
    set R' := (c + 2 * |(n : ℝ) - m|) / (4 * |(n : ℝ) - m|) with R'def

    set y := (x - R', x + R') with ydef
    --TODO: seems like we do not use the right theorem here...
    --apply le_iSup
    --apply le_iSup_iff.2
    --rw [le_ciSup_iff']
    --apply lt_ciSup
    calc c
      _ < 2 * R' * |↑n - ↑m| := by
        rw [R'def]
        sorry
      _ ≤ ‖(↑n - ↑m) * (y.1 - x) - (↑n - ↑m) * (y.2 - x)‖ := by
        simp
        rw [sub_eq_add_neg (-((n - m) * R')), ←neg_add, abs_neg, ←two_mul, abs_mul, abs_mul, mul_comm |(n : ℝ) - m|, mul_assoc]
        simp
        gcongr
        apply le_abs_self
      _ ≤ ⨆ z ∈ Metric.ball x R ×ˢ Metric.ball x R, ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
        apply ConditionallyCompleteLattice.le_biSup
        . --apply bddAbove_localOscillation
          sorry
        . use y
          simp
          sorry


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

--TODO: probably not needed any more
lemma bciSup_of_emptyset  {α : Type} [ConditionallyCompleteLattice α] {ι : Type} [Nonempty ι] {f : ι → α} :
    ⨆ i ∈ (∅ : Set ι), f i = sSup ∅ := by
  rw [iSup]
  convert csSup_singleton _
  have : ∀ i : ι, IsEmpty (i ∈ ∅) := by
    intro i
    simp
    apply Set.not_mem_empty
  have : (fun (i : ι) ↦ ⨆ (_ : i ∈ (∅ : Set ι)), f i) = fun i ↦ sSup ∅ := by
    ext i
    --rw [csSup_empty]
    rw [iSup]
    congr
    rw [Set.range_eq_empty_iff]
    simp
  rw [this]
  apply Set.range_const

--lemma frequency_ball_doubling {x R : ℝ} (Rpos : 0 < R) :

instance h4 : IsCompatible Θ where
  /- Lemma frequency_ball_doubling from the paper. -/
  localOscillation_two_mul_le := by
    intro x₁ x₂ R f g hf hg _
    /-TODO: move case split to standard definition? -/
    by_cases Rpos : 0 ≥ R
    . rw [localOscillation_on_empty_ball (by linarith), localOscillation_on_empty_ball Rpos]
      simp
    push_neg at Rpos
    obtain ⟨n, hθnf⟩ := hf
    obtain ⟨m, hθmg⟩ := hg
    rw [←hθnf, ←hθmg]
    rw [localOscillation_of_integer_linear, localOscillation_of_integer_linear]
    ring_nf
    gcongr
    norm_num
    exact Rpos.le
    linarith
  /- Lemma frequency_ball_growth from the paper. -/
  localOscillation_le_of_subset := by
    intro x₁ x₂ R f g hf hg _ _
    by_cases Rpos : 0 ≥ R
    . rw [localOscillation_on_empty_ball Rpos, localOscillation_on_empty_ball (by linarith)]
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
    . --trivial case
      use {f}
      constructor
      . simp
      simp
      rw [Metric.ball_eq_empty.mpr R'pos, Set.subset_empty_iff]
      convert Set.empty_inter _
      rw [Metric.ball_eq_empty]
      linarith
    push_neg at R'pos
    by_cases Rpos : 0 ≥ R
    . --trivial case
      use {f}
      constructor
      . simp
      simp
      convert Set.subset_univ _
      ext g
      constructor
      . simp
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
    intro φ ⟨hφ, φ_memΘ⟩
    obtain ⟨n', hn'⟩ := φ_memΘ
    rw [←hn'] at hφ
    simp at hφ
    rw [dist_comm] at hφ
    --rw [localOscillation_of_integer_linear] at hφ
    /- m₁, m₂, m₃ each correspond to one case. -/
    rw [←hn']
    simp
    by_cases h : n' ≤ n - R' / (2 * R)
    . use θ m₁
      constructor
      . rw [balls_def]
        simp
      calc localOscillation (Metric.ball x R) (θ n') (θ m₁)
        _ = 2 * R * |(n' : ℝ) - m₁| := by
          apply localOscillation_of_integer_linear Rpos.le
        _ = 2 * R * (m₁ - n') := by
          rw [abs_of_nonpos]
          simp
          simp
          rwa [m₁def, Int.le_floor]
        _ = 2 * R * (m₁ - n) + 2 * R * (n - n') := by ring
        _ < - R' + 2 * R' := by
          apply add_lt_add_of_le_of_lt
          . rw [m₁def]
            calc 2 * R * (⌊n - R' / (2 * R)⌋ - n)
              _ ≤ 2 * R * (n - R' / (2 * R) - n) := by
                gcongr
                apply Int.floor_le
              _ = -R' := by
                ring_nf
                rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
          . calc 2 * R * (↑n - ↑n')
              _ ≤ 2 * R * |↑n - ↑n'| := by
                gcongr
                apply le_abs_self
              _ = localOscillation (Metric.ball x R) (θ n) (θ n') := by
                symm
                apply localOscillation_of_integer_linear Rpos.le
              _ < 2 * R' := by exact hφ
        _ = R' := by ring
    push_neg at h
    by_cases h' : n' < n + R' / (2 * R)
    . use θ m₂
      constructor
      . rw [balls_def]
        simp
      rw [m₂def, dist_comm]
      calc localOscillation (Metric.ball x R) (θ n) (θ n')
        _ = 2 * R * |(n : ℝ) - n'| := by apply localOscillation_of_integer_linear Rpos.le
        _ < 2 * R * (R' / (2 * R)) := by
          gcongr
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        _ = R' := by field_simp
    push_neg at h'
    use θ m₃
    constructor
    . rw [balls_def]
      simp
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
        . calc 2 * R * (↑n' - ↑n)
            _ ≤ 2 * R * |↑n' - ↑n| := by
              gcongr
              apply le_abs_self
            _ = 2 * R * |↑n - ↑n'| := by
              congr 1
              apply abs_sub_comm
            _ = localOscillation (Metric.ball x R) (θ n) (θ n') := by
              symm
              apply localOscillation_of_integer_linear Rpos.le
            _ < 2 * R' := by exact hφ
        . rw [m₃def]
          calc 2 * R * (n - ⌈n + R' / (2 * R)⌉)
            _ ≤ 2 * R * (n - (n + R' / (2 * R))) := by
              gcongr
              apply Int.le_ceil
            _ = -R' := by
              ring_nf
              rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
      _ = R' := by ring



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
    ∫ x in G, T f x ≤
    C1_2 4 2 * (MeasureTheory.volume.real G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real F) ^ (2 : ℝ)⁻¹ := by
  rw [CarlesonOperatorReal_eq_CarlesonOperator]
  --WARNING : theorem1_2C does not yet require all necessary implicit parameters since no proof using them has been provided yet.
  convert theorem1_2C K (by simp) h1 h2 hF hG h3 f hf <;> sorry


end section
