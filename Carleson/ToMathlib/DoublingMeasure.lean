import Carleson.ToMathlib.CoverByBalls
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder

open MeasureTheory Measure NNReal ENNReal Metric Filter Topology TopologicalSpace
noncomputable section

section Doubling

/-- The blow-up factor of repeatedly increasing the size of balls. -/
def As (A : ℝ≥0) (s : ℝ) : ℝ≥0 := A ^ ⌈Real.logb 2 s⌉₊

lemma le_pow_natCeil_logb {b x : ℝ} (hb : 1 < b) (hx : 0 < x) :
    x ≤ b ^ ⌈Real.logb b x⌉₊ := by
  calc
    x = b ^ Real.logb b x := by rw [Real.rpow_logb (by linarith) hb.ne' hx]
    _ ≤ b ^ ⌈Real.logb b x⌉₊ := by
      rw [← Real.rpow_natCast]
      gcongr
      · exact hb.le
      apply Nat.le_ceil

end Doubling

namespace MeasureTheory

/-- A doubling measure is a measure on a metric space with the condition that doubling
the radius of a ball only increases the volume by a constant factor, independent of the ball. -/
class Measure.IsDoubling {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (A : outParam ℝ≥0) : Prop where
  measure_ball_two_le_same : ∀ (x : X) r, μ (ball x (2 * r)) ≤ A * μ (ball x r)
export IsDoubling (measure_ball_two_le_same)

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

lemma ball_subset_ball_of_le {x x' : X} {r r' : ℝ}
    (hr : dist x x' + r' ≤ r) : ball x' r' ⊆ ball x r := by
  rw [dist_comm, add_comm] at hr
  exact ball_subset_ball' hr

lemma dist_lt_of_not_disjoint_ball {x x' : X} {r r' : ℝ} (hd : ¬Disjoint (ball x r) (ball x' r')) :
    dist x x' < r + r' := by
  obtain ⟨y, dy₁, dy₂⟩ := Set.not_disjoint_iff.mp hd
  rw [mem_ball] at dy₁ dy₂
  calc
    _ ≤ dist y x + dist y x' := dist_triangle_left ..
    _ < _ := by gcongr

lemma eq_zero_of_isDoubling_zero [MeasurableSpace X] (μ : Measure X) [hμ : μ.IsDoubling 0] :
    μ = 0 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · exact eq_zero_of_isEmpty μ
  have M (r : ℝ) : μ (ball x r) = 0 := by
    have := hμ.measure_ball_two_le_same x (r / 2)
    simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at this
    convert this
    ring
  rw [← measure_univ_eq_zero, ← iUnion_ball_nat x]
  exact measure_iUnion_null_iff.mpr fun i ↦ M ↑i

variable {A : ℝ≥0} [MeasurableSpace X] {μ : Measure X} [μ.IsDoubling A]

variable (μ) in
lemma eq_zero_of_isDoubling_lt_one [ProperSpace X] [IsFiniteMeasureOnCompacts μ] (hA : A < 1) :
    μ = 0 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · simp [eq_zero_of_isEmpty μ]
  have M (r : ℝ) (hr : 0 ≤ r) : μ (ball x r) = 0 := by
    have I : μ (ball x r) ≤ A * μ (ball x r) := calc
      _ = μ (ball x (2 * (r / 2))) := by
        have : 2 * (r / 2) = r := by ring
        simp [this]
      _ ≤ A * μ (ball x (r / 2)) := by
        apply measure_ball_two_le_same (μ := μ)
      _ ≤ A * μ (ball x r) := by gcongr; linarith
    by_contra H
    have : μ (ball x r) < 1 * μ (ball x r) := by
      apply I.trans_lt (ENNReal.mul_lt_mul_right' H measure_ball_lt_top.ne (mod_cast hA))
    simp at this
  rw [← measure_univ_eq_zero, ← iUnion_ball_nat x]
  exact measure_iUnion_null_iff.mpr fun i ↦ M ↑i (Nat.cast_nonneg' i)

lemma IsDoubling.mono {A'} (h : A ≤ A') : IsDoubling μ A' where
  measure_ball_two_le_same := by
    intro x r
    calc μ (Metric.ball x (2 * r))
      _ ≤ A * μ (Metric.ball x r) := measure_ball_two_le_same _ _
      _ ≤ A' * μ (Metric.ball x r) := by gcongr

lemma measure_ball_two_le_same_iterate (x : X) (r : ℝ) (n : ℕ) :
    μ (ball x ((2 ^ n) * r)) ≤ A ^ n * μ (ball x r) := by
  induction n with
  | zero => simp
  | succ m ih =>
      simp_rw [add_comm m 1, pow_add, pow_one, mul_assoc]
      exact le_trans (measure_ball_two_le_same x _) (mul_le_mul_left' ih A)

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]

lemma measure_real_ball_two_le_same (x : X) (r : ℝ) :
    μ.real (ball x (2 * r)) ≤ A * μ.real (ball x r) := by
  simp_rw [Measure.real, ← ENNReal.coe_toReal, ← toReal_mul]
  gcongr
  · exact ENNReal.mul_ne_top coe_ne_top measure_ball_lt_top.ne
  · exact measure_ball_two_le_same x r

lemma measure_real_ball_two_le_same_iterate (x : X) (r : ℝ) (n : ℕ) :
    μ.real (ball x ((2 ^ n) * r)) ≤ A ^ n * μ.real (ball x r) := by
  induction n with
  | zero => simp
  | succ m ih =>
      simp_rw [add_comm m 1, pow_add, pow_one, mul_assoc]
      exact le_trans (measure_real_ball_two_le_same x _) (by gcongr)

lemma measure_real_ball_pos [μ.IsOpenPosMeasure] (x : X) {r : ℝ} (hr : 0 < r) :
    0 < μ.real (ball x r) :=
  toReal_pos ((measure_ball_pos μ x hr).ne.symm) (measure_ball_lt_top.ne)

variable (μ) in
lemma one_le_A [Nonempty X] [μ.IsOpenPosMeasure] : 1 ≤ A := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have : 0 < μ.real (ball x 1) := measure_real_ball_pos x (by linarith)
  apply le_of_mul_le_mul_right _ this
  simp only [val_eq_coe, NNReal.coe_one, one_mul]
  calc
    μ.real (ball x 1)
      ≤ μ.real (ball x (2 * 1)) := by
        rw [mul_one]
        exact ENNReal.toReal_mono (measure_ball_lt_top.ne)
          (μ.mono (ball_subset_ball (by linarith)))
    _ ≤ A * μ.real (ball x 1) := measure_real_ball_two_le_same x 1

variable (μ) in
lemma A_pos [Nonempty X] [μ.IsOpenPosMeasure] : 0 < A := by
  calc
    0 < 1 := by norm_num
    _ ≤ A := one_le_A μ

variable (μ) in
lemma A_pos' [Nonempty X] [μ.IsOpenPosMeasure] : 0 < (A : ℝ≥0∞) := by
  rw [ENNReal.coe_pos]
  exact A_pos μ

-- lemma measure_ball_two_le_same' (x:X) (r:ℝ): μ (ball x (2 * r)) ≤ A * μ (ball x r) := by
--   have hv1 : μ (ball x (2 * r)) < ⊤ := measure_ball_lt_top
--   have hv2 : μ (ball x r) < ⊤ := measure_ball_lt_top
--   rw [← ENNReal.ofReal_toReal hv1.ne, ← ENNReal.ofReal_toReal hv2.ne, ← ENNReal.ofReal_toReal
--     (coe_ne_top : (A : ℝ≥0∞) ≠ ⊤), ← ENNReal.ofReal_mul (by exact toReal_nonneg)]
--   exact ENNReal.ofReal_le_ofReal (measure_ball_two_le_same x r)

lemma measure_ball_four_le_same (x : X) (r : ℝ) :
    μ.real (ball x (4 * r)) ≤ A ^ 2 * μ.real (ball x r) := by
  calc μ.real (ball x (4 * r))
      = μ.real (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * μ.real (ball x (2 * r)) := measure_real_ball_two_le_same ..
    _ ≤ A * (A * μ.real (ball x r)) := mul_le_mul_of_nonneg_left
      (measure_real_ball_two_le_same ..) (zero_le_coe)
    _ = A ^ 2 * μ.real (ball x r) := by ring_nf

lemma measure_ball_ne_top (x : X) (r : ℝ) : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne

lemma measure_ball_four_le_same' (x : X) (r : ℝ) :
    μ (ball x (4 * r)) ≤ A ^ 2 * μ (ball x r) := by
  have hfactor : (A ^ 2 : ℝ≥0∞) ≠ ⊤ := ne_of_beq_false rfl
  rw [← ENNReal.ofReal_toReal (measure_ball_ne_top x (4 * r)),
    ← ENNReal.ofReal_toReal (measure_ball_ne_top x r), ← ENNReal.ofReal_toReal hfactor,
    ← ENNReal.ofReal_mul]
  · exact ENNReal.ofReal_le_ofReal <| measure_ball_four_le_same x r
  · simp

attribute [aesop (rule_sets := [finiteness]) safe apply] measure_ball_ne_top

variable (μ) in
lemma As_pos [Nonempty X] [μ.IsOpenPosMeasure] (s : ℝ) : 0 < As A s :=
  pow_pos (A_pos μ) ⌈Real.logb 2 s⌉₊

variable (μ) in
lemma As_pos' [Nonempty X] [μ.IsOpenPosMeasure] (s : ℝ) : 0 < (As A s : ℝ≥0∞) := by
  rw [ENNReal.coe_pos]; exact As_pos μ s

/- Proof sketch: First do for powers of 2 by induction, then use monotonicity. -/
omit [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
lemma measure_ball_le_same' (x : X) {r s r' : ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
    μ (ball x r') ≤ As A s * μ (ball x r) := by
  /-If the large ball is empty, then they all are-/
  if hr: r < 0 then
    have hr' : r' < 0 := by
      calc r' ≤ s * r := hs
      _ < 0 := mul_neg_of_pos_of_neg hsp hr
    rw [ball_eq_empty.mpr hr.le,ball_eq_empty.mpr hr'.le]
    simp only [measure_empty, mul_zero, le_refl]
  else
  push_neg at hr
  /- Show inclusion in larger ball -/
  have haux : s * r ≤ 2 ^ ⌈Real.logb 2 s⌉₊ * r := by
    gcongr
    apply le_pow_natCeil_logb (by norm_num) hsp
  have h1 : ball x r' ⊆ ball x (2 ^ ⌈Real.logb 2 s⌉₊ * r) :=
    ball_subset_ball <| hs.trans haux
  /- Apply result for power of two to slightly larger ball -/
  calc μ (ball x r')
      ≤ μ (ball x (2 ^ ⌈Real.logb 2 s⌉₊ * r)) := by gcongr
    _ ≤ As A s * μ (ball x r) := measure_ball_two_le_same_iterate x r _

lemma measure_ball_le_same (x : X) {r s r' : ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
    μ.real (ball x r') ≤ As A s * μ.real (ball x r) := by
  have hz := measure_ball_le_same' (μ := μ) x hsp hs
  have hbr': μ (ball x r') ≠ ⊤ := measure_ball_ne_top x r'
  have hbr: μ (ball x r) ≠ ⊤ := measure_ball_ne_top x r
  have hAs : (As A s: ℝ≥0∞) ≠ ⊤ := coe_ne_top
  rw [← ENNReal.ofReal_toReal hbr,← ENNReal.ofReal_toReal hbr',
    ← ENNReal.ofReal_toReal hAs, ← ENNReal.ofReal_mul] at hz
  · simp only [coe_toReal] at hz
    rw [← ENNReal.ofReal_le_ofReal_iff]
    · exact hz
    positivity
  · simp only [coe_toReal, zero_le_coe]

/-- Version of `measure_ball_le_same` without ceiling function. -/
lemma measure_ball_le_same'' (x : X) {r t : ℝ} (ht : 0 < t) (h't : t ≤ 1) :
    μ.real (ball x r) ≤ A * t ^ (- Real.logb 2 A) * μ.real (ball x (t * r)) := by
  rcases lt_or_le A 1 with hA | hA
  · simp [eq_zero_of_isDoubling_lt_one μ hA]
  have : r = t⁻¹ * (t * r) := (eq_inv_mul_iff_mul_eq₀ ht.ne').mpr rfl
  apply (measure_ball_le_same x (inv_pos_of_pos ht) this.le).trans
  gcongr
  simp only [As, Real.logb_inv, NNReal.coe_pow]
  have : t = 2 ^ (Real.logb 2 t) := by rw [Real.rpow_logb (by norm_num) (by norm_num) ht]
  conv_rhs => rw [this]
  have : (A : ℝ) = 2 ^ (Real.logb 2 (A : ℝ)) := by
    rw [Real.rpow_logb (by norm_num) (by norm_num)]
    apply zero_lt_one.trans_le hA
  nth_rewrite 1 2 [this]
  rw [← Real.rpow_mul zero_le_two, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
    ← Real.rpow_add zero_lt_two]
  apply (Real.rpow_le_rpow_left_iff one_lt_two).2
  have : (⌈-Real.logb 2 t⌉₊ : ℝ) < -Real.logb 2 t + 1 := by
    apply Nat.ceil_lt_add_one
    simp only [Left.nonneg_neg_iff]
    rw [Real.logb_nonpos_iff one_lt_two ht]
    exact h't
  calc
  Real.logb 2 ↑A * ↑⌈-Real.logb 2 t⌉₊
  _ ≤ Real.logb 2 ↑A * (-Real.logb 2 t + 1) := by
    gcongr
    exact Real.logb_nonneg one_lt_two hA
  _ = _ := by ring

omit [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
lemma measure_ball_le_of_dist_le' {x x' : X} {r r' s : ℝ} (hs : 0 < s)
    (h : dist x x' + r' ≤ s * r) :
    μ (ball x' r') ≤ As A s * μ (ball x r) := by
  calc
    μ (ball x' r')
      ≤ μ (ball x (dist x x' + r')) := by gcongr; exact ball_subset_ball_of_le le_rfl
    _ ≤ As A s * μ (ball x r) := measure_ball_le_same' x hs h

lemma measureNNReal_ball_le_of_dist_le' {x x' : X} {r r' s : ℝ} (hs : 0 < s)
    (h : dist x x' + r' ≤ s * r) :
    (μ (ball x' r')).toNNReal ≤ As A s * (μ (ball x r)).toNNReal := by
  simp only [← ENNReal.coe_le_coe, coe_mul, ENNReal.coe_toNNReal
    (measure_ball_ne_top x r), ENNReal.coe_toNNReal (measure_ball_ne_top x' r')]
  exact measure_ball_le_of_dist_le' hs h

section

variable {x x': X} {r r' s d : ℝ} (hs : 0 < s)

-- #check (@measure_ball_le_of_dist_le X A _ _ x' x r (2 * r) s s hs hs)

end
/-
-- def Ai (A : ℝ≥0) (s : ℝ) : ℝ≥0 := As A s -- maybe wrong

-- lemma measure_ball_le_of_subset {x' x : X} {r r' s : ℝ}
--     (hs : r' ≤ s * r) (hr : ball x' r ⊆ ball x r') :
--     μ.real (ball x (2 * r)) ≤ Ai A s * μ.real (ball x' r) := by sorry

-- def Ai2 (A : ℝ≥0) : ℝ≥0 := Ai A 2

-- lemma measure_ball_two_le_of_subset {x' x : X} {r : ℝ} (hr : ball x' r ⊆ ball x (2 * r)) :
--     μ.real (ball x (2 * r)) ≤ Ai2 A * μ.real (ball x' r) :=
--   measure_ball_le_of_subset le_rfl hr

-- def Np (A : ℝ≥0) (s : ℝ) : ℕ := ⌊As A (s * A + 2⁻¹)⌋₊ -- probably wrong

-- /- Proof sketch: take a ball of radius `r / (2 * A)` around each point in `s`.
-- These are disjoint, and are subsets of `ball x (r * (2 * A + 2⁻¹))`. -/
-- lemma card_le_of_le_dist (x : X) {r r' s : ℝ} (P : Set X) (hs : r' ≤ s * r) (hP : P ⊆ ball x r')
--   (h2P : ∀ x y, x ∈ P → y ∈ P → x ≠ y → r ≤ dist x y) : P.Finite ∧ Nat.card P ≤ Np A s := by sorry

-- /- Proof sketch: take any maximal set `s` of points that are at least distance `r` apart.
-- By the previous lemma, you only need a bounded number of points.
-- -/
-- lemma ballsCoverBalls {r r' s : ℝ} (hs : r' ≤ s * r) : BallsCoverBalls X r' r (Np A s) := by
--   sorry

-- /- [Stein, 1.1.3(iv)] -/
-- lemma continuous_measure_ball_inter {U : Set X} (hU : IsOpen U) {δ} (hδ : 0 < δ) :
--   Continuous fun x ↦ μ.real (ball x δ ∩ U) := sorry

-- /- [Stein, 1.1.4] -/
-- lemma continuous_average {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X → E}
--     (hf : LocallyIntegrable f μ) {δ : ℝ} (hδ : 0 < δ) :
--     Continuous (fun x ↦ ⨍ y in ball x δ, f y ∂μ) :=
--   sorry

-- /- [Stein, 1.3.1], cor -/
-- lemma tendsto_average_zero {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X → E}
--     (hf : LocallyIntegrable f μ) {x : X} :
--     Tendsto (fun δ ↦ ⨍ y in ball x δ, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) :=
--   sorry
-/

end PseudoMetric

section Metric

variable {X : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsDoubling A] [IsFiniteMeasureOnCompacts μ] [ProperSpace X]
  [Nonempty X] [IsOpenPosMeasure μ] -- only needed sometimes

instance : IsUnifLocDoublingMeasure (μ : Measure X) where
  exists_measure_closedBall_le_mul'' := by
    use A^2, Set.univ, by simp only [univ_mem]
    simp only [mem_principal]
    use Set.univ
    simp only [Set.subset_univ, Set.inter_self, true_and]
    ext r
    simp only [ENNReal.coe_pow, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro x
    letI : Nonempty X := ⟨x⟩
    if hr : r ≤ 0 then
      have cball_eq : closedBall x (2 * r) = closedBall x r:= by
        if hr' : r < 0 then
          have : 2 * r < 0 := by linarith
          rw [closedBall_eq_empty.mpr hr',closedBall_eq_empty.mpr this]
        else
          push_neg at hr'
          have : r = 0 := le_antisymm hr hr'
          rw [this]
          simp only [mul_zero, closedBall_zero]
      rw [cball_eq]
      nth_rw 1 [← one_mul (μ (closedBall x r))]
      gcongr
      have : 1 ≤ (A:ℝ≥0∞) := by rw [one_le_coe_iff]; exact one_le_A μ
      rw [← one_mul 1, pow_two]
      gcongr
    else
    calc
      μ (closedBall x (2 * r))
        ≤ μ (ball x (2 * (2 * r))) := μ.mono (closedBall_subset_ball (by linarith))
      _ ≤ A * μ (ball x (2 * r)) := measure_ball_two_le_same x (2 * r)
      _ ≤ A * (A * μ (ball x r)) := mul_le_mul_of_nonneg_left
        (measure_ball_two_le_same x r) (zero_le _)
      _ = ↑(A ^ 2) * μ (ball x r) := by simp only [pow_two, coe_mul,mul_assoc]
      _ ≤ ↑(A ^ 2) * μ (closedBall x r) := mul_le_mul_of_nonneg_left
        (μ.mono ball_subset_closedBall) (zero_le ((A ^ 2 : ℝ≥0) : ℝ≥0∞))
end Metric

section Normed

open Module ENNReal

lemma Subsingleton.ball_eq {α} [PseudoMetricSpace α] [Subsingleton α] {x : α} {r : ℝ} :
    ball x r = if r > 0 then {x} else ∅ := by
  ext y; cases Subsingleton.elim x y; simp

instance InnerProductSpace.IsDoubling {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    IsDoubling (volume : Measure E) (2 ^ finrank ℝ E) where
  measure_ball_two_le_same x r := by
    obtain hE|hE := subsingleton_or_nontrivial E
    · simp_rw [Subsingleton.ball_eq, finrank_zero_of_subsingleton]; simp
    simp_rw [InnerProductSpace.volume_ball, ofReal_mul zero_le_two, ← ENNReal.rpow_natCast,
      ENNReal.mul_rpow_of_ne_top ofReal_ne_top ofReal_ne_top, ENNReal.rpow_natCast, mul_assoc]
    simp

end Normed

/- # Instances of spaces of homogeneous type -/

/-- A metric space with a measure and a doubling condition.
This is called a "doubling metric measure space" in the blueprint.
`A` will usually be `2 ^ a`.

This class is not Mathlib-ready code, and results moved to Mathlib should be reformulated using
a (locally) doubling measure and more minimal other classes.

Note (F): we currently assume that the space is proper, which we should probably add to the
blueprint.
Remark: `IsUnifLocDoublingMeasure` which is a weaker notion in Mathlib. -/

class DoublingMeasure (X : Type*) (A : outParam ℝ≥0) [PseudoMetricSpace X] extends
  MeasureSpace X, ProperSpace X, BorelSpace X,
  Regular (volume : Measure X), IsOpenPosMeasure (volume : Measure X),
  IsDoubling (volume : Measure X) A

variable {X : Type*} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

-- the following classes hold
-- #synth ProperSpace X
-- #synth LocallyCompactSpace X
-- #synth CompleteSpace X
-- #synth SigmaCompactSpace X
-- #synth SigmaFinite (volume : Measure X)
-- #synth SecondCountableTopology X
-- #synth SeparableSpace X


section MetricSpace
variable {Y : Type*} [MetricSpace Y] [DoublingMeasure Y A]
-- Moreover, the following classes hold if we assume that `Y` is a metric space
-- #synth T4Space Y
-- #synth PolishSpace Y
-- #synth MeasurableSingletonClass Y
end MetricSpace


/-- Monotonicity of doubling measure metric spaces in `A`. -/
@[reducible]
def DoublingMeasure.mono {A'} (h : A ≤ A') : DoublingMeasure X A' where
  toIsDoubling := IsDoubling.mono h
  __ := ‹DoublingMeasure X A›

open Module
/- Preferably we prove that in this form. -/
instance InnerProductSpace.DoublingMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    DoublingMeasure E (2 ^ finrank ℝ E) where

/- todo: ℝ^n with nonstandard metric: `dist x y = ∑ i, |x i - y i| ^ α i` for `α i > 0` -/
end MeasureTheory
