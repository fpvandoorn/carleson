import Carleson.CoverByBalls
import Carleson.ToMathlib.Misc
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Constructions.Polish

open MeasureTheory Measure NNReal ENNReal Metric Filter Topology TopologicalSpace
noncomputable section

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
  Regular (volume : Measure X), IsOpenPosMeasure (volume : Measure X) where
  volume_ball_two_le_same : ∀ (x : X) r, volume.real (ball x (2 * r)) ≤ A * volume.real (ball x r)

export DoublingMeasure (volume_ball_two_le_same)

variable {X : Type*} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]


-- the following classes hold
#synth ProperSpace X
#synth LocallyCompactSpace X
#synth CompleteSpace X
#synth SigmaCompactSpace X
#synth SigmaFinite (volume : Measure X)
#synth SecondCountableTopology X
#synth SeparableSpace X


section MetricSpace
variable {Y : Type*} [MetricSpace Y] [DoublingMeasure Y A]
-- Moreover, the following classes hold if we assume that `Y` is a metric space
#synth T4Space Y
#synth PolishSpace Y
#synth MeasurableSingletonClass Y
end MetricSpace

lemma coe_volume_ball_pos_of_pos_radius (x :X) {r : ℝ} (hr : 0 < r) : 0 < volume.real (ball x r) :=
  toReal_pos ((measure_ball_pos volume x hr).ne.symm) (measure_ball_lt_top.ne)

variable (X) in
lemma one_le_A [Nonempty X]: 1 ≤ A := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have : 0 < volume.real (ball x 1) := coe_volume_ball_pos_of_pos_radius x (by linarith)
  apply le_of_mul_le_mul_right _ this
  simp only [val_eq_coe, NNReal.coe_one, one_mul]
  calc
    volume.real (ball x 1)
      ≤ volume.real (ball x (2 * 1)) := by
        rw [mul_one]
        exact ENNReal.toReal_mono (measure_ball_lt_top.ne)
          (volume.mono (ball_subset_ball (by linarith)))
    _ ≤ A * volume.real (ball x 1) := volume_ball_two_le_same x 1

variable (X) in lemma A_nonneg [DoublingMeasure X A]: 0 ≤ (A : ℝ≥0∞) := zero_le (A : ℝ≥0∞)
variable (X) in lemma A_pos [Nonempty X] : 0 < A := by
  calc
    0 < 1 := by norm_num
    _ ≤ A := one_le_A X

variable (X) in lemma A_pos' [Nonempty X] : 0 < (A : ℝ≥0∞) := by
  rw [ENNReal.coe_pos]
  exact A_pos X

lemma volume_ball_two_le_same' (x:X) (r:ℝ): volume (ball x (2 * r)) ≤ A * volume (ball x r) := by
  have hv1 : volume (ball x (2 * r)) < ⊤ := measure_ball_lt_top
  have hv2 : volume (ball x r) < ⊤ := measure_ball_lt_top
  rw [← ENNReal.ofReal_toReal hv1.ne, ← ENNReal.ofReal_toReal hv2.ne, ← ENNReal.ofReal_toReal
    (coe_ne_top : (A : ℝ≥0∞) ≠ ⊤), ← ENNReal.ofReal_mul (by exact toReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal (volume_ball_two_le_same x r)

@[reducible]
def DoublingMeasure.mono {A'} (h : A ≤ A') : DoublingMeasure X A' where
  volume_ball_two_le_same := by
    intro x r
    calc MeasureTheory.volume.real (Metric.ball x (2 * r))
    _ ≤ A * MeasureTheory.volume.real (Metric.ball x r) := volume_ball_two_le_same _ _
    _ ≤ A' * MeasureTheory.volume.real (Metric.ball x r) := by gcongr

lemma volume_ball_four_le_same (x : X) (r : ℝ) :
    volume.real (ball x (4 * r)) ≤ A ^ 2 * volume.real (ball x r) := by
  have : Nonempty X := ⟨x⟩
  calc volume.real (ball x (4 * r))
      = volume.real (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * volume.real (ball x (2 * r)) := volume_ball_two_le_same _ _
    _ ≤ A * (A * volume.real (ball x r)) := mul_le_mul_of_nonneg_left
      (volume_ball_two_le_same _ _) (zero_le_coe)
    _ = A ^ 2 * volume.real (ball x r) := by ring_nf


lemma measure_ball_ne_top (x : X) (r : ℝ) : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne

attribute [aesop (rule_sets := [Finiteness]) safe apply] measure_ball_ne_top

lemma volume_ball_le_pow_two {x : X} {r : ℝ} {n : ℕ} :
    volume.real (ball x (2 ^ n * r)) ≤ A ^ n * volume.real (ball x r) := by
  have : Nonempty X := ⟨x⟩
  induction n
  case zero => simp
  case succ m hm =>
    calc volume.real (ball x (2 ^ (m.succ) * r))
        = volume.real (ball x (2 ^ (m+1) * r)) := rfl
      _ = volume.real (ball x ((2 ^ m*2^1) * r)) := by norm_cast
      _ = volume.real (ball x (2 * 2 ^ m * r)) := by ring_nf
      _ ≤ A * volume.real (ball x (2 ^ m * r)) := by
        rw[mul_assoc]; norm_cast; exact volume_ball_two_le_same _ _
      _ ≤ A * (↑(A ^ m) * volume.real (ball x r)) := by
        exact mul_le_mul_of_nonneg_left hm (by exact zero_le_coe)
      _ = A^(m.succ) * volume.real (ball x r) := by rw [NNReal.coe_pow,← mul_assoc, pow_succ']

lemma volume_ball_le_pow_two' {x:X} {r:ℝ} {n : ℕ} :
    volume (ball x (2 ^ n * r)) ≤ A ^ n * volume (ball x r) := by
  letI : Nonempty X := ⟨x⟩
  have hleft : volume (ball x (2 ^ n * r)) ≠ ⊤ := measure_ball_ne_top x (2 ^ n * r)
  have hright : volume (ball x r) ≠ ⊤ := measure_ball_ne_top x r
  have hfactor : (A ^n : ℝ≥0∞) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)
  rw [← ENNReal.ofReal_toReal hleft,← ENNReal.ofReal_toReal hright,← ENNReal.ofReal_toReal hfactor,
    ← ENNReal.ofReal_mul]
  · exact ENNReal.ofReal_le_ofReal volume_ball_le_pow_two
  simp only [toReal_pow, coe_toReal, ge_iff_le, zero_le_coe, pow_nonneg]

def As (A : ℝ≥0) (s : ℝ) : ℝ≥0 := A ^ ⌈Real.logb 2 s⌉₊

variable (X) in
lemma As_pos [Nonempty X] (s:ℝ) : 0 < As A s := pow_pos (A_pos X) ⌈Real.logb 2 s⌉₊

variable (X) in
lemma As_pos' [Nonempty X] (s:ℝ) : 0 < (As A s : ℝ≥0∞) := by
  rw [ENNReal.coe_pos]
  exact As_pos X s

/- Proof sketch: First do for powers of 2 by induction, then use monotonicity. -/
lemma volume_ball_le_same' (x : X) {r s r': ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
    volume (ball x r') ≤ As A s * volume (ball x r) := by
  /-If the large ball is empty, then they all are-/
  if hr: r < 0 then
    have hr' : r' < 0 := by
      calc r' ≤ s * r := hs
      _ < 0 := mul_neg_of_pos_of_neg hsp hr
    rw [ball_eq_empty.mpr hr.le,ball_eq_empty.mpr hr'.le]
    simp only [measure_empty, mul_zero, le_refl]
  else
  push_neg at hr
  /-Show inclusion in larger ball-/
  have haux : s * r ≤ 2 ^ ⌈Real.log s / Real.log 2⌉₊ * r := by
    apply mul_le_mul_of_nonneg_right _ hr
    calc s
      = 2 ^ (Real.logb 2 s) := (Real.rpow_logb (by linarith) (by linarith) hsp ).symm
    _ ≤ 2 ^ (⌈Real.logb 2 s⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by linarith) (Nat.le_ceil (Real.logb 2 s))
    _ = 2 ^ ⌈Real.logb 2 s⌉₊ := Real.rpow_natCast 2 ⌈Real.logb 2 s⌉₊

  have h1 : ball x r' ⊆ ball x (2 ^ ⌈Real.log s / Real.log 2⌉₊ * r) := by
    calc ball x r' ⊆ ball x (s * r) := ball_subset_ball hs
        _ ⊆ ball x (2 ^ ⌈Real.log s / Real.log 2⌉₊ * r) := ball_subset_ball haux

  /-Apply result for power of two to slightly larger ball-/
  calc volume (ball x r')
      ≤ volume (ball x (2 ^ ⌈Real.log s / Real.log 2⌉₊ * r)) := by gcongr
    _ ≤ A^(⌈Real.log s / Real.log 2⌉₊) * volume (ball x r) := volume_ball_le_pow_two'
    _ = As A s * volume (ball x r) := rfl

lemma volume_ball_le_same (x : X) {r s r': ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
    volume.real (ball x r') ≤ As A s * volume.real (ball x r) := by
  obtain hz := volume_ball_le_same' x hsp hs
  have hbr': volume (ball x r') ≠ ⊤ := measure_ball_ne_top x r'
  have hbr: volume (ball x r) ≠ ⊤ := measure_ball_ne_top x r
  have hAs : (As A s: ℝ≥0∞) ≠ ⊤ := coe_ne_top
  rw [← ENNReal.ofReal_toReal hbr,← ENNReal.ofReal_toReal hbr',
    ← ENNReal.ofReal_toReal hAs, ← ENNReal.ofReal_mul] at hz
  simp only [coe_toReal] at hz
  rw [← ENNReal.ofReal_le_ofReal_iff]
  · exact hz
  positivity
  simp only [coe_toReal, zero_le_coe]


def Ad (A : ℝ≥0) (s d : ℝ) : ℝ≥0 := As A s * A * As A d

lemma ball_subset_ball_of_le {x x' : X} {r r' : ℝ}
    (hr : dist x x' + r' ≤ r) : ball x' r' ⊆ ball x r := by
  intro y h
  have h1 : dist x y < r := by
    calc dist x y ≤ dist x x' + dist x' y := dist_triangle _ _ _
        _ < dist x x' + r' := by gcongr; exact mem_ball'.mp h
        _ ≤ r := hr
  exact mem_ball'.mpr h1




lemma volume_ball_le_of_dist_le' {x x' : X} {r r' s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (hsr : r' ≤ s * dist x x') (hdr : dist x x' ≤ d * r) :
    volume (ball x' r') ≤ Ad A s d * volume (ball x r) := by
  letI : Nonempty X := ⟨x⟩
  calc
    volume (ball x' r')
      ≤ As A s * volume (ball x' (dist x x')) := volume_ball_le_same' x' hs hsr
    _ ≤ As A s * volume (ball x (2 * dist x x')) := by
      rw [ENNReal.mul_le_mul_left (As_pos' X s).ne.symm (coe_ne_top)]
      apply MeasureTheory.measure_mono
      rw [two_mul]
      exact ball_subset_ball_of_le (le_refl _)
    _ ≤ As A s * A * volume (ball x (dist x x')) := by
      rw [mul_assoc, ENNReal.mul_le_mul_left (As_pos' X s).ne.symm coe_ne_top]
      exact volume_ball_two_le_same' x (dist x x')
    _ ≤ As A s * A * As A d * volume (ball x r) := by
      rw [mul_assoc (As A s * A : ℝ≥0∞)]
      apply mul_le_mul_of_nonneg_left _
      · exact zero_le ((As A s : ℝ≥0∞) * A)
      exact volume_ball_le_same' x hd hdr
    _ = Ad A s d * volume (ball x r) := by
      dsimp only [Ad]
      simp only [coe_mul]

section
variable {x x': X} {r r' s d : ℝ} (hs : 0 < s)

-- #check (@volume_ball_le_of_dist_le X A _ _ x' x r (2 * r) s s hs hs)

end
def Ai (A : ℝ≥0) (s : ℝ) : ℝ≥0 := Ad A s s

lemma volume_ball_le_of_subset {x' x : X} {r r' s : ℝ}
    (hs : r' ≤ s * r) (hr : ball x' r ⊆ ball x r') :
    volume.real (ball x (2 * r)) ≤ Ai A s * volume.real (ball x' r) := by sorry

def Ai2 (A : ℝ≥0) : ℝ≥0 := Ai A 2

lemma volume_ball_two_le_of_subset {x' x : X} {r : ℝ} (hr : ball x' r ⊆ ball x (2 * r)) :
    volume.real (ball x (2 * r)) ≤ Ai2 A * volume.real (ball x' r) :=
  volume_ball_le_of_subset le_rfl hr

def Np (A : ℝ≥0) (s : ℝ) : ℕ := ⌊Ad A (s * A + 2⁻¹) s⌋₊

/- Proof sketch: take a ball of radius `r / (2 * A)` around each point in `s`.
These are disjoint, and are subsets of `ball x (r * (2 * A + 2⁻¹))`. -/
lemma card_le_of_le_dist (x : X) {r r' s : ℝ} (P : Set X) (hs : r' ≤ s * r) (hP : P ⊆ ball x r')
  (h2P : ∀ x y, x ∈ P → y ∈ P → x ≠ y → r ≤ dist x y) : P.Finite ∧ Nat.card P ≤ Np A s := by sorry

/- Proof sketch: take any maximal set `s` of points that are at least distance `r` apart.
By the previous lemma, you only need a bounded number of points.
-/
lemma ballsCoverBalls {r r' s : ℝ} (hs : r' ≤ s * r) : BallsCoverBalls X r' r (Np A s) := by
  sorry

/- [Stein, 1.1.3(iv)] -/
lemma continuous_measure_ball_inter {U : Set X} (hU : IsOpen U) {δ} (hδ : 0 < δ) :
  Continuous fun x ↦ volume.real (ball x δ ∩ U) := sorry

/- [Stein, 1.1.4] -/
lemma continuous_average {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X → E}
    (hf : LocallyIntegrable f) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun x ↦ ⨍ y, f y ∂volume.restrict (ball x δ)) :=
  sorry

/- [Stein, 1.3.1], cor -/
lemma tendsto_average_zero {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X → E}
    (hf : LocallyIntegrable f) {x : X} :
    Tendsto (fun δ ↦ ⨍ y, f y ∂volume.restrict (ball x δ)) (𝓝[>] 0) (𝓝 (f x)) :=
  sorry

/- # Instances of spaces of homogeneous type -/

/- ℝ^n is a space of homogenous type. -/
--instance {ι : Type*} [Fintype ι] : DoublingMeasure (ι → ℝ) (2 ^ Fintype.card ι) := sorry

open FiniteDimensional
/- Preferably we prove that in this form. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] : DoublingMeasure E (2 ^ finrank ℝ E) where
      lt_top_of_isCompact := sorry
      outerRegular := sorry
      innerRegular := sorry
      open_pos := sorry
      volume_ball_two_le_same := sorry

/- Maybe we can even generalize the field? (at least for `𝕜 = ℂ` as well) -/
def NormedSpace.DoublingMeasure {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : DoublingMeasure E (2 ^ finrank 𝕜 E) := sorry

/- todo: ℝ^n with nonstandard metric: `dist x y = ∑ i, |x i - y i| ^ α i` for `α i > 0` -/
end
section

instance {X:Type*} [MetricSpace X] {A:ℝ≥0}
    [DoublingMeasure X A] : IsUnifLocDoublingMeasure (volume : Measure X) where
  exists_measure_closedBall_le_mul'' := by
    use A^2
    use Set.univ
    constructor
    · simp only [univ_mem]
    · simp only [mem_principal]
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
        nth_rw 1 [← one_mul (volume (closedBall x r))]
        apply mul_le_mul_of_nonneg_right _ (zero_le _)
        have : 1 ≤ (A:ℝ≥0∞) := by rw [one_le_coe_iff]; exact one_le_A X
        rw [← one_mul 1,pow_two]
        exact mul_le_mul this this (by norm_num) (A_nonneg X)
      else
      calc
        volume (closedBall x (2 * r))
          ≤ volume (ball x (2 * (2 * r))) := volume.mono (closedBall_subset_ball (by linarith))
        _ ≤ A * volume (ball x (2 * r)) := volume_ball_two_le_same' x (2 * r)
        _ ≤ A * (A * volume (ball x r)) := mul_le_mul_of_nonneg_left
          (volume_ball_two_le_same' x r) (A_nonneg X)
        _ = ↑(A ^ 2) * volume (ball x r) := by
          simp only [pow_two, coe_mul,mul_assoc]
        _ ≤ ↑(A ^ 2) * volume (closedBall x r) := mul_le_mul_of_nonneg_left
          (volume.mono ball_subset_closedBall) (zero_le ((A ^ 2 : ℝ≥0) : ℝ≥0∞))
end
