import Carleson.CoverByBalls
import Carleson.ToMathlib.MeasureReal
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Doubling

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
class DoublingMeasure (X : Type*) (A : outParam ℝ) [PseudoMetricSpace X] extends
  MeasureSpace X, ProperSpace X, BorelSpace X,
  Regular (volume : Measure X), IsOpenPosMeasure (volume : Measure X) where
  volume_ball_two_le_same : ∀ (x : X) r, volume.real (ball x (2 * r)) ≤ A * volume.real (ball x r)

export DoublingMeasure (volume_ball_two_le_same)

variable {X : Type*} {A : ℝ} [PseudoMetricSpace X] [DoublingMeasure X A]

example : ProperSpace X := by infer_instance
example : LocallyCompactSpace X := by infer_instance
example : CompleteSpace X := by infer_instance
example : SigmaCompactSpace X := by infer_instance
example : SigmaFinite (volume : Measure X) := by infer_instance
example : SecondCountableTopology X := by infer_instance
example : SeparableSpace X := by infer_instance

variable (X) in
lemma one_le_A : 1 ≤ A := by
  let _ := ‹DoublingMeasure X A› -- remove after proof is finished
  sorry

variable (X) in lemma A_nonneg : 0 ≤ A := by linarith [one_le_A X]
variable (X) in lemma A_pos : 0 < A := by linarith [one_le_A X]

instance [MetricSpace X] [DoublingMeasure X A] : IsUnifLocDoublingMeasure (volume : Measure X) := by
  sorry

def DoublingMeasure.mono {A'} (h : A ≤ A') : DoublingMeasure X A' where
  volume_ball_two_le_same := sorry

lemma volume_ball_four_le_same (x : X) (r : ℝ) :
    volume.real (ball x (4 * r)) ≤ A ^ 2 * volume.real (ball x r) := by
  calc volume.real (ball x (4 * r))
      = volume.real (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * volume.real (ball x (2 * r)) := by apply volume_ball_two_le_same
    _ ≤ A * (A * volume.real (ball x r)) := by
      gcongr; exact A_nonneg X; apply volume_ball_two_le_same
    _ = A ^ 2 * volume.real (ball x r) := by ring_nf


lemma measure_ball_ne_top (x : X) (r : ℝ) : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne

attribute [aesop (rule_sets := [Finiteness]) safe apply] measure_ball_ne_top

def As (A : ℝ) (s : ℝ) : ℝ :=
  A ^ ⌈ Real.log s / Real.log 2⌉₊

/- Proof sketch: First do for powers of 2 by induction, then use monotonicity. -/
lemma volume_ball_le_same (x : X) {r s r': ℝ} (hsp : s > 0) (hs : r' ≤ s * r) :
    volume.real (ball x r') ≤ As A s * volume.real (ball x r) := by
  /-First show statement for s a power of two-/
  have hn (n : ℕ) : volume.real (ball x (2^n * r)) ≤ A^n * volume.real (ball x r) := by
    induction n
    case zero =>
      simp
    case succ m hm =>
      calc volume.real (ball x (2 ^ (Nat.succ m) * r))
          = volume.real (ball x (2 ^ (m+1) * r)) := by rfl
        _ = volume.real (ball x ((2 ^ m*2^1) * r)) := by norm_cast
        _ = volume.real (ball x (2 * 2 ^ m * r)) := by ring_nf
        _ ≤ A * volume.real (ball x (2 ^ m * r)) := by
          rw[mul_assoc]; norm_cast; apply volume_ball_two_le_same
        _ ≤ A * (↑(A ^ m) * volume.real (ball x r)) := by gcongr; exact A_nonneg X
        _ = A^(Nat.succ m) * volume.real (ball x r) := by rw[<- mul_assoc, pow_succ']

  /-Show inclusion in larger ball-/
  have haux : s * r ≤ 2 ^ ⌈Real.log s / Real.log 2⌉₊ * r := by
    sorry
  have h1 : ball x r' ⊆ ball x (2 ^ ⌈Real.log s / Real.log 2⌉₊ * r) := by
    calc ball x r' ⊆ ball x (s * r) := by apply ball_subset_ball hs
        _ ⊆ ball x (2 ^ ⌈Real.log s / Real.log 2⌉₊ * r) := by apply ball_subset_ball haux

  /-Apply result for power of two to slightly larger ball-/
  calc volume.real (ball x r')
          ≤ volume.real (ball x (2 ^ ⌈Real.log s / Real.log 2⌉₊ * r)) := by gcongr; finiteness
        _ ≤ A^(⌈Real.log s / Real.log 2⌉₊) * volume.real (ball x r) := by apply hn



def Ad (A : ℝ) (s d : ℝ) : ℝ :=
  As A (A * (d + s))

lemma ball_subset_ball_of_le {x x' : X} {r r' : ℝ}
  (hr : dist x x' + r' ≤ r) : ball x' r' ⊆ ball x r := by
    intro y h
    have h1 : dist x y < r := by
      calc dist x y ≤ dist x x' + dist x' y := by apply dist_triangle
          _ < dist x x' + r' := by gcongr; apply mem_ball'.mp h
          _ ≤ r := by apply hr
    exact mem_ball'.mpr h1


lemma volume_ball_le_of_dist_le {x x' : X} {r r' s d : ℝ}
  (hs : r' ≤ s * r) (hd : dist x x' ≤ d * r) :
    volume.real (ball x' r') ≤ Ad A s d * volume.real (ball x r) := by sorry

def Ai (A : ℝ) (s : ℝ) : ℝ := Ad A s s

lemma volume_ball_le_of_subset {x' x : X} {r r' s : ℝ}
    (hs : r' ≤ s * r) (hr : ball x' r ⊆ ball x r') :
    volume.real (ball x (2 * r)) ≤ Ai A s * volume.real (ball x' r) := by sorry

def Ai2 (A : ℝ) : ℝ := Ai A 2

lemma volume_ball_two_le_of_subset {x' x : X} {r : ℝ} (hr : ball x' r ⊆ ball x (2 * r)) :
    volume.real (ball x (2 * r)) ≤ Ai2 A * volume.real (ball x' r) :=
  volume_ball_le_of_subset le_rfl hr

def Np (A : ℝ) (s : ℝ) : ℕ := ⌊Ad A (s * A + 2⁻¹) s⌋₊

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
