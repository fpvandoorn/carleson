import Carleson.CoverByBalls
import Mathlib.MeasureTheory.Measure.Haar.Basic

open MeasureTheory Measure NNReal ENNReal Metric
noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-! Question(F): should a space of homogeneous type extend `PseudoQuasiMetricSpace` or
`QuasiMetricSpace`? -/

/-- A space of homogeneous type.
Note(F): I added `ProperSpace` to the definition (which I think doesn't follow from the rest?)
and removed `SigmaFinite` (which follows from the rest).
Should we assume `volume ≠ 0` / `IsOpenPosMeasure`? -/
class IsSpaceOfHomogeneousType (X : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)] extends
  PseudoQuasiMetricSpace X A, MeasureSpace X, ProperSpace X, BorelSpace X,
  Regular (volume : Measure X) where
  volume_ball_two_le_same : ∀ (x : X) r, volume (ball x (2 * r)) ≤ A * volume (ball x r)

export IsSpaceOfHomogeneousType (volume_ball_two_le_same)

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A]

example : ProperSpace X := by infer_instance
example : LocallyCompactSpace X := by infer_instance
example : CompleteSpace X := by infer_instance
example : SigmaCompactSpace X := by infer_instance
example : SigmaFinite (volume : Measure X) := by infer_instance

lemma volume_ball_four_le_same (x : X) (r : ℝ) :
    volume (ball x (4 * r)) ≤ A ^ 2 * volume (ball x r) := by
  calc volume (ball x (4 * r))
      = volume (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * volume (ball x (2 * r)) := by apply volume_ball_two_le_same
    _ ≤ A * (A * volume (ball x r)) := by gcongr; apply volume_ball_two_le_same
    _ = A ^ 2 * volume (ball x r) := by ring_nf; norm_cast; ring_nf


example (x : X) (r : ℝ) : volume (ball x r) < ∞ := measure_ball_lt_top

def As (A : ℝ≥0) (s : ℝ) : ℝ≥0 :=
  A * 2 ^ ⌊s⌋₊

/- Proof sketch: First do for powers of 2 by induction, then use monotonicity. -/
lemma volume_ball_le_same (x : X) {r r' s : ℝ} (hs : r' ≤ s * r) :
    volume (ball x r') ≤ As A s * volume (ball x r) := by sorry

def Ad (A : ℝ≥0) (s d : ℝ) : ℝ≥0 :=
  As A (A * (d + s))

lemma volume_ball_le_of_dist_le {x x' : X} {r r' s d : ℝ}
  (hs : r' ≤ s * r) (hd : dist x x' ≤ d * r) :
    volume (ball x' r') ≤ Ad A s d * volume (ball x r) := by sorry

def Ai (A : ℝ≥0) (s : ℝ) : ℝ≥0 := Ad A s s

lemma volume_ball_le_of_subset {x' x : X} {r r' s : ℝ}
    (hs : r' ≤ s * r) (hr : ball x' r ⊆ ball x r') :
    volume (ball x (2 * r)) ≤ Ai A s * volume (ball x' r) := by sorry

def Ai2 (A : ℝ≥0) : ℝ≥0 := Ai A 2

lemma volume_ball_two_le_of_subset {x' x : X} {r : ℝ} (hr : ball x' r ⊆ ball x (2 * r)) :
    volume (ball x (2 * r)) ≤ Ai2 A * volume (ball x' r) :=
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

/- # Instances of spaces of homogeneous type -/

/- ℝ^n is a space of homogenous type. -/
instance {ι : Type*} [Fintype ι] : IsSpaceOfHomogeneousType (ι → ℝ) 1 := sorry

/- Preferrably we prove that in this form. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : IsSpaceOfHomogeneousType E 1 := by
  sorry

/- Maybe we can even generalize the field? (at least for `𝕜 = ℂ` as well) -/
def NormedSpace.isSpaceOfHomogeneousType {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : IsSpaceOfHomogeneousType E 1 := sorry

/- todo: ℝ^n with nonstandard metric: `dist x y = ∑ i, |x i - y i| ^ α i` for `α i > 0` -/
