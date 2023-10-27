import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.MetricSpace.Holder
import Carleson.QuasiMetricSpace


set_option linter.unusedVariables false in
/-- `s` can be covered by at most `N` balls with radius `r` under distance function `d`. -/
class inductive CoveredByBalls {α : Type*} (d : α → α → ℝ) (s : Set α) (n : ℕ) (r : ℝ) : Prop where
  | mk (balls : Set α)
    (balls_finite : Set.Finite balls)
    (card_balls : Nat.card balls ≤ n)
    (union_balls : ∀ x ∈ s, ∃ z ∈ balls, d x z < r) : CoveredByBalls d s n r

variable {α : Type*} {d : α → α → ℝ} {s t : Set α} {n m : ℕ} {r r' r₁ r₂ r₃ : ℝ}

/- Good first project: prove the following basic properties about `CoveredByBalls`.
Feel free to state some more properties. -/

lemma CoveredByBalls.mono_set (h : CoveredByBalls d t n r) (h2 : s ⊆ t) : CoveredByBalls d s n r := by
  induction h
  case mk b hb hn hs =>
    exact ⟨b, hb, hn, fun x hx ↦ hs x (h2 hx)⟩

lemma CoveredByBalls.mono_nat (h : CoveredByBalls d s n r) (h2 : n ≤ m) :
    CoveredByBalls d s m r := by
  sorry

lemma CoveredByBalls.mono_real (h : CoveredByBalls d s n r) (h2 : r ≤ r') :
    CoveredByBalls d s n r' := by
  sorry

@[simp]
lemma CoveredByBalls.empty : CoveredByBalls d ∅ n r := by
  sorry

@[simp]
lemma CoveredByBalls.zero_left : CoveredByBalls d s 0 r ↔ s = ∅ := by
  sorry

@[simp]
lemma CoveredByBalls.zero_right : CoveredByBalls d s n 0 ↔ s = ∅ := by
  sorry

/-- Balls of radius `r` in `α` are covered by `n` balls of radius `r'` -/
def BallsCoverBalls (d : α → α → ℝ) (r r' : ℝ) (n : ℕ) : Prop :=
  ∀ x : α, CoveredByBalls d { y | d y x < r} n r'

lemma CoveredByBalls.trans (h : CoveredByBalls d s n r)
    (h2 : BallsCoverBalls d r r' m) : CoveredByBalls d s (n * m) r' := by
  sorry

lemma BallsCoverBalls.trans (h1 : BallsCoverBalls d r₁ r₂ n) (h2 : BallsCoverBalls d r₂ r₃ m) :
    BallsCoverBalls d r₁ r₃ (n * m) :=
  fun x ↦ (h1 x).trans h2

lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls d (a * r) r n) :
    BallsCoverBalls d (a^k * r) r (n^k) := by
  sorry

lemma BallsCoverBalls.pow {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls d (a * r) r n) :
    BallsCoverBalls d (a^k) 1 (n^k) := by
  convert BallsCoverBalls.pow_mul h using 1
  simp
