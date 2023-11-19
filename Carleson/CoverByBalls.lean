import Carleson.QuasiMetricSpace
import Carleson.ToMathlib

open Metric
open scoped NNReal

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [PseudoQuasiMetricSpace X A]
  {s t : Set X} {n m : ℕ} {r r' r₁ r₂ r₃ : ℝ}

set_option linter.unusedVariables false in
/-- `s` can be covered by at most `N` balls with radius `r`. -/
class inductive CoveredByBalls (s : Set X) (n : ℕ) (r : ℝ) : Prop where
  | mk (balls : Set X)
    (balls_finite : Set.Finite balls)
    (card_balls : Nat.card balls ≤ n)
    (union_balls : s ⊆ ⋃ x ∈ balls, ball x r) : CoveredByBalls s n r

/- Good first project: prove the following basic properties about `CoveredByBalls`.
Feel free to state some more properties. -/

lemma CoveredByBalls.mono_set (h : CoveredByBalls t n r) (h2 : s ⊆ t) : CoveredByBalls s n r := by
  induction h
  case mk b hb hn ht =>
    exact ⟨b, hb, hn, fun x hx ↦ ht (h2 hx)⟩

lemma CoveredByBalls.mono_nat (h : CoveredByBalls s n r) (h2 : n ≤ m) :
    CoveredByBalls s m r := by
      induction h
      case mk b hb hn hs =>
        exact ⟨b, hb, hn.trans h2, hs⟩

lemma CoveredByBalls.mono_real (h : CoveredByBalls s n r) (h2 : r ≤ r') :
    CoveredByBalls s n r' := by
      induction h
      case mk b hb hn hs =>
        exact ⟨b, hb, hn, hs.trans (by gcongr)⟩

@[simp]
lemma CoveredByBalls.empty : CoveredByBalls (∅ : Set X) n r := by
  have h1 : (∅ : Set X) ⊆ ⋃ x ∈ (∅ : Set X), ball x r := by
    exact Set.empty_subset (⋃ x ∈ ∅, ball x r)
  have hfinite :  Set.Finite (∅ : Set X) := by exact Set.finite_empty
  have h_Card_0 :  Nat.card (∅ : Set X) ≤ 0 := by
    refine Nat.le_of_eq ?p
    exact Nat.card_of_isEmpty
  have h2 : CoveredByBalls (∅ : Set X) 0 r := by
    exact ⟨ (∅ : Set X), hfinite, h_Card_0,h1 ⟩
  apply CoveredByBalls.mono_nat h2
  exact Nat.zero_le n

@[simp]
lemma CoveredByBalls.zero_left : CoveredByBalls s 0 r ↔ s = ∅ := by
  have h1 : CoveredByBalls s 0 r → s = ∅ := by
    intro hs_covered
    sorry
  have h2 : s = ∅ → CoveredByBalls s 0 r:= by
    intro hs_empty
    have h21 : s ⊆ ⋃ x ∈ (∅ : Set X) , ball x r := by
      rw [hs_empty]
      exact Set.empty_subset (⋃ x ∈ ∅, ball x r)
    have hfinite :  Set.Finite (∅ : Set X) := by exact Set.finite_empty
    have h_Card_0 :  Nat.card (∅ : Set X) ≤ 0 := by
      refine Nat.le_of_eq ?p
      exact Nat.card_of_isEmpty
    exact ⟨(∅ : Set X), hfinite, h_Card_0 , h21⟩
  exact { mp := h1, mpr := h2 }



@[simp]
lemma CoveredByBalls.zero_right : CoveredByBalls s n 0 ↔ s = ∅ := by
  sorry

variable (X) in
/-- Balls of radius `r` in are covered by `n` balls of radius `r'` -/
def BallsCoverBalls (r r' : ℝ) (n : ℕ) : Prop :=
  ∀ x : X, CoveredByBalls (ball x r) n r'

lemma CoveredByBalls.trans (h : CoveredByBalls s n r)
    (h2 : BallsCoverBalls X r r' m) : CoveredByBalls s (n * m) r' := by
  sorry

lemma BallsCoverBalls.trans (h1 : BallsCoverBalls X r₁ r₂ n) (h2 : BallsCoverBalls X r₂ r₃ m) :
    BallsCoverBalls X r₁ r₃ (n * m) :=
  fun x ↦ (h1 x).trans h2

lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
    BallsCoverBalls X (a^k * r) r (n^k) := by
  sorry

lemma BallsCoverBalls.pow {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
    BallsCoverBalls X (a^k) 1 (n^k) := by
  convert BallsCoverBalls.pow_mul h using 1
  simp
