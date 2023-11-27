import Carleson.QuasiMetricSpace
import Carleson.ToMathlib

open Metric Finset
open scoped NNReal

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [PseudoQuasiMetricSpace X A]
  {s t : Set X} {n m : ℕ} {r r' r₁ r₂ r₃ : ℝ}

set_option linter.unusedVariables false in
/-- `s` can be covered by at most `N` balls with radius `r`. -/
@[mk_iff]
class inductive CoveredByBalls (s : Set X) (n : ℕ) (r : ℝ) : Prop where
  | mk (balls : Finset X)
    (card_balls : balls.card ≤ n)
    (union_balls : s ⊆ ⋃ x ∈ balls, ball x r) : CoveredByBalls s n r

/- Good first project: prove the following basic properties about `CoveredByBalls`.
Feel free to state some more properties. -/

lemma CoveredByBalls.mono_set (h : CoveredByBalls t n r) (h2 : s ⊆ t) : CoveredByBalls s n r := by
  induction h
  case mk b hn ht =>
    exact ⟨b, hn, fun x hx ↦ ht (h2 hx)⟩

lemma CoveredByBalls.mono_nat (h : CoveredByBalls s n r) (h2 : n ≤ m) :
    CoveredByBalls s m r := by
      induction h
      case mk b hn hs =>
        exact ⟨b, hn.trans h2, hs⟩

lemma CoveredByBalls.mono_real (h : CoveredByBalls s n r) (h2 : r ≤ r') :
    CoveredByBalls s n r' := by
      induction h
      case mk b hn hs =>
        exact ⟨b, hn, hs.trans (by gcongr)⟩

@[simp]
protected lemma CoveredByBalls.empty : CoveredByBalls (∅ : Set X) n r :=
  ⟨∅, by simp, by simp⟩

@[simp]
lemma CoveredByBalls.zero_left : CoveredByBalls s 0 r ↔ s = ∅ := by
  have h1 : CoveredByBalls s 0 r → s = ∅ := by
    intro ⟨b, hn, hs⟩
    simp at hn
    subst hn
    simp at hs
    exact Set.subset_eq_empty hs rfl
  have h2 : s = ∅ → CoveredByBalls s 0 r := by
    rintro rfl
    exact CoveredByBalls.empty
  exact { mp := h1, mpr := h2 }



@[simp]
lemma CoveredByBalls.zero_right : CoveredByBalls s n 0 ↔ s = ∅ := by
  have h1 : CoveredByBalls s n 0 → s =∅ := by
    intro hcovered
    cases hcovered
    case mk b hn hs
    have h11 : ∀ x ∈b, ball x 0 = ∅ := by
      exact fun x a ↦ ball_zero
    simp at hs
    exact Set.subset_eq_empty hs rfl
  have h2 : s = ∅ → CoveredByBalls s n 0 := by
    intro hs
    have h21 : (∅ : Finset X).card ≤ n := by exact tsub_add_cancel_iff_le.mp rfl
    have h22 : s ⊆ ⋃ x ∈ (∅ : Finset X), ball x 0 := by
      simp
      exact Set.subset_empty_iff.mpr hs
    exact ⟨(∅ : Finset X), h21, h22⟩
  exact { mp := h1, mpr := h2 }

variable (X) in
/-- Balls of radius `r` in are covered by `n` balls of radius `r'` -/
def BallsCoverBalls (r r' : ℝ) (n : ℕ) : Prop :=
  ∀ x : X, CoveredByBalls (ball x r) n r'

lemma CoveredByBalls.trans (h : CoveredByBalls s n r)
    (h2 : BallsCoverBalls X r r' m) : CoveredByBalls s (n * m) r' := by
    cases h
    case mk b0 hb0 hs0
    sorry



lemma BallsCoverBalls.trans (h1 : BallsCoverBalls X r₁ r₂ n) (h2 : BallsCoverBalls X r₂ r₃ m) :
    BallsCoverBalls X r₁ r₃ (n * m) :=
  fun x ↦ (h1 x).trans h2

lemma BallCoversSelf (x : X) (r : ℝ) : CoveredByBalls (ball x r) 1 r := by {
  let a : Finset X := singleton x
  have h : a.card ≤ 1 := by rfl
  have h2 : ball x r ⊆ ⋃ x ∈ a, ball x r := by
    simp
    rfl
  exact ⟨a, h, h2⟩
}

lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
    BallsCoverBalls X (a^k * r) r (n^k) := by
  induction k
  case zero =>
    simp
    rw[BallsCoverBalls]
    intro x
    exact BallCoversSelf x r
  case succ m h2 =>
    specialize h (r * a^m)
    simp at h
    rw[<- mul_assoc, mul_comm, <- mul_assoc] at h
    norm_cast
    rw[Nat.succ_eq_add_one, Nat.pow_add, pow_add, pow_one, pow_one, mul_comm (n^m) n]
    rw[mul_comm] at h2
    norm_cast at h2
    exact BallsCoverBalls.trans h h2

lemma BallsCoverBalls.pow {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
    BallsCoverBalls X (a^k) 1 (n^k) := by
  convert BallsCoverBalls.pow_mul h using 1
  simp
