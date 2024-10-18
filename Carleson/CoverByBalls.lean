import Carleson.ToMathlib.Misc

open Metric Finset
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]
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
  obtain ⟨b, hn, ht⟩ := h
  exact ⟨b, hn, fun x hx ↦ ht (h2 hx)⟩

lemma CoveredByBalls.mono_nat (h : CoveredByBalls s n r) (h2 : n ≤ m) : CoveredByBalls s m r := by
  obtain ⟨b, hn, hs⟩ := h
  exact ⟨b, hn.trans h2, hs⟩

lemma CoveredByBalls.mono_real (h : CoveredByBalls s n r) (h2 : r ≤ r') :
    CoveredByBalls s n r' := by
  obtain ⟨b, hn, hs⟩ := h
  exact ⟨b, hn, hs.trans (by gcongr)⟩

@[simp]
protected lemma CoveredByBalls.empty : CoveredByBalls (∅ : Set X) n r :=
  ⟨∅, by simp, by simp⟩

@[simp]
lemma CoveredByBalls.zero_left : CoveredByBalls s 0 r ↔ s = ∅ := by
  refine ⟨fun ⟨b, hn, hs⟩ ↦ ?_, by rintro rfl; exact CoveredByBalls.empty⟩
  simp at hn; subst hn; simpa using hs

@[simp]
lemma CoveredByBalls.zero_right : CoveredByBalls s n 0 ↔ s = ∅ := by
  refine ⟨fun ⟨_, _, hs⟩ ↦ ?_, fun hs ↦ ?_⟩
  · simpa using hs
  · have h22 : s ⊆ ⋃ x ∈ (∅ : Finset X), ball x 0 := by
      simp only [not_mem_empty, ball_zero, Set.iUnion_of_empty, Set.iUnion_empty]
      exact Set.subset_empty_iff.mpr hs
    use ∅, tsub_add_cancel_iff_le.mp rfl, h22

variable (X) in
/-- Balls of radius `r` in are covered by `n` balls of radius `r'` -/
def BallsCoverBalls (r r' : ℝ) (n : ℕ) : Prop := ∀ x : X, CoveredByBalls (ball x r) n r'

lemma CoveredByBalls.trans (h : CoveredByBalls s n r)
    (h2 : BallsCoverBalls X r r' m) : CoveredByBalls s (n * m) r' := by
  obtain ⟨b0, hb0, hs0⟩ := h
  rw [coveredByBalls_iff]
  have := fun x ↦ ((coveredByBalls_iff ..).mp (h2 x))
  classical
    use b0.biUnion fun x ↦ (this x).choose
    refine ⟨?_, fun p hp ↦ ?_⟩
    · calc
        _ ≤ ∑ x ∈ b0, (this x).choose.card := card_biUnion_le ..
        _ ≤ ∑ _ ∈ b0, m := sum_le_sum fun x _ ↦ (this x).choose_spec.1
        _ ≤ _ := by
          rw [sum_const_nat fun x ↦ congrFun rfl]
          exact Nat.mul_le_mul_right m hb0
    · obtain ⟨b, _, hb⟩ := Set.mem_iUnion₂.mp (hs0 hp)
      have tmp := ((this b).choose_spec.2) hb
      rw [Set.mem_iUnion₂] at tmp ⊢
      obtain ⟨c, _, hc⟩ := tmp
      use c, (by rw [mem_biUnion]; use b), hc

lemma BallsCoverBalls.mono (h : BallsCoverBalls X r₂ r₃ n) (h2 : r₁ ≤ r₂) :
    BallsCoverBalls X r₁ r₃ n := fun x ↦ (h x).mono_set (ball_subset_ball h2)

lemma BallsCoverBalls.trans (h1 : BallsCoverBalls X r₁ r₂ n) (h2 : BallsCoverBalls X r₂ r₃ m) :
    BallsCoverBalls X r₁ r₃ (n * m) := fun x ↦ (h1 x).trans h2

lemma BallCoversSelf (x : X) (r : ℝ) : CoveredByBalls (ball x r) 1 r := by
  let a : Finset X := singleton x
  have h : a.card ≤ 1 := by rfl
  have h2 : ball x r ⊆ ⋃ x ∈ a, ball x r := by simp [a]
  exact ⟨a, h, h2⟩

lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
    BallsCoverBalls X (a^k * r) r (n^k) := by
  induction k with
  | zero => simpa using fun x ↦ BallCoversSelf x r
  | succ m h2 =>
    specialize h (r * a^m)
    rw [← mul_assoc, mul_comm, ← mul_assoc] at h
    rw [pow_succ, pow_succ']
    rw [mul_comm] at h2
    exact h.trans h2

lemma BallsCoverBalls.pow {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
    BallsCoverBalls X (a^k) 1 (n^k) := by
  convert BallsCoverBalls.pow_mul h using 1
  exact (MulOneClass.mul_one (a ^ k)).symm
