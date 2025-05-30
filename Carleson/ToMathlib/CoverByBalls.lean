import Carleson.ToMathlib.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Base

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
  simp only [nonpos_iff_eq_zero, card_eq_zero] at hn; subst hn; simpa using hs

@[simp]
lemma CoveredByBalls.zero_right : CoveredByBalls s n 0 ↔ s = ∅ := by
  refine ⟨fun ⟨_, _, hs⟩ ↦ ?_, fun hs ↦ ?_⟩
  · simpa using hs
  · have h22 : s ⊆ ⋃ x ∈ (∅ : Finset X), ball x 0 := by
      simp only [not_mem_empty, ball_zero, Set.iUnion_of_empty, Set.iUnion_empty]
      exact Set.subset_empty_iff.mpr hs
    use ∅, tsub_add_cancel_iff_le.mp rfl, h22

protected lemma CoveredByBalls.ball (x : X) (r : ℝ) : CoveredByBalls (ball x r) 1 r := by
  let a : Finset X := singleton x
  have h : a.card ≤ 1 := by rfl
  have h2 : ball x r ⊆ ⋃ x ∈ a, ball x r := by simp [a]
  exact ⟨a, h, h2⟩

variable (X) in
/-- Balls of radius `r` in `X` are covered by `n` balls of radius `r'` -/
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

lemma BallsCoverBalls.zero : BallsCoverBalls X 0 r n := by
  intro x
  convert CoveredByBalls.empty
  simp

lemma BallsCoverBalls.nonpos (hr' : r' ≤ 0) : BallsCoverBalls X r' r n :=
  BallsCoverBalls.zero.mono hr'

variable (X) in
/-- For all `r`, balls of radius `r` in `X` are covered by `n` balls of radius `a * r` -/
def AllBallsCoverBalls (a : ℝ) (n : ℕ) : Prop := ∀ r : ℝ, BallsCoverBalls X (a * r) r n

lemma AllBallsCoverBalls.pow {a : ℝ} {k : ℕ} (h : AllBallsCoverBalls X a n) :
    AllBallsCoverBalls X (a ^ k) (n ^ k) := by
  intro r
  induction k with
  | zero => simpa using fun x ↦ .ball x r
  | succ m h2 =>
    specialize h (r * a^m)
    rw [← mul_assoc, mul_comm, ← mul_assoc] at h
    rw [pow_succ, pow_succ']
    rw [mul_comm] at h2
    exact h.trans h2

lemma AllBallsCoverBalls.ballsCoverBalls_pow {a : ℝ} {k : ℕ} (h : AllBallsCoverBalls X a n) :
    BallsCoverBalls X (a ^ k) 1 (n ^ k) := by
  apply h.pow _ |>.mono
  rw [mul_one]

lemma AllBallsCoverBalls.ballsCoverBalls {a : ℝ} (h : AllBallsCoverBalls X a n)
    (h2 : 1 < a) (hr : 0 < r) :
    BallsCoverBalls X r' r (n ^ ⌈Real.logb a (r' / r)⌉₊) := by
  obtain hr'|hr' := le_or_lt r' 0
  · exact .nonpos hr'
  refine h.pow _ |>.mono ?_
  calc
    r' = r' / r * r := by rw [div_mul_cancel₀]; exact hr.ne'
    _ ≤ a ^ ⌈Real.logb a (r' / r)⌉₊ * r := by
      gcongr
      apply Real.le_pow_natCeil_logb h2
      positivity


-- todo: move near `secondCountable_of_almost_dense_set`
/-- A pseudometric space is second countable if, for every `ε > 0` and every ball `B`
with natural number radius around a fiven point `x₀`,
there is a countable set which is `ε`-dense in `B`. -/
theorem Metric.secondCountableTopology_of_almost_dense_set_balls_nat
    {α} [PseudoMetricSpace α] (x₀ : α)
    (H : ∀ ε > (0 : ℝ), ∀ (n : ℕ),
    ∃ s : Set α, s.Countable ∧ ∀ x ∈ ball x₀ n, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α := by
  apply secondCountable_of_almost_dense_set
  intro ε hε
  specialize H ε hε
  choose s h1s y h1y h2y using H
  use ⋃ n, s n, by simp [*]
  intro x
  use y (⌊dist x x₀⌋₊ + 1) x (by simp [Nat.lt_floor_add_one])
  simp only [Set.mem_iUnion, and_true, h2y]
  exact ⟨_, h1y ..⟩

-- todo: move near `secondCountable_of_almost_dense_set`
/-- A pseudometric space is second countable if, for every `ε > 0` and every ball `B`,
there is a countable set which is `ε`-dense in `B`. -/
theorem Metric.secondCountableTopology_of_almost_dense_set_balls
    {α} [PseudoMetricSpace α]
    (H : ∀ (x₀ : α), ∀ ε > (0 : ℝ), ∀ r,
    ∃ s : Set α, s.Countable ∧ ∀ x ∈ ball x₀ r, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α := by
  obtain hX|hX := isEmpty_or_nonempty α
  · exact Finite.toSecondCountableTopology
  inhabit α
  apply secondCountableTopology_of_almost_dense_set_balls_nat default
  intro ε hε n
  obtain ⟨s, hs, h2⟩ := H default ε hε n
  use s


/-- A pseudometric space is second countable if, for every `ε > 0` and every ball `B` is covered
by finitely many balls of radius `ε`. -/
theorem BallsCoverBalls.secondCountableTopology
    (H : ∀ ε > (0 : ℝ), ∀ r, ∃ n, BallsCoverBalls X r ε n) :
    SecondCountableTopology X := by
  refine Metric.secondCountableTopology_of_almost_dense_set_balls fun x₀ ε hε r ↦ ?_
  obtain ⟨n, hn⟩ := H ε hε r
  obtain ⟨s, hs, h2⟩ := hn x₀
  use s, countable_toSet s, fun x hx ↦ ?_
  have := h2 hx
  simp only [Set.mem_iUnion, mem_ball, exists_prop] at this
  obtain ⟨y, hy, h2y⟩ := this
  use y, hy, h2y.le

/-- A pseudometric space is second countable if every ball of radius `a * r` is covered by
`b` many balls of radius `r`. -/
lemma AllBallsCoverBalls.secondCountableTopology {a : ℝ} (h : AllBallsCoverBalls X a n)
    (h2 : 1 < a) : SecondCountableTopology X :=
  BallsCoverBalls.secondCountableTopology fun _ hε _ ↦ ⟨_, h.ballsCoverBalls h2 hε⟩
