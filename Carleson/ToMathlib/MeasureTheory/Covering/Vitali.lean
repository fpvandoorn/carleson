module

public import Mathlib.MeasureTheory.Covering.Vitali

-- PR #38903 upstream.

@[expose] public section

variable {α : Type _} {ι : Type _}

open Set Metric

/- Note: it seems easier to do the analogous proof again than to apply the previous one, because the
interior of a closed ball may not equal the open ball. -/

/-- Vitali covering theorem, open balls version: given a family `t` of balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the τ-times
dilations of balls in `u`, for some `τ > 3`. -/
theorem exists_disjoint_subfamily_covering_enlargement_ball
    [PseudoMetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => ball (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases! ht : ∀ a ∈ t, r a ≤ 0
  · exact ⟨t, Subset.rfl, fun a ha b _ _ => by
      simp only [ball_eq_empty.2 (ht a ha), empty_disjoint, Function.onFun],
      fun a ha => ⟨a, ha, by simp only [ball_eq_empty.2 (ht a ha), empty_subset]⟩⟩
  let t' := { a ∈ t | 0 < r a }
  rcases Vitali.exists_disjoint_subfamily_covering_enlargement (fun a => ball (x a) (r a)) t' r
      ((τ - 1) / 2) (by linarith) (fun a ha => ha.2.le) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_ball_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) < r a + r b := dist_lt_add_of_nonempty_ball_inter_ball hb
    apply ball_subset_ball'
    linarith
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases lt_or_ge 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _⟩
    exact ⟨c, cu, by simp only [ball_eq_empty.2 h'a, empty_subset]⟩
