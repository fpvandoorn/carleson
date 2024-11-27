import Carleson.TileStructure
import Carleson.HardyLittlewood
import Carleson.Psi

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ENNReal NNReal ShortVariables

open MeasureTheory Set

namespace Antichain

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

-- Lemma 6.3.1
lemma tile_reach {ϑ : Θ X} {N : ℕ} {p p' : 𝔓 X} (hp : dist_(p) (𝒬 p) ϑ ≤ 2^N)
    (hp' : dist_(p') (𝒬 p') ϑ ≤ 2^N) (hI : 𝓘 p ≤ 𝓘 p') (hs : 𝔰 p < 𝔰 p'):
  smul (2^(N + 2)) p ≤ smul (2^(N + 2)) p' := sorry

-- Def 6.3.15
def 𝔄_aux (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) : Finset (𝔓 X) :=
  {p ∈ 𝔄 | 1 + dist_(p) (𝒬 p) ϑ ∈ Icc (2^N) (2^(N+1))}

open Classical Metric

-- Lemma 6.3.2
lemma stack_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) (L : Grid X) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L}), volume (E p ∩ G) ≤
      2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := sorry


-- Lemma 6.3.3
-- p' is 𝔭_ϑ in the blueprint
lemma local_antichain_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) {p' : 𝔓 X} (hp' : ϑ ∈ Ω p') :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝔰 p' < 𝔰 p}), volume (E p ∩ G ∩ 𝓘 p') ≤
      volume (E₂ (2 ^ (N + 3)) p') := by
  by_cases h : {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝔰 p' < 𝔰 p ∧ ((𝓘 p' : Set X) ∩ (𝓘 p)).Nonempty}.Nonempty
  · -- Let `p ∈ (𝔄_aux 𝔄 ϑ N)` with `𝔰 p' < 𝔰 p` and assume that `(𝓘 p : Set X) ∩ (𝓘 p') ≠ ∅`.
    obtain ⟨p, hp⟩ := h
    obtain ⟨hpin, hps, hnemp⟩ := Finset.mem_filter.mp hp
    have hle : 𝓘 p' ≤ 𝓘 p :=
      ⟨Or.resolve_right (fundamental_dyadic (le_of_lt hps))
        (not_disjoint_iff_nonempty_inter.mpr hnemp), le_of_lt hps⟩
    -- 6.3.22
    have hϑaux : ϑ ∈ ball_(p') (𝒬 p') 1 := subset_cball hp'-- TODO: add _(p) in blueprint
    have hϑin' : dist_(p') (𝒬 p') ϑ < ((2 : ℝ)^(N + 1)) := by
      have h12 : (1 : ℝ) < 2 := one_lt_two
      have h0N : 0 < N + 1 := Nat.zero_lt_succ N
      simp only [mem_ball'] at hϑaux
      apply lt_trans hϑaux
      nth_rewrite 1 [← pow_zero 2]
      gcongr -- uses h12, h0N
    -- 6.3.23
    have hϑin : dist_(p) (𝒬 p) ϑ < ((2 : ℝ)^(N + 1)) := by -- TODO: add _(p) in blueprint
      simp only [𝔄_aux, Finset.mem_filter] at hpin
      exact lt_of_lt_of_le (lt_one_add (dist_(p) (𝒬 p) ϑ)) hpin.2.2
    -- 6.3.24
    have hsmul_le : smul (2 ^ (N + 3)) p' ≤ smul (2 ^ (N + 3)) p :=
      tile_reach (le_of_lt hϑin') (le_of_lt hϑin) hle hps
    -- 6.3.25
    have hss : E p ∩ G ⊆ E₂ (2^(N + 3)) p' := sorry
    -- 6.3.21
    have hLHS : ∑ p ∈ Finset.filter (fun p ↦ 𝔰 p' < 𝔰 p) (𝔄_aux 𝔄 ϑ N), volume (E p ∩ G ∩ ↑(𝓘 p')) ≤
        volume (E p ∩ G ∩ ↑(𝓘 p')) := by

      sorry
    exact le_trans hLHS (measure_mono (le_trans inter_subset_left hss))

  · -- If for every `p ∈ (𝔄_aux 𝔄 ϑ N)` with `𝔰 p' < 𝔰 p` we have `(𝓘 p : Set X) ∩ (𝓘 p') = ∅`, then
    -- the sum on the LHS is zero and the lemma follows trivially.
    have h0 : ∑ p ∈ Finset.filter (fun p ↦ 𝔰 p' < 𝔰 p) (𝔄_aux 𝔄 ϑ N),
        volume (E p ∩ G ∩ ↑(𝓘 p')) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hpin, hps⟩ := Finset.mem_filter.mp hp
      have hemp : ¬ ((𝓘 p' : Set X) ∩ (𝓘 p)).Nonempty := by
        by_contra hpp'
        exact h ⟨p,  Finset.mem_filter.mpr ⟨hpin, hps, hpp'⟩⟩
      have hemp' : (𝓘 p' : Set X) ∩ E p = ∅ := by
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        exact eq_empty_of_subset_empty (hemp ▸ inter_subset_inter_right _
          (sep_subset ↑(𝓘 p) fun x ↦ Q x ∈ Ω p ∧ 𝔰 p ∈ Icc (σ₁ x) (σ₂ x)))
      suffices E p ∩ G ∩ ↑(𝓘 p') = ∅ by
        rw [this, measure_empty]
      rw [inter_comm, ← inter_assoc, hemp', empty_inter]
    simp_rw [h0]
    simp only [h ,Finset.sum_empty, zero_le]

def C_6_3_4 (a N : ℕ) : ℝ≥0 := 2^(101*a^3 + N*a)

-- Lemma 6.3.4
lemma global_antichain_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) :
    ∑ (p ∈ 𝔄_aux 𝔄 ϑ N), volume (E p ∩ G) ≤
      (C_6_3_4 a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ (p ∈ 𝔄), (𝓘 p : Set X)) := sorry

-- p in Lemma 6.1.6
private def p (a : ℕ) := 4 * a^2

def C_6_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (104 * a)

-- Lemma 6.1.6
-- Note: p' is introduced in the statement in the blueprint but not used. There may be a typo.
lemma tile_count {𝔄 𝔄' : Finset (𝔓 X)} (h_le : 𝔄' ⊆ 𝔄) (ϑ : Θ X) :
    eLpNorm (∑ 𝔭 ∈ 𝔄', (1 + dist_(𝔭) (𝒬 𝔭) ϑ) ^ ((-1 : ℝ)/(2*a^2 + a^3)) •
      ((E 𝔭).indicator 1) *  (G.indicator (1 : X → ℝ))) (p a) volume ≤
      (C_6_1_6 a) * dens₁ (𝔄 : Set (𝔓 X)) ^ ((1 : ℝ)/(p a)) *
        (volume (⋃ (p ∈ 𝔄), (𝓘 p : Set X))) ^ ((1 : ℝ)/(p a)) := by
  sorry

end Antichain
