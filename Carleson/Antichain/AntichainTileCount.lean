import Carleson.Antichain.AntichainOperator

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

-- We prove inclusion 6.3.25 for every `p ∈ (𝔄_aux 𝔄 ϑ N)` with `𝔰 p' < 𝔰 p` such that
-- `(𝓘 p : Set X) ∩ (𝓘 p') ≠ ∅`.
-- p' is 𝔭_ϑ in the blueprint
lemma Ep_inter_G_inter_Ip'_subset_E2 {𝔄 : Finset (𝔓 X)} (ϑ : Θ X) (N : ℕ) {p p' : 𝔓 X}
    (hpin : p ∈ (𝔄_aux 𝔄 ϑ N)) (hp' : ϑ ∈ Ω p') (hs : 𝔰 p' < 𝔰 p)
    (h𝓘 : ((𝓘 p' : Set X) ∩ (𝓘 p)).Nonempty) :
    E p ∩ G ∩ ↑(𝓘 p') ⊆ E₂ (2^(N + 3)) p' := by -- TODO: add ∩ ↑(𝓘 p') in blueprint
  have hle : 𝓘 p' ≤ 𝓘 p := ⟨Or.resolve_right (fundamental_dyadic (le_of_lt hs))
    (not_disjoint_iff_nonempty_inter.mpr h𝓘), le_of_lt hs⟩
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
    tile_reach (le_of_lt hϑin') (le_of_lt hϑin) hle hs
  -- NOTE: TileLike.toSet is not a mono.
  -- 6.3.25
  have hss : E p ∩ G ∩ ↑(𝓘 p') ⊆ E₂ (2^(N + 3)) p' := by -- TODO: add ∩ ↑(𝓘 p') in blueprint
    simp only [TileLike.le_def, smul_snd] at hsmul_le
    simp only [E, E₂, TileLike.toSet, smul_fst, smul_snd, subset_inter_iff, inter_subset_right,
      true_and]
    constructor
    · rw [inter_assoc, inter_comm, inter_assoc]
      exact inter_subset_left
    · have h1N : (1 : ℝ) ≤ 2 ^ (N + 3) := by exact_mod_cast Nat.one_le_two_pow
      intro x hx
      apply mem_of_subset_of_mem (le_trans (le_trans subset_cball (ball_subset_ball h1N))
        hsmul_le.2) hx.1.1.2.1
  exact hss

-- Lemma 6.3.3
-- p' is 𝔭_ϑ in the blueprint
lemma local_antichain_density {𝔄 : Finset (𝔓 X)} (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X)))
    (ϑ : Θ X) (N : ℕ) {p' : 𝔓 X} (hp' : ϑ ∈ Ω p') :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝔰 p' < 𝔰 p}), volume (E p ∩ G ∩ 𝓘 p') ≤
      volume (E₂ (2 ^ (N + 3)) p') := by
  rw [← MeasureTheory.measure_biUnion_finset _
    (fun _ _ ↦  MeasurableSet.inter (measurableSet_E.inter measurableSet_G) coeGrid_measurable)]
  · apply measure_mono
    simp only [ Finset.mem_filter, iUnion_subset_iff, and_imp]
    intro p hp hs
    by_cases h𝓘 : ((𝓘 p' : Set X) ∩ ↑(𝓘 p)).Nonempty
    · exact Ep_inter_G_inter_Ip'_subset_E2 ϑ N hp hp' hs h𝓘
    · rw [not_nonempty_iff_eq_empty] at h𝓘
      have hemp : (𝓘 p' : Set X) ∩ E p = ∅ :=
        eq_empty_of_subset_empty (h𝓘 ▸ inter_subset_inter_right _
          (sep_subset ↑(𝓘 p) fun x ↦ Q x ∈ Ω p ∧ 𝔰 p ∈ Icc (σ₁ x) (σ₂ x)))
      rw [inter_comm, ← inter_assoc, hemp, empty_inter]
      exact empty_subset _
  · simp only [Finset.coe_filter]
    intro q hq q' hq' hqq'
    simp only [𝔄_aux, Finset.mem_filter, mem_setOf_eq] at hq hq'
    have hE : E q ∩ E q' = ⊥ := by
      rw [bot_eq_empty]
      contrapose! hqq'
      exact E_disjoint h𝔄 hq.1.1 hq'.1.1  hqq'
    simp only [disjoint_iff, eq_bot_iff]
    rw [← hE]
    simp only [inf_eq_inter, le_eq_subset, subset_inter_iff]
    constructor
    · simp only [inter_assoc, inter_subset_left]
    · rw [inter_comm]
      simp only [inter_assoc, inter_subset_left]

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
