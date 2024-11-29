import Carleson.Antichain.AntichainOperator

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ENNReal NNReal ShortVariables

open MeasureTheory Metric Set

namespace Antichain

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

-- Lemma 6.3.1
-- hp is eq. 6.3.1, hp' is eq. 6.3.2.
lemma tile_reach (ha : 4 ≤ a) {ϑ : Θ X} {N : ℕ} {p p' : 𝔓 X} (hp : dist_(p) (𝒬 p) ϑ ≤ 2^N)
    (hp' : dist_(p') (𝒬 p') ϑ ≤ 2^N) (hI : 𝓘 p ≤ 𝓘 p') (hs : 𝔰 p < 𝔰 p') :
    smul (2^(N + 2)) p ≤ smul (2^(N + 2)) p' := by
  -- 6.3.4
  have hp2 : dist_(p) ϑ (𝒬 p') ≤ 2^N := by
    rw [dist_comm]
    exact le_trans (Grid.dist_mono hI) hp'
  -- 6.3.5
  have hp'2 : dist_(p) (𝒬 p) (𝒬 p') ≤ 2^(N + 1) :=
    calc dist_(p) (𝒬 p) (𝒬 p')
      _ ≤ dist_(p) (𝒬 p) ϑ + dist_(p) ϑ (𝒬 p') := dist_triangle _ _ _
      _ ≤ 2^N + 2^N := add_le_add hp hp2
      _ = 2^(N + 1) := by ring
  -- Start proof of 6.3.3.
  simp only [TileLike.le_def, smul_fst, smul_snd]
  refine ⟨hI, fun o' ho' ↦ ?_⟩ -- o' is ϑ' in blueprint, ho' is 6.3.6.
  -- 6.3.7
  have hlt : dist_{𝔠 p', 8 * D^𝔰 p'} (𝒬 p') o' < 2^(5*a + N + 2) := by
    have hle : dist_{𝔠 p', 8 * D^𝔰 p'} (𝒬 p') o' ≤ (defaultA a) ^ 5 * dist_(p') (𝒬 p') o' := by
      have hpos : (0 : ℝ) < D^𝔰 p'/4 := by
        rw [div_eq_mul_one_div, mul_comm]
        apply mul_defaultD_pow_pos _ (by linarith)
      have h8 : (8 : ℝ) * D^𝔰 p' = 2^5 * (D^𝔰 p'/4) := by ring
      rw [h8]
      exact cdist_le_iterate hpos (𝒬 p') o' 5
    apply lt_of_le_of_lt hle
    simp only [defaultA, add_assoc]
    rw [pow_add, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm a, dist_comm]
    gcongr
    exact ho'
  -- 6.3.8
  have hin : 𝔠 p ∈ ball (𝔠 p') (4 * D^𝔰 p') := Grid_subset_ball (hI.1 Grid.c_mem_Grid)
  -- 6.3.9
  have hball_le : ball (𝔠 p) (4 * D^𝔰 p') ⊆ ball (𝔠 p') (8 * D^𝔰 p') := by
    intro x hx
    rw [mem_ball] at hx hin ⊢
    calc dist x (𝔠 p')
      _ ≤ dist x (𝔠 p)  + dist (𝔠 p) (𝔠 p') := dist_triangle _ _ _
      _ < 4 * ↑D ^ 𝔰 p' + 4 * ↑D ^ 𝔰 p' := add_lt_add hx hin
      _ = 8 * ↑D ^ 𝔰 p' := by ring
  -- 6.3.10
  have hlt2 : dist_{𝔠 p, 4 * D^𝔰 p'} (𝒬 p') o' < 2^(5*a + N + 2) :=
    lt_of_le_of_lt (cdist_mono hball_le) hlt
  -- 6.3.11
  have hlt3 : dist_{𝔠 p, 2^((2 : ℤ) - 5*a^2 - 2*a) * D^𝔰 p'} (𝒬 p') o' < 2^N := by
    have hle : 2 ^ ((5 : ℤ)*a + 2) * dist_{𝔠 p, 2^((2 : ℤ) - 5*a^2 - 2*a) * D^𝔰 p'} (𝒬 p') o' ≤
        dist_{𝔠 p, 4 * D^𝔰 p'} (𝒬 p') o' := by
      have heq : (defaultA a : ℝ) ^ ((5 : ℤ)*a + 2) * 2^((2 : ℤ) - 5*a^2 - 2*a) = 4 := by
        simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_mul]
        rw [← zpow_add₀ two_ne_zero]
        ring_nf
      rw [← heq, mul_assoc]
      exact le_cdist_iterate (by positivity) (𝒬 p') o' (5*a + 2)
    rw [← le_div_iff₀' (by positivity), div_eq_mul_inv, ← zpow_neg, neg_add, ← neg_mul,
      ← sub_eq_add_neg, mul_comm _ ((2 : ℝ) ^ _)] at hle
    calc dist_{𝔠 p, 2^((2 : ℤ) - 5*a^2 - 2*a) * D^𝔰 p'} (𝒬 p') o'
      _ ≤ 2^(-(5 : ℤ)*a - 2) * dist_{𝔠 p, 4 * D^𝔰 p'} (𝒬 p') o' := hle
      _ < 2^(-(5 : ℤ)*a - 2) * 2^(5*a + N + 2) := (mul_lt_mul_left (by positivity)).mpr hlt2
      _ = 2^N := by
        rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
        simp only [Int.reduceNeg, neg_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          sub_add_add_cancel, neg_add_cancel_left, zpow_natCast]
  -- 6.3.12
  have hp'3 : dist_(p) (𝒬 p') o' < 2^N := by
    apply lt_of_le_of_lt (cdist_mono _) hlt3
    gcongr
    rw [div_le_iff₀ (by positivity)]
    rw [mul_comm, ← mul_assoc]
    calc (D : ℝ) ^ 𝔰 p
      _ = 1 * (D : ℝ) ^ 𝔰 p := by rw [one_mul]
      _ ≤ 4 * 2 ^ (2 - 5 * (a : ℤ) ^ 2 - 2 * ↑a) * D * D ^ 𝔰 p := by
        have h4 : (4 : ℝ) = 2^(2 : ℤ) := by ring
        apply mul_le_mul _ (le_refl _) (by positivity) (by positivity)
        · have h12 : (1 : ℝ) ≤ 2 := one_le_two
          simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat]
          rw [h4, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
            ← zpow_zero (2 : ℝ)]
          rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
          gcongr --uses h12
          have : (2 : ℝ)^a = 2^(a : ℤ) := by rw [@zpow_natCast]
          ring_nf
          nlinarith
      _ = (4 * 2 ^ (2 - 5 * (a : ℤ)  ^ 2 - 2 * ↑a)) * (D * D ^ 𝔰 p) := by ring
      _ ≤ 4 * 2 ^ (2 - 5 * (a : ℤ)  ^ 2 - 2 * ↑a) * D ^ 𝔰 p' := by
        have h1D : 1 ≤ (D : ℝ) := one_le_D
        nth_rewrite 1 [mul_le_mul_left (by positivity), ← zpow_one (D : ℝ),
          ← zpow_add₀ (ne_of_gt (defaultD_pos _))]
        gcongr
        rw [add_comm]
        exact hs
  -- 6.3.13 (and 6.3.3.)
  have h34 : (3 : ℝ) < 4 := by linarith
  calc dist_(p) o' (𝒬 p)
    _ = dist_(p) (𝒬 p) o' := by rw [dist_comm]
    _ ≤ dist_(p) (𝒬 p) (𝒬 p') + dist_(p) (𝒬 p') o' := dist_triangle _ _ _
    _ < 2^(N + 1) + 2^N := add_lt_add_of_le_of_lt hp'2 hp'3
    _ < 2^(N + 2) := by ring_nf; gcongr -- uses h34
  -- 6.3.14 -- Not needed


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
lemma Ep_inter_G_inter_Ip'_subset_E2 (ha : 4 ≤ a) {𝔄 : Finset (𝔓 X)} (ϑ : Θ X) (N : ℕ)
    {p p' : 𝔓 X} (hpin : p ∈ (𝔄_aux 𝔄 ϑ N)) (hp' : ϑ ∈ Ω p') (hs : 𝔰 p' < 𝔰 p)
    (h𝓘 : ((𝓘 p' : Set X) ∩ (𝓘 p)).Nonempty) :
    E p ∩ G ∩ ↑(𝓘 p') ⊆ E₂ (2^(N + 3)) p' := by
  have hle : 𝓘 p' ≤ 𝓘 p := ⟨Or.resolve_right (fundamental_dyadic (le_of_lt hs))
    (not_disjoint_iff_nonempty_inter.mpr h𝓘), le_of_lt hs⟩
  -- 6.3.22
  have hϑaux : ϑ ∈ ball_(p') (𝒬 p') 1 := subset_cball hp'
  have hϑin' : dist_(p') (𝒬 p') ϑ < ((2 : ℝ)^(N + 1)) := by
    have h12 : (1 : ℝ) < 2 := one_lt_two
    have h0N : 0 < N + 1 := Nat.zero_lt_succ N
    simp only [mem_ball'] at hϑaux
    apply lt_trans hϑaux
    nth_rewrite 1 [← pow_zero 2]
    gcongr -- uses h12, h0N
  -- 6.3.23
  have hϑin : dist_(p) (𝒬 p) ϑ < ((2 : ℝ)^(N + 1)) := by
    simp only [𝔄_aux, Finset.mem_filter] at hpin
    exact lt_of_lt_of_le (lt_one_add (dist_(p) (𝒬 p) ϑ)) hpin.2.2
  -- 6.3.24
  have hsmul_le : smul (2 ^ (N + 3)) p' ≤ smul (2 ^ (N + 3)) p :=
    tile_reach ha (le_of_lt hϑin') (le_of_lt hϑin) hle hs
  -- NOTE: TileLike.toSet is not a mono.
  -- 6.3.25
  have hss : E p ∩ G ∩ ↑(𝓘 p') ⊆ E₂ (2^(N + 3)) p' := by
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
lemma local_antichain_density (ha : 4 ≤ a) {𝔄 : Finset (𝔓 X)}
    (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X))) (ϑ : Θ X) (N : ℕ) {p' : 𝔓 X} (hp' : ϑ ∈ Ω p') :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝔰 p' < 𝔰 p}), volume (E p ∩ G ∩ 𝓘 p') ≤
      volume (E₂ (2 ^ (N + 3)) p') := by
  rw [← MeasureTheory.measure_biUnion_finset _
    (fun _ _ ↦  MeasurableSet.inter (measurableSet_E.inter measurableSet_G) coeGrid_measurable)]
  · apply measure_mono
    simp only [ Finset.mem_filter, iUnion_subset_iff, and_imp]
    intro p hp hs
    by_cases h𝓘 : ((𝓘 p' : Set X) ∩ ↑(𝓘 p)).Nonempty
    · exact Ep_inter_G_inter_Ip'_subset_E2 ha ϑ N hp hp' hs h𝓘
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
