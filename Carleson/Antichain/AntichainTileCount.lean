import Carleson.TileStructure
import Carleson.HardyLittlewood
import Carleson.Psi

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

open Classical

-- Lemma 6.3.2
lemma stack_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) (L : Grid X) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L}), volume (E p ∩ G) ≤
      2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
  -- 6.3.17
  set 𝔄' : Finset (𝔓 X) := {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L} with 𝔄'_def
  by_cases h𝔄' : 𝔄'.Nonempty
  · -- 6.3.18
    have h_aux : ∀ (p : 𝔓 X) (hp : p ∈ 𝔄'), volume (E p ∩ G) ≤
        2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X) := by
      intro p hp
      calc volume (E p ∩ G)
        _ ≤ volume (E₂ 2 p) := by
          apply measure_mono
          intro x hx
          have hQ : Q x ∈ ball_(p) (𝒬 p) 1 := subset_cball hx.1.2.1
          simp only [E₂, TileLike.toSet, smul_fst, smul_snd, mem_inter_iff, mem_preimage, mem_ball]
          exact ⟨⟨hx.1.1, hx.2⟩, lt_trans hQ one_lt_two⟩
        _ ≤ 2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X) := by
          -- Wow this is messy.
          have hIL : 𝓘 p = L := by
            simp only [𝔄'_def, Finset.mem_filter] at hp
            simp_rw [← hp.2]
          have h2a : ((2 : ℝ≥0∞) ^ a)⁻¹ = 2^(-(a : ℤ)) := by
            rw [← zpow_natCast, ENNReal.zpow_neg two_ne_zero ENNReal.two_ne_top]
          rw [← ENNReal.div_le_iff, ← ENNReal.div_le_iff' (Ne.symm (NeZero.ne' (2 ^ a))),
            ENNReal.div_eq_inv_mul, h2a, dens₁]
          refine le_iSup₂_of_le p hp fun c ↦ ?_
          · intro hc
            have h2c : 2 ^ (-(a : ℤ)) * (volume (E₂ 2 p) / volume (L : Set X)) ≤
                (c : WithTop ℝ≥0) := by
              simp only [← hc]
              refine le_iSup₂_of_le 2 (le_refl _) fun d ↦ ?_
              intro hd
              have h2d : 2 ^ (-(a : ℤ)) * (volume (E₂ 2 p) / volume (L : Set X)) ≤
                  (d : WithTop ℝ≥0)  := by
                rw [← hd]
                gcongr
                · norm_cast
                · refine le_iSup₂_of_le p (mem_lowerClosure.mpr ⟨p, hp, le_refl _⟩) fun r hr ↦ ?_
                  have h2r : (volume (E₂ 2 p) / volume (L : Set X)) ≤ (r : WithTop ℝ≥0)  := by
                    rw [← hr]
                    refine le_iSup_of_le (le_refl _) ?_
                    gcongr
                    · simp only [NNReal.coe_ofNat, subset_refl]
                    · rw [hIL]
                  exact ENNReal.le_coe_iff.mp h2r
              exact ENNReal.le_coe_iff.mp h2d
            exact ENNReal.le_coe_iff.mp h2c
          · exact Ne.symm (ne_of_beq_false rfl)
          · have hD_pos : 0 < D := by rw [defaultD]; positivity
            rw [← hIL]
            apply ne_of_gt (volume_coeGrid_pos hD_pos)
          · rw [← hIL, ← lt_top_iff_ne_top]
            exact volume_coeGrid_lt_top
    let p : 𝔓 X := h𝔄'.choose
    have hp : p ∈ 𝔄' := h𝔄'.choose_spec
    -- 6.3.19
    have hth : ∃ (Θ' : Finset (Θ X)), Θ'.card ≤ 2^(a*(N+4)) ∧
        ball_(p) ϑ (2^(N+1)) ⊆ ⋃ ϑ' ∈ Θ', ball_(p) ϑ' 0.2 := by
      have hs : ball_(p) ϑ (2^(N+1)) ⊆ ball_(p) ϑ (2^(N+4)*0.2) := sorry
      --TODO: ask
      /- lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
        BallsCoverBalls X (a^k * r) r (n^k) := by-/
      sorry
    obtain ⟨Θ', hΘ'_card, hΘ'_cover⟩ := hth
    have hex : ∀ (p' : 𝔓 X) (hp' : p' ∈ 𝔄'), ∃ (ϑ' : Θ X) (hϑ' : ϑ' ∈ Θ'),
        𝒬 p' ∈ ball_(p) ϑ' 0.2 := by
      intro p' hp'
      have hp'_in : 𝒬 p' ∈ ball_(p) ϑ (2 ^ (N + 1)) := by
        simp only [𝔄'_def, Finset.mem_filter, 𝔄_aux] at hp'
        -- TODO: ask
        sorry
      have hp'_in' := hΘ'_cover hp'_in
      simp only [mem_iUnion] at hp'_in'
      exact hp'_in'
    --6.3.20
    -- TODO: Fix in blueprint (need 3 points for the argument to work)
    have hcap : ∀ (q q' : 𝔓 X) (hq : q ∈ 𝔄') (hq' : q' ∈ 𝔄') (hqq' : q ≠ q') (ϑ' : Θ X)
      (hϑ' : ϑ' ∈ Θ'), ϑ' ∉ ball_(p) (𝒬 q) 0.2 ∩ ball_(p) (𝒬 q') 0.2 := sorry
    have hcard : 𝔄'.card ≤ 2^(a*(N+4)) := by
      -- We only care about the restriction of f to 𝔄'
      set f : 𝔓 X → Θ X := fun q ↦ if hq : q ∈ 𝔄' then (hex q hq).choose else ϑ with hf_def
      refine le_trans (Finset.card_le_card_of_injOn f
        (fun q hq ↦ by simp only [hf_def, dif_pos hq, (hex q hq).choose_spec.1]) ?_) hΘ'_card
      intro q hq q' hq' hf
      simp only [Finset.mem_coe] at hq hq'
      have hfq : f q = (hex q hq).choose := by simp only [hf_def, dif_pos hq]
      have hfq' : f q' = (hex q' hq').choose := by simp only [hf_def, dif_pos hq']
      specialize hcap q q' hq hq'
      contrapose! hcap
      refine ⟨hcap, ⟨(hex q hq).choose, ⟨(hex q hq).choose_spec.1, ?_⟩⟩⟩
      simp only [mem_ball, mem_inter_iff]
      rw [dist_comm (α := WithFunctionDistance (𝔠 p) ((D : ℝ) ^ 𝔰 p / 4)) _ (𝒬 q),
        dist_comm (α := WithFunctionDistance (𝔠 p) ((D : ℝ) ^ 𝔰 p / 4)) _ (𝒬 q')]
      use (hex q hq).choose_spec.2
      rw [← hfq, hf, hfq']
      exact (hex q' hq').choose_spec.2
    --6.3.16
    calc ∑ p ∈ 𝔄', volume (E p ∩ G)
      _ ≤ ∑ p ∈ 𝔄', 2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X) := Finset.sum_le_sum h_aux
      _ = 𝔄'.card * (2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ (a * (N + 5)) * dens₁  (𝔄' : Set (𝔓 X)) * volume (L : Set X) := by
        simp only [← mul_assoc]
        gcongr
        norm_cast
        calc 𝔄'.card * 2 ^ a
          _ ≤ 2 ^ (a * (N + 4)) * 2 ^ a := mul_le_mul_right' hcard _
          _ = 2 ^ (a * (N + 5)) := by ring
      _ ≤ 2 ^ (a * (N + 5)) * dens₁  (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
        have hss : 𝔄' ⊆ 𝔄 :=
          calc 𝔄'
            _ ⊆ 𝔄_aux 𝔄 ϑ N := Finset.filter_subset _ _
            _ ⊆ 𝔄 := Finset.filter_subset _ _
        gcongr
        exact dens₁_mono hss
  · simp only [Finset.not_nonempty_iff_eq_empty] at h𝔄'
    simp only [h𝔄', defaultA, defaultD, defaultκ.eq_1, Finset.sum_empty, zero_le]

-- Lemma 6.3.3
-- p' is 𝔭_ϑ in the blueprint
lemma local_antichain_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) {p' : 𝔓 X} (hp' : ϑ ∈ Ω p') :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝔰 p' < 𝔰 p}), volume (E p ∩ G ∩ 𝓘 p') ≤
      volume (E₂ (2 ^ (N + 3)) p') := by
  sorry

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
