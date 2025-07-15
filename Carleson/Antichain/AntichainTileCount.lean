import Carleson.Antichain.Basic
import Carleson.Calculations

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ENNReal NNReal ShortVariables

open MeasureTheory Metric Set

namespace Antichain

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

-- Lemma 6.3.1
-- hp is eq. 6.3.1, hp' is eq. 6.3.2.
lemma tile_reach {ϑ : Θ X} {N : ℕ} {p p' : 𝔓 X} (hp : dist_(p) (𝒬 p) ϑ ≤ 2 ^ N)
    (hp' : dist_(p') (𝒬 p') ϑ ≤ 2 ^ N) (hI : 𝓘 p ≤ 𝓘 p') (hs : 𝔰 p < 𝔰 p') :
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
        norm_num
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
          ring_nf
          nlinarith only
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

/-- Def 6.3.15. -/
def 𝔄_aux (𝔄 : Set (𝔓 X)) (ϑ : Θ X) (N : ℕ) : Set (𝔓 X) :=
  {p ∈ 𝔄 | 1 + dist_(p) (𝒬 p) ϑ ∈ Ico (2 ^ N) (2 ^ (N + 1))}

open Classical in
lemma pairwiseDisjoint_𝔄_aux {𝔄 : Set (𝔓 X)} {ϑ : Θ X} :
    univ.PairwiseDisjoint (fun N ↦ (𝔄_aux 𝔄 ϑ N).toFinset) := fun i mi j mj hn ↦ by
  change Disjoint (𝔄_aux _ _ _).toFinset ((𝔄_aux _ _ _).toFinset)
  wlog hl : i < j generalizing i j
  · exact (this _ mj _ mi hn.symm (by omega)).symm
  simp_rw [Finset.disjoint_left, 𝔄_aux, mem_toFinset, mem_setOf_eq, not_and, and_imp]
  refine fun p mp md _ ↦ ?_
  rw [mem_Ico, not_and_or, not_le]; left
  exact md.2.trans_le (pow_le_pow_right₀ one_le_two (by omega))

open Classical in
lemma biUnion_𝔄_aux {𝔄 : Set (𝔓 X)} {ϑ : Θ X} :
    ∃ N, (Finset.range N).biUnion (fun N ↦ (𝔄_aux 𝔄 ϑ N).toFinset) = 𝔄.toFinset := by
  rcases 𝔄.eq_empty_or_nonempty with rfl | h𝔄
  · use 0; simp
  let f (p : 𝔓 X) := ⌊Real.logb 2 (1 + dist_(p) (𝒬 p) ϑ)⌋₊
  have h𝔄' : 𝔄.toFinset.Nonempty := Aesop.toFinset_nonempty_of_nonempty h𝔄
  obtain ⟨p₀, mp₀, hp₀⟩ := 𝔄.toFinset.exists_max_image f h𝔄'
  use f p₀ + 1; ext p
  simp only [𝔄_aux, mem_Ico, sep_and, toFinset_inter, toFinset_setOf, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, mem_toFinset]
  refine ⟨fun hp ↦ hp.choose_spec.2.1.1, fun hp ↦ ?_⟩
  simp only [hp, true_and]
  use f p, Nat.lt_add_one_iff.mpr (hp₀ p (mem_toFinset.mpr hp))
  have one_le_y : 1 ≤ 1 + dist_(p) (𝒬 p) ϑ := le_add_of_nonneg_right dist_nonneg
  rw [← Real.rpow_logb zero_lt_two (by norm_num) (zero_lt_one.trans_le one_le_y)]
  simp only [← Real.rpow_natCast]
  exact ⟨Real.rpow_le_rpow_of_exponent_le one_le_two
      (Nat.floor_le (Real.logb_nonneg one_lt_two one_le_y)),
    Real.rpow_lt_rpow_of_exponent_lt one_lt_two (Nat.lt_succ_floor _)⟩

open Metric

open scoped Classical in
-- Lemma 6.3.2
lemma stack_density (𝔄 : Set (𝔓 X)) (ϑ : Θ X) (N : ℕ) (L : Grid X) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N).toFinset | 𝓘 p = L}), volume (E p ∩ G) ≤
      2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
  -- 6.3.17
  set 𝔄' : Set (𝔓 X) := {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L} with 𝔄'_def
  have hI : ∀ {q q' : 𝔓 X} (hq : q ∈ 𝔄') (hq' : q' ∈ 𝔄'), 𝓘 q = 𝓘 q' := fun hq hq' ↦ by
      simp only [𝔄'_def, 𝔄_aux] at hq hq'
      rw [hq.2, hq'.2]
  have heq : ∑ p ∈ (𝔄_aux 𝔄 ϑ N).toFinset with 𝓘 p = L, volume (E p ∩ G) =
      ∑ p ∈ 𝔄'.toFinset, volume (E p ∩ G) := by congr; aesop
  by_cases h𝔄' : 𝔄'.Nonempty
  · -- 6.3.18
    have h_aux : ∀ (p : 𝔓 X) (hp : p ∈ 𝔄'.toFinset), volume (E p ∩ G) ≤
        2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X) := by
      intro p hp
      rw [mem_toFinset] at hp
      calc volume (E p ∩ G)
        _ ≤ volume (E₂ 2 p) := by
          apply measure_mono
          intro x hx
          have hQ : Q x ∈ ball_(p) (𝒬 p) 1 := subset_cball hx.1.2.1
          simp only [E₂, TileLike.toSet, smul_fst, smul_snd, mem_inter_iff, mem_preimage, mem_ball]
          exact ⟨⟨hx.1.1, hx.2⟩, lt_trans hQ one_lt_two⟩
        _ ≤ 2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X) := by
          -- Wow this is messy.
          have hIL : 𝓘 p = L := by simp_rw [← hp.2]
          have h2a : ((2 : ℝ≥0∞) ^ a)⁻¹ = 2^(-(a : ℤ)) := by
            rw [← zpow_natCast, ENNReal.zpow_neg two_ne_zero ENNReal.ofNat_ne_top]
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
                · refine le_iSup₂_of_le p (mem_lowerCubes.mpr ⟨p, hp, le_refl _⟩) fun r hr ↦ ?_
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
      have hs : ball_(p) ϑ (2^(N+1)) ⊆ ball_(p) ϑ (2^(N+4)*0.2) := by
        have hN4 : (2 : ℝ) ^ (N + 4) = 2 ^ (N + 1) * 2 ^ 3 := by ring
        refine ball_subset_ball ?_
        rw [← mul_one ((2 : ℝ)^ (N + 1) ), hN4, mul_assoc,
          mul_le_mul_iff_of_pos_left (by positivity)]
        norm_num
      have hballs : BallsCoverBalls (WithFunctionDistance (𝔠 p) (↑D ^ 𝔰 p / 4)) (2 ^ (N + 4) * 0.2)
        0.2 (defaultA a ^ (N + 4)) := ballsCoverBalls_iterate_nat
      simp only [BallsCoverBalls, coveredByBalls_iff, defaultA, ← pow_mul] at hballs
      obtain ⟨Θ', hΘ'_card, hΘ'_cover⟩ := hballs ϑ
      exact ⟨Θ', hΘ'_card, subset_trans hs hΘ'_cover⟩
    obtain ⟨Θ', hΘ'_card, hΘ'_cover⟩ := hth
    have hex : ∀ (p' : 𝔓 X) (hp' : p' ∈ 𝔄'), ∃ (ϑ' : Θ X) (hϑ' : ϑ' ∈ Θ'),
        𝒬 p' ∈ ball_(p) ϑ' 0.2 := by
      intro p' hp'
      have hp'_in : 𝒬 p' ∈ ball_(p) ϑ (2 ^ (N + 1)) := by
        rw [ball_eq_of_grid_eq (hI hp hp')]
        exact (lt_one_add _).trans hp'.1.2.2
      have hp'_in' := hΘ'_cover hp'_in
      simp only [mem_iUnion] at hp'_in'
      exact hp'_in'
    --6.3.20
    have hcap : ∀ (q q' : 𝔓 X) (hq : q ∈ 𝔄') (hq' : q' ∈ 𝔄') (hqq' : q ≠ q') (ϑ' : Θ X)
        (hϑ' : ϑ' ∈ Θ'), ϑ' ∉ ball_(p) (𝒬 q) (0.2 : ℝ) ∩ ball_(p) (𝒬 q') (0.2 : ℝ) := by
      intro q q' hq hq' hqq' ϑ' hϑ'
      have hdis := disjoint_Ω hqq' (hI hq hq')
      simp only [disjoint_iff, inf_eq_inter, bot_eq_empty] at hdis
      intro hint
      have h5 : (0.2 : ℝ) = 5⁻¹ := by norm_num
      rw [h5] at hint
      have hsub : ϑ' ∈ (Ω q) ∩ (Ω q') :=
        mem_of_subset_of_mem (inter_subset_inter (ball_eq_of_grid_eq (hI hp hq) ▸ cball_subset)
          (ball_eq_of_grid_eq (hI hp hq') ▸ cball_subset)) hint
      rw [hdis] at hsub
      exact hsub
    have hcard : 𝔄'.toFinset.card ≤ 2^(a*(N+4)) := by
      -- We only care about the restriction of f to 𝔄'
      set f : 𝔓 X → Θ X := fun q ↦ if hq : q ∈ 𝔄' then (hex q hq).choose else ϑ with hf_def
      refine (Finset.card_le_card_of_injOn f (fun q hq ↦ ?_) ?_).trans hΘ'_card
      · simp_rw [hf_def, dif_pos (mem_toFinset.mp hq)]
        exact (hex q (mem_toFinset.mp hq)).choose_spec.1
      intro q hq q' hq' hf
      simp only [coe_toFinset] at hq hq'
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
    calc ∑ p ∈ (𝔄_aux 𝔄 ϑ N).toFinset with 𝓘 p = L, volume (E p ∩ G)
      _ = ∑ p ∈ 𝔄'.toFinset, volume (E p ∩ G) := heq
      _ ≤ ∑ p ∈ 𝔄'.toFinset, 2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X) :=
        Finset.sum_le_sum h_aux
      _ = 𝔄'.toFinset.card * (2^a * dens₁ (𝔄' : Set (𝔓 X)) * volume (L : Set X)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ (a * (N + 5)) * dens₁  (𝔄' : Set (𝔓 X)) * volume (L : Set X) := by
        simp only [← mul_assoc]
        gcongr
        norm_cast
        calc 𝔄'.toFinset.card * 2 ^ a
          _ ≤ 2 ^ (a * (N + 4)) * 2 ^ a := mul_le_mul_right' hcard _
          _ = 2 ^ (a * (N + 5)) := by ring
      _ ≤ 2 ^ (a * (N + 5)) * dens₁  (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
        have hss : 𝔄' ⊆ 𝔄 := by
          calc 𝔄'
            _ ⊆ 𝔄_aux 𝔄 ϑ N := sep_subset _ _
            _ ⊆ 𝔄 := sep_subset _ _
        gcongr
        exact dens₁_mono hss
  · simp only [Set.not_nonempty_iff_eq_empty] at h𝔄'
    simp only [heq, h𝔄', toFinset_empty, Finset.sum_empty, zero_le]

-- We prove inclusion 6.3.24 for every `p ∈ (𝔄_aux 𝔄 ϑ N)` with `𝔰 p' < 𝔰 p` such that
-- `(𝓘 p : Set X) ∩ (𝓘 p') ≠ ∅`.
-- p' is 𝔭_ϑ in the blueprint
open Classical in
lemma Ep_inter_G_inter_Ip'_subset_E2 {𝔄 : Set (𝔓 X)} (ϑ : Θ X) (N : ℕ)
    {p p' : 𝔓 X} (hpin : p ∈ (𝔄_aux 𝔄 ϑ N).toFinset)
    (hp' : ϑ ∈ ball_(p') (𝒬 p') (2 ^ (N + 1))) (hs : 𝔰 p' < 𝔰 p)
    (h𝓘 : ((𝓘 p' : Set X) ∩ (𝓘 p)).Nonempty) :
    E p ∩ G ∩ ↑(𝓘 p') ⊆ E₂ (2^(N + 3)) p' := by
  have hle : 𝓘 p' ≤ 𝓘 p := ⟨Or.resolve_right (fundamental_dyadic (le_of_lt hs))
    (not_disjoint_iff_nonempty_inter.mpr h𝓘), le_of_lt hs⟩
  -- 6.3.22
  have hϑin : dist_(p) (𝒬 p) ϑ < ((2 : ℝ)^(N + 1)) := by
    simp only [𝔄_aux, mem_Ico, sep_and, toFinset_inter, toFinset_setOf, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and] at hpin
    exact (lt_one_add (dist_(p) (𝒬 p) ϑ)).trans hpin.2.2
  -- 6.3.24
  have hsmul_le : smul (2 ^ (N + 3)) p' ≤ smul (2 ^ (N + 3)) p :=
    tile_reach (le_of_lt (mem_ball'.mpr hp')) (le_of_lt hϑin) hle hs
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
open Classical in
lemma local_antichain_density {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (ϑ : Θ X) (N : ℕ)
    {p' : 𝔓 X} (hp' : ϑ ∈ ball_(p') (𝒬 p') (2 ^ (N + 1))) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N).toFinset | 𝔰 p' < 𝔰 p}), volume (E p ∩ G ∩ 𝓘 p') ≤
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
    simp only [𝔄_aux, mem_Ico, sep_and, toFinset_inter,
      toFinset_setOf, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_setOf_eq] at hq hq'
    have hE : Disjoint (E q) (E q') := by simpa using (E_disjoint h𝔄 hq.1.1.1 hq'.1.1.1).mt hqq'
    change Disjoint (_ ∩ _ ∩ _) (_ ∩ _ ∩ _)
    rw [inter_assoc, inter_assoc]; exact (hE.inter_right _).inter_left _

/-- The constant appearing in Lemma 6.3.4. -/
def C6_3_4 (a N : ℕ) : ℝ≥0 := 2^(101*a^3 + N*a)

/-- Auxiliary constant for Lemma 6.3.4. -/
def C6_3_4' (a N : ℕ) : ℝ≥0 :=
  (((2 : ℝ≥0)^(a * (N + 5)) + 2^(a * N + a * 3)) * 2 ^ (100*a^3 + 5*a))

variable (𝔄 : Set (𝔓 X)) (ϑ : range (Q (X := X))) (N : ℕ)

/-- The set `𝔄'` defined in Lemma 6.3.4. -/
def 𝔄' : Set (𝔓 X) := {p ∈ 𝔄_aux 𝔄 ϑ N | ((𝓘 p : Set X) ∩ G) ≠ ∅ ∧ 𝔰 p > -S}

/-- The set `𝔄_-S` defined in Lemma 6.3.4. -/
def 𝔄_min : Set (𝔓 X) := {p ∈ 𝔄_aux 𝔄 ϑ N | ((𝓘 p : Set X) ∩ G) ≠ ∅ ∧ 𝔰 p = -S}

open Classical in
private lemma 𝔄_aux_sum_splits :
    ∑ p ∈ (𝔄_aux 𝔄 ϑ N).toFinset, volume (E p ∩ G) =
      ∑ p ∈ (𝔄' 𝔄 ϑ N).toFinset, volume (E p ∩ G) +
      ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G) := by
  rw [← Finset.sum_union]
  · have hss : (𝔄' 𝔄 ϑ N).toFinset ∪ (𝔄_min 𝔄 ϑ N).toFinset ⊆ (𝔄_aux 𝔄 ϑ N).toFinset := by
      simp only [subset_toFinset, Finset.coe_union, coe_toFinset, union_subset_iff]
      exact ⟨sep_subset _ _, sep_subset _ _⟩
    rw [Finset.sum_subset hss]
    intro p hp hp'
    have hem : ((𝓘 p : Set X) ∩ G) = ∅ := by
      simp only [Finset.mem_union, mem_toFinset, not_or] at hp'
      by_contra h
      by_cases hs : 𝔰 p = -S
      · have h' : p ∈ 𝔄_min 𝔄 ϑ N := by
          simp only [𝔄_min, mem_setOf_eq]; use mem_toFinset.mp hp
        exact hp'.2 h'
      · have h' : p ∈ 𝔄' 𝔄 ϑ N := ⟨mem_toFinset.mp hp, h,
          lt_of_le_of_ne (range_s_subset (X := X) (mem_range_self (𝓘 p))).1 (Ne.symm hs)⟩
        exact hp'.1 h'
    have : E p ∩ G  = ∅ := by rw [← subset_empty_iff, ← hem]; gcongr; exact fun _ hx ↦ hx.1
    exact this ▸ OuterMeasureClass.measure_empty volume
  · by_contra h
    simp only [disjoint_toFinset, not_disjoint_iff, 𝔄', 𝔄_min] at h
    obtain ⟨p, hp', hpmin⟩ := h
    exact (ne_of_gt hp'.2.2) hpmin.2.2

/-- The set `𝓛_-S` defined in Lemma 6.3.4. -/
def 𝓛_min : Set (Grid X) := {I : Grid X | ∃ (p : 𝔄_min 𝔄 ϑ N), I = 𝓘 (p : 𝔓 X)}

-- Ineq 6.3.26
open Classical in
private lemma 𝔄_min_sum_le :
    ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G) ≤
      2 ^ (a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
  calc ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G)
    _ = ∑ L ∈ (𝓛_min 𝔄 ϑ N).toFinset,
          ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N).toFinset | 𝓘 p = L}), volume (E p ∩ G) := by
      rw [Finset.sum_comm' (t' := (𝔄_min 𝔄 ϑ N).toFinset)
        (s' := fun p ↦ {L ∈ (𝓛_min 𝔄 ϑ N).toFinset | 𝓘 p = L})]
      · apply Finset.sum_congr rfl
        intro p hp
        have h1 : {L ∈ (𝓛_min 𝔄 ϑ N).toFinset | 𝓘 p = L}.card = 1 := by
          rw [Finset.card_eq_one]
          use 𝓘 p
          rw [Finset.eq_singleton_iff_unique_mem]
          simp only [𝓛_min, Subtype.exists, exists_prop, toFinset_setOf, Finset.mem_filter,
            Finset.mem_univ, true_and, and_true]
          exact ⟨⟨p, (mem_toFinset.mp hp), rfl⟩, fun _ hL ↦ hL.2.symm⟩
        simp only [Finset.sum_const, h1, one_smul]
      · intro L p
        refine ⟨fun ⟨hL, hp⟩ ↦ ?_, fun ⟨hL, hp⟩ ↦ ?_⟩
        · simp only [𝔄_min, mem_setOf_eq, mem_toFinset,Finset.mem_filter] at hL hp ⊢
          use ⟨hL, hp.2⟩, hp.1
          simp only [𝓛_min, Subtype.exists, exists_prop, mem_setOf_eq] at hL
          obtain ⟨p', hp', hpL'⟩ := hL
          simp only [𝔰, hp.2, hpL']
          exact hp'.2
        · simp only [𝔄_min, mem_setOf_eq, mem_toFinset,Finset.mem_filter] at hL hp ⊢
          use hL.1, hp.1, hL.2
    _ ≤ ∑ L ∈ (𝓛_min 𝔄 ϑ N).toFinset, 2 ^ (a * (N + 5)) * dens₁ 𝔄 * volume (L : Set X) := by
      gcongr; apply stack_density
    _ = 2 ^ (a * (N + 5)) * dens₁ 𝔄 * ∑ L ∈ (𝓛_min 𝔄 ϑ N).toFinset, volume (L : Set X) := by
      rw [Finset.mul_sum]
    _ ≤ 2 ^ (a * (N + 5)) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
      gcongr
      rw [← measure_biUnion_finset _ (fun _ _ ↦ coeGrid_measurable)]
      · apply measure_mono
        intro x hx
        simp only [mem_toFinset, mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨L, hL, hLx⟩ := hx
        simp only [𝓛_min, Subtype.exists, exists_prop, mem_setOf_eq] at hL
        obtain ⟨p, hp, hpL⟩ := hL
        use p, hp.1.1, (hpL ▸ hLx)
      · simp only [coe_toFinset, pairwiseDisjoint_iff]
        intro L hL L' hL' h
        simp only [𝓛_min, Subtype.exists, exists_prop, mem_setOf_eq] at hL hL'
        obtain ⟨p, hp, hpL⟩ := hL
        obtain ⟨p', hp', hpL'⟩ := hL'
        have := hp.2.2
        have hs : 𝔰 p = 𝔰 p' := by rw [hp.2.2, hp'.2.2]
        rw [hpL, hpL'] at h ⊢
        exact Or.resolve_right (eq_or_disjoint hs) h.not_disjoint

/-- The set `𝓛` defined in Lemma 6.3.4. -/
def 𝓛 : Set (Grid X) := {I : Grid X | (∃ (p : 𝔄' 𝔄 ϑ N), I ≤ 𝓘 (p : 𝔓 X)) ∧
    (∀ (p : 𝔄' 𝔄 ϑ N), 𝓘 (p : 𝔓 X) ≤ I → 𝔰 (p : 𝔓 X) = - S)}

-- Ineq 6.3.27
lemma I_p_subset_union_L (p : 𝔄' 𝔄 ϑ N) : (𝓘 (p : 𝔓 X) : Set X) ⊆ ⋃ (L ∈ 𝓛 𝔄 ϑ N), L := by
  calc (𝓘 (p : 𝔓 X) : Set X)
    _ ⊆ ⋃ (I ∈ {I : Grid X | s I = -S ∧ I ≤ 𝓘 (p : 𝔓 X)}), I := by
      intro x hx
      -- Apply 2.0.7
      obtain ⟨I, hI, hxI⟩ := Grid.exists_containing_subcube (i := 𝓘 (p : 𝔓 X)) (-S)
        (by simp [mem_Icc, le_refl, scale_mem_Icc.1]) hx
      have hsI : s I ≤ s (𝓘 (p : 𝔓 X)) := hI ▸ scale_mem_Icc.1
      simp only [Grid.le_def, mem_setOf_eq, mem_iUnion, exists_prop]
      exact ⟨I, ⟨hI, Or.resolve_right (GridStructure.fundamental_dyadic' hsI)
        (not_disjoint_iff.mpr ⟨x, hxI, hx⟩), hsI⟩, hxI⟩
    _ ⊆ ⋃ (L ∈ 𝓛 𝔄 ϑ N), L := by
      intro x hx
      simp only [mem_iUnion] at hx ⊢
      obtain ⟨I, ⟨hsI, hI⟩, hxI⟩ := hx
      simp only [𝓛, Subtype.exists, exists_prop, Subtype.forall]
      exact ⟨I, ⟨⟨p, p.2, hI⟩, fun _ _ hqI ↦ le_antisymm (hsI ▸ hqI.2) scale_mem_Icc.1⟩, hxI⟩

-- Ineq 6.3.28
lemma union_L_eq_union_I_p : ⋃ (L ∈ 𝓛 𝔄 ϑ N), L = ⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 (p : 𝔓 X) : Set X) := by
  apply le_antisymm
  · intro _ hx
    simp only [mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨L, hL, hLx⟩ := hx
    obtain ⟨q, hqL⟩ := hL.1
    exact ⟨q, q.2, hqL.1 hLx⟩
  · intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨q, hq, hq'⟩ := hx
    exact I_p_subset_union_L 𝔄 ϑ N ⟨q, hq⟩ hq'

/-- The set `𝓛*` defined in Lemma 6.3.4. -/
def 𝓛' : Set (Grid X) := {I : Grid X | Maximal (· ∈ 𝓛 𝔄 ϑ N) I}

open Classical in
lemma pairwiseDisjoint_𝓛' :
    ((𝓛' 𝔄 ϑ N).toFinset : Set (Grid X)).PairwiseDisjoint (fun I ↦ (I : Set X)) :=
  fun I mI J mJ hn ↦ by
    have : IsAntichain (· ≤ ·) (𝓛' 𝔄 ϑ N : Set (Grid X)) := setOf_maximal_antichain _
    exact (le_or_ge_or_disjoint.resolve_left
        (this (mem_toFinset.mp mI) (mem_toFinset.mp mJ) hn)).resolve_left
      (this (mem_toFinset.mp mJ) (mem_toFinset.mp mI) hn.symm)

-- Equality 6.3.29
lemma union_L'_eq_union_I_p : ⋃ (L ∈ 𝓛' 𝔄 ϑ N), L = ⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 (p : 𝔓 X) : Set X) := by
  classical
  rw [← union_L_eq_union_I_p]
  apply le_antisymm
  · simp only [le_eq_subset, iUnion_subset_iff, 𝓛']
    exact fun _ hL ↦ subset_biUnion_of_mem hL.1
  intro x hx
  simp only [mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨L, hL, hLx⟩ := hx
  obtain ⟨M, lM, maxM⟩ := (𝓛 𝔄 ϑ N).toFinset.exists_le_maximal (mem_toFinset.mpr hL)
  refine ⟨M, ?_, lM.1 hLx⟩
  simpa [𝓛', mem_setOf_eq, mem_toFinset] using maxM

variable {𝔄 ϑ N}

private lemma exists_p'_ge_L {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ∃ (p : 𝔄' 𝔄 ϑ N), L ≤ 𝓘 (p : 𝔓 X) := hL.1.1

variable (𝔄 ϑ N) in private def SL (L : Grid X) : Set (𝔓 X) :=
  {p : 𝔓 X | p ∈ 𝔄' 𝔄 ϑ N ∧ L ≤ 𝓘 (p : 𝔓 X)}

open Classical in
private lemma SL_nonempty {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    (SL 𝔄 ϑ N L).toFinset.Nonempty := by
  use (exists_p'_ge_L hL).choose
  simp only [mem_toFinset, SL, mem_setOf_eq, (exists_p'_ge_L hL).choose_spec, and_true,
    Subtype.coe_prop]

open Classical in
/-- `p'` in the blueprint. -/
private def p' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : 𝔓 X :=
  (Finset.exists_minimalFor 𝔰 (SL 𝔄 ϑ N L).toFinset (SL_nonempty hL)).choose

open Classical in
private lemma p'_mem {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    p' hL ∈ (SL 𝔄 ϑ N L).toFinset :=
  ((Finset.exists_minimalFor 𝔰 (SL 𝔄 ϑ N L).toFinset (SL_nonempty hL)).choose_spec).1

private lemma L_le_I_p' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    L ≤ 𝓘 (p' hL : 𝔓 X) := by
  have hp' := p'_mem hL
  simp only [SL, mem_setOf_eq, mem_toFinset] at hp'
  exact hp'.2

private lemma not_I_p'_le_L {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : ¬ 𝓘 (p' hL) ≤ L := by
  classical
  have hL' : L ∈ 𝓛 𝔄 ϑ N  := hL.1
  simp only [𝓛] at hL'
  have hp' : p' hL ∈ (SL 𝔄 ϑ N L).toFinset :=
    (Finset.exists_minimalFor 𝔰 (SL 𝔄 ϑ N L).toFinset (SL_nonempty hL)).choose_spec.1
  simp only [Grid.le_def, Antichain.SL, SL] at hp'
  simp only [sep_and, toFinset_inter, toFinset_setOf, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp'
  by_cases hIqL : 𝓘 (p' hL) ≤ L
  · simp only [Subtype.forall, mem_setOf_eq] at hL'
    exact absurd (hL'.2 (p' hL) hp'.1.1 hIqL) (ne_of_gt (hp'.1.1.2.2))
  · exact hIqL

private lemma s_L_le_s_p' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : s L < 𝔰 (p' hL) := by
    have hp'L := not_I_p'_le_L hL
    have hp' := p'_mem hL
    simp only [SL, Grid.le_def, sep_and, mem_setOf_eq,
      mem_toFinset, mem_inter_iff] at hp'
    have := hp'.1.2
    by_contra! h
    have h' : ¬ Disjoint (𝓘 (p' hL) : Set X) ↑L := by
      rw [Set.not_disjoint_iff_nonempty_inter, inter_eq_right.mpr hp'.1.2]
      exact Grid.nonempty L
    exact hp'L (Or.resolve_right (le_or_disjoint h) h')

lemma exists_larger_grid {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ∃ (L' : Grid X), L ≤ L' ∧ s L' = s L + 1 := by
  classical
  obtain ⟨p, hp⟩ : ∃ (p : 𝔄' 𝔄 ϑ N), L ≤ 𝓘 (p : 𝔓 X) := exists_p'_ge_L hL
  set SL : Finset (𝔓 X) := (SL 𝔄 ϑ N L).toFinset with SL_def
  have hSL : SL.Nonempty := SL_nonempty hL
  set q := p' hL
  have hq' : q ∈ SL := ((Finset.exists_minimalFor 𝔰 SL (SL_nonempty hL)).choose_spec).1
  simp only [defaultA, defaultD.eq_1, defaultκ.eq_1, Grid.le_def, Antichain.SL, SL] at hq'
  have hqL : ¬ 𝓘 q ≤ L := not_I_p'_le_L hL
  simp only [Grid.le_def, not_and_or, not_le] at hqL
  have : s L < 𝔰 q  := s_L_le_s_p' hL
  have hS : s L < s topCube (X := X) := by
    conv_rhs => simp only [s, s_topCube]
    exact lt_of_lt_of_le this scale_mem_Icc.2
  exact Grid.exists_scale_succ (X := X) hS

/-- The `L'` introduced in the proof of Lemma 6.3.4. -/
def L' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : Grid X := (exists_larger_grid hL).choose

lemma L_le_L' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : L ≤ L' hL :=
  (exists_larger_grid hL).choose_spec.1

lemma s_L'_eq {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : s (L' hL) = s L + 1 :=
  (exists_larger_grid hL).choose_spec.2

lemma c_L_mem {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : c L ∈ L' hL :=
    (L_le_L' hL).1 Grid.c_mem_Grid

private lemma L'_not_mem {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : ¬ L' hL ∈ 𝓛 𝔄 ϑ N := by
  have hL2 := hL
  by_contra h
  have := hL2.2 h (L_le_L' hL)
  simp [Grid.le_def, s_L'_eq] at this

private lemma L'_le_I_p' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : L' hL ≤ 𝓘 (p' hL : 𝔓 X) := by
  have hle : s (L' hL) ≤ s (𝓘 (p' hL)) := by rw [s_L'_eq]; exact s_L_le_s_p' hL
  have hpL : (𝓘 (p' hL) : Set X) ∩ L ≠ ∅ := by
    rw [inter_eq_self_of_subset_right (L_le_I_p' hL).1, ← Set.nonempty_iff_ne_empty]
    exact Grid.nonempty L
  have := le_or_disjoint hle
  apply Or.resolve_right this
  rw [disjoint_iff]
  simp only [ne_eq, ← nonempty_iff_ne_empty, bot_eq_empty] at hpL ⊢
  obtain ⟨x, ⟨hxp, hxL⟩⟩ := hpL
  use x, (L_le_L' hL).1 hxL

private lemma exists_p''_le_L' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ∃ (p : 𝔓 X), p ∈ 𝔄' 𝔄 ϑ N ∧ 𝓘 p ≤ L' hL := by
  let p' := p' hL
  have hp'_mem := p'_mem hL
  simp only [SL, mem_setOf_eq, mem_toFinset] at hp'_mem
  have hex : ∃ p' ∈ 𝔄' 𝔄 ϑ N, L' hL ≤ 𝓘 p' := ⟨p', hp'_mem.1, L'_le_I_p' hL⟩
  have hL' : ¬ L' hL ∈ 𝓛 𝔄 ϑ N := L'_not_mem hL
  simp only [𝓛, Subtype.exists, exists_prop, Subtype.forall, mem_setOf_eq, not_and_or] at hL'
  have := Or.neg_resolve_left hL' hex
  simp only [not_forall] at this
  obtain ⟨p, ⟨hp_mem, ⟨hp_le, hp⟩⟩⟩ := this
  use p

/-- p'' in the blueprint -/
def p'' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : 𝔓 X := (exists_p''_le_L' hL).choose

lemma p''_mem {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : p'' hL ∈ 𝔄' 𝔄 ϑ N :=
  (exists_p''_le_L' hL).choose_spec.1

lemma I_p''_le_L' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : 𝓘 (p'' hL) ≤ L' hL :=
  (exists_p''_le_L' hL).choose_spec.2

private lemma exists_pΘ_eq_L' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ∃! (p : 𝔓 X), 𝓘 p = L' hL ∧ ϑ.val ∈ Ω p := by
  have hu := biUnion_Ω (i := L' hL) ϑ.prop
  obtain ⟨q, qin, qΩ⟩ := mem_iUnion₂.mp hu
  simp only [mem_preimage, mem_singleton_iff] at qin
  use q, ⟨qin, qΩ⟩
  intro p hp
  by_contra h
  rw [← qin] at hp
  have := disjoint_Ω h hp.1
  rw [disjoint_iff, bot_eq_empty] at this
  have hne : Ω p ⊓ Ω q ≠ ∅ := by
    rw [← nonempty_iff_ne_empty]
    use ϑ, hp.2
  exact hne this

/-- p_Θ in the blueprint -/
def pΘ {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : 𝔓 X := by
  classical
  exact if 𝓘 (p'' hL) = L' hL then p'' hL else (exists_pΘ_eq_L' hL).choose

lemma I_pΘ_eq_L' {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) : 𝓘 (pΘ hL) = L' hL := by
  simp only [pΘ]
  split_ifs with h
  · exact h
  · exact (exists_pΘ_eq_L' hL).choose_spec.1.1

lemma theta_mem_Omega_pΘ {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) (h : ¬ 𝓘 (p'' hL) = L' hL) :
    ϑ.val ∈ Ω (pΘ hL)  := by
  simp only [pΘ, if_neg h]
  exact (exists_pΘ_eq_L' hL).choose_spec.1.2

lemma pΘ_unique {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) (h : ¬ 𝓘 (p'' hL) = L' hL) :
    ∀ (y : 𝔓 X), (fun p ↦ 𝓘 p = L' hL ∧ ↑ϑ ∈ Ω p) y → y = (pΘ hL) := by
  simp only [pΘ, if_neg h]
  exact (exists_pΘ_eq_L' hL).choose_spec.2

-- Eq. 6.3.35
private lemma eq_6_3_35 {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ϑ.val ∈ ball_(p'' hL) (𝒬 (p'' hL)) (2 ^ (N + 1)) := by
  have hp'' := p''_mem hL
  simp only [𝔄', 𝔄_aux, mem_Ico, sep_and, mem_inter_iff, mem_setOf_eq, ne_eq] at hp''
  apply lt_trans _ hp''.1.2.2
  rw [dist_comm (α := WithFunctionDistance _ _)]
  exact lt_one_add _

-- Eq. 6.3.37
private lemma eq_6_3_37 {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ϑ.val ∈ ball_(pΘ hL) (𝒬 (pΘ hL)) (2 ^ (N + 1)) := by
  simp only [pΘ]
  split_ifs with h
  · convert eq_6_3_35 hL <;> rw [if_pos h]
  · have h1 : (1 : ℝ) ≤ (2 ^ (N + 1)) := by exact_mod_cast Nat.one_le_two_pow
    apply ball_subset_ball (α := WithFunctionDistance _ _) h1
    convert subset_cball (theta_mem_Omega_pΘ hL h)
    simp only [pΘ, if_neg h]

-- Ineq. 6.3.36
private lemma ineq_6_3_36 {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    smul (2^(N + 3)) (p'' hL) ≤ smul (2^(N + 3)) (pΘ hL) := by
  by_cases heq : 𝓘 (p'' hL) = L' hL
  · have heq' : p'' hL = pΘ hL := by simp only [pΘ, if_pos heq]
    rw [heq']
  · -- Eq. 6.3.37
    have hpθ : ϑ.val ∈ ball_(pΘ hL) (𝒬 (pΘ hL)) (2 ^ (N + 1)) := eq_6_3_37 hL
    have hp'' : ϑ.val ∈ ball_(p'' hL) (𝒬 (p'' hL)) (2 ^ (N + 1)) := eq_6_3_35 hL
    simp only [mem_ball] at hpθ hp''
    rw [dist_comm (α := WithFunctionDistance _ _)] at hpθ hp''
    apply tile_reach (le_of_lt hp'') (le_of_lt hpθ)
    · rw [I_pΘ_eq_L']; exact I_p''_le_L' hL
    · simp only [𝔰, I_pΘ_eq_L']
      exact (Grid.lt_def.mp (lt_of_le_of_ne (I_p''_le_L' hL) heq)).2

-- Ineq. 6.3.38
private lemma ineq_6_3_38 {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    volume (E₂ (2 ^ (N + 3)) (pΘ hL)) ≤
      2 ^ (a * N + a * 3) * (dens₁ (𝔄 : Set (𝔓 X)) * volume (L' hL : Set X)) := by
  have h2 : (2 : ℝ≥0∞) ^ (a * N + a * 3) = (2 ^ (N + 3) : ℝ≥0) ^ a := by
    norm_cast; rw [← pow_mul]; ring
  rw [← I_pΘ_eq_L', h2, ← mul_assoc]
  apply volume_E₂_le_dens₁_mul_volume (𝔓' := 𝔄) (p' := p'' hL) (p := pΘ hL)
    (l := 2 ^ (N + 3)) _ (p''_mem hL).1.1 _ (ineq_6_3_36 hL)
  · simp only [lowerCubes, mem_setOf_eq]
    have hL2 := hL
    refine ⟨p' hL, ?_, I_pΘ_eq_L' hL ▸ L'_le_I_p' hL⟩
    have := (p'_mem hL)
    simp only [SL, 𝔄', 𝔄_aux, mem_setOf_eq, mem_toFinset] at this
    exact this.1.1.1
  · exact_mod_cast Nat.le_self_pow (by linarith) 2

-- Ineq. 6.3.39
open Classical in
private lemma ineq_6_3_39 (h𝔄 : IsAntichain (· ≤ ·) 𝔄) {L : Grid X}
    (hL : L ∈ 𝓛' 𝔄 ϑ N) : ∑ p ∈ 𝔄' 𝔄 ϑ N with ¬𝓘 p = L' hL, volume (E p ∩ G ∩ L) ≤
      volume (E₂ (2 ^ (N + 3)) (pΘ hL)) := by
  apply le_trans _ (local_antichain_density h𝔄 ϑ N (eq_6_3_37 hL))
  calc ∑ p ∈ (𝔄' 𝔄 ϑ N).toFinset with ¬𝓘 p = L' hL, volume (E p ∩ G ∩ ↑L)
    _ ≤ ∑ p ∈ (𝔄' 𝔄 ϑ N).toFinset with 𝔰 (pΘ hL) < 𝔰 p, volume (E p ∩ G ∩ ↑(𝓘 (pΘ hL))) := by
      simp only [Finset.sum_filter, ite_not]
      gcongr
      rename_i p hp
      by_cases hpL : (L : Set X) ∩ (𝓘 p) = ∅ -- Nonempty when p contributes to the sum.
      · have : E p ∩ G ∩ L = ∅ := by
          refine subset_empty_iff.mp ?_
          simp only [← hpL, inter_comm ↑L (𝓘 p : Set X), E]
          gcongr
          exact fun _ hx ↦ hx.1.1
        simp only [this, measure_empty, ite_self, zero_le]
      · have hL2 := hL
        simp only [𝓛', Maximal, 𝓛, Grid.le_def,
          Subtype.exists, exists_and_left, exists_prop, and_imp, Subtype.forall, mem_setOf_eq,
          forall_exists_index] at hL2
        by_cases hp' : 𝓘 p = L' hL
        · simp [if_pos hp']
        · have hs : 𝔰 (pΘ hL) < 𝔰 p := by
            have hpL' : (L' hL : Set X)  ∩ (𝓘 p : Set X) ≠ ∅ := by
              simp only [← Set.nonempty_iff_ne_empty] at hpL ⊢
              obtain ⟨x, ⟨hxL, hxp⟩⟩ := hpL
              use x, (L_le_L' hL).1 hxL, hxp
            have hss : L ≤ 𝓘 p := by
              rcases le_or_ge_or_disjoint (i := L) (j := 𝓘 p) with (hle | (hge | hdisj))
              · exact hle
              · exact absurd (hL2.1.2 p (mem_toFinset.mp hp) hge.1 hge.2)
                  (ne_of_gt (mem_toFinset.mp hp).2.2)
              · exact absurd (disjoint_iff_inter_eq_empty.mp hdisj) hpL
            have hne : L ≠ 𝓘 p := by
              by_contra h
              have := hL2.1.2 p (mem_toFinset.mp hp) (h ▸ le_refl _) (h ▸ le_refl _)
              exact (ne_of_gt (mem_toFinset.mp hp).2.2)
                (hL2.1.2 p (mem_toFinset.mp hp) (h ▸ le_refl _) (h ▸ le_refl _))
            have hlt : s L < 𝔰 p := by
              by_contra! h
              have := le_or_disjoint h
              simp only [disjoint_iff] at this
              rw [inter_comm] at hpL
              exact hne (le_antisymm hss (Or.resolve_right this hpL))
            have hle : s (L' hL) ≤ 𝔰 p := by rw [s_L'_eq]; linarith
            have hss' : (L' hL : Set X) ⊆ 𝓘 p := by
              have := le_or_disjoint hle
              simp only [disjoint_iff] at this
              exact (Or.resolve_right this hpL').1
            simp only [𝔰, I_pΘ_eq_L' hL]
            apply lt_of_le_of_ne hle
            by_contra hs
            have heq : L' hL = 𝓘 p := by
              have := eq_or_disjoint hs
              simp only [disjoint_iff] at this
              simp [Or.resolve_right this hpL']
            exact hp' heq.symm
          rw [if_neg hp', if_pos hs]
          gcongr
          exact I_pΘ_eq_L' hL ▸ (L_le_L' hL).1
    _ ≤ ∑ p ∈ (𝔄_aux 𝔄 ϑ N).toFinset with 𝔰 (pΘ hL) < 𝔰 p, volume (E p ∩ G ∩ ↑(𝓘 (pΘ hL))) := by
      gcongr; simp only [𝔄']
      exact sep_subset _ _

-- Copied from`ForestOperator.LargeSeparation`, where it is called
-- `IF_subset_THEN_distance_between_centers`.
-- **TODO**: move to common import.
private lemma dist_c_le_of_subset {J J' : Grid X} (subset : (J : Set X) ⊆ J') :
    dist (c J) (c J') < 4 * D ^ s J' :=
  Grid_subset_ball (subset Grid.c_mem_Grid)

-- Ineq. 6.3.41
private lemma volume_L'_le {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    volume (L' hL : Set X) ≤ 2 ^ (100*a^3 + 5*a) * volume (L : Set X) := by
  have hc : dist (c L) (c (L' hL)) + 4 * D ^ s (L' hL) ≤ 8 * D ^ s (L' hL) := by
    calc dist (c L) (c (L' hL)) + 4 * D ^ s (L' hL)
      _ ≤ 4 * ↑D ^ s (L' hL) + 4 * D ^ s (L' hL) := by grw [dist_c_le_of_subset (L_le_L' hL).1]
      _ ≤ 8 * ↑D ^ s (L' hL) := by linarith
  calc volume (L' hL : Set X)
    _ ≤ volume (ball (c (L' hL)) (4 * D ^ s (L' hL))) := by
      gcongr; exact Grid_subset_ball
    _ ≤ volume (ball (c L) (8 * D ^ s (L' hL))) := by
      gcongr; exact ball_subset_ball_of_le hc
    _ = volume (ball (c L) ((32 * D) * (D ^ (s L))/4)) := by
      rw [s_L'_eq hL, zpow_add₀ (by simp), zpow_one]
      ring_nf
    _ = volume (ball (c L) ((2^(100*a^2 + 5)) * ((D ^ (s L))/4))) := by
      have h32 : (32 : ℝ) = (2^5 : ℕ) := by norm_num
      congr; simp only [defaultD, h32]; norm_cast; ring_nf
    _ ≤ 2 ^ (100*a^3 + 5*a) * volume (ball (c L) ((D ^ (s L))/4)) := by
      have : (2 : ℝ≥0∞) ^ (100*a^3 + 5*a) = (defaultA a)^(100*a^2 + 5) := by
        simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
        ring
      rw [this]
      exact DoublingMeasure.volume_ball_two_le_same_repeat (c L) ((D ^ (s L))/4)
        (100 * a ^ 2 + 5)
    _ ≤ 2 ^ (100*a^3 + 5*a) * volume (L : Set X) := by gcongr; exact ball_subset_Grid

-- Ineq. 6.3.30
open Classical in
lemma global_antichain_density_aux (h𝔄 : IsAntichain (· ≤ ·) 𝔄) {L : Grid X}
    (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ∑ (p ∈ 𝔄' 𝔄 ϑ N), volume (E p ∩ G ∩ L) ≤
      (C6_3_4' a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
  classical
  calc ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G ∩ ↑L)
    -- Express LHS as 6.3.31 + 6.3.32.
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N with 𝓘 p = L' hL, volume (E p ∩ G ∩ ↑L) +
        ∑ p ∈ 𝔄' 𝔄 ϑ N with ¬𝓘 p = L' hL, volume (E p ∩ G ∩ ↑L) := by
      rw [← (Finset.sum_filter_add_sum_filter_not (𝔄' 𝔄 ϑ N).toFinset (fun x ↦ 𝓘 x = L' hL) fun x ↦
        volume (E x ∩ G ∩ ↑L))]
    -- Apply ineq. 6.3.33 : Estimate 6.3.31 with Lemma 6.3.2.
    _ ≤ 2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L' hL : Set X) +
        ∑ p ∈ 𝔄' 𝔄 ϑ N with ¬𝓘 p = L' hL, volume (E p ∩ G ∩ ↑L) := by
      gcongr
      calc ∑ p ∈ 𝔄' 𝔄 ϑ N with 𝓘 p = L' hL, volume (E p ∩ G ∩ ↑L)
        _ ≤ ∑ p ∈ 𝔄' 𝔄 ϑ N with 𝓘 p = L' hL, volume (E p ∩ G) :=
          Finset.sum_le_sum (fun _ _ ↦ OuterMeasureClass.measure_mono volume inter_subset_left)
        _ ≤ ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N).toFinset | 𝓘 p = L' hL}), volume (E p ∩ G) := by
          gcongr
          intro _ hp
          simp only [𝔄', ne_eq] at hp
          exact hp.1
        _ ≤ 2 ^ (a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L' hL : Set X) :=
          stack_density 𝔄 ϑ N (L' hL)
    -- Apply ineq. 6.3.39: estimate 6.3.32.
    _ ≤ 2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L' hL : Set X) +
        volume (E₂ (2 ^ (N + 3)) (pΘ hL)) := by grw [ineq_6_3_39 h𝔄 hL]
    -- Ineq. 6.3.40, using 6.3.38
    _ ≤ (2^(a * (N + 5)) + 2^(a * N + a * 3)) * dens₁ (𝔄 : Set (𝔓 X)) *
        volume (L' hL : Set X) := by
      conv_rhs => rw [mul_assoc]
      rw [add_mul, ← mul_assoc]
      gcongr
      exact ineq_6_3_38 hL
    _ ≤ (2^(a * (N + 5)) + 2^(a * N + a * 3)) * dens₁ (𝔄 : Set (𝔓 X)) *
        2 ^ (100*a^3 + 5*a) * volume (L : Set X) := by
      grw [mul_assoc _ (2 ^ (100*a^3 + 5*a))  _, volume_L'_le hL]
    _ = ((2^(a * (N + 5)) + 2^(a * N + a * 3)) * 2 ^ (100*a^3 + 5*a)) * dens₁ (𝔄 : Set (𝔓 X)) *
        volume (L : Set X) := by ring
    _ = ↑(C6_3_4' a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by rfl

variable (𝔄 ϑ N)

open Classical in
private lemma volume_union_I_p_eq_sum :
    volume (⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 p : Set X)) = ∑ (L ∈ 𝓛' 𝔄 ϑ N), volume (L : Set X) := by
  rw [← union_L'_eq_union_I_p 𝔄 ϑ N]
  convert MeasureTheory.measure_biUnion_finset (pairwiseDisjoint_𝓛' 𝔄 ϑ N)
    (fun _ _ ↦ coeGrid_measurable)
  ext
  rw [mem_toFinset]

open Classical in
private lemma lhs' : ∑ (p ∈ (𝔄' 𝔄 ϑ N).toFinset), volume (E p ∩ G) =
    (∑ (L ∈ (𝓛' 𝔄 ϑ N).toFinset), ∑ (p ∈ (𝔄' 𝔄 ϑ N).toFinset), volume (E p ∩ G ∩ L)) := by
  calc ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G)
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G ∩ (⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 (p : 𝔓 X) : Set X))) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      rw [eq_comm, inter_eq_left]
      intro _ hx
      simp only [mem_iUnion]
      use p, mem_toFinset.mp hp, hx.1.1
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G ∩ (⋃ (L ∈ 𝓛' 𝔄 ϑ N), L)) := by rw [union_L'_eq_union_I_p]
    _ = ∑ p ∈ (𝔄' 𝔄 ϑ N), volume (⋃ (L ∈ (𝓛' 𝔄 ϑ N).toFinset), E p ∩ G ∩ L):= by
        congr; ext p; simp_rw [inter_iUnion₂, mem_toFinset]
    _ = ∑ p ∈ (𝔄' 𝔄 ϑ N), ∑ L ∈ (𝓛' 𝔄 ϑ N).toFinset, volume (E p ∩ G ∩ ↑L) := by
      congr
      ext p
      -- Note that both measurability and fun_prop fail here.
      apply MeasureTheory.measure_biUnion_finset ?_
        (fun _ _ ↦ (measurableSet_E.inter measurableSet_G).inter coeGrid_measurable)
      have hdist := pairwiseDisjoint_𝓛' 𝔄 ϑ N
      rw [pairwiseDisjoint_iff] at hdist ⊢
      intro L hL M hM hLM
      apply hdist hL hM
      simp only [Set.Nonempty, mem_inter_iff] at hLM ⊢
      obtain ⟨x, hxL, hxM⟩ := hLM
      exact ⟨x, hxL.2, hxM.2⟩
    _ = ∑ L ∈ 𝓛' 𝔄 ϑ N, ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G ∩ ↑L) := Finset.sum_comm

open Classical in
private lemma lhs : ∑ (p ∈ (𝔄_aux 𝔄 ϑ N).toFinset), volume (E p ∩ G) =
    (∑ (L ∈ (𝓛' 𝔄 ϑ N).toFinset), ∑ (p ∈ (𝔄' 𝔄 ϑ N).toFinset), volume (E p ∩ G ∩ L)) +
    ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G) := by
  calc ∑ p ∈ (𝔄_aux 𝔄 (↑ϑ) N).toFinset, volume (E p ∩ G)
    _ = ∑ p ∈ (𝔄' 𝔄 ϑ N).toFinset, volume (E p ∩ G) +
          ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G) := by rw [𝔄_aux_sum_splits]
    _ = ∑ L ∈ (𝓛' 𝔄 ϑ N).toFinset, ∑ p ∈ (𝔄' 𝔄 ϑ N).toFinset, volume (E p ∩ G ∩ ↑L) +
          ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G) := by rw [lhs']

private lemma le_C6_3_4 (ha : 4 ≤ a) :
    (((2 : ℝ≥0∞) ^ (a * (N + 5)) + 2 ^ (a * N + a * 3)) * 2 ^ (100 * a ^ 3 + 5 * a)) +
      2 ^ (a * (N + 5)) ≤ (C6_3_4 a N) := by
  calc ((2 : ℝ≥0∞) ^ (a * (N + 5)) + 2 ^ (a * N + a * 3)) * 2 ^ (100 * a ^ 3 + 5 * a) +
      2 ^ (a * (N + 5))
    _ ≤ (2^(a * N + a * 5) + 2^(a * N + a * 5)) * 2 ^ (100*a^3 + 5*a) + 2 ^ (a * N + a* 5) * 1 := by
      have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
      have h35 : 3 ≤ 5 := by omega
      gcongr <;> apply le_of_eq <;> ring
    _ = 2^(a * N + a * 5) * (2 * 2 ^ (100*a^3 + 5*a)) + 2 ^ (a * N + a* 5) * 1 := by
      rw [← two_mul]; ring
    _ = 2^(a * N + a * 5) * (2 * 2 ^ (100*a^3 + 5*a) + 1) := by ring
    _ ≤ 2^(a * N + a * 5) * (2^2 * 2 ^ (100*a^3 + 5*a)) := by
      gcongr
      norm_cast
      rw [pow_two, mul_assoc 2 2]
      conv_rhs => rw [two_mul]
      gcongr
      exact NeZero.one_le
    _ = 2^(100*a^3 + a * N + a * 10 + 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ ↑(C6_3_4 a N) := by
      have h101 : 101 * a ^ 3 = 100 * a ^ 3 +  a ^ 3 := by ring
      have ha3 : a ^ 3 = a * (a^2 - 1) + a := by
        simp only [mul_tsub, mul_one]
        rw [tsub_add_cancel_of_le]
        · ring
        · nth_rewrite 1 [← mul_one a]
          have ha' : 1 ≤ a^1 := by linarith
          gcongr
          apply le_trans ha' (Nat.pow_le_pow_right (by linarith) one_le_two)
      rw [C6_3_4]
      norm_cast
      apply pow_le_pow (le_refl _) one_le_two
      rw [add_assoc, add_assoc, add_comm (a * N), ← add_assoc, ← add_assoc, mul_comm N]
      gcongr
      rw [add_assoc, h101]
      nth_rewrite 3 [ha3]
      gcongr
      · calc 10
        _ ≤ 4^2 - 1 := by norm_num
        _ ≤ a ^ 2 - 1 := by gcongr
      · linarith

-- Lemma 6.3.4
open Classical in
lemma global_antichain_density {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (ϑ : range Q) (N : ℕ) :
    ∑ p ∈ (𝔄_aux 𝔄 ϑ.val N).toFinset, volume (E p ∩ G) ≤
      C6_3_4 a N * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
  rw [lhs]
  calc ∑ L ∈ (𝓛' 𝔄 ϑ N).toFinset, ∑ p ∈ (𝔄' 𝔄 ϑ N).toFinset, volume (E p ∩ G ∩ ↑L) +
          ∑ p ∈ (𝔄_min 𝔄 ϑ N).toFinset, volume (E p ∩ G)
    _ ≤ ∑ L ∈ (𝓛' 𝔄 ϑ N).toFinset, ↑(C6_3_4' a N) * dens₁ 𝔄 * volume (L : Set X) +
        2 ^ (a * (N + 5)) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) :=
        add_le_add (Finset.sum_le_sum (fun L (hL : L ∈ (𝓛' 𝔄 ϑ N).toFinset) ↦
          global_antichain_density_aux h𝔄 (mem_toFinset.mp hL))) (𝔄_min_sum_le _ _ _)
    _ = ↑(C6_3_4'  a N) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄' 𝔄 ϑ N, (𝓘 p : Set X)) +
        2 ^ (a * (N + 5)) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
      rw [volume_union_I_p_eq_sum 𝔄 ϑ N, Finset.mul_sum]
    _ ≤ ↑(C6_3_4'  a N) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) +
        2 ^ (a * (N + 5)) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
      gcongr
      apply iUnion_subset_iUnion_const
      simp only [𝔄', 𝔄_aux]
      exact fun h ↦ h.1.1
    _ ≤ ↑(C6_3_4 a N) * dens₁ 𝔄 * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
      simp only [mul_assoc, ← add_mul]
      gcongr
      simp only [C6_3_4', ENNReal.coe_pow, ENNReal.coe_ofNat, C6_3_4]
      exact le_C6_3_4 N (four_le_a X)

/-- `p` in Lemma 6.1.6. We append a subscript `₆` to keep `p` available for tiles. -/
def p₆ (a : ℕ) : ℝ := 4 * a ^ 4

/-- `p'` in the proof of Lemma 6.1.4, the Hölder conjugate exponent of `p₆`. -/
def q₆ (a : ℕ) : ℝ := (1 - (p₆ a)⁻¹)⁻¹

lemma p₆_ge_1024 (a4 : 4 ≤ a) : 1024 ≤ p₆ a := by
  unfold p₆; norm_cast
  calc
    _ = 4 * 4 ^ 4 := by norm_num
    _ ≤ _ := by gcongr

lemma one_lt_p₆ (a4 : 4 ≤ a) : 1 < p₆ a :=
  lt_of_lt_of_le (by norm_num) (p₆_ge_1024 a4)

lemma p₆_pos (a4 : 4 ≤ a) : 0 < p₆ a :=
  lt_of_lt_of_le (by norm_num) (p₆_ge_1024 a4)

lemma holderConjugate_p₆ (a4 : 4 ≤ a) : (p₆ a).HolderConjugate (q₆ a) := by
  rw [Real.holderConjugate_iff_eq_conjExponent (one_lt_p₆ a4), q₆, inv_eq_iff_eq_inv, inv_div,
    sub_div, one_div, div_self (zero_lt_one.trans (one_lt_p₆ a4)).ne']

lemma q₆_le_superparticular (a4 : 4 ≤ a) : q₆ a ≤ 1024 / 1023 := by
  have pil : (p₆ a)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact .inr (one_lt_p₆ a4)
  rw [q₆, show (1024 : ℝ) / 1023 = (1 - 1024⁻¹)⁻¹ by norm_num,
    inv_le_inv₀ (by linarith) (by norm_num), sub_le_sub_iff_left,
    inv_le_inv₀ (p₆_pos a4) (by norm_num)]
  exact p₆_ge_1024 a4

lemma one_lt_q₆ (a4 : 4 ≤ a) : 1 < q₆ a := by
  have := (holderConjugate_p₆ a4).symm
  rw [Real.holderConjugate_iff] at this; exact this.1

lemma q₆_pos (a4 : 4 ≤ a) : 0 < q₆ a :=
  zero_lt_one.trans (one_lt_q₆ a4)

/-- A very involved bound needed for Lemma 6.1.4. -/
lemma C2_0_6_q₆_le (a4 : 4 ≤ a) : C2_0_6 (defaultA a) (q₆ a).toNNReal 2 ≤ 2 ^ (a + 2) := by
  rw [C2_0_6, Real.coe_toNNReal _ (q₆_pos a4).le]
  nth_rw 1 [show (2 : ℝ≥0) = (2 : ℝ).toNNReal by simp]
  rw [← Real.toNNReal_div zero_le_two, CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  simp_rw [ENNReal.top_ne_one, ENNReal.one_lt_top, lt_self_iff_false, ite_true, ite_false,
    ENNReal.coe_one, ENNReal.one_rpow, zero_mul, add_zero, NNReal.coe_one, one_mul, mul_one,
    ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_one]
  have dvg1 : 1 < 2 / q₆ a :=
    (one_lt_div (q₆_pos a4)).mpr ((q₆_le_superparticular a4).trans_lt (by norm_num))
  have dvpos : 0 < 2 / q₆ a := zero_lt_one.trans dvg1
  have ipos : 0 < (2 / q₆ a - 1)⁻¹ := by rwa [inv_pos, sub_pos]
  rw [Real.coe_toNNReal _ dvpos.le, abs_of_nonneg (by rw [sub_nonneg]; exact dvg1.le),
    ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_rpow_of_pos dvpos, ← ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_rpow_of_pos (by rwa [inv_pos, sub_pos]),
    ← ENNReal.ofReal_mul' (Real.rpow_nonneg ipos.le _)]
  have Acast : ENNReal.ofNNReal (defaultA a ^ 2) = ENNReal.ofReal (2 ^ (a * 2)) := by
    simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat, ENNReal.coe_pow, ENNReal.coe_ofNat]
    norm_cast; rw [pow_mul]
  rw [Acast, ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_mul' (by positivity),
    mul_assoc, ← Real.mul_rpow ipos.le (by positivity), ← ENNReal.toNNReal_rpow,
    mul_assoc, ← Real.mul_rpow dvpos.le (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity)]
  have RHScast : (2 : ℝ≥0) ^ (a + 2) = (ENNReal.ofReal (2 ^ (a + 2))).toNNReal := by
    rw [ENNReal.ofReal_pow zero_le_two, ENNReal.toNNReal_pow]; norm_cast
  rw [RHScast]; refine ENNReal.toNNReal_mono (by finiteness) (ENNReal.ofReal_le_ofReal ?_)
  -- Now everything is in `ℝ`
  calc
    _ = (2 * (2 / (2 - q₆ a) * 2 ^ (a * 2)) ^ (2 / q₆ a)⁻¹) ^ (q₆ a)⁻¹ := by
      rw [← mul_assoc]; congr 4
      rw [← div_eq_mul_inv, div_div, mul_sub_one, mul_div_cancel₀ _ (q₆_pos a4).ne']
    _ ≤ (2 * (2 ^ ((1 + a) * 2)) ^ (2 / q₆ a)⁻¹) ^ (q₆ a)⁻¹ := by
      have : 0 < 2 / (2 - q₆ a) := by
        apply div_pos zero_lt_two; rw [sub_pos]
        exact (q₆_le_superparticular a4).trans_lt (by norm_num)
      rw [one_add_mul, pow_add]; gcongr
      · rw [inv_nonneg]; exact (q₆_pos a4).le
      · rw [sq, ← div_inv_eq_mul]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        rw [le_sub_comm]; exact (q₆_le_superparticular a4).trans (by norm_num)
    _ = 2 ^ (q₆ a)⁻¹ * 2 ^ (1 + a) := by
      rw [Real.mul_rpow zero_le_two (by positivity), ← Real.rpow_mul (by positivity), inv_div,
        ← div_eq_mul_inv, div_div_cancel_left' (q₆_pos a4).ne', pow_mul, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity), show (2 : ℕ) * 2⁻¹ = (1 : ℝ) by norm_num, Real.rpow_one]
    _ ≤ _ := by
      rw [pow_succ', add_comm]; gcongr
      apply Real.rpow_le_self_of_one_le one_le_two
      rw [inv_le_one_iff₀]; right; exact (one_lt_q₆ a4).le

open Classical in
lemma tile_count_aux {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (ϑ : range (Q (X := X)))
    {n : ℕ} : eLpNorm (fun x ↦ ∑ p ∈ 𝔄_aux 𝔄 ϑ n, (2 : ℝ) ^ (-n * (2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
      (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume ≤
    (2 ^ (101 * a ^ 3 - n : ℝ)) ^ (p₆ a)⁻¹ * dens₁ 𝔄 ^ (p₆ a)⁻¹ *
    volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) ^ (p₆ a)⁻¹ := by
  have a4 := four_le_a X
  have p₆p := p₆_pos a4
  have p₆c : ENNReal.ofReal (p₆ a) = ↑(p₆ a).toNNReal := by norm_cast
  rw [← ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < (p₆ a).toNNReal by simpa), p₆c,
    eLpNorm_nnreal_pow_eq_lintegral (by simpa), Real.coe_toNNReal _ p₆p.le,
    ENNReal.mul_rpow_of_nonneg _ _ p₆p.le, ENNReal.mul_rpow_of_nonneg _ _ p₆p.le]
  iterate 3 rw [← ENNReal.rpow_mul, inv_mul_cancel₀ p₆p.ne', ENNReal.rpow_one]
  calc
    _ = ∫⁻ x, ∑ p ∈ 𝔄_aux 𝔄 ϑ n,
        ((2 : ℝ≥0∞) ^ (-n * (2 * a ^ 2 + a ^ 3 : ℝ)⁻¹)) ^ (4 * a ^ 4) *
        (E p).indicator 1 x * G.indicator 1 x := by
      congr! 2 with x; rw [← Real.enorm_rpow_of_nonneg _ p₆p.le, p₆]; swap
      · refine Finset.sum_nonneg fun p mp ↦ mul_nonneg ?_ (indicator_nonneg (by simp) _)
        exact mul_nonneg (Real.rpow_nonneg zero_le_two _) (indicator_nonneg (by simp) _)
      conv_lhs => enter [1, 2]; norm_cast
      have p₆p' : 1 ≤ 4 * a ^ 4 := by rw [p₆] at p₆p; norm_cast at p₆p
      rw [Real.rpow_natCast, Finset.pow_sum_comm _ p₆p']; swap
      · intro i mi j mj hn
        rw [mul_assoc (2 ^ _), ← inter_indicator_mul, mul_assoc _ _ (G.indicator 1 x),
          ← inter_indicator_mul, mul_mul_mul_comm, ← inter_indicator_mul, inter_inter_inter_comm]
        simp only [𝔄_aux, mem_Ico, sep_and, toFinset_inter, toFinset_setOf, Finset.mem_inter,
          Finset.mem_filter, Finset.mem_univ, true_and] at mi mj
        have key := (E_disjoint h𝔄 mi.1.1 mj.1.1).mt hn
        rw [not_not, disjoint_iff_inter_eq_empty] at key; simp [key]
      rw [ENNReal.enorm_sum_eq_sum_enorm]; swap
      · refine fun p mp ↦ pow_nonneg (mul_nonneg ?_ (indicator_nonneg (by simp) _)) _
        exact mul_nonneg (Real.rpow_nonneg zero_le_two _) (indicator_nonneg (by simp) _)
      simp_rw [enorm_pow, enorm_mul, mul_pow]
      have an0 : a ≠ 0 := by omega
      congr! 3 with p mp
      · rw [Real.rpow_mul zero_le_two, ENNReal.rpow_mul,
          Real.enorm_rpow_of_nonneg (by positivity) (by positivity), Real.rpow_neg zero_le_two,
          enorm_inv (by positivity), Real.enorm_rpow_of_nonneg zero_le_two n.cast_nonneg,
          ENNReal.rpow_neg, Real.enorm_eq_ofReal zero_le_two, ENNReal.ofReal_ofNat]
      · unfold indicator; split_ifs <;> simp [an0]
      · unfold indicator; split_ifs <;> simp [an0]
    _ = ((2 : ℝ≥0∞) ^ (-n * (2 * a ^ 2 + a ^ 3 : ℝ)⁻¹)) ^ (4 * a ^ 4) *
        ∑ p ∈ 𝔄_aux 𝔄 ϑ n, volume (E p ∩ G) := by
      have meg {p : 𝔓 X} : MeasurableSet (E p ∩ G) := measurableSet_E.inter measurableSet_G
      conv_lhs =>
        enter [2, x, 2, p]; rw [mul_assoc, ← inter_indicator_mul, ← indicator_const_mul]
        simp only [Pi.one_apply, mul_one]
      rw [lintegral_finset_sum _ fun _ _ ↦ Measurable.indicator (by simp) meg]
      conv_lhs => enter [2, p]; rw [lintegral_indicator meg, setLIntegral_const]
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ≥0∞) ^ (-(n * a) - n : ℝ) * (C6_3_4 a n * dens₁ 𝔄 *
        volume (⋃ p ∈ 𝔄, (𝓘 p : Set X))) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      gcongr
      · exact one_le_two
      · rw [neg_sub_left, ← mul_one_add, neg_mul, neg_mul, neg_le_neg_iff, mul_assoc]
        gcongr; push_cast
        calc
          _ ≤ 3⁻¹ * (4 * a : ℝ) := by rw [le_inv_mul_iff₀ zero_lt_three]; norm_cast; omega
          _ = (3 * a ^ 3 : ℝ)⁻¹ * (4 * a ^ 4) := by
            rw [pow_succ' _ 3, ← mul_assoc 4, ← div_eq_inv_mul, ← div_eq_inv_mul,
              mul_div_mul_right _ _ (by positivity)]
          _ ≤ _ := by
            rw [show (3 * a ^ 3 : ℝ) = 2 * a ^ 3 + a ^ 3 by ring]; gcongr
            · norm_cast; omega
            · norm_num
      · exact global_antichain_density h𝔄 ϑ n
    _ = _ := by
      simp_rw [← mul_assoc, C6_3_4, ENNReal.coe_pow, ENNReal.coe_ofNat]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      congr 3; push_cast; ring

/-- The constant appearing in Lemma 6.1.6. -/
def C6_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (5 * a)

lemma le_C6_1_6 (a4 : 4 ≤ a) :
    (2 : ℝ≥0∞) ^ (101 * a ^ 3 / p₆ a) * ∑ n ∈ Finset.range N, (2 ^ (-(p₆ a)⁻¹)) ^ n ≤ C6_1_6 a := by
  have p₆p := p₆_pos a4
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (101 * a ^ 3 / p₆ a) * (8 * a ^ 4) := by
      gcongr
      calc
        _ ≤ _ := ENNReal.sum_le_tsum _
        _ = _ := ENNReal.tsum_geometric _
        _ ≤ 2 * (ENNReal.ofReal (p₆ a)⁻¹)⁻¹ := by
          apply near_1_geometric_bound; constructor
          · rw [inv_nonneg]; exact p₆p.le
          · rw [inv_le_one₀ p₆p]; exact (one_lt_p₆ a4).le
        _ = _ := by rw [ENNReal.ofReal_inv_of_pos p₆p, inv_inv, p₆]; norm_cast; ring
    _ ≤ 2 ^ (7 : ℝ) * 2 ^ (2 * a + 3) := by
      gcongr
      · exact one_le_two
      · rw [div_le_iff₀ p₆p, p₆]; norm_cast; rw [show 7 * (4 * a ^ 4) = 28 * a * a ^ 3 by ring]
        gcongr; omega
      · exact_mod_cast calculation_6_1_6 a4
    _ ≤ _ := by
      rw [C6_1_6]; norm_cast; rw [← pow_add]; gcongr
      · exact one_le_two
      · omega

open Classical in
/-- Lemma 6.1.6 -/
lemma tile_count {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (ϑ : range (Q (X := X))) :
    eLpNorm (fun x ↦ ∑ p with p ∈ 𝔄, (1 + edist_(p) (𝒬 p) ϑ.val) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
      (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume ≤
    C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) ^ (p₆ a)⁻¹ := by
  obtain ⟨N, 𝔄_decomp⟩ := biUnion_𝔄_aux (𝔄 := 𝔄) (ϑ := ϑ)
  calc
    _ = eLpNorm (∑ n ∈ Finset.range N, fun x ↦ ∑ p ∈ 𝔄_aux 𝔄 ϑ n,
        (1 + edist_(p) (𝒬 p) ϑ.val) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
        (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume := by
      congr! with x; rw [Finset.sum_apply]
      nth_rw 1 [filter_mem_univ_eq_toFinset, ← 𝔄_decomp,
        Finset.sum_biUnion (pairwiseDisjoint_𝔄_aux.subset (subset_univ _))]
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (fun x ↦ ∑ p ∈ 𝔄_aux 𝔄 ϑ n,
        (1 + edist_(p) (𝒬 p) ϑ.val) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
        (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume := by
      refine eLpNorm_sum_le (fun p mp ↦ ?_) ?_
      · refine Finset.aestronglyMeasurable_sum _ fun p mp ↦ ?_
        simp_rw [mul_assoc, ← inter_indicator_mul]
        exact ((AEMeasurable.indicator (by simp)
          (measurableSet_E.inter measurableSet_G)).const_mul _).aestronglyMeasurable
      · rw [ENNReal.one_le_ofReal]; exact (one_lt_p₆ (four_le_a X)).le
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (fun x ↦ ∑ p ∈ 𝔄_aux 𝔄 ϑ n,
        (2 : ℝ) ^ (-n * (2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
        (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume := by
      refine Finset.sum_le_sum fun n mn ↦ eLpNorm_mono_enorm fun x ↦ ?_
      rw [enorm_eq_self, ENNReal.enorm_sum_eq_sum_enorm]; swap
      · refine fun p mp ↦ mul_nonneg ?_ (indicator_nonneg (by simp) _)
        exact mul_nonneg (Real.rpow_nonneg zero_le_two _) (indicator_nonneg (by simp) _)
      refine Finset.sum_le_sum fun p mp ↦ ?_
      simp_rw [enorm_mul, enorm_indicator_eq_indicator_enorm, Pi.one_apply, enorm_one]; gcongr
      rw [Real.rpow_mul zero_le_two, Real.enorm_rpow_of_nonneg (by positivity) (by positivity),
        ENNReal.rpow_neg, ← ENNReal.inv_rpow]; gcongr
      rw [Real.rpow_neg zero_le_two, enorm_inv (by positivity), ENNReal.inv_le_inv, edist_dist,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one dist_nonneg, Real.rpow_natCast,
        Real.enorm_eq_ofReal (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      simp only [𝔄_aux, mem_toFinset] at mp
      exact mp.2.1
    _ ≤ ∑ n ∈ Finset.range N, (2 ^ (101 * a ^ 3 - n : ℝ)) ^ (p₆ a)⁻¹ * dens₁ 𝔄 ^ (p₆ a)⁻¹ *
        volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) ^ (p₆ a)⁻¹ :=
      Finset.sum_le_sum fun _ _ ↦ tile_count_aux h𝔄 ϑ
    _ = 2 ^ (101 * a ^ 3 / p₆ a) * (∑ n ∈ Finset.range N, (2 ^ (-(p₆ a)⁻¹)) ^ n) *
        dens₁ 𝔄 ^ (p₆ a)⁻¹ * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) ^ (p₆ a)⁻¹ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.mul_sum]; congr! with n mn
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, neg_mul, ← div_eq_inv_mul,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ← sub_eq_add_neg, ← sub_div,
        ← div_eq_mul_inv]
    _ ≤ _ := by gcongr; exact le_C6_1_6 _ (four_le_a X)

end Antichain
