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
lemma tile_reach {ϑ : Θ X} {N : ℕ} {p p' : 𝔓 X} (hp : dist_(p) (𝒬 p) ϑ ≤ 2^N)
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
def 𝔄_aux (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) : Finset (𝔓 X) :=
  {p ∈ 𝔄 | 1 + dist_(p) (𝒬 p) ϑ ∈ Ico (2 ^ N) (2 ^ (N + 1))}

open Classical in
lemma pairwiseDisjoint_𝔄_aux {𝔄 : Finset (𝔓 X)} {ϑ : Θ X} :
    univ.PairwiseDisjoint (𝔄_aux 𝔄 ϑ ·) := fun i mi j mj hn ↦ by
  change Disjoint (𝔄_aux _ _ _) (𝔄_aux _ _ _)
  wlog hl : i < j generalizing i j
  · exact (this _ mj _ mi hn.symm (by omega)).symm
  simp_rw [Finset.disjoint_left, 𝔄_aux, Finset.mem_filter, not_and, and_imp]
  refine fun p mp md _ ↦ ?_
  rw [mem_Ico, not_and_or, not_le]; left
  exact md.2.trans_le (pow_le_pow_right₀ one_le_two (by omega))

open Classical in
lemma biUnion_𝔄_aux {𝔄 : Finset (𝔓 X)} {ϑ : Θ X} :
    ∃ N, (Finset.range N).biUnion (𝔄_aux 𝔄 ϑ ·) = 𝔄 := by
  rcases 𝔄.eq_empty_or_nonempty with rfl | h𝔄
  · use 0; simp
  let f (p : 𝔓 X) := ⌊Real.logb 2 (1 + dist_(p) (𝒬 p) ϑ)⌋₊
  obtain ⟨p₀, mp₀, hp₀⟩ := 𝔄.exists_max_image f h𝔄
  use f p₀ + 1; ext p
  simp_rw [𝔄_aux, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
  constructor <;> intro hp
  · exact hp.choose_spec.2.1
  · simp only [hp, true_and]; use f p, Nat.lt_add_one_iff.mpr (hp₀ p hp)
    have one_le_y : 1 ≤ 1 + dist_(p) (𝒬 p) ϑ := le_add_of_nonneg_right dist_nonneg
    rw [← Real.rpow_logb zero_lt_two (by norm_num) (zero_lt_one.trans_le one_le_y)]
    constructor <;> rw [← Real.rpow_natCast]
    · exact Real.rpow_le_rpow_of_exponent_le one_le_two
        (Nat.floor_le (Real.logb_nonneg one_lt_two one_le_y))
    · exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (Nat.lt_succ_floor _)

open Metric

open scoped Classical in
-- Lemma 6.3.2
lemma stack_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) (L : Grid X) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L}), volume (E p ∩ G) ≤
      2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
  -- 6.3.17
  set 𝔄' : Finset (𝔓 X) := {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L} with 𝔄'_def
  have hI : ∀ {q q' : 𝔓 X} (hq : q ∈ 𝔄') (hq' : q' ∈ 𝔄'), 𝓘 q = 𝓘 q' := fun hq hq' ↦ by
      simp only [𝔄'_def, Finset.mem_filter, 𝔄_aux] at hq hq'
      rw [hq.2, hq'.2]
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
        simp only [𝔄'_def, Finset.mem_filter, 𝔄_aux] at hp'
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

-- We prove inclusion 6.3.25 for every `p ∈ (𝔄_aux 𝔄 ϑ N)` with `𝔰 p' < 𝔰 p` such that
-- `(𝓘 p : Set X) ∩ (𝓘 p') ≠ ∅`.
-- p' is 𝔭_ϑ in the blueprint
lemma Ep_inter_G_inter_Ip'_subset_E2 {𝔄 : Finset (𝔓 X)} (ϑ : Θ X) (N : ℕ)
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
    exact (lt_one_add (dist_(p) (𝒬 p) ϑ)).trans hpin.2.2
  -- 6.3.24
  have hsmul_le : smul (2 ^ (N + 3)) p' ≤ smul (2 ^ (N + 3)) p :=
    tile_reach (le_of_lt hϑin') (le_of_lt hϑin) hle hs
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
lemma local_antichain_density {𝔄 : Finset (𝔓 X)}
    (h𝔄 : IsAntichain (·≤·) (𝔄 : Set (𝔓 X))) (ϑ : Θ X) (N : ℕ) {p' : 𝔓 X} (hp' : ϑ ∈ Ω p') :
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
    have hE : Disjoint (E q) (E q') := by simpa using (E_disjoint h𝔄 hq.1.1 hq'.1.1).mt hqq'
    change Disjoint (_ ∩ _ ∩ _) (_ ∩ _ ∩ _)
    rw [inter_assoc, inter_assoc]; exact (hE.inter_right _).inter_left _

/-- The constant appearing in Lemma 6.3.4. -/
def C6_3_4 (a N : ℕ) : ℝ≥0 := 2^(101*a^3 + N*a)

variable (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ)

/-- The set `𝔄'` defined in Lemma 6.3.4. -/
def 𝔄' : Finset (𝔓 X) := by
  classical
  exact {p ∈ 𝔄_aux 𝔄 ϑ N | ((𝓘 p : Set X) ∩ G) ≠ ∅ }

-- TODO: change ⊆ to ≤ in the blueprint
/-- The set `𝓛` defined in Lemma 6.3.4. -/
def 𝓛 : Finset (Grid X) := by
  classical
  exact {I : Grid X | (∃ (p : 𝔄' 𝔄 ϑ N), I ≤ 𝓘 (p : 𝔓 X)) ∧
    (∀ (p : 𝔄' 𝔄 ϑ N), 𝓘 (p : 𝔓 X) ≤ I → 𝔰 (p : 𝔓 X) = - S)}

-- Ineq 6.3.27
lemma I_p_subset_union_L (p : 𝔄' 𝔄 ϑ N) : (𝓘 (p : 𝔓 X) : Set X) ⊆ ⋃ (L ∈ 𝓛 𝔄 ϑ N), L := by
  calc (𝓘 (p : 𝔓 X) : Set X)
    _ ⊆ ⋃ (I ∈ {I : Grid X | s I = -S ∧ I ≤ 𝓘 (p : 𝔓 X)}), I := by
      intro x hx
      -- Apply 2.0.7
      obtain ⟨I, hI, hxI⟩ := Grid.exists_containing_subcube (i := 𝓘 (p : 𝔓 X)) (-S)
        (by simp [mem_Icc, le_refl, true_and, scale_mem_Icc.1]) hx
      have hsI : s I ≤ s (𝓘 (p : 𝔓 X)) := hI ▸ scale_mem_Icc.1
      simp only [Grid.le_def, mem_setOf_eq, mem_iUnion, exists_prop]
      exact ⟨I, ⟨hI, Or.resolve_right (GridStructure.fundamental_dyadic' hsI)
            (not_disjoint_iff.mpr ⟨x, hxI, hx⟩), hsI⟩, hxI⟩
    _ ⊆ ⋃ (L ∈ 𝓛 𝔄 ϑ N), L := by
      intro x hx
      simp only [Subtype.exists, mem_iUnion] at hx ⊢
      obtain ⟨I, ⟨hsI, hI⟩, hxI⟩ := hx
      simp only [ 𝓛, Subtype.exists, exists_and_left, exists_prop, and_imp, Subtype.forall,
        Finset.mem_filter, Finset.mem_univ,true_and]
      exact ⟨I, ⟨⟨p, p.2, hI⟩, fun _ _ hqI ↦ le_antisymm (hsI ▸ hqI.2) scale_mem_Icc.1⟩, hxI⟩

-- Ineq 6.3.28
lemma union_L_eq_union_I_p : ⋃ (L ∈ 𝓛 𝔄 ϑ N), L = ⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 (p : 𝔓 X) : Set X) := by
  apply le_antisymm
  · intro _ hx
    simp only [iUnion_coe_set, mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨L, hL, hLx⟩ := hx
    simp only [𝓛, and_imp, Subtype.forall, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    obtain ⟨q, hqL⟩ := hL.1
    exact ⟨q, q.2, hqL.1 hLx⟩
  · intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨q, hq, hq'⟩ := hx
    exact I_p_subset_union_L 𝔄 ϑ N ⟨q, hq⟩ hq'

/-- The set `𝓛*` defined in Lemma 6.3.4. -/
def 𝓛' : Finset (Grid X) := by
  classical
  exact {I : Grid X | Maximal (· ∈ 𝓛 𝔄 ϑ N) I}

lemma pairwiseDisjoint_𝓛' : (𝓛' 𝔄 ϑ N : Set (Grid X)).PairwiseDisjoint (fun I ↦ (I : Set X)) :=
  fun I mI J mJ hn ↦ by
    have : IsAntichain (· ≤ ·) (𝓛' 𝔄 ϑ N : Set (Grid X)) := by
      simp only [𝓛', Finset.coe_filter, Finset.mem_univ, true_and]
      exact setOf_maximal_antichain _
    exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

-- Equality 6.3.29
lemma union_L'_eq_union_I_p : ⋃ (L ∈ 𝓛' 𝔄 ϑ N), L = ⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 (p : 𝔓 X) : Set X) := by
  classical
  rw [← union_L_eq_union_I_p]
  apply le_antisymm
  · simp only [le_eq_subset, iUnion_subset_iff, 𝓛', Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ hL ↦ subset_biUnion_of_mem hL.1
  intro x hx
  simp only [mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨L, hL, hLx⟩ := hx
  obtain ⟨M, lM, maxM⟩ := (𝓛 𝔄 ϑ N).exists_le_maximal hL
  refine ⟨M, ?_, lM.1 hLx⟩
  simp only [𝓛', Finset.mem_filter, Finset.mem_univ, true_and]
  exact maxM

-- Ineq. 6.3.30
lemma global_antichain_density_aux {L : Grid X} (hL : L ∈ 𝓛' 𝔄 ϑ N) :
    ∑ (p ∈ 𝔄' 𝔄 ϑ N), volume (E p ∩ G ∩ L) ≤
      (C6_3_4 a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := by
  sorry

private lemma volume_union_I_p_eq_sum :
    volume (⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 p : Set X)) = ∑ (L ∈ 𝓛' 𝔄 ϑ N), volume (L : Set X) := by
  rw [← union_L'_eq_union_I_p 𝔄 ϑ N]
  exact MeasureTheory.measure_biUnion_finset (pairwiseDisjoint_𝓛' 𝔄 ϑ N)
    (fun _ _ ↦ coeGrid_measurable)

private lemma lhs : ∑ (p ∈ 𝔄_aux 𝔄 ϑ N), volume (E p ∩ G) =
    ∑ (L ∈ 𝓛' 𝔄 ϑ N), ∑ (p ∈ 𝔄' 𝔄 ϑ N), volume (E p ∩ G ∩ L) := by
  calc ∑ p ∈ 𝔄_aux 𝔄 ϑ N, volume (E p ∩ G)
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G) := by
      rw [eq_comm]
      apply Finset.sum_subset (by simp [𝔄'])
      intro p hp hp'
      simp only [𝔄', ne_eq, Finset.mem_filter, not_and, not_not] at hp'
      have hemp : E p ∩ G = ∅ := by
        apply eq_empty_of_subset_empty
        rw [← hp' hp]
        gcongr
        exact fun _ hx ↦ hx.1
      rw [hemp, measure_empty]
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G ∩ (⋃ (p ∈ 𝔄' 𝔄 ϑ N), (𝓘 (p : 𝔓 X) : Set X))) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      rw [eq_comm, inter_eq_left]
      intro _ hx
      simp only [mem_iUnion]
      use p, hp, hx.1.1
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (E p ∩ G ∩ (⋃ (L ∈ 𝓛' 𝔄 ϑ N), L)) := by rw [union_L'_eq_union_I_p]
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, volume (⋃ (L ∈ 𝓛' 𝔄 ϑ N), E p ∩ G ∩ L):= by congr; ext p; rw [inter_iUnion₂]
    _ = ∑ p ∈ 𝔄' 𝔄 ϑ N, ∑ L ∈ 𝓛' 𝔄 ϑ N, volume (E p ∩ G ∩ ↑L) := by
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

-- Lemma 6.3.4
lemma global_antichain_density :
    ∑ p ∈ 𝔄_aux 𝔄 ϑ N, volume (E p ∩ G) ≤
    C6_3_4 a N * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
  -- Reduce to ineq 6.3.30
  have hle: ↑(C6_3_4 a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ p ∈ 𝔄' 𝔄 ϑ N, (𝓘 p : Set X)) ≤
      ↑(C6_3_4 a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) := by
    gcongr
    apply iUnion_subset_iUnion_const
    simp only [𝔄', 𝔄_aux, Finset.mem_filter]
    exact fun h ↦ h.1.1
  apply le_trans _ hle
  rw [volume_union_I_p_eq_sum 𝔄 ϑ N, Finset.mul_sum, lhs]
  -- Conclude by Ineq. 6.3.30
  exact Finset.sum_le_sum (fun _ hL ↦ global_antichain_density_aux 𝔄 ϑ N hL)

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
lemma tile_count_aux {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (ϑ : Θ X) {n : ℕ} :
    eLpNorm (fun x ↦ ∑ p ∈ 𝔄_aux 𝔄.toFinset ϑ n, (2 : ℝ) ^ (-n * (2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
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
    _ = ∫⁻ x, ∑ p ∈ 𝔄_aux 𝔄.toFinset ϑ n,
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
        simp_rw [𝔄_aux, mem_Ico, Finset.mem_filter, mem_toFinset] at mi mj
        have key := (E_disjoint h𝔄 mi.1 mj.1).mt hn
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
        ∑ p ∈ 𝔄_aux 𝔄.toFinset ϑ n, volume (E p ∩ G) := by
      have meg {p : 𝔓 X} : MeasurableSet (E p ∩ G) := measurableSet_E.inter measurableSet_G
      conv_lhs =>
        enter [2, x, 2, p]; rw [mul_assoc, ← inter_indicator_mul, ← indicator_const_mul]
        simp only [Pi.one_apply, mul_one]
      rw [lintegral_finset_sum _ fun _ _ ↦ Measurable.indicator (by simp) meg]
      conv_lhs => enter [2, p]; rw [lintegral_indicator meg, setLIntegral_const]
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ≥0∞) ^ (-(n * a) - n : ℝ) * (C6_3_4 a n * dens₁ (𝔄.toFinset : Set (𝔓 X)) *
        volume (⋃ p ∈ 𝔄.toFinset, (𝓘 p : Set X))) := by
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
      · apply global_antichain_density
    _ = _ := by
      simp_rw [coe_toFinset, mem_toFinset, ← mul_assoc, C6_3_4, ENNReal.coe_pow, ENNReal.coe_ofNat]
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
lemma tile_count {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (· ≤ ·) 𝔄) (ϑ : Θ X) :
    eLpNorm (fun x ↦ ∑ p with p ∈ 𝔄, (1 + edist_(p) (𝒬 p) ϑ) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
      (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume ≤
    C6_1_6 a * dens₁ 𝔄 ^ (p₆ a)⁻¹ * volume (⋃ p ∈ 𝔄, (𝓘 p : Set X)) ^ (p₆ a)⁻¹ := by
  have p₆p := p₆_pos (four_le_a X)
  obtain ⟨N, 𝔄_decomp⟩ := biUnion_𝔄_aux (𝔄 := 𝔄.toFinset) (ϑ := ϑ)
  calc
    _ = eLpNorm (∑ n ∈ Finset.range N, fun x ↦ ∑ p ∈ 𝔄_aux 𝔄.toFinset ϑ n,
        (1 + edist_(p) (𝒬 p) ϑ) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
        (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume := by
      congr! with x; rw [Finset.sum_apply]
      nth_rw 1 [filter_mem_univ_eq_toFinset, ← 𝔄_decomp,
        Finset.sum_biUnion (pairwiseDisjoint_𝔄_aux.subset (subset_univ _))]
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (fun x ↦ ∑ p ∈ 𝔄_aux 𝔄.toFinset ϑ n,
        (1 + edist_(p) (𝒬 p) ϑ) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) *
        (E p).indicator 1 x * G.indicator 1 x) (ENNReal.ofReal (p₆ a)) volume := by
      refine eLpNorm_sum_le (fun p mp ↦ ?_) ?_
      · refine Finset.aestronglyMeasurable_sum _ fun p mp ↦ ?_
        simp_rw [mul_assoc, ← inter_indicator_mul]
        exact ((AEMeasurable.indicator (by simp)
          (measurableSet_E.inter measurableSet_G)).const_mul _).aestronglyMeasurable
      · rw [ENNReal.one_le_ofReal]; exact (one_lt_p₆ (four_le_a X)).le
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (fun x ↦ ∑ p ∈ 𝔄_aux 𝔄.toFinset ϑ n,
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
      simp only [𝔄_aux, Finset.mem_filter, mem_toFinset] at mp
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
