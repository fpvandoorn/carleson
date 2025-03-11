import Carleson.ForestOperator.L2Estimate
import Carleson.ToMathlib.BoundedCompactSupport

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.3 and Lemma 7.3.1 -/

/-- The constant used in `local_dens1_tree_bound`.
Has value `2 ^ (101 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_2 (a : ℕ) : ℝ≥0 := 2 ^ (101 * (a : ℝ) ^ 3)

/-- Part 1 of Lemma 7.3.2. -/
lemma local_dens1_tree_bound_exists (hu : u ∈ t) (hL : L ∈ 𝓛 (t u))
    (hp₂ : ∃ p ∈ t u, ¬Disjoint ↑L (E p) ∧ 𝔰 p ≤ s L) :
    volume (L ∩ G ∩ ⋃ p ∈ t u, E p) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) := by
  obtain ⟨p, mp, dp, sp⟩ := hp₂; rw [disjoint_comm] at dp
  replace dp : ¬Disjoint (𝓘 p : Set X) L := by contrapose! dp; exact dp.mono_left E_subset_𝓘
  have lip := le_antisymm (le_of_mem_𝓛 hL mp dp) ((le_or_disjoint sp).resolve_right dp)
  calc
    _ ≤ volume (E₂ 9 p) := by
      refine measure_mono fun x ⟨⟨mxL, mxG⟩, mxU⟩ ↦ ⟨⟨by apply lip ▸ mxL, mxG⟩, ?_⟩
      rw [mem_iUnion₂] at mxU; obtain ⟨q, mq, hq⟩ := mxU; rw [smul_snd, mem_preimage]
      have plq := lip ▸ le_of_mem_𝓛 hL mq (not_disjoint_iff.mpr ⟨x, E_subset_𝓘 hq, mxL⟩)
      simp_rw [mem_ball']
      calc
        _ ≤ dist_(p) (𝒬 p) (𝒬 u) + dist_(p) (𝒬 u) (𝒬 q) + dist_(p) (𝒬 q) (Q x) :=
          dist_triangle4 ..
        _ ≤ dist_(p) (𝒬 p) (𝒬 u) + dist_(q) (𝒬 u) (𝒬 q) + dist_(q) (𝒬 q) (Q x) := by
          gcongr <;> exact Grid.dist_mono plq
        _ < 4 + 4 + 1 := by
          gcongr
          · exact t.dist_lt_four hu mp
          · exact t.dist_lt_four' hu mq
          · rw [← mem_ball']; exact subset_cball hq.2.1
        _ = _ := by norm_num
    _ ≤ 9 ^ a * dens₁ (t u) * volume (L : Set X) := by
      rw [lip]
      exact volume_E₂_le_dens₁_mul_volume (subset_lowerCubes mp) mp (by norm_num) le_rfl
    _ ≤ _ := by
      gcongr; rw [C7_3_2]; norm_cast
      calc
        _ ≤ 2 ^ (4 * a) := by rw [pow_mul]; gcongr; norm_num
        _ ≤ _ := by gcongr; exacts [one_le_two, by norm_num, Nat.le_self_pow three_ne_zero a]

lemma volume_bound_of_Grid_lt {L L' : Grid X} (lL : L ≤ L') (sL : s L' = s L + 1) :
    volume (L' : Set X) ≤ 2 ^ (100 * a ^ 3 + 5 * a) * volume (L : Set X) := by
  suffices volume (ball (c L') (4 * D ^ s L')) ≤
      2 ^ (100 * a ^ 3 + 5 * a) * volume (ball (c L) (D ^ s L / 4)) by
    refine (le_trans ?_ this).trans ?_
    · exact measure_mono Grid_subset_ball
    · gcongr; exact ball_subset_Grid
  have db : dist (c L) (c L') + 4 * D ^ s L' < 2 ^ (100 * a ^ 2 + 5) * (D ^ s L / 4) := by
    calc
      _ < (4 : ℝ) * D ^ s L' + 4 * D ^ s L' := by
        gcongr; rw [← mem_ball]
        exact ((ball_subset_Grid.trans lL.1).trans Grid_subset_ball)
          (mem_ball_self (by unfold defaultD; positivity))
      _ = D * 2 ^ 5 * (D ^ s L / 4) := by
        rw [← add_mul, show (4 : ℝ) + 4 = 2 ^ 5 / 4 by norm_num, sL, zpow_add_one₀ (by simp)]
        ring
      _ = _ := by congr 1; unfold defaultD; norm_cast; rw [pow_add]
  convert measure_ball_le_of_dist_le' (μ := volume) (by simp) db.le
  simp_rw [As, defaultA, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one, Nat.ceil_natCast, ENNReal.coe_pow, ENNReal.coe_ofNat]
  ring

/-- Lemma 7.3.2. -/
lemma local_dens1_tree_bound (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) :
    volume (L ∩ G ∩ ⋃ p ∈ t u, E p) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) := by
  by_cases hq : (L : Set X) ∩ ⋃ p ∈ t u, E p = ∅
  · rw [inter_comm (L : Set X), inter_assoc, hq, inter_empty, measure_empty]; exact zero_le _
  rw [← disjoint_iff_inter_eq_empty, disjoint_iUnion₂_right] at hq; push_neg at hq
  by_cases hp₂ : ∃ p ∈ t u, ¬Disjoint (L : Set X) (E p) ∧ 𝔰 p ≤ s L
  · exact local_dens1_tree_bound_exists hu hL hp₂
  push_neg at hp₂; obtain ⟨p, mp, hp⟩ := hq; have sLp := hp₂ p mp hp
  have lip : L < 𝓘 p := by
    refine Grid.lt_def.mpr ⟨(le_of_mem_𝓛 hL mp ?_).1, sLp⟩
    contrapose! hp; exact (hp.mono_left E_subset_𝓘).symm
  obtain ⟨L', lL', sL'⟩ := Grid.exists_scale_succ sLp
  replace lL' : L < L' := Grid.lt_def.mpr ⟨lL'.1, by omega⟩
  obtain ⟨p'', mp'', lp''⟩ : ∃ p'' ∈ t u, 𝓘 p'' ≤ L' := by
    have L'nm : L' ∉ 𝓛₀ (t u) := by
      by_contra h
      simp_rw [𝓛, mem_setOf, maximal_iff] at hL
      exact lL'.ne (hL.2 h lL'.le)
    rw [𝓛₀, mem_setOf, not_or, not_and_or] at L'nm; push_neg at L'nm
    have nfa : ¬∀ p ∈ t u, ¬L' ≤ 𝓘 p := by
      push_neg; refine ⟨p, mp, Grid.le_dyadic ?_ lL'.le lip.le⟩; change s L' ≤ 𝔰 p; omega
    simp_rw [nfa, false_or] at L'nm; exact L'nm.2
  suffices ∃ p' ∈ lowerCubes (t u),
      𝓘 p' = L' ∧ dist_(p') (𝒬 p') (𝒬 u) < 4 ∧ smul 9 p'' ≤ smul 9 p' by
    obtain ⟨p', mp', ip', dp', sp'⟩ := this
    calc
      _ ≤ volume (E₂ 9 p') := by
        refine measure_mono fun x ⟨⟨mxL, mxG⟩, mxU⟩ ↦ ?_
        have mxp' : x ∈ L' := lL'.le.1 mxL
        rw [← ip'] at mxp'; refine ⟨⟨mxp', mxG⟩, ?_⟩
        rw [mem_iUnion₂] at mxU; obtain ⟨q, mq, hq⟩ := mxU; rw [smul_snd, mem_preimage]
        have p'lq : 𝓘 p' ≤ 𝓘 q := by
          refine le_of_mem_of_mem ?_ mxp' (E_subset_𝓘 hq)
          change s (𝓘 p') ≤ 𝔰 q; rw [ip']; suffices s L < 𝔰 q by omega
          exact hp₂ q mq (not_disjoint_iff.mpr ⟨x, mxL, hq⟩)
        simp_rw [mem_ball']
        calc
          _ ≤ dist_(p') (𝒬 p') (𝒬 u) + dist_(p') (𝒬 u) (𝒬 q) + dist_(p') (𝒬 q) (Q x) :=
            dist_triangle4 ..
          _ ≤ dist_(p') (𝒬 p') (𝒬 u) + dist_(q) (𝒬 u) (𝒬 q) + dist_(q) (𝒬 q) (Q x) := by
            gcongr <;> exact Grid.dist_mono p'lq
          _ < 4 + 4 + 1 := by
            gcongr
            · exact t.dist_lt_four' hu mq
            · rw [← mem_ball']; exact subset_cball hq.2.1
          _ = _ := by norm_num
      _ ≤ 9 ^ a * dens₁ (t u) * volume (L' : Set X) := by
        rw [← ip']
        exact volume_E₂_le_dens₁_mul_volume mp' mp'' (by norm_num) sp'
      _ ≤ 2 ^ (4 * a) * 2 ^ (100 * a ^ 3 + 5 * a) * dens₁ (t u) * volume (L : Set X) := by
        rw [show 2 ^ (4 * a) * _ * dens₁ (t u) * volume (L : Set X) =
          2 ^ (4 * a) * dens₁ (t u) * (2 ^ (100 * a ^ 3 + 5 * a) * volume (L : Set X)) by ring]
        gcongr ?_ * _ * ?_
        · norm_cast; rw [pow_mul]; exact pow_le_pow_left' (by norm_num) a
        · exact volume_bound_of_Grid_lt lL'.le sL'
      _ ≤ _ := by
        gcongr; rw [C7_3_2]; norm_cast; rw [← pow_add]; apply Nat.pow_le_pow_right zero_lt_two
        rw [← add_assoc, ← add_rotate, ← add_mul, show 4 + 5 = 9 by norm_num]
        calc
          _ ≤ 4 * 4 * a + 100 * a ^ 3 := by gcongr; norm_num
          _ ≤ a * a * a + 100 * a ^ 3 := by gcongr <;> exact four_le_a X
          _ = _ := by ring
  obtain lp'' | lp'' := lp''.eq_or_lt
  · use p'', subset_lowerCubes mp'', lp'', t.dist_lt_four hu mp''
  have m₁ := biUnion_Ω (i := L') (range_𝒬 (mem_range_self u))
  rw [mem_iUnion₂] at m₁; obtain ⟨p', mp', hp'⟩ := m₁
  rw [mem_preimage, mem_singleton_iff] at mp'; change 𝓘 p' = L' at mp'
  have ip'lp : 𝓘 p' ≤ 𝓘 p := by
    rw [mp']; refine Grid.le_dyadic ?_ lL'.le lip.le; change s L' ≤ 𝔰 p; omega
  use p', mem_lowerCubes.mp ⟨p, mp, ip'lp⟩, mp'; constructor
  · rw [← mem_ball']; exact mem_of_mem_of_subset (subset_cball hp') (ball_subset_ball (by norm_num))
  · rw [← mp'] at lp''
    refine ⟨lp''.le, fun x mx ↦ ?_⟩
    calc
      _ ≤ dist_(p'') x (𝒬 p') + dist_(p'') (𝒬 p') (𝒬 u) + dist_(p'') (𝒬 u) (𝒬 p'') :=
        dist_triangle4 ..
      _ ≤ C2_1_2 a * (dist_(p') x (𝒬 p') + dist_(p') (𝒬 p') (𝒬 u)) + dist_(p'') (𝒬 u) (𝒬 p'') := by
        rw [mul_add]; gcongr <;> exact Grid.dist_strictMono lp''
      _ < C2_1_2 a * (9 + 1) + 4 := by
        gcongr
        · unfold C2_1_2; positivity
        · exact mx
        · rw [← mem_ball']; exact subset_cball hp'
        · exact t.dist_lt_four' hu mp''
      _ ≤ 1 / 512 * 10 + 4 := by
        rw [show (9 : ℝ) + 1 = 10 by norm_num]; gcongr; exact C2_1_2_le_inv_512 X
      _ < _ := by norm_num

/-- The constant used in `local_dens2_tree_bound`.
Has value `2 ^ (200 * a ^ 3 + 19)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
-- feel free to modify the constant to something simpler.
irreducible_def C7_3_3 (a : ℕ) : ℝ≥0 := 2 ^ (201 * (a : ℝ) ^ 3)

/-- Lemma 7.3.3. -/
lemma local_dens2_tree_bound (hJ : J ∈ 𝓙 (t u)) {q : 𝔓 X} (hq : q ∈ t u)
    (hJq : ¬ Disjoint (J : Set X) (𝓘 q)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  sorry

/-- The constant used in `density_tree_bound1`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_1 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- First part of Lemma 7.3.1. -/
lemma density_tree_bound1
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_1 a *  dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-- The constant used in `density_tree_bound2`.
Has value `2 ^ (256 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (256 * (a : ℝ) ^ 3)

/-- Second part of Lemma 7.3.1. -/
lemma density_tree_bound2 -- some assumptions on f are superfluous
    (hf : BoundedCompactSupport f)
    (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

end TileStructure.Forest
