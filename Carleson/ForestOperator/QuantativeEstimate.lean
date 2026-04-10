import Carleson.ForestOperator.L2Estimate
import Carleson.ToMathlib.BoundedCompactSupport

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.3 and Lemma 7.3.1 -/

/-- The constant used in `local_dens1_tree_bound`.
Has value `2 ^ (101 * a ^ 3)` in the blueprint. -/
irreducible_def C7_3_2 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 1) * a ^ 3)

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
      gcongr
      rw [C7_3_2]
      norm_cast
      calc
        _ ≤ 2 ^ (4 * a) := by rw [pow_mul]; gcongr; norm_num
        _ ≤ _ := by
          gcongr
          · norm_num
          · linarith [seven_le_c]
          · apply Nat.le_pow (by norm_num)

lemma volume_bound_of_Grid_lt {L L' : Grid X} (lL : L ≤ L') (sL : s L' = s L + 1) :
    volume (L' : Set X) ≤ 2 ^ (𝕔 * a ^ 3 + 5 * a) * volume (L : Set X) := by
  suffices volume (ball (c L') (4 * D ^ s L')) ≤
      2 ^ (𝕔 * a ^ 3 + 5 * a) * volume (ball (c L) (D ^ s L / 4)) by
    refine (le_trans ?_ this).trans ?_
    · exact measure_mono Grid_subset_ball
    · gcongr; exact ball_subset_Grid
  have db : dist (c L) (c L') + 4 * D ^ s L' < 2 ^ (𝕔 * a ^ 2 + 5) * (D ^ s L / 4) := by
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
  rw [← disjoint_iff_inter_eq_empty, disjoint_iUnion₂_right] at hq; push Not at hq
  by_cases! hp₂ : ∃ p ∈ t u, ¬Disjoint (L : Set X) (E p) ∧ 𝔰 p ≤ s L
  · exact local_dens1_tree_bound_exists hu hL hp₂
  obtain ⟨p, mp, hp⟩ := hq; have sLp := hp₂ p mp hp
  have lip : L < 𝓘 p := by
    refine Grid.lt_def.mpr ⟨(le_of_mem_𝓛 hL mp ?_).1, sLp⟩
    contrapose! hp; exact (hp.mono_left E_subset_𝓘).symm
  obtain ⟨L', lL', sL'⟩ := Grid.exists_scale_succ sLp
  replace lL' : L < L' := Grid.lt_def.mpr ⟨lL'.1, by lia⟩
  obtain ⟨p'', mp'', lp''⟩ : ∃ p'' ∈ t u, 𝓘 p'' ≤ L' := by
    have L'nm : L' ∉ 𝓛₀ (t u) := by
      by_contra h
      simp_rw [𝓛, mem_setOf, maximal_iff] at hL
      exact lL'.ne (hL.2 h lL'.le)
    rw [𝓛₀, mem_setOf, not_or, not_and_or] at L'nm; push Not at L'nm
    have nfa : ¬∀ p ∈ t u, ¬L' ≤ 𝓘 p := by
      push Not; refine ⟨p, mp, Grid.le_dyadic ?_ lL'.le lip.le⟩; change s L' ≤ 𝔰 p; lia
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
          change s (𝓘 p') ≤ 𝔰 q; rw [ip']; suffices s L < 𝔰 q by lia
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
      _ ≤ 2 ^ (4 * a) * 2 ^ (𝕔 * a ^ 3 + 5 * a) * dens₁ (t u) * volume (L : Set X) := by
        rw [show 2 ^ (4 * a) * _ * dens₁ (t u) * volume (L : Set X) =
          2 ^ (4 * a) * dens₁ (t u) * (2 ^ (𝕔 * a ^ 3 + 5 * a) * volume (L : Set X)) by ring]
        gcongr ?_ * _ * ?_
        · norm_cast; rw [pow_mul]; exact pow_le_pow_left' (by norm_num) a
        · exact volume_bound_of_Grid_lt lL'.le sL'
      _ ≤ _ := by
        gcongr; rw [C7_3_2]; norm_cast; rw [← pow_add]; apply Nat.pow_le_pow_right zero_lt_two
        rw [← add_assoc, ← add_rotate, ← add_mul, show 4 + 5 = 9 by norm_num]
        calc
          _ ≤ 4 * 4 * a + 𝕔 * a ^ 3 := by gcongr; norm_num
          _ ≤ a * a * a + 𝕔 * a ^ 3 := by gcongr <;> exact four_le_a X
          _ = _ := by ring
  obtain lp'' | lp'' := lp''.eq_or_lt
  · use p'', subset_lowerCubes mp'', lp'', t.dist_lt_four hu mp''
  have m₁ := biUnion_Ω (i := L') (range_𝒬 (mem_range_self u))
  rw [mem_iUnion₂] at m₁; obtain ⟨p', mp', hp'⟩ := m₁
  rw [mem_preimage, mem_singleton_iff] at mp'; change 𝓘 p' = L' at mp'
  have ip'lp : 𝓘 p' ≤ 𝓘 p := by
    rw [mp']; refine Grid.le_dyadic ?_ lL'.le lip.le; change s L' ≤ 𝔰 p; lia
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
      _ ≤ 1 / 256 * 10 + 4 := by
        rw [show (9 : ℝ) + 1 = 10 by norm_num]; gcongr; exact C2_1_2_le_inv_256 X
      _ < _ := by norm_num

/-- The constant used in `local_dens2_tree_bound`.
Has value `2 ^ (201 * a ^ 3)` in the blueprint. -/
irreducible_def C7_3_3 (a : ℕ) : ℝ≥0 := 2 ^ ((2 * 𝕔 + 1) * (a : ℝ) ^ 3)

private lemma le_C7_3_3_exponent (ha : 4 ≤ a) (b : ℕ) (hb : b ≤ 16) :
    2 * 𝕔 * a ^ 3 + b * a ≤ (2 * 𝕔 + 1) * a ^ 3 := by
  nlinarith [pow_le_pow_left' ha 2]

-- Auxiliary result used to prove `local_dens2_tree_bound`
private lemma local_dens2_tree_bound_aux {p : 𝔓 X} (hpu : p ∈ t u) {r : ℝ}
    (hr : r ≥ 4 * (D : ℝ) ^ (𝔰 p)) (h₁ : (J : Set X) ⊆ ball (𝔠 p) r)
    (h₂ : volume (ball (𝔠 p) r) ≤ C7_3_3 a * volume (J : Set X)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  rw [mul_comm (C7_3_3 a : ℝ≥0∞), mul_assoc, ← ENNReal.div_le_iff]
  · apply le_trans <| ENNReal.div_le_div (measure_mono (inter_subset_inter_right F h₁)) h₂
    exact le_dens₂ (t u) hpu hr
  · refine mul_ne_zero ?_ (volume_coeGrid_pos (defaultD_pos a)).ne.symm
    rw [C7_3_3]
    exact_mod_cast (pow_pos two_pos _).ne.symm
  · finiteness

-- Special case of `local_dens2_tree_bound_aux` which is used twice
private lemma local_dens2_tree_bound_aux' {p : 𝔓 X} (hpu : p ∈ t u)
    (h₁ : (J : Set X) ⊆ ball (𝔠 p) (4 * (D : ℝ) ^ (𝔰 p)))
    (h₂ : volume (𝓘 p : Set X) ≤ 2 ^ (2 * 𝕔 * a ^ 3 + 10 * a) * volume (J : Set X)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  apply local_dens2_tree_bound_aux hpu (le_refl _) h₁
  rw [show 4 * (D : ℝ) ^ 𝔰 p = 2 ^ 4 * (D ^ 𝔰 p / 4) by ring]
  apply le_trans (measure_ball_two_le_same_iterate (𝔠 p) (D ^ 𝔰 p / 4) 4)
  apply le_trans <| mul_le_mul_right ((measure_mono ball_subset_Grid).trans h₂) _
  simp_rw [defaultA, C7_3_3, ← mul_assoc]
  apply mul_le_mul_left
  norm_cast
  rw [← pow_mul, ← pow_add]
  apply pow_le_pow_right' one_le_two
  exact le_of_eq_of_le (by ring) <| le_C7_3_3_exponent (four_le_a X) 14 (by norm_num)

/-- Lemma 7.3.3. -/
lemma local_dens2_tree_bound (hu : u ∈ t) (hJ : J ∈ 𝓙 (t u)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  by_cases J_top : J = topCube
  · have ⟨p, hpu⟩ := t.nonempty hu
    have S0 : S = 0 := S_eq_zero_of_topCube_mem_𝓙₀ (t.nonempty hu) (𝓙_subset_𝓙₀ (J_top ▸ hJ))
    have 𝓘p_eq_J : 𝓘 p = J := ((𝓘 p).eq_topCube_of_S_eq_zero S0).trans J_top.symm
    apply local_dens2_tree_bound_aux' hpu (𝓘p_eq_J ▸ Grid_subset_ball)
    exact 𝓘p_eq_J ▸ le_mul_of_one_le_left (zero_le _) (one_le_pow_of_one_le' one_le_two _)
  have ⟨J', hJJ', hsJ'⟩ := J.exists_scale_succ (J.scale_lt_scale_topCube J_top)
  have : J' ∉ 𝓙₀ (t u) := fun h ↦ succ_ne_self (s J) <| hJ.eq_of_le h hJJ' ▸ hsJ'.symm
  rw [𝓙₀, mem_setOf_eq] at this
  push Not at this
  obtain ⟨p, hpu, hp⟩ := this.2
  have d0 := realD_pos a
  have volume_le : volume (ball (c J') (204 * D ^ (s J' + 1))) ≤
                     2 ^ (2 * 𝕔 * a ^ 3 + 10 * a) * volume (J : Set X) := calc
    _ ≤ volume (ball (c J) ((204 * D + 4) * D ^ (s J'))) := by
      refine measure_mono <| ball_subset_ball' ?_
      rw [add_mul, mul_assoc, zpow_add₀ d0.ne.symm, mul_comm (D : ℝ), zpow_one]
      apply add_le_add_right (mem_ball'.mp <| Grid_subset_ball <| hJJ'.1 J.c_mem_Grid).le
    _ ≤ volume (ball (c J) (2 ^ (2 * 𝕔 * a ^ 2 + 8) * D ^ (s J))) := by
      rw [hsJ', zpow_add₀ d0.ne.symm, mul_comm ((D : ℝ) ^ (s J)), ← mul_assoc, zpow_one]
      refine measure_mono (ball_subset_ball <| mul_le_mul_of_nonneg_right ?_ (zpow_pos d0 (s J)).le)
      calc
          _ ≤ 2 ^ 8 * (D : ℝ) ^ 2   := by nlinarith [one_lt_realD X]
          _ = 2 ^ (2 * 𝕔 * a ^ 2 + 8) := by norm_cast; rw [pow_add, defaultD, ← pow_mul]; ring_nf
    _ ≤ (defaultA a) ^ (2 * 𝕔 * a ^ 2 + 10) * volume (ball (c J) (D ^ (s J) / 4)) := by
        rw [show 2 ^ (2 * 𝕔 * a^2 + 8) * (D : ℝ) ^ s J = 2 ^ (2 * 𝕔 * a^2 + 10) * (D ^ s J / 4) by ring]
        apply measure_ball_two_le_same_iterate
    _ ≤ 2 ^ (2 * 𝕔 * a ^ 3 + 10 * a) * volume (J : Set X) := by
      apply le_of_le_of_eq <| mul_le_mul_right (measure_mono ball_subset_Grid) _
      simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul, mul_comm a, add_mul, mul_assoc, show a ^ 2 * a = a ^ 3 by rfl]
  by_cases hJB : (J : Set X) ⊆ ball (𝔠 p) (4 * D ^ (𝔰 p))
  · refine local_dens2_tree_bound_aux' hpu hJB <| (measure_mono ?_).trans volume_le
    exact hp.trans <| ball_subset_ball (by gcongr; norm_num)
  have hcJ' : dist (c J') (𝔠 p) < 100 * (D : ℝ) ^ (s J' + 1) := by
    refine mem_ball'.mp <| hp <| ball_subset_Grid <| mem_ball.mpr ?_
    rw [𝔠, c, dist_self]
    positivity
  have hJp : (J : Set X) ⊆ ball (𝔠 p) (104 * D ^ (s J' + 1)) := by
    rw [show (104 : ℝ) = 4 + 100 by norm_num, add_mul]
    refine (hJJ'.1.trans Grid_subset_ball).trans <| ball_subset_ball' <| add_le_add ?_ hcJ'.le
    exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (one_le_realD _) (Int.le.intro 1 rfl))
      four_pos.le
  apply local_dens2_tree_bound_aux hpu (le_of_not_ge (hJB <| hJp.trans <| ball_subset_ball ·)) hJp
  have B_subset : ball (𝔠 p) (104 * D ^ (s J' + 1)) ⊆ ball (c J') (204 * D ^ (s J' + 1)) := by
    apply ball_subset_ball'
    rw [show (204 : ℝ) = 104 + 100 by norm_num, add_mul]
    exact add_le_add_right (dist_comm (c J') (𝔠 p) ▸ hcJ'.le) (104 * (D : ℝ) ^ (s J' + 1))
  refine (measure_mono B_subset).trans <| volume_le.trans <| mul_le_mul_left ?_ _
  rw [C7_3_3]
  norm_cast
  exact pow_le_pow_right' one_le_two (le_C7_3_3_exponent (four_le_a X) 10 (by norm_num))

/-- The constant used in `density_tree_bound1` and `adjoint_tree_estimate`.
Has value `2 ^ (181 * a ^ 3)` in the blueprint. -/
irreducible_def C7_3_1_1 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)

-- Main bound in the proof of Lemma 7.3.1
private lemma eLpNorm_approxOnCube_two_le {C : Set (Grid X)}
    (disj_C : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    {s : Set X} (hs : MeasurableSet s) {c : ℝ≥0∞}
    (hc : ∀ J ∈ C, volume (J ∩ s) ≤ c * volume (J : Set X))
    {f : X → ℂ} (hf : BoundedCompactSupport f) (h2f : ∀ x ∉ s, f x = 0) :
    eLpNorm (approxOnCube C (‖f ·‖)) 2 volume ≤ c ^ (2 : ℝ)⁻¹ * eLpNorm f 2 := by
  classical
  simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
    ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div, approxOnCube]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg_of_nonneg two_pos.le)]
  refine ENNReal.rpow_le_rpow ?_ (inv_pos.mpr two_pos).le
  have : ∀ x, ∑ J ∈ Finset.univ.filter (· ∈ C),
      (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x ≥ 0 := by
    intro x
    refine Finset.sum_nonneg (fun J hJ ↦ ?_)
    by_cases hx : x ∈ (J : Set X)
    · rw [indicator_of_mem hx]; exact integral_nonneg (fun _ ↦ by simp)
    · rw [indicator_of_notMem hx]
  simp_rw [Real.enorm_eq_ofReal (this _)]
  calc
    _ = ∫⁻ x, (∑ J ∈ Finset.univ.filter (· ∈ C),
          ENNReal.ofReal ((J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x)) ^ 2 := by
      congr with x
      congr
      refine ENNReal.ofReal_sum_of_nonneg (fun J hJ ↦ ?_)
      rw [indicator]
      split_ifs
      · exact integral_nonneg (fun _ ↦ norm_nonneg _)
      · exact le_refl 0
    _ = ∫⁻ x, (∑ J ∈ Finset.univ.filter (· ∈ C),
          (J : Set X).indicator (fun _ ↦ ENNReal.ofReal (⨍ y in J, ‖f y‖)) x) ^ 2 := by
      congr with x
      congr with J
      by_cases hx : x ∈ (J : Set X) <;> simp [hx]
    _ = ∫⁻ x, ∑ J ∈ Finset.univ.filter (· ∈ C),
          (J : Set X).indicator (fun _ ↦ (ENNReal.ofReal (⨍ y in J, ‖f y‖)) ^ 2) x := by
      congr with x
      by_cases! ex : ∃ J₀ ∈ Finset.univ.filter (· ∈ C), x ∈ (J₀ : Set X)
      · obtain ⟨J₀, hJ₀, hx⟩ := ex
        calc
          _ = ((J₀ : Set X).indicator (fun _ ↦ ENNReal.ofReal (⨍ y in J₀, ‖f y‖)) x) ^ 2 := by
            rw [Finset.sum_eq_single_of_mem _ hJ₀]
            intro J hJ J_ne_J₀
            have := disj_C (Finset.mem_filter.mp hJ).2 (Finset.mem_filter.mp hJ₀).2 J_ne_J₀
            exact indicator_of_notMem (disjoint_right.mp this hx) _
          _ = (J₀ : Set X).indicator (fun _ ↦ ENNReal.ofReal (⨍ (y : X) in ↑J₀, ‖f y‖) ^ 2) x := by
            rw [indicator]
            split_ifs
            apply (indicator_of_mem hx _).symm
          _ = _ := by
            rw [Finset.sum_eq_single_of_mem _ hJ₀]
            intro J hJ J_ne_J₀
            have := disj_C (Finset.mem_filter.mp hJ).2 (Finset.mem_filter.mp hJ₀).2 J_ne_J₀
            apply indicator_of_notMem (disjoint_right.mp this hx)
      · rw [Finset.sum_eq_zero fun J h ↦ indicator_of_notMem (ex J h) _, zero_pow two_pos.ne',
          Finset.sum_eq_zero fun J h ↦ indicator_of_notMem (ex J h) _]
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C),
          ENNReal.ofReal (⨍ y in J, ‖f y‖) ^ 2 * volume (J : Set X) := by
      rw [lintegral_finset_sum _ (fun _ _ ↦ measurable_const.indicator coeGrid_measurable)]
      simp_rw [lintegral_indicator coeGrid_measurable, setLIntegral_const]
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ y in J, ‖f y‖ₑ) ^ 2 / volume (J : Set X) := by
      congr with J
      rw [ofReal_setAverage hf.norm.integrable.integrableOn (Eventually.of_forall (by simp)),
        div_eq_mul_inv, mul_pow, div_eq_mul_inv, mul_assoc]
      simp_rw [ofReal_norm_eq_enorm]
      by_cases hJ : volume (J : Set X) = 0
      · simp [setLIntegral_measure_zero _ _ hJ]
      congr
      rw [sq, mul_assoc, ENNReal.inv_mul_cancel hJ volume_coeGrid_lt_top.ne, mul_one]
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ y in J ∩ s, ‖f y‖ₑ * 1) ^ 2 / volume (J : Set X) := by
      congr with J
      congr 2
      rw [← lintegral_inter_add_diff _ (J : Set X) hs]
      suffices ∫⁻ x in J \ s, ‖f x‖ₑ = 0 by rw [this, add_zero]; simp_rw [mul_one]
      rw [setLIntegral_eq_zero_iff' (coeGrid_measurable.diff hs)
        hf.restrict.aestronglyMeasurable.enorm]
      exact Eventually.of_forall (fun x hx ↦ by rw [h2f x hx.2, enorm_zero])
    _ ≤ ∑ J ∈ Finset.univ.filter (· ∈ C),
          ((∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ y in J ∩ s, 1) ^ (1 / 2 : ℝ)) ^ 2 /
          volume (J : Set X) := by
      refine Finset.sum_le_sum fun J hJ ↦ ENNReal.div_le_div_right (pow_le_pow_left' ?_ 2) _
      simpa using ENNReal.lintegral_mul_le_Lp_mul_Lq (f := (‖f ·‖ₑ)) (g := 1)
        (volume.restrict (J ∩ s)) ((Real.holderConjugate_iff (p := 2) (q := 2)).mpr (by norm_num))
        hf.restrict.aestronglyMeasurable.enorm aemeasurable_const
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) ^ (1 / (2 : ℝ) * 2) *
          volume (J ∩ s) ^ (1 / (2 : ℝ) * 2) / volume (J : Set X) := by
      simp_rw [setLIntegral_one, mul_pow, ENNReal.rpow_mul]; norm_cast
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C),
          (∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) * volume (J ∩ s) / volume (J : Set X) := by
      simp_rw [div_mul_cancel_of_invertible, ENNReal.rpow_one]
    _ ≤ ∑ J ∈ Finset.univ.filter (· ∈ C),
          (∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) * (c * volume (J : Set X)) / volume (J : Set X) := by
      refine Finset.sum_le_sum fun J hJ ↦ ENNReal.div_le_div_right ?_ _
      exact mul_le_mul_right (hc J (Finset.mem_filter.mp hJ).2) (∫⁻ (y : X) in ↑J ∩ s, ‖f y‖ₑ ^ 2)
    _ = c * ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ (y : X) in J ∩ s, ‖f y‖ₑ ^ 2) := by
      simp_rw [mul_div_assoc,
        ENNReal.div_self ((volume_coeGrid_pos (defaultD_pos a)).ne.symm) volume_coeGrid_lt_top.ne]
      rw [mul_one, ← Finset.sum_mul, mul_comm]
    _ ≤ _ := by
      rw [← setLIntegral_univ]
      have h : (GridStructure.coeGrid · ∩ s) ≤ GridStructure.coeGrid := fun _ ↦ inter_subset_left
      have hC : C = (Finset.univ.filter (· ∈ C) : Set (Grid X)) := by simp
      rw [← lintegral_biUnion_finset (hC ▸ disj_C.mono h) (fun _ _ ↦ coeGrid_measurable.inter hs)]
      exact mul_right_mono <| lintegral_mono_set (subset_univ _)

lemma eLpNorm_approxOnCube_two_le_self (hf : BoundedCompactSupport f)
    {C : Set (Grid X)} (pdC : C.PairwiseDisjoint (fun I ↦ (I : Set X))) :
    eLpNorm (approxOnCube C (‖f ·‖)) 2 volume ≤ eLpNorm f 2 volume := by
  have hv : ∀ L ∈ C, volume ((L : Set X) ∩ univ) ≤ 1 * volume (L : Set X) := by intros; simp
  have key := eLpNorm_approxOnCube_two_le pdC .univ hv hf (by tauto)
  rwa [ENNReal.one_rpow, one_mul] at key

-- Generalization that implies both parts of Lemma 7.3.1
private lemma density_tree_bound_aux (hf : BoundedCompactSupport f)
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t)
    {c : ℝ≥0∞} (hc : eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume ≤ c * eLpNorm f 2 volume) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * c * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  let ℰ := ⋃ p ∈ t u, E p
  have hgℰ : BoundedCompactSupport (ℰ.indicator g) :=
    hg.indicator ((t u).toFinite.measurableSet_biUnion (fun _ _ ↦ measurableSet_E))
  calc
    _ = ‖∫ x, conj (ℰ.indicator g x) * carlesonSum (t u) f x‖ₑ := by
      classical
      congr with x
      by_cases hx : x ∈ ℰ
      · rw [indicator_of_mem hx]
      suffices carlesonSum (t u) f x = 0 by simp [hx, this]
      refine Finset.sum_eq_zero (fun p hp ↦ indicator_of_notMem (fun hxp ↦ ?_) _)
      exact hx ⟨E p, ⟨p, by simp [Finset.mem_filter.mp hp]⟩, hxp⟩
    _ ≤ _ := tree_projection_estimate hf hgℰ hu
    _ ≤ C7_2_1 a * (c * eLpNorm f 2 volume) *
        (2 ^ (((𝕔 / 2 : ℕ) + 1) * (a : ℝ) ^ 3) * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 volume) := by
      refine mul_le_mul' (mul_le_mul_right hc (C7_2_1 a)) ?_
      have hgℰ' : ∀ x ∉ G ∩ ℰ, ℰ.indicator g x = 0 := by
        intro x hx
        rw [mem_inter_iff] at hx
        push Not at hx
        by_cases xG : x ∈ G
        · apply indicator_of_notMem (hx xG)
        · have : g x = 0 := by rw [← notMem_support]; exact xG ∘ (h2g ·)
          exact indicator_apply_eq_zero.mpr (fun _ ↦ this)
      have hℰ : MeasurableSet (G ∩ ℰ) :=
        measurableSet_G.inter <| .biUnion (to_countable (t u)) (fun _ _ ↦ measurableSet_E)
      have : ∀ L ∈ 𝓛 (t u), volume (L ∩ (G ∩ ℰ)) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) :=
        fun L ↦ inter_assoc L G ℰ ▸ local_dens1_tree_bound hu
      apply le_trans <| eLpNorm_approxOnCube_two_le pairwiseDisjoint_𝓛 hℰ this hgℰ hgℰ'
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg_of_nonneg two_pos.le)]
      refine mul_le_mul' (mul_le_mul_left ?_ _) ?_
      · rw [C7_3_2, ENNReal.rpow_ofNNReal (inv_nonneg_of_nonneg two_pos.le)]
        rw [← NNReal.rpow_natCast]
        rw [← NNReal.rpow_mul 2 _ 2⁻¹, ← ENNReal.rpow_ofNNReal (by positivity)]
        simp only [ENNReal.coe_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
        gcongr 2 ^ ?_
        · norm_num
        rw [show (𝕔 + 1 : ℝ) * a ^ 3 * 2⁻¹ = ((𝕔 + 1) * a ^ 3) / 2 by ring]
        apply div_le_of_le_mul₀ (zero_le_two) (by positivity)
        norm_cast
        rw [mul_comm _ 2, ← mul_assoc]
        gcongr
        lia
      · refine eLpNorm_mono (fun x ↦ ?_)
        rw [indicator]
        split_ifs <;> simp
    _ = C7_2_1 a * 2 ^ (((𝕔 / 2 : ℕ) + (1 : ℝ)) * a ^ 3) * dens₁ ((fun x ↦ t.𝔗 x) u) ^ (2 : ℝ)⁻¹
          * c * eLpNorm f 2 volume * eLpNorm g 2 volume := by ring
    _ = _ := by
      rw [C7_2_1, C7_3_1_1, ENNReal.coe_pow, ← ENNReal.rpow_natCast]
      congr
      simp only [ENNReal.coe_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow,
        ENNReal.coe_pow, ← ENNReal.rpow_natCast]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
      congr 1
      norm_cast
      ring

/-- First part of Lemma 7.3.1. -/
lemma density_tree_bound1 (hf : BoundedCompactSupport f)
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hc : eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume ≤ 1 * eLpNorm f 2 volume := by
    have : ∀ L ∈ 𝓙 (t u), volume ((L : Set X) ∩ univ) ≤ 1 * volume (L : Set X) := by intros; simp
    apply le_of_le_of_eq <| eLpNorm_approxOnCube_two_le pairwiseDisjoint_𝓙 .univ this hf (by tauto)
    rw [ENNReal.one_rpow]
  simpa using density_tree_bound_aux hf hg h2g hu hc

/-- The constant used in `density_tree_bound2` and `indicator_adjoint_tree_estimate`.
Has value `2 ^ (282 * a ^ 3)` in the blueprint. -/
irreducible_def C7_3_1_2 (a : ℕ) : ℝ≥0 := 2 ^ ((2 * 𝕔 + 7 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)

/-- Second part of Lemma 7.3.1. -/
lemma density_tree_bound2
    (hf : BoundedCompactSupport f) (h2f : support f ⊆ F)
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hc : eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume ≤
      (C7_3_3 a * dens₂ (t u)) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    have h2f : ∀ x ∉ F, f x = 0 := fun x hx ↦ notMem_support.mp <| hx ∘ (h2f ·)
    have : ∀ J ∈ 𝓙 (t u), volume (J ∩ F) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) :=
      fun J hJ ↦ by rw [inter_comm]; apply local_dens2_tree_bound hu hJ
    exact eLpNorm_approxOnCube_two_le pairwiseDisjoint_𝓙 measurableSet_F this hf h2f
  apply le_trans (density_tree_bound_aux hf hg h2g hu hc)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_pos_of_pos two_pos).le]
  calc
    _ = (C7_3_1_1 a) * (C7_3_3 a) ^ (2 : ℝ)⁻¹ * dens₁ ((fun x ↦ t.𝔗 x) u) ^ (2 : ℝ)⁻¹ *
          dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by ring
    _ ≤ C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
        eLpNorm f 2 volume * eLpNorm g 2 volume := by
      rw [C7_3_1_1, C7_3_1_2, C7_3_3, ENNReal.rpow_ofNNReal (inv_pos.mpr two_pos).le,
        ← ENNReal.coe_mul, ← NNReal.rpow_mul, ← NNReal.rpow_natCast,
        ← NNReal.rpow_add two_pos.ne.symm, ← NNReal.rpow_natCast,
        ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_rpow_of_nonneg _ (by positivity)]
      gcongr
      · norm_num
      rw [← mul_le_mul_iff_left₀ zero_lt_two]
      simp only [add_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc,
        one_mul]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀, mul_one]
      norm_cast
      ring_nf
      gcongr
      norm_num

end TileStructure.Forest

section Extras

omit [TileStructure Q D κ S o] in
-- TODO: move somewhere else
lemma _root_.MeasureTheory.BoundedCompactSupport.const_smul (hf : BoundedCompactSupport f) (c : ℝ) :
    BoundedCompactSupport (c • f) := by
  simp_rw [Pi.smul_def, Complex.real_smul]
  fun_prop

omit [TileStructure Q D κ S o] [MetricSpace X] in
-- rename, move somewhere else
lemma smul_le_indicator {A : Set X} (hf : f.support ⊆ A) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hCpos : 0 < C) : ∀ x, ‖(C⁻¹ • f) x‖ ≤ A.indicator 1 x := by
  intro x
  simp only [Pi.smul_apply, real_smul, ofReal_inv, Complex.norm_mul, norm_inv, norm_real,
    Real.norm_eq_abs]
  rw [inv_mul_le_iff₀ (by positivity),mul_comm,← indicator_mul_const]
  simp only [Pi.one_apply, one_mul]
  by_cases h : x ∈ A
  · rw [indicator_of_mem h]
    exact le_trans (hC x) (by exact le_abs_self C)
  · rw [notMem_support.mp (fun a ↦ h (hf a)), indicator_of_notMem h]
    simp only [norm_zero, le_refl]

end Extras
