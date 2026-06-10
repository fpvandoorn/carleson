module

public import Carleson.Discrete.Defs
public import Carleson.ToMathlib.HardyLittlewood

@[expose] public section

open MeasureTheory Measure NNReal Metric Set
open scoped ENNReal

noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

variable (X) in
/-- The constant in Lemma 5.2.9, with value `D ^ (1 - κ * Z * (n + 1))` -/
@[nolint unusedArguments]
def C5_2_9 [ProofData a q K σ₁ σ₂ F G] (n : ℕ) : ℝ≥0 := D ^ (1 - κ * Z * (n + 1))

/-- A rearrangement for Lemma 5.2.9 that does not require the tile structure. -/
lemma third_exception_rearrangement :
    (∑' n, ∑' k, if k ≤ n then ∑' (j : ℕ),
      C5_2_9 X n * 2 ^ (9 * a - j : ℤ) * 2 ^ (n + k + 3) * volume G else 0) =
    ∑' k, 2 ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G *
      ∑' n, if k ≤ n then (2 * D ^ (-κ * Z) : ℝ≥0∞) ^ (n - k : ℝ) else 0 := by
  calc
    _ = ∑' n, ∑' k, if k ≤ n then C5_2_9 X n * 2 ^ (9 * a) * 2 ^ (n + k + 3) * volume G *
        ∑' (j : ℕ), 2 ^ (-j : ℤ) else 0 := by
      congr!; rw [← ENNReal.tsum_mul_left]; congr! 2 with j
      rw [← mul_rotate (2 ^ (-j : ℤ)), ← mul_assoc (2 ^ (-j : ℤ)), ← mul_assoc (2 ^ (-j : ℤ)),
        mul_rotate (2 ^ (-j : ℤ)), mul_assoc _ _ (2 ^ (-j : ℤ))]; congr
      rw [sub_eq_add_neg, ENNReal.zpow_add two_ne_zero (by simp)]; congr 1; norm_cast
    _ = ∑' k, ∑' n, if k ≤ n then
        C5_2_9 X n * 2 ^ (9 * a) * 2 ^ (n + k + 3) * volume G * 2 else 0 := by
      rw [ENNReal.tsum_comm]; congr!; exact ENNReal.sum_geometric_two_pow_neg_one
    _ = ∑' k, 2 ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G *
        ∑' n, if k ≤ n then (2 : ℝ≥0∞) ^ (n - k : ℝ) * D ^ (-κ * Z * (n - k)) else 0 := by
      congr! 2 with k; rw [← ENNReal.tsum_mul_left]
      congr! 2 with n; rw [mul_ite, mul_zero]; congr 1
      have c1 : (C5_2_9 X n : ℝ≥0∞) = D ^ (1 - κ * Z * (k + 1)) * D ^ (-κ * Z * (n - k)) := by
        rw [C5_2_9, ENNReal.coe_rpow_of_ne_zero (by rw [defaultD]; positivity),
          ENNReal.coe_natCast,
          ← ENNReal.rpow_add _ _ (by rw [defaultD]; positivity) (by rw [defaultD]; simp)]
        congr; ring
      have c2 : (2 : ℝ≥0∞) ^ (n + k + 3) = 2 ^ (2 * k + 3) * 2 ^ (n - k : ℝ) := by
        rw [show (2 : ℝ≥0∞) ^ (2 * k + 3) = 2 ^ (2 * k + 3 : ℝ) by norm_cast,
          show (2 : ℝ≥0∞) ^ (n + k + 3) = 2 ^ (n + k + 3 : ℝ) by norm_cast,
          ← ENNReal.rpow_add _ _ two_ne_zero (by simp)]
        congr 1; ring
      rw [c1, c2]; ring
    _ = _ := by congr!; rw [ENNReal.rpow_mul, ENNReal.mul_rpow_of_ne_top (by simp) (by simp)]

variable [TileStructure Q D κ S o] {k n j l : ℕ} {p p' u u' : 𝔓 X} {x : X}

/-! ## Section 5.2 and Lemma 5.1.1 -/

section first_exception

open ENNReal

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 5.2.1 -/
lemma first_exception' : volume (G₁ : Set X) ≤ 2 ^ (- 5 : ℤ) * volume G := by
  -- Handle trivial cases
  classical
  by_cases hF : volume F = 0
  · simp [G₁_empty hF]
  by_cases hG : volume G = 0
  · exact (G₁_empty' hG ▸ OuterMeasureClass.measure_empty volume) ▸ zero_le
  -- Define constant `K` and prove 0 < K < ⊤
  let K := 2 ^ (2 * a + 5) * volume F / volume G
  have K0 : K > 0 := by
    refine ENNReal.div_pos (ne_of_gt ?_) volume_G_ne_top
    exact mul_pos_iff.2 ⟨ENNReal.pow_pos two_pos _, measure_pos_of_superset subset_rfl hF⟩
  have K_ne_top : K ≠ ⊤ := by
    simp only [K]
    finiteness [volume_F_ne_top (X := X)]
  -- Define function `r : 𝔓 X → ℝ`, with garbage value `0` for `p ∉ highDensityTiles`
  have : ∀ p ∈ highDensityTiles, ∃ r ≥ 4 * (D : ℝ) ^ 𝔰 p,
      volume (F ∩ (ball (𝔠 p) r)) ≥ K * volume (ball (𝔠 p) r) := by
    intro p hp
    simp_rw [highDensityTiles, mem_setOf_eq, dens₂, lt_iSup_iff, mem_singleton_iff] at hp
    rcases hp with ⟨p, rfl, r, hr, h⟩
    use r, hr
    refine ENNReal.lt_div_iff_mul_lt ?_ (Or.inl measure_ball_ne_top) |>.mp h |>.le
    have r0 : r > 0 := lt_of_lt_of_le (by have := realD_pos a; positivity) hr
    exact Or.inl <| (measure_ball_pos volume (𝔠 p) r0).ne.symm
  let r (p : 𝔓 X) := dite (p ∈ highDensityTiles) (fun hp ↦ Classical.choose (this p hp)) (fun _ ↦ 0)
  have hr {p : 𝔓 X} (hp : p ∈ highDensityTiles) := Classical.choose_spec (this p hp)
  -- Show that balls with centers in `highDensityTiles` covers `G₁`.
  let 𝓑 : Finset (𝔓 X) := highDensityTiles.toFinset
  have : (G₁ : Set X) ⊆ ⋃ p ∈ 𝓑, (ball (𝔠 p) (r p)) := by
    refine fun x hx ↦ mem_iUnion.2 ?_
    simp only [G₁, mem_iUnion, exists_prop] at hx
    rcases hx with ⟨p, hp, xp⟩
    use p
    simp only [mem_iUnion, exists_prop, 𝓑, mem_toFinset]
    refine ⟨hp, ?_⟩
    suffices (𝓘 p : Set X) ⊆ ball (𝔠 p) (r p) from this xp
    apply Grid_subset_ball.trans ∘ ball_subset_ball
    convert (hr hp).1.le
    simp only [r, dif_pos hp]
  apply (OuterMeasureClass.measure_mono volume this).trans
  -- Apply `measure_biUnion_le_lintegral` to `u := F.indicator 1` to bound the volume of ⋃ 𝓑.
  let u := F.indicator (1 : X → ℝ≥0∞)
  have h2u : ∀ p ∈ 𝓑, K * volume (Metric.ball (𝔠 p) (r p)) ≤
      ∫⁻ (x : X) in ball (𝔠 p) (r p), u x := by
    intro p h
    simp_rw [𝓑, mem_toFinset] at h
    simpa [u, lintegral_indicator, Measure.restrict_apply, measurableSet_F, r, h] using (hr h).2.le
  have ineq := measure_biUnion_le_lintegral (A := defaultA a) _ K u h2u
  simp only [u, lintegral_indicator, measurableSet_F, Pi.one_apply, lintegral_const,
    MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul] at ineq
  rw [← ENNReal.mul_le_mul_iff_right K0.ne.symm K_ne_top]
  apply ineq.trans_eq
  -- Prove that the desired bound for the volume of ⋃ 𝓑 is equal to the bound proven above.
  simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, ENNReal.coe_pow, coe_ofNat, K]
  have : (volume G)⁻¹ * (2 ^ (2 * a + 5) * volume F) * (2 ^ (-5 : ℤ) * volume G) =
      (2 ^ (2 * a + 5) * 2 ^ (-5 : ℤ)) * volume F * ((volume G)⁻¹ * volume G) := by ring
  rw [ENNReal.div_eq_inv_mul, ← mul_one (_ * _), this]
  congr
  · have h : (2 : ℝ≥0∞) ^ (2 * a + 5) = (2 : ℝ≥0∞) ^ (2 * a + 5 : ℤ) := by norm_cast
    rw [h, ← ENNReal.zpow_add (NeZero.ne 2) ofNat_ne_top, add_neg_cancel_right, ← pow_mul, mul_comm 2]
    norm_cast
  · exact ENNReal.inv_mul_cancel hG volume_G_ne_top |>.symm

lemma first_exception : volume (G₁ : Set X) ≤ 2 ^ (- 4 : ℤ) * volume G := by
  calc volume G₁ ≤ 2 ^ (-5 : ℤ) * volume G := first_exception'
    _ ≤ 2 ^ (-4 : ℤ) * volume G := by gcongr <;> norm_num

end first_exception

/-- Lemma 5.2.2 -/
lemma dense_cover (k : ℕ) : volume (⋃ i ∈ 𝓒 (X := X) k, (i : Set X)) ≤ 2 ^ (k + 1) * volume G := by
  classical
  let M : Finset (Grid X) :=
    { j | 2 ^ (-(k + 1 : ℕ) : ℤ) * volume (j : Set X) < volume (G ∩ j) }
  have s₁ : ⋃ i ∈ 𝓒 (X := X) k, (i : Set X) ⊆ ⋃ i ∈ M, ↑i := by
    simp_rw [𝓒]; intro q mq; rw [mem_iUnion₂] at mq ⊢; obtain ⟨i, hi, mi⟩ := mq
    rw [aux𝓒, mem_diff, mem_setOf] at hi; obtain ⟨j, hj, mj⟩ := hi.1
    use j, ?_, mem_of_mem_of_subset mi hj.1
    simp only [M, Finset.mem_filter_univ]; exact mj
  let M' := Grid.maxCubes M
  have s₂ : ⋃ i ∈ M, (i : Set X) ⊆ ⋃ i ∈ M', ↑i := iUnion₂_mono' fun i mi ↦ by
    obtain ⟨j, mj, hj⟩ := Grid.exists_maximal_supercube mi; use j, mj, hj.1
  calc
    _ ≤ volume (⋃ i ∈ M', (i : Set X)) := measure_mono (s₁.trans s₂)
    _ ≤ ∑ i ∈ M', volume (i : Set X) := measure_biUnion_finset_le M' _
    _ ≤ 2 ^ (k + 1) * ∑ j ∈ M', volume (G ∩ j) := by
      rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i hi ↦ ?_
      replace hi : i ∈ M := Finset.mem_of_subset (Finset.filter_subset _ M) hi
      rw [Finset.mem_filter_univ, ← ENNReal.rpow_intCast,
        show (-(k + 1 : ℕ) : ℤ) = (-(k + 1) : ℝ) by simp, mul_comm,
        ← ENNReal.lt_div_iff_mul_lt (by simp) (by simp), ENNReal.div_eq_inv_mul,
        ← ENNReal.rpow_neg, neg_neg] at hi
      exact_mod_cast hi.le
    _ = 2 ^ (k + 1) * volume (⋃ j ∈ M', G ∩ j) := by
      congr; refine (measure_biUnion_finset (fun _ mi _ mj hn ↦ ?_) (fun _ _ ↦ ?_)).symm
      · exact ((Grid.maxCubes_pairwiseDisjoint mi mj hn).inter_right' G).inter_left' G
      · exact measurableSet_G.inter coeGrid_measurable
    _ ≤ _ := mul_le_mul_right (measure_mono (iUnion₂_subset fun _ _ ↦ inter_subset_left)) _

/-- Lemma 5.2.3 -/
lemma pairwiseDisjoint_E1 : (𝔐 (X := X) k n).PairwiseDisjoint E₁ := fun p mp p' mp' h ↦ by
  change Disjoint _ _
  contrapose! h
  have h𝓘 := (Disjoint.mono (E₁_subset p) (E₁_subset p')).mt h
  wlog hs : s (𝓘 p') ≤ s (𝓘 p) generalizing p p'
  · rw [disjoint_comm] at h h𝓘; rw [not_le] at hs; rw [this p' mp' p mp h h𝓘 hs.le]
  obtain ⟨x, ⟨-, mxp⟩, ⟨-, mxp'⟩⟩ := not_disjoint_iff.mp h
  rw [mem_preimage] at mxp mxp'
  have l𝓘 := Grid.le_def.mpr ⟨(fundamental_dyadic hs).resolve_right (disjoint_comm.not.mpr h𝓘), hs⟩
  have sΩ := (relative_fundamental_dyadic l𝓘).resolve_left <| not_disjoint_iff.mpr ⟨_, mxp', mxp⟩
  rw [𝔐, mem_setOf] at mp mp'
  exact mp'.eq_of_ge mp.prop ⟨l𝓘, sΩ⟩

open scoped Classical in
/-- Lemma 5.2.4 -/
lemma dyadic_union (hx : x ∈ setA l k n) : ∃ i : Grid X, x ∈ i ∧ (i : Set X) ⊆ setA l k n := by
  let M : Finset (𝔓 X) := { p | p ∈ 𝔐 k n ∧ x ∈ 𝓘 p }
  simp_rw [setA, mem_setOf, stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
    Finset.filter_filter] at hx ⊢
  obtain ⟨b, memb, minb⟩ := M.exists_min_image 𝔰 (Finset.card_pos.mp (zero_le'.trans_lt hx))
  simp_rw [M, Finset.mem_filter_univ] at memb minb
  use 𝓘 b, memb.2; intro c mc; rw [mem_setOf]
  refine hx.trans_le (Finset.card_le_card fun y hy ↦ ?_)
  rw [Finset.mem_filter_univ] at hy ⊢
  exact ⟨hy.1, mem_of_mem_of_subset mc (le_of_mem_of_mem (minb y hy) memb.2 hy.2).1⟩

lemma iUnion_MsetA_eq_setA : ⋃ i ∈ MsetA (X := X) l k n, ↑i = setA (X := X) l k n := by
  ext x
  simp_rw [mem_iUnion₂, MsetA, Finset.mem_filter_univ]
  constructor <;> intro mx
  · obtain ⟨j, mj, lj⟩ := mx; exact mem_of_mem_of_subset lj mj
  · obtain ⟨j, mj, lj⟩ := dyadic_union mx; use j, lj, mj

set_option backward.isDefEq.respectTransparency false in
/-- Equation (5.2.7) in the proof of Lemma 5.2.5. -/
lemma john_nirenberg_aux1 {L : Grid X} (mL : L ∈ Grid.maxCubes (MsetA l k n))
    (mx : x ∈ setA (l + 1) k n) (mx₂ : x ∈ L) : 2 ^ (n + 1) ≤
    stackSize { q ∈ 𝔐 (X := X) k n | 𝓘 q ≤ L} x := by
  classical
  -- LHS of equation (5.2.6) is strictly greater than `(l + 1) * 2 ^ (n + 1)`
  rw [setA, mem_setOf, ← stackSize_setOf_add_stackSize_setOf_not (P := fun p' ↦ 𝓘 p' ≤ L)] at mx
  -- Rewrite second sum of RHS of (5.2.6) so that it sums over tiles `q` satisfying `L < 𝓘 q`
  nth_rw 2 [← stackSize_setOf_add_stackSize_setOf_not (P := fun p' ↦ Disjoint (𝓘 p' : Set X) L)]
    at mx
  simp_rw [mem_setOf_eq, and_assoc] at mx
  have mid0 : stackSize { p' ∈ 𝔐 k n | ¬𝓘 p' ≤ L ∧ Disjoint (𝓘 p' : Set X) L} x = 0 := by
    simp_rw [stackSize, Finset.sum_eq_zero_iff, indicator_apply_eq_zero, Finset.mem_filter_univ,
      show ¬(1 : X → ℕ) x = 0 by simp, imp_false]
    rintro y ⟨-, -, dj2⟩
    exact disjoint_right.mp dj2 mx₂
  rw [mid0, zero_add] at mx
  have req :
      { p' | p' ∈ 𝔐 k n ∧ ¬𝓘 p' ≤ L ∧ ¬Disjoint (𝓘 p' : Set X) L } =
      { p' | p' ∈ 𝔐 k n ∧ L < 𝓘 p' } := by
    ext q
    simp_rw [mem_setOf_eq, and_congr_right_iff]
    refine fun _ ↦ ⟨fun h ↦ ?_, ?_⟩
    · apply lt_of_le_of_ne <| (le_or_ge_or_disjoint.resolve_left h.1).resolve_right h.2
      by_contra k; subst k; exact absurd le_rfl h.1
    · rw [Grid.lt_def, Grid.le_def, not_and_or, not_le]
      exact fun h ↦ ⟨Or.inr h.2, not_disjoint_iff.mpr ⟨x, mem_of_mem_of_subset mx₂ h.1, mx₂⟩⟩
  rw [req] at mx
  -- The new second sum of RHS is at most `l * 2 ^ (n + 1)`
  set Q₁ := { q ∈ 𝔐 (X := X) k n | 𝓘 q ≤ L }
  set Q₂ := { q ∈ 𝔐 (X := X) k n | L < 𝓘 q }
  have Ql : stackSize Q₂ x ≤ l * 2 ^ (n + 1) := by
    by_cases h : IsMax L
    · rw [Grid.isMax_iff] at h
      have : Q₂ = ∅ := by
        ext y; simp_rw [Q₂, mem_setOf_eq, Set.notMem_empty, iff_false, not_and, h, Grid.lt_def,
          not_and_or, not_lt]
        exact fun _ ↦ Or.inr (Grid.le_topCube).2
      simp [stackSize, this]
    have Lslq : ∀ q ∈ Q₂, L.succ ≤ 𝓘 q := fun q mq ↦ Grid.succ_le_of_lt mq.2
    have Lout : ¬(L.succ : Set X) ⊆ setA (X := X) l k n := by
      by_contra! hs
      rw [Grid.maxCubes, Finset.mem_filter] at mL
      apply absurd _ h
      exact Grid.max_of_le_succ
        (mL.2 L.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩) Grid.le_succ).symm.le
    rw [not_subset_iff_exists_mem_notMem] at Lout
    obtain ⟨x', mx', nx'⟩ := Lout
    calc
      _ = stackSize Q₂ x' := by
        refine stackSize_congr fun q mq ↦ ?_
        simp_rw [mem_of_mem_of_subset mx₂ (Grid.le_succ.trans (Lslq q mq)).1,
          mem_of_mem_of_subset mx' (Lslq q mq).1]
      _ ≤ stackSize (𝔐 (X := X) k n) x' := by
        refine stackSize_mono <| sep_subset ..
      _ ≤ l * 2 ^ (n + 1) := by rwa [setA, mem_setOf_eq, not_lt] at nx'
  -- so the (unchanged) first sum of RHS is at least `2 ^ (n + 1)`
  rw [add_one_mul] at mx; lia

/-- Equation (5.2.11) in the proof of Lemma 5.2.5. -/
lemma john_nirenberg_aux2 {L : Grid X} (mL : L ∈ Grid.maxCubes (MsetA l k n)) :
    2 * volume (setA (X := X) (l + 1) k n ∩ L) ≤ volume (L : Set X) := by
  classical
  let Q₁ : Finset (𝔓 X) := { q | q ∈ 𝔐 (X := X) k n ∧ 𝓘 q ≤ L }
  have Q₁m : ∀ i ∈ Q₁, Measurable ((𝓘 i : Set X).indicator (1 : X → ℝ≥0∞)) := fun _ _ ↦
    measurable_one.indicator coeGrid_measurable
  have e528 : ∑ q ∈ Q₁, volume (E₁ q) ≤ volume (L : Set X) :=
    calc
      _ = volume (⋃ q ∈ Q₁, E₁ q) := by
        refine (measure_biUnion_finset (fun p mp q mq hn ↦ ?_) (fun _ _ ↦ ?_)).symm
        · simp_rw [Finset.mem_coe, Q₁, Finset.mem_filter] at mp mq
          exact pairwiseDisjoint_E1 mp.2.1 mq.2.1 hn
        · exact (coeGrid_measurable.inter measurableSet_G).inter
            (SimpleFunc.measurableSet_preimage ..)
      _ ≤ volume (⋃ q ∈ Q₁, (𝓘 q : Set X)) := measure_mono (iUnion₂_mono fun q _ ↦ E₁_subset q)
      _ ≤ _ := by
        apply measure_mono (iUnion₂_subset fun q mq ↦ ?_)
        simp_rw [Q₁, Finset.mem_filter] at mq; exact mq.2.2.1
  have e529 : ∑ q ∈ Q₁, volume (𝓘 q : Set X) ≤ 2 ^ n * volume (L : Set X) :=
    calc
      _ ≤ ∑ q ∈ Q₁, 2 ^ n * volume (E₁ q) := by
        refine Finset.sum_le_sum fun q mq ↦ ?_
        simp_rw [Q₁, Finset.mem_filter, 𝔐, mem_setOf, maximal_iff, aux𝔐, mem_setOf] at mq
        replace mq := mq.2.1.1.2
        rw [← ENNReal.rpow_intCast, show (-(n : ℕ) : ℤ) = (-n : ℝ) by simp, mul_comm,
          ← ENNReal.lt_div_iff_mul_lt (by simp) (by simp), ENNReal.div_eq_inv_mul,
          ← ENNReal.rpow_neg, neg_neg] at mq
        exact_mod_cast mq.le
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_right e528 _
  rw [← ENNReal.mul_le_mul_iff_right (a := 2 ^ n) (by simp) (by simp), ← mul_assoc, ← pow_succ]
  calc
    _ = ∫⁻ x in setA (X := X) (l + 1) k n ∩ L, 2 ^ (n + 1) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in setA (X := X) (l + 1) k n ∩ L, ∑ q ∈ Q₁, (𝓘 q : Set X).indicator 1 x := by
      refine setLIntegral_mono (Finset.measurable_sum Q₁ Q₁m) fun x ⟨mx, mx₂⟩ ↦ ?_
      have : 2 ^ (n + 1) ≤ ∑ q ∈ Q₁, (𝓘 q : Set X).indicator 1 x := by
        convert john_nirenberg_aux1 mL mx mx₂
        simp_rw [stackSize, Q₁, mem_setOf_eq]
      have lcast : (2 : ℝ≥0∞) ^ (n + 1) = ((2 ^ (n + 1) : ℕ) : ℝ).toNNReal := by
        rw [Real.toNNReal_coe_nat, ENNReal.coe_natCast]; norm_cast
      have rcast : ∑ q ∈ Q₁, (𝓘 q : Set X).indicator (1 : X → ℝ≥0∞) x =
          (((∑ q ∈ Q₁, (𝓘 q : Set X).indicator (1 : X → ℕ) x) : ℕ) : ℝ).toNNReal := by
        rw [Real.toNNReal_coe_nat, ENNReal.coe_natCast, Nat.cast_sum]; congr!; simp [indicator]
      rw [lcast, rcast, ENNReal.coe_le_coe]
      exact Real.toNNReal_le_toNNReal (Nat.cast_le.mpr this)
    _ ≤ ∫⁻ x, ∑ q ∈ Q₁, (𝓘 q : Set X).indicator 1 x := setLIntegral_le_lintegral _ _
    _ = ∑ q ∈ Q₁, ∫⁻ x, (𝓘 q : Set X).indicator 1 x := lintegral_finsetSum _ Q₁m
    _ = ∑ q ∈ Q₁, volume (𝓘 q : Set X) := by
      congr!; exact lintegral_indicator_one coeGrid_measurable
    _ ≤ _ := e529

/-- Lemma 5.2.5 -/
lemma john_nirenberg : volume (setA (X := X) l k n) ≤ 2 ^ (k + 1 - l : ℤ) * volume G := by
  induction l with
  | zero =>
    calc
      _ ≤ volume (⋃ i ∈ 𝓒 (X := X) k, (i : Set X)) := measure_mono setA_subset_iUnion_𝓒
      _ ≤ _ := by
        rw [← ENNReal.rpow_intCast, show (k + 1 - (0 : ℕ) : ℤ) = (k + 1 : ℝ) by simp]
        exact_mod_cast dense_cover k
  | succ l ih =>
    suffices 2 * volume (setA (X := X) (l + 1) k n) ≤ volume (setA (X := X) l k n) by
      rw [← ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp), ← mul_assoc]
      apply this.trans
      convert ih using 2; nth_rw 1 [← zpow_one 2, ← ENNReal.zpow_add (by simp) (by simp)]
      congr 1; lia
    calc
      _ = 2 * ∑ L ∈ Grid.maxCubes (MsetA (X := X) l k n),
          volume (setA (X := X) (l + 1) k n ∩ L) := by
        congr; rw [← measure_biUnion_finset]
        · congr with x; constructor <;> intro h
          · obtain ⟨L', mL'⟩ := dyadic_union h
            have := mem_of_mem_of_subset mL'.1 (mL'.2.trans setA_subset_setA)
            rw [← iUnion_MsetA_eq_setA, mem_iUnion₂] at this
            obtain ⟨M, mM, lM⟩ := this
            obtain ⟨L, mL, lL⟩ := Grid.exists_maximal_supercube mM
            rw [mem_iUnion₂]; use L, mL
            exact ⟨mem_of_mem_of_subset mL'.1 mL'.2, mem_of_mem_of_subset lM lL.1⟩
          · rw [mem_iUnion₂] at h; obtain ⟨i, _, mi₂⟩ := h; exact mem_of_mem_inter_left mi₂
        · exact fun i mi j mj hn ↦
            ((Grid.maxCubes_pairwiseDisjoint mi mj hn).inter_left' _).inter_right' _
        · exact fun _ _ ↦ measurable_setA.inter coeGrid_measurable
      _ ≤ ∑ L ∈ Grid.maxCubes (MsetA (X := X) l k n), volume (L : Set X) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun L mL ↦ john_nirenberg_aux2 mL
      _ = _ := by
        rw [← measure_biUnion_finset Grid.maxCubes_pairwiseDisjoint (fun _ _ ↦ coeGrid_measurable)]
        congr with x; constructor <;> intro h
        · rw [mem_iUnion₂] at h; obtain ⟨i, mi₁, mi₂⟩ := h
          simp only [Grid.maxCubes, Finset.mem_filter, MsetA, Finset.mem_univ, true_and] at mi₁
          exact mem_of_mem_of_subset mi₂ mi₁.1
        · obtain ⟨L', mL'⟩ := dyadic_union h
          have := mem_of_mem_of_subset mL'.1 mL'.2
          rw [← iUnion_MsetA_eq_setA, mem_iUnion₂] at this
          obtain ⟨M, mM, lM⟩ := this
          obtain ⟨L, mL, lL⟩ := Grid.exists_maximal_supercube mM
          rw [mem_iUnion₂]; use L, mL, mem_of_mem_of_subset lM lL.1

/-- Lemma 5.2.6 -/
lemma second_exception : volume (G₂ (X := X)) ≤ 2 ^ (-2 : ℤ) * volume G :=
  calc
    _ ≤ ∑' (n : ℕ), volume (⋃ (k ≤ n), setA (X := X) (2 * n + 6) k n) := measure_iUnion_le _
    _ = ∑' (n : ℕ), volume (⋃ (k : ℕ), if k ≤ n then setA (X := X) (2 * n + 6) k n else ∅) := by
      congr!; exact iUnion_eq_if _
    _ ≤ ∑' (n : ℕ) (k : ℕ), volume (if k ≤ n then setA (X := X) (2 * n + 6) k n else ∅) := by
      gcongr; exact measure_iUnion_le _
    _ = ∑' (k : ℕ) (n : ℕ), if k ≤ n then volume (setA (X := X) (2 * n + 6) k n) else 0 := by
      rw [ENNReal.tsum_comm]; congr!; split_ifs <;> simp
    _ ≤ ∑' (k : ℕ) (n : ℕ), if k ≤ n then 2 ^ (k - 5 - 2 * n : ℤ) * volume G else 0 := by
      gcongr; split_ifs
      · convert john_nirenberg using 3; lia
      · rfl
    _ = ∑' (k : ℕ), 2 ^ (-k - 5 : ℤ) * volume G * ∑' (n' : ℕ), 2 ^ (- 2 * n' : ℤ) := by
      congr with k -- n' = n - k - 1; n = n' + k + 1
      have rearr : ∀ n : ℕ, (k - 5 - 2 * n : ℤ) = (-k - 5 + (-2 * (n - k)) : ℤ) := by lia
      conv_lhs =>
        enter [1, n]
        rw [rearr, ENNReal.zpow_add (by simp) (by simp), ← mul_rotate,
          ← mul_zero (volume G * 2 ^ (-k - 5 : ℤ)), ← mul_ite]
      rw [ENNReal.tsum_mul_left, mul_comm (volume G)]; congr 1
      exact tsum_geometric_ite_eq_tsum_geometric
    _ ≤ ∑' (k : ℕ), 2 ^ (-k - 5 : ℤ) * volume G * 2 ^ (2 : ℤ) := by
      gcongr
      rw [ENNReal.sum_geometric_two_pow_neg_two, zpow_two]; norm_num
      rw [← ENNReal.coe_ofNat, ← Real.toNNReal_ofNat, ENNReal.coe_le_coe]; norm_num
    _ = 2 ^ (-4 : ℤ) * volume G * 2 ^ (2 : ℤ) := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_right]; congr
      conv_lhs => enter [1, k]; rw [sub_eq_add_neg, ENNReal.zpow_add (by simp) (by simp)]
      nth_rw 1 [ENNReal.tsum_mul_right, ENNReal.sum_geometric_two_pow_neg_one,
        ← zpow_one 2, ← ENNReal.zpow_add] <;> simp
    _ = _ := by rw [← mul_rotate, ← ENNReal.zpow_add] <;> simp

section TopTiles

open scoped Classical in
/-- The volume of a "layer" in the key function of Lemma 5.2.7. -/
def layervol (k n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  volume {x | t ≤ ∑ m with m ∈ 𝔐 (X := X) k n,
    (𝓘 m : Set X).indicator (1 : X → ℝ) x}

lemma indicator_sum_eq_natCast {s : Finset (𝔓 X)} :
    ∑ m ∈ s, (𝓘 m : Set X).indicator (1 : X → ℝ) x =
    Nat.cast (∑ m ∈ s, (𝓘 m : Set X).indicator (1 : X → ℕ) x) := by
  push_cast; congr!; simp [indicator]

open scoped Classical in
lemma layervol_eq_zero_of_lt {t : ℝ} (ht : (𝔐 (X := X) k n).toFinset.card < t) :
    layervol (X := X) k n t = 0 := by
  rw [layervol, measure_eq_zero_iff_ae_notMem]
  refine ae_of_all volume fun x ↦ ?_; rw [mem_setOf, not_le]
  calc
    _ ≤ ((𝔐 (X := X) k n).toFinset.card : ℝ) := by
      simp_rw [indicator_sum_eq_natCast, Nat.cast_le, indicator_apply, Pi.one_apply,
        Finset.sum_boole, Nat.cast_id, filter_mem_univ_eq_toFinset]
      exact Finset.card_le_card (Finset.filter_subset ..)
    _ < _ := ht

lemma lintegral_Ioc_layervol_one {l : ℕ} :
    ∫⁻ t in Ioc (l : ℝ) (l + 1), layervol (X := X) k n t = layervol (X := X) k n (l + 1) :=
  calc
    _ = ∫⁻ t in Ioc (l : ℝ) (l + 1), layervol (X := X) k n (l + 1) := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      unfold layervol; congr with x; constructor <;> intro h
      · rw [indicator_sum_eq_natCast, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
        rw [indicator_sum_eq_natCast, ← Nat.ceil_le] at h; convert h; symm
        rwa [Nat.ceil_eq_iff (by lia), add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
      · exact ht.2.trans h
    _ = layervol k n (l + 1) * volume (Ioc (l : ℝ) (l + 1)) := setLIntegral_const ..
    _ = _ := by rw [Real.volume_Ioc, add_sub_cancel_left, ENNReal.ofReal_one, mul_one]

lemma antitone_layervol : Antitone fun t ↦ layervol (X := X) k n t := fun i j h ↦ by
  unfold layervol; exact measure_mono fun x hx ↦ h.trans hx

lemma lintegral_Ioc_layervol_le {a b : ℕ} : ∫⁻ t in Ioc (a : ℝ) b, layervol (X := X) k n t ≤
    (b - a : ℕ) * layervol (X := X) k n (a + 1) := by
  calc
    _ = ∑ l ∈ Finset.Ico a b, ∫⁻ t in Ioc (l : ℝ) (l + 1), layervol (X := X) k n t := by
      nth_rw 1 [← mul_one (a : ℝ), ← mul_one (b : ℝ)]
      convert lintegral_Ioc_partition zero_le_one using 4; simp
    _ = ∑ l ∈ Finset.Ico a b, layervol (X := X) k n (l + 1) := by
      congr! 2; exact lintegral_Ioc_layervol_one
    _ ≤ ∑ l ∈ Finset.Ico a b, layervol (X := X) k n (a + 1) :=
      Finset.sum_le_sum fun l ml ↦ antitone_layervol (by simp_all)
    _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

open scoped Classical in
lemma top_tiles_aux : ∑ m with m ∈ 𝔐 (X := X) k n, volume (𝓘 m : Set X) =
    ∫⁻ t in Ioc 0 ((𝔐 (X := X) k n).toFinset.card * 2 ^ (n + 1) : ℝ), layervol (X := X) k n t := by
  set M := 𝔐 (X := X) k n
  set Mc := M.toFinset.card
  calc
    _ = ∑ m with m ∈ M, ∫⁻ x, (𝓘 m : Set X).indicator 1 x := by
      congr! with m; exact (lintegral_indicator_one coeGrid_measurable).symm
    _ = ∫⁻ x, ∑ m with m ∈ M, (𝓘 m : Set X).indicator 1 x :=
      (lintegral_finsetSum _ fun _ _ ↦ measurable_one.indicator coeGrid_measurable).symm
    _ = ∫⁻ x, ENNReal.ofReal (∑ m with m ∈ M, (𝓘 m : Set X).indicator 1 x) := by
      congr! 2 with x; rw [ENNReal.ofReal_sum_of_nonneg]
      · congr!; unfold indicator; split_ifs <;> simp
      · exact fun _ _ ↦ indicator_nonneg (fun _ _ ↦ by simp) _
    _ = ∫⁻ t in Ioi 0, layervol k n t := by
      apply lintegral_eq_lintegral_meas_le
      · exact ae_of_all volume fun _ ↦
          Finset.sum_nonneg' fun _ ↦ indicator_nonneg (fun _ _ ↦ by simp) _
      · exact Measurable.aemeasurable <|
          Finset.measurable_sum _ (fun _ _ ↦ measurable_one.indicator coeGrid_measurable)
    _ = _ := by
      have nn : 0 ≤ (Mc * 2 ^ (n + 1) : ℝ) := by positivity
      rw [← Ioc_union_Ioi_eq_Ioi nn, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
      nth_rw 3 [← add_zero (lintegral ..)]; congr 1
      have cgr : ∫⁻ (t : ℝ) in Ioi (Mc * 2 ^ (n + 1) : ℝ), layervol (X := X) k n t =
          ∫⁻ _ in Ioi (Mc * 2 ^ (n + 1) : ℝ), 0 := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun t mt ↦
          layervol_eq_zero_of_lt (lt_of_le_of_lt ?_ mt))
        exact_mod_cast Nat.le_mul_of_pos_right Mc (by positivity)
      rw [cgr, lintegral_zero]

open scoped Classical in
/-- Lemma 5.2.7 -/
lemma top_tiles : ∑ m with m ∈ 𝔐 (X := X) k n, volume (𝓘 m : Set X) ≤
    2 ^ (n + k + 3) * volume G := by
  set M := 𝔐 (X := X) k n
  let Mc := M.toFinset.card
  calc
    _ = ∫⁻ t in Ioc 0 (Mc * 2 ^ (n + 1) : ℝ), layervol (X := X) k n t := top_tiles_aux
    _ = ∑ l ∈ Finset.range Mc,
        ∫⁻ t in Ioc ((l : ℝ) * 2 ^ (n + 1)) ((l + 1 : ℕ) * 2 ^ (n + 1)),
          layervol (X := X) k n t := by
      rw [Finset.range_eq_Ico, show (0 : ℝ) = (0 : ℕ) * 2 ^ (n + 1) by simp]
      exact lintegral_Ioc_partition (by positivity)
    _ ≤ ∑ l ∈ Finset.range Mc,
        (((l + 1) * 2 ^ (n + 1) - l * 2 ^ (n + 1) : ℕ)) *
          layervol (X := X) k n ((l * 2 ^ (n + 1) : ℕ) + 1) := by
      convert Finset.sum_le_sum fun _ _ ↦ lintegral_Ioc_layervol_le <;> simp
    _ = 2 ^ (n + 1) * ∑ l ∈ Finset.range Mc, layervol (X := X) k n (l * 2 ^ (n + 1) + 1 : ℕ) := by
      rw [Finset.mul_sum]; congr! 2
      · rw [← Nat.mul_sub_right_distrib]; simp
      · congr; simp
    _ = 2 ^ (n + 1) * ∑ l ∈ Finset.range Mc, volume (setA (X := X) l k n) := by
      unfold layervol setA stackSize; congr! 3; ext x
      rw [mem_setOf, mem_setOf, indicator_sum_eq_natCast, Nat.cast_le]
      exact Nat.add_one_le_iff
    _ ≤ 2 ^ (n + 1) * ∑ l ∈ Finset.range Mc, 2 ^ (k + 1 - l : ℤ) * volume G :=
      mul_le_mul_right (Finset.sum_le_sum fun _ _ ↦ john_nirenberg) _
    _ ≤ 2 ^ (n + 1) * ∑' (l : ℕ), 2 ^ (k + 1 - l : ℤ) * volume G :=
      mul_le_mul_right (ENNReal.sum_le_tsum _) _
    _ = 2 ^ (n + 1) * (volume G * 2 ^ (k + 1) * 2) := by
      conv_lhs =>
        enter [2, 1, l]
        rw [sub_eq_add_neg, ENNReal.zpow_add (by simp) (by simp), ← mul_rotate]
      rw [ENNReal.tsum_mul_left]; congr 3
      · norm_cast
      · exact ENNReal.sum_geometric_two_pow_neg_one
    _ = _ := by
      nth_rw 3 [← pow_one 2]
      rw [mul_rotate, ← pow_add, ← mul_assoc, ← pow_add,
        show n + 1 + (k + 1 + 1) = n + k + 3 by lia]

end TopTiles

/-! Definition of function `𝔘(m)` used in the proof of Lemma 5.2.8, and some properties of `𝔘(m)` -/
section 𝔘

open Finset

variable (k) (n) (j) (x)
open scoped Classical in
/-- The function `𝔘(m)` used in the proof of Lemma 5.2.8 -/
def 𝔘 (m : 𝔓 X) := (𝔘₁ k n j).toFinset.filter (fun u ↦ x ∈ 𝓘 u ∧ smul 100 u ≤ smul 1 m)

-- Ball that covers the image of `𝒬`. Radius chosen for convenience with `BallsCoverBalls.pow_mul`
private def big_ball (m : 𝔓 X) (u : 𝔓 X) := ball_(u) (𝒬 m) (2 ^ 9 * 0.2)

variable {k} {n} {j} {x}
variable {x : X} {m u u' u'' : 𝔓 X}
variable (hu : u ∈ 𝔘 k n j x m) (hu' : u' ∈ 𝔘 k n j x m) (hu'' : u'' ∈ 𝔘 k n j x m)

include hu in
private lemma x_mem_𝓘u : x ∈ (𝓘 u) := by
  simp only [𝔘, mem_filter] at hu
  exact hu.2.1

set_option backward.isDefEq.respectTransparency false in
include hu in
private lemma 𝒬m_mem_ball : 𝒬 m ∈ ball_(u) (𝒬 u) 100 := by
  simp only [𝔘, mem_filter, smul] at hu
  exact hu.2.2.2 (by simp)

include hu hu' in
private lemma 𝓘_not_lt_𝓘 : ¬𝓘 u < 𝓘 u' := by
  classical
  intro h
  rw [Grid.lt_def] at h
  have 𝒬m_mem_inter := mem_inter (𝒬m_mem_ball hu) (𝒬m_mem_ball hu')
  simp only [𝔘, 𝔘₁, Grid.lt_def, and_imp, toFinset_setOf, mem_filter] at hu
  exact not_disjoint_iff_nonempty_inter.2 (nonempty_of_mem 𝒬m_mem_inter) <| hu.1.2.2
    u' (mem_toFinset.mp (mem_filter.mp hu').1).1 h.1 h.2

include hu hu' in
private lemma 𝓘_eq_𝓘 : 𝓘 u = 𝓘 u' :=
  have not_disj := Set.not_disjoint_iff.mpr ⟨x, ⟨x_mem_𝓘u hu, x_mem_𝓘u hu'⟩⟩
  le_or_ge_or_disjoint.elim (fun h ↦ (h.lt_or_eq).resolve_left (𝓘_not_lt_𝓘 hu hu'))
    (fun h ↦ ((h.resolve_right not_disj).lt_or_eq.resolve_left (𝓘_not_lt_𝓘 hu' hu)).symm)

include hu hu' in
private lemma ball_eq_ball : ball_(u) = ball_(u') := by
  delta 𝔠 𝔰; rw [𝓘_eq_𝓘 hu hu']

include hu hu' hu'' in
private lemma disjoint_balls (h : u' ≠ u'') :
    Disjoint (ball_(u) (𝒬 u') 0.2) (ball_(u) (𝒬 u'') 0.2) := by
  nth_rewrite 1 [ball_eq_ball hu hu', ball_eq_ball hu hu'']
  convert cball_disjoint h (𝓘_eq_𝓘 hu' hu'') using 2 <;> norm_num

set_option backward.isDefEq.respectTransparency false in
include hu hu' in
private lemma mem_big_ball : 𝒬 u' ∈ big_ball m u := by
  have : 𝒬 m ∈ ball_(u) (𝒬 u') 100 := ball_eq_ball hu hu' ▸ 𝒬m_mem_ball hu'
  rw [@mem_ball_comm] at this
  simp only [big_ball, mem_ball] at this ⊢
  exact this.trans (by norm_num)

open scoped Classical in
include hu in
private lemma subset_big_ball (f : Θ X) (hf : f ∈ (𝔘 k n j x m).image 𝒬) : f ∈ big_ball m u := by
  simp_rw [Finset.mem_image] at hf
  rcases hf with ⟨u', hu', rfl⟩
  exact mem_big_ball hu hu'

variable (m) (u : 𝔓 X) in
private lemma balls_cover_big_ball : CoveredByBalls (big_ball m u) (defaultA a ^ 9) 0.2 :=
  ballsCoverBalls_iterate_nat (𝒬 m)

private lemma 𝒬_injOn_𝔘m : InjOn 𝒬 (SetLike.coe (𝔘 k n j x m)) :=
  fun _ hu _ hu' h ↦ 𝒬_inj h (𝓘_eq_𝓘 hu hu')

set_option backward.isDefEq.respectTransparency false in
private lemma card_𝔘m_le : (𝔘 k n j x m).card ≤ (defaultA a) ^ 9 := by
  classical
  by_cases h : 𝔘 k n j x m = ∅
  · simp only [h, Finset.card_empty]; exact Nat.zero_le _
  have ⟨u, hu⟩ := Finset.nonempty_of_ne_empty h
  let pm := instPseudoMetricSpaceWithFunctionDistance (x := 𝔠 u) (r := (D ^ 𝔰 u / 4))
  have ⟨𝓑, 𝓑_card_le, 𝓑_cover⟩ := balls_cover_big_ball m u
  let 𝓕 (f : Θ X) := ((𝔘 k n j x m).image 𝒬).filter (· ∈ @ball _ pm f 0.2)
  -- `𝒬` is 1-1, `𝓑.biUnion 𝓕` covers `(𝔘 k n j x m).image 𝒬`, and each `𝓕 f` has cardinality
  -- ≤ 1, so `(𝔘 k n j x m).card = ((𝔘 k n j x m).image 𝒬).card ≤ (𝓑.biUnion 𝓕).card ≤ 𝓑.card`
  have 𝒬𝔘_eq_union: (𝔘 k n j x m).image 𝒬 = 𝓑.biUnion 𝓕 := by
    ext f
    simp only [𝓕, Finset.mem_biUnion, mem_filter]
    refine ⟨fun hf ↦ ?_, fun ⟨_, _, h, _⟩ ↦ h⟩
    obtain ⟨g, hg⟩ : ∃ g ∈ 𝓑, f ∈ @ball _ pm g 0.2 := by
      simpa only [mem_iUnion, exists_prop] using 𝓑_cover (subset_big_ball hu f hf)
    exact ⟨g, hg.1, hf, hg.2⟩
  have card_le_one : ∀ f ∈ 𝓑, (𝓕 f).card ≤ 1 := by
    refine fun f _ ↦ card_le_one.mpr (fun g₁ hg₁ g₂ hg₂ ↦ ?_)
    by_contra! h
    simp only [mem_filter, 𝓕] at hg₁ hg₂
    obtain ⟨u₁, hu₁, rfl⟩ := Finset.mem_image.mp hg₁.1
    obtain ⟨u₂, hu₂, rfl⟩ := Finset.mem_image.mp hg₂.1
    apply Set.not_disjoint_iff.mpr ⟨f, mem_ball_comm.mp hg₁.2, mem_ball_comm.mp hg₂.2⟩
    exact disjoint_balls hu hu₁ hu₂ (ne_of_apply_ne 𝒬 h)
  rw [← card_image_iff.mpr 𝒬_injOn_𝔘m, 𝒬𝔘_eq_union]
  exact (mul_one 𝓑.card ▸ card_biUnion_le_card_mul 𝓑 𝓕 1 card_le_one).trans 𝓑_card_le

variable (k n j) (x) in
open scoped Classical in
private def 𝔐' (u : 𝔓 X) := (𝔐 k n).toFinset.filter (fun m ↦ smul 100 u ≤ smul 1 m)

-- Interchange the summations in the proof of Lemma 5.2.8
open scoped Classical in
private lemma interchange :
    ((𝔘₁ k n j).toFinset.filter (x ∈ 𝓘 ·)).sum (fun u ↦ (𝔐' k n u).sum
    (fun m ↦ (𝓘 m : Set X).indicator (1 : X → ℝ) x)) =
    (𝔐 k n).toFinset.sum (fun m ↦ (𝔘 k n j x m).sum
    (fun _ ↦ (𝓘 m : Set X).indicator (1 : X → ℝ) x)) :=
  Finset.sum_comm' fun u m ↦ by simp only [𝔐', 𝔘, Finset.mem_filter]; tauto

end 𝔘

-- Inequality (5.2.20) in the proof of Lemma 5.2.8
open scoped Classical in
private lemma indicator_le : ∀ u ∈ (𝔘₁ k n j).toFinset.filter (x ∈ 𝓘 ·),
    (𝓘 u : Set X).indicator 1 x ≤ (2 : ℝ) ^ (-j : ℤ) * stackSize (𝔐' k n u) x := by
  intro u hu
  by_cases hx : x ∈ (𝓘 u : Set X); swap
  · simp only [Set.indicator_of_notMem hx]
    exact mul_nonneg (zpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  suffices (2 : ℝ) ^ (j : ℤ) ≤ stackSize (𝔐' k n u) x by calc
    _ ≤ (2 : ℝ) ^ (-j : ℤ) * (2 : ℝ) ^ (j : ℤ)       := by
        rw [Set.indicator_of_mem hx, Pi.one_apply, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
    _ ≤ (2 : ℝ) ^ (-j : ℤ) * stackSize (𝔐' k n u) x := by gcongr
  norm_cast
  simp only [𝔘₁, Finset.mem_filter, toFinset_setOf] at hu
  apply le_of_le_of_eq hu.1.2.1.1.2
  simp only [Finset.coe_filter, mem_toFinset, 𝔐', Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun m hm ↦ ?_)
  simp only [TileLike.le_def, smul_fst, Finset.mem_filter] at hm
  simp only [Set.indicator_of_mem (hm.2.2.1.1 hx), Pi.one_apply]

open Finset in
/-- Lemma 5.2.8 -/
lemma tree_count :
    stackSize (𝔘₁ k n j) x ≤ (2 : ℝ) ^ (9 * a - j : ℤ) * stackSize (𝔐 k n) x := by
  classical
  -- When calculating the LHS, we need only sum over those `u` for which `x ∈ 𝓘 u`.
  have : ∑ u ∈ univ.filter (· ∈ 𝔘₁ (X := X) k n j), (𝓘 u : Set X).indicator (1 : X → ℝ) x =
      ∑ u ∈ (𝔘₁ k n j).toFinset.filter (x ∈ 𝓘 ·), (𝓘 u : Set X).indicator (1 : X → ℝ) x := by
    rw [filter_mem_univ_eq_toFinset (𝔘₁ k n j), sum_filter]
    exact sum_congr rfl <|
      fun u _ ↦ by simp [Membership.mem]
  rw [stackSize_real, this]
  -- Use inequality (5.2.20) to bound the LHS by a double sum, then interchange the sums.
  apply le_trans (sum_le_sum indicator_le)
  simp_rw [← mul_sum, stackSize_real, mem_coe, filter_univ_mem, interchange, sum_const]
  let _ : PosMulReflectLE ℝ := inferInstance -- perf: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/performance.20example.20with.20type-class.20inference
  -- Replace the cardinality of `𝔘` with the upper bound proven in `card_𝔘m_le`, and simplify.
  apply le_of_le_of_eq <| (mul_le_mul_iff_right₀ (zpow_pos two_pos _)).mpr <| sum_le_sum <|
    fun _ _ ↦ smul_le_smul_of_nonneg_right card_𝔘m_le <| Set.indicator_apply_nonneg (by simp)
  simp_rw [← smul_sum, nsmul_eq_mul, ← mul_assoc, filter_mem_univ_eq_toFinset (𝔐 k n), defaultA]
  rw [sub_eq_add_neg, zpow_add₀ two_ne_zero, ← pow_mul, mul_comm 9, mul_comm (2 ^ _)]
  norm_cast

/-- Lemma 5.2.9 -/
lemma boundary_exception {u : 𝔓 X} :
    volume (⋃ i ∈ 𝓛 (X := X) n u, (i : Set X)) ≤ C5_2_9 X n * volume (𝓘 u : Set X) := by
  by_cases  h_𝓛_n_u_non_empty : Set.Nonempty (𝓛 (X := X) n u)
  · set X_u := { x ∈ GridStructure.coeGrid (𝓘 u) | Metric.infEDist x (GridStructure.coeGrid (𝓘 u))ᶜ ≤ 12 * (D ^ (𝔰 u - Z * (n + 1) - 1 : ℤ) : ℝ≥0∞)} with h_X_u -- 5.2.25
    calc volume (⋃ i ∈ 𝓛 (X := X) n u, (i : Set X))
      _ ≤ volume X_u := by
          have i_subset_X_u : ∀ i ∈ 𝓛 (X := X) n u, GridStructure.coeGrid i ⊆ X_u := by
            intro i ⟨⟨i_subset_I_u, _⟩, s_i_eq_stuff, I_not_contain_8_ball⟩ ipt hipt
            refine ⟨i_subset_I_u hipt, ?_⟩
            rw [show 𝔰 u - Z * (n + 1) - 1 = s i by norm_cast; linarith]
            obtain ⟨bpt, hbpt, h_bpt_not_in_I_u⟩ : ∃ b ∈ ball (c i) (8 * ↑D ^ s i), b ∉ ↑(𝓘 u) := not_subset.mp I_not_contain_8_ball
            -- triangle inequality between ipt, bpt, c i
            have ipt_bpt_triangle_ineq : dist ipt bpt ≤ (12 * D ^ s i : ℝ) :=
              calc dist ipt bpt
                _ ≤ dist ipt (c i) + dist (c i) bpt := dist_triangle ipt (c i) bpt
                _ ≤ 4 * D ^ s i + dist (c i) bpt := by
                  have dist_ipt_c_i_le : dist ipt (c i) < 4 * D ^ s i := by
                    have ipt_in_ball_4 : ipt ∈ ball (c i) (4 * D ^ s i) := Grid_subset_ball hipt
                    simp_all only [le_eq_subset, ball, mem_setOf_eq, Grid.mem_def]
                  rel [dist_ipt_c_i_le]
                _ ≤ 4 * D ^ s i + dist bpt (c i) := by rw [dist_comm]
                _ ≤ 4 * D ^ s i + 8 * D ^ s i := by
                    have dist_bpt_c_i_le : dist bpt (c i) < 8 * D ^ s i := by
                      simp_all only [le_eq_subset, ball, mem_setOf_eq, Grid.mem_def]
                    rel [dist_bpt_c_i_le]
                _ ≤ 12 * D ^ s i := by linarith
            -- show the the triangle inequality implies distance between ipt and (𝓘 u)ᶜ <= 12 * D ^ s i
            calc Metric.infEDist ipt (GridStructure.coeGrid (𝓘 u))ᶜ
              _ ≤ edist ipt bpt := Metric.infEDist_le_edist_of_mem <| Set.mem_compl h_bpt_not_in_I_u
              _ ≤ ENNReal.ofReal (12 * D ^ s i) := by
                rw [edist_dist]
                exact ENNReal.ofReal_le_ofReal ipt_bpt_triangle_ineq
              _ ≤ ENNReal.ofNNReal (12 * D ^ s i) := le_of_eq <|
                congr_arg (ENNReal.ofNNReal) <| NNReal.coe_injective <| by
                    simpa using zpow_nonneg (by simp) (s i)
              _ ≤ 12 * (D ^ (s i : ℤ) :  ℝ≥0∞) := by
                  push_cast
                  rw [ENNReal.coe_zpow]
                  · push_cast
                    rfl
                  · simp
          exact measure_mono (Set.iUnion₂_subset i_subset_X_u)
      _ ≤ 2 * (12 * D ^ (- Z * (n + 1) - 1 : ℤ) : ℝ≥0) ^ κ * volume (𝓘 u : Set X) := by
          have small_boundary_observation : ∀ i ∈ 𝓛 (X := X) n u, volume X_u ≤ 2 * (12 * D ^ (- Z * (n + 1) - 1 : ℤ) : ℝ≥0) ^ κ * volume (𝓘 u : Set X) := by
            intro i ⟨_, s_i_eq_stuff, _⟩
            -- choose t for small boundary property
            set t := 12 * (D ^ (- Z * (n + 1) - 1 : ℤ) : ℝ≥0) with ht
            -- algebra useful in multiple steps of the proof
            have D_pow_algebra : 12 * (D ^ (- Z * (n + 1) - 1 : ℤ) : ℝ≥0)  * (D ^ (𝔰 u : ℤ) : ℝ≥0) = 12 * (D ^ ( 𝔰 u - Z * (n + 1) - 1 : ℤ) : ℝ≥0) := by
              have : 12 * (D ^ (- Z * (n + 1) - 1 : ℤ) : ℝ≥0)  * (D ^ (𝔰 u : ℤ) : ℝ≥0) = 12 * (D ^ (- Z * (n + 1) - 1 + 𝔰 u : ℤ) : ℝ≥0) := by
                rw [zpow_add₀ (show (D : ℝ≥0) ≠ 0 by norm_num) _ _]
                ring
              rw [this]
              rw [show - Z * (n + 1) - 1 + 𝔰 u = 𝔰 u - Z * (n + 1) - 1 by linarith]
            -- small boundary property assumption for 𝓘 u
            have small_boundary_h : D ^ ((- S - s (𝓘 u)) : ℤ) ≤ t := by
              have one_le_nnreal_D : 1 ≤ (D : ℝ≥0) := by
                have h1 : 1 ≤ (D : ℝ) := one_le_realD _
                assumption_mod_cast
              have small_boundary_h_intermediate : D ^ (- S : ℤ) ≤ t * D ^ (𝔰 u: ℤ) := by
                rw [ht, D_pow_algebra,
                    show 𝔰 u - Z * (n + 1) - 1 = s i by rw [← s_i_eq_stuff]; norm_cast; linarith]
                have bound_i_neg_S : -S ≤ s i := (mem_Icc.mp (range_s_subset ⟨i, rfl⟩)).1
                exact le_mul_of_one_le_of_le (by simp) <| zpow_le_zpow_right₀ (one_le_nnreal_D) bound_i_neg_S
              apply (mul_inv_le_iff₀ <| by positivity).mpr at small_boundary_h_intermediate
              rw [← NNReal.rpow_neg_one] at small_boundary_h_intermediate
              have : (D ^ (𝔰 u : ℤ) : ℝ≥0) ^ (-1 : ℝ) = (D ^ (𝔰 u * (-1)) : ℝ≥0) := by
                rw [show (D ^ (𝔰 u : ℤ) : ℝ≥0) = (D ^ (𝔰 u : ℝ) : ℝ≥0) by norm_cast, ← NNReal.rpow_mul]
                norm_cast
              rwa [this, mul_neg_one, ← zpow_add₀ (show (D : ℝ≥0) ≠ 0 by norm_num),
                   show 𝔰 u = s (𝓘 u) from rfl, add_comm,
                   neg_add_eq_sub] at small_boundary_h_intermediate
            have small_b := GridStructure.small_boundary small_boundary_h
            have X_u_in_terms_of_t : X_u = { x ∈ GridStructure.coeGrid (𝓘 u) | Metric.infEDist x (GridStructure.coeGrid (𝓘 u))ᶜ ≤ ((t * D ^ (s (𝓘 u))):ℝ≥0∞)} := by
              rw [ht, show s (𝓘 u) = 𝔰 u from rfl,
                  show (D ^ 𝔰 u : ℝ≥0∞) = (D ^ 𝔰 u : ℝ≥0) by simp]
              rw_mod_cast [D_pow_algebra, h_X_u]
              have : 12 * (D ^ (𝔰 u - (Z * (n + 1) : ℤ) - 1) : ℝ≥0∞) = ((12 * (D ^ (𝔰 u - (Z * (n + 1)) - 1) : ℝ≥0)) : ℝ≥0∞) := by
                simp
              rw_mod_cast [this]
            rw [show s (𝓘 u) = GridStructure.s (𝓘 u) from rfl] at X_u_in_terms_of_t
            rw [← X_u_in_terms_of_t, measureReal_def, measureReal_def] at small_b
            rw [← ENNReal.toReal_le_toReal] -- this requires showing everything is finite
            · rw [ENNReal.toReal_mul]
              have : (2 * (t ^ κ : ℝ≥0∞)).toReal = 2 * t ^ κ  := by
                norm_cast
                rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
                rfl
              rwa [this]
            · apply LT.lt.ne
              rw [h_X_u]
              apply lt_of_le_of_lt <| volume.mono inter_subset_left
              simp [volume_coeGrid_lt_top]
            · apply LT.lt.ne
              have t_k_lt_top : 2 * (t : ℝ≥0∞) ^ κ < ⊤ := by
                rw [ht]
                exact WithTop.mul_lt_top (by apply WithTop.coe_lt_top) <|
                  (ENNReal.rpow_lt_top_of_nonneg κ_nonneg) (lt_top_iff_ne_top.mp (by apply WithTop.coe_lt_top))
              exact WithTop.mul_lt_top t_k_lt_top volume_coeGrid_lt_top
          obtain ⟨i, hi⟩ := h_𝓛_n_u_non_empty
          exact small_boundary_observation i hi
      _ ≤ C5_2_9 X n * volume (𝓘 u : Set X) := by -- choosing the right k and D
        have coeff_lt : 2 * (12 * D ^ (-Z * (n + 1) - 1 : ℝ)) ^ κ
            ≤ (D ^ (1 - κ * Z * (n + 1)) : ℝ≥0) := by
          have twelve_le_D : 12 ≤ D := by
            apply le_trans (by norm_num) (hundred_lt_D X).le
          have two_time_twelve_over_D_to_the_k_le_D : 2 * (12 / D) ^ κ ≤ (D : ℝ≥0) := by
            have two_le_D : 2 ≤ D := by linarith
            have : 2 * (12 / D) ^ κ ≤ (2 : ℝ≥0) := by
              apply (MulLECancellable.mul_le_iff_le_one_right ?_).mpr
              · apply NNReal.rpow_le_one
                · apply div_le_one_of_le₀ <| by norm_cast
                  simp only [zero_le]
                · apply κ_nonneg
              · simp [MulLECancellable]
            exact this.trans <| by norm_cast
          have two_times_twelve_k_D_minus_k_le_D : 2 * 12 ^ κ * D ^ (-κ) ≤ (D : ℝ≥0) := by
            rwa [← inv_mul_eq_div, NNReal.mul_rpow, NNReal.inv_rpow,
                ← NNReal.rpow_neg, mul_comm _ (12 ^ κ), ← mul_assoc] at two_time_twelve_over_D_to_the_k_le_D
          have mul_by_D_to_the_k_Z : 2 * 12 ^ κ * D ^ (-1*κ)  * D ^ (-1* κ  * Z * (n + 1)) ≤ (D : ℝ≥0) * D ^ (-κ * Z * (n + 1)) := by
            have : 2 * 12 ^ κ * D ^ (-κ) * D ^ (-κ * Z * (n + 1)) ≤ (D : ℝ≥0) * D ^ (-κ * Z * (n + 1)) :=
              mul_le_mul_of_nonneg_right two_times_twelve_k_D_minus_k_le_D (by positivity)
            rwa [← neg_eq_neg_one_mul]
          have rearrange_exponents : 2 * (12 : ℝ≥0) ^ κ * (D ^ (-(1 : ℝ))) ^ κ * (D ^ (-(1 : ℝ) * Z * (n + 1)) : ℝ≥0) ^ κ ≤ (D : ℝ≥0) ^ (1 : ℝ) * D ^ (-κ * Z * (n + 1)) := by
            have : (-1* κ  * Z * (n + 1) : ℝ) = (-1 * Z * (n + 1)) * κ := by ring
            rw [this, NNReal.rpow_mul, NNReal.rpow_mul] at mul_by_D_to_the_k_Z
            rwa [NNReal.rpow_one]
          rwa [mul_assoc, ← NNReal.mul_rpow, mul_assoc, ← NNReal.mul_rpow,
              ← NNReal.rpow_add (by positivity), ← NNReal.rpow_add (by positivity), add_comm,
              ← neg_eq_neg_one_mul, ← Ring.sub_eq_add_neg,
              show  1 + -κ * Z * (n + 1) = 1 - κ * Z * (n + 1) by ring] at rearrange_exponents
        rw [C5_2_9]
        apply ENNReal.coe_le_coe.mpr at coeff_lt
        norm_cast
        have : 12 * (D ^ (-Z * (n + 1) - 1: ℤ ) : ℝ≥0) ≠ 0 := by
          simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultZ, neg_mul, ne_eq, mul_eq_zero,
            OfNat.ofNat_ne_zero, false_or]
          positivity
        rw [← ENNReal.coe_rpow_of_ne_zero (by exact this)]
        exact_mod_cast mul_le_mul_left coeff_lt (volume (𝓘 u : Set X))
  · have : volume (⋃ i ∈ 𝓛 (X := X) n u, (i : Set X)) = 0 := by
      have h1 : volume (⋃ i ∈ 𝓛 (X := X) n u, (i : Set X)) ≤
        ∑' i : 𝓛 (X := X) n u, volume (i : Set X) := measure_biUnion_le _ (𝓛 n u).to_countable _
      have h2 : ∑' i : 𝓛 (X := X) n u, volume (i : Set X) = 0 := by
        have : IsEmpty (𝓛 (X := X) n u) := by
          rw [Set.isEmpty_coe_sort]
          exact Set.not_nonempty_iff_eq_empty.mp h_𝓛_n_u_non_empty
        exact tsum_empty
      exact (le_of_le_of_eq h1 h2).antisymm (by simp)
    simp only [this, zero_le]

lemma third_exception_aux :
    volume (⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X)) ≤
    C5_2_9 X n * 2 ^ (9 * a - j : ℤ) * 2 ^ (n + k + 3) * volume G := by
  classical calc
    _ ≤ volume (⋃ u ∈ 𝔘₁ (X := X) k n j, ⋃ i ∈ 𝓛 (X := X) n u, (i : Set X)) := by
      refine measure_mono (iUnion₂_subset fun p mp ↦ ?_)
      obtain ⟨u, mu, hu⟩ := mp.2; exact subset_iUnion₂_of_subset u mu hu
    _ ≤ ∑' u : 𝔘₁ (X := X) k n j, volume (⋃ i ∈ 𝓛 (X := X) n u, (i : Set X)) :=
      measure_biUnion_le _ (𝔘₁ k n j).to_countable _
    _ ≤ ∑' u : 𝔘₁ (X := X) k n j, C5_2_9 X n * volume (𝓘 u.1 : Set X) :=
      ENNReal.tsum_le_tsum fun x ↦ boundary_exception
    _ = C5_2_9 X n * ∑ u with u ∈ 𝔘₁ (X := X) k n j, volume (𝓘 u : Set X) := by
      rw [filter_mem_univ_eq_toFinset, ENNReal.tsum_mul_left]; congr
      rw [tsum_fintype]; convert (Finset.sum_subtype _ (fun u ↦ mem_toFinset) _).symm; rfl
    _ ≤ C5_2_9 X n * 2 ^ (9 * a - j : ℤ) *
        ∑ m with m ∈ 𝔐 (X := X) k n, volume (𝓘 m : Set X) := by
      rw [mul_assoc]; refine mul_le_mul_right ?_ _
      simp_rw [← lintegral_indicator_one coeGrid_measurable,
        ← lintegral_finsetSum _ fun _ _ ↦ measurable_one.indicator coeGrid_measurable]
      have c1 : ∀ C : Set (𝔓 X),
          ∫⁻ x, ∑ u with u ∈ C, (𝓘 u : Set X).indicator 1 x =
          ∫⁻ x, stackSize C x := fun C ↦ by
        refine lintegral_congr fun _ ↦ ?_; rw [stackSize, Nat.cast_sum]; congr!
        simp_rw [indicator]; split_ifs <;> simp
      rw [c1, c1, ← lintegral_const_mul _ stackSize_measurable]
      refine lintegral_mono fun x ↦ ?_
      simp_rw [← ENNReal.coe_natCast, show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl,
        ← ENNReal.coe_zpow two_ne_zero, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← Real.toNNReal_coe_nat]
      have c2 : (2 : ℝ≥0) ^ (9 * a - j : ℤ) = ((2 : ℝ) ^ (9 * a - j : ℤ)).toNNReal := by
        refine ((fun h ↦ (Real.toNNReal_eq_iff_eq_coe h).mpr) ?_ rfl).symm
        positivity
      rw [c2, ← Real.toNNReal_mul (by positivity)]
      refine Real.toNNReal_le_toNNReal tree_count
    _ ≤ _ := by rw [mul_assoc _ _ (volume G)]; gcongr; exact top_tiles

/-- Lemma 5.2.10 -/
lemma third_exception : volume (G₃ (X := X)) ≤ 2 ^ (-4 : ℤ) * volume G := by
  calc
    _ ≤ ∑' n, volume (⋃ k, ⋃ (_ : k ≤ n), ⋃ j, ⋃ (_ : j ≤ 2 * n + 3),
        ⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X)) := measure_iUnion_le _
    _ ≤ ∑' n, ∑' k, volume (⋃ (_ : k ≤ n), ⋃ j, ⋃ (_ : j ≤ 2 * n + 3),
        ⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X)) := by gcongr; exact measure_iUnion_le _
    _ = ∑' n, ∑' k, volume (if k ≤ n then ⋃ j, ⋃ (_ : j ≤ 2 * n + 3),
        ⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X) else ∅) := by congr!; exact iUnion_eq_if _
    _ = ∑' n, ∑' k, if k ≤ n then volume (⋃ j, ⋃ (_ : j ≤ 2 * n + 3),
        ⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X)) else 0 := by congr!; split_ifs <;> simp
    _ ≤ ∑' n, ∑' k, if k ≤ n then ∑' j, volume (⋃ (_ : j ≤ 2 * n + 3),
        ⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X)) else 0 := by
      gcongr; split_ifs
      · exact measure_iUnion_le _
      · exact le_rfl
    _ ≤ ∑' n, ∑' k, if k ≤ n then ∑' j, volume (⋃ p ∈ 𝔏₄ (X := X) k n j, (𝓘 p : Set X)) else 0 := by
      gcongr; split_ifs
      · gcongr; exact iUnion_subset fun _ _ ↦ id
      · exact le_rfl
    _ ≤ ∑' n, ∑' k, if k ≤ n then ∑' (j : ℕ),
        C5_2_9 X n * 2 ^ (9 * a - j : ℤ) * 2 ^ (n + k + 3) * volume G else 0 := by
      gcongr; split_ifs
      · gcongr; exact third_exception_aux
      · exact le_rfl
    _ = ∑' k, 2 ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G *
        ∑' n, if k ≤ n then (2 * D ^ (-κ * Z) : ℝ≥0∞) ^ (n - k : ℝ) else 0 :=
      third_exception_rearrangement
    _ ≤ ∑' k, 2 ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G *
        ∑' n, if k ≤ n then 2⁻¹ ^ (n - k : ℝ) else 0 := by
      gcongr with k n; split_ifs with hnk
      · refine ENNReal.rpow_le_rpow ?_ (by simpa using hnk)
        calc
          _ ≤ 2 * (2 : ℝ≥0∞) ^ (-100 : ℝ) := mul_le_mul_right (DκZ_le_two_rpow_100 (X := X)) 2
          _ ≤ _ := by
            nth_rw 1 [← ENNReal.rpow_one 2, ← ENNReal.rpow_add _ _ (by simp) (by simp),
              ← ENNReal.rpow_neg_one 2]
            exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
      · exact le_rfl
    _ = ∑' k, 2 ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G *
        ∑' (n : ℕ), 2 ^ (-(1 : ℕ) * n : ℤ) := by
      congr! 3 with k; convert tsum_geometric_ite_eq_tsum_geometric with n hnk
      rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul]; norm_cast
    _ = ∑' k, 2 ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G * 2 := by
      congr!; simpa using ENNReal.sum_geometric_two_pow_neg_one
    _ = 2 ^ (9 * a + 5) * D ^ (1 - κ * Z) * volume G *
        ∑' (k : ℕ), (2 : ℝ≥0∞) ^ (2 * k) * D ^ (-κ * Z * k) := by
      rw [← ENNReal.tsum_mul_left]; congr with k
      have lhsr :
          (2 : ℝ≥0∞) ^ (9 * a + 4 + 2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G * 2 =
          2 ^ (9 * a + 5) * 2 ^ (2 * k) * D ^ (1 - κ * Z * (k + 1)) * volume G := by ring
      have rhsr :
          (2 : ℝ≥0∞) ^ (9 * a + 5) * D ^ (1 - κ * Z) * volume G * (2 ^ (2 * k) * D ^ (-κ * Z * k)) =
          2 ^ (9 * a + 5) * 2 ^ (2 * k) * (D ^ (1 - κ * Z) * D ^ (-κ * Z * k)) * volume G := by
        ring
      rw [lhsr, rhsr]; congr
      rw [← ENNReal.rpow_add _ _ (by rw [defaultD]; simp) (by rw [defaultD]; simp)]
      congr; ring
    _ = 2 ^ (9 * a + 5) * D ^ (1 - κ * Z) * volume G *
        ∑' k, ((2 : ℝ≥0∞) ^ 2 * D ^ (-κ * Z)) ^ k := by
      congr! with k
      rw [ENNReal.rpow_mul, ← ENNReal.rpow_natCast, Nat.cast_mul, ENNReal.rpow_mul 2,
        ← ENNReal.mul_rpow_of_ne_top (by simp) (by simp), ENNReal.rpow_natCast]
      congr 2; norm_cast
    _ ≤ 2 ^ (9 * a + 5) * D ^ (1 - κ * Z) * volume G * ∑' k, 2⁻¹ ^ k := by
      gcongr _ * ∑' _, ?_
      refine pow_le_pow_left' ?_ _
      calc
        _ ≤ 2 ^ 2 * (2 : ℝ≥0∞) ^ (-100 : ℝ) := mul_le_mul_right (DκZ_le_two_rpow_100 (X := X)) _
        _ ≤ _ := by
          nth_rw 1 [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ (by simp) (by simp),
            ← ENNReal.rpow_neg_one 2]
          exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
    _ = 2 ^ (9 * a + 5) * D ^ (1 - κ * Z) * volume G * 2 := by
      congr; convert ENNReal.sum_geometric_two_pow_neg_one with k
      rw [← ENNReal.rpow_intCast, show (-k : ℤ) = (-k : ℝ) by norm_cast, ENNReal.rpow_neg,
        ← ENNReal.inv_pow, ENNReal.rpow_natCast]
    _ ≤ 2 ^ (9 * a + 5) * D ^ (-1 : ℝ) * volume G * 2 := by
      gcongr
      · exact_mod_cast one_le_realD _
      · linarith [two_le_κZ (X := X)]
    _ = 2 ^ (9 * a + 6 - 𝕔 * a ^ 2 : ℤ) * volume G := by
      rw [← mul_rotate, ← mul_assoc, ← pow_succ', defaultD, Nat.cast_pow,
        show ((2 : ℕ) : ℝ≥0∞) = 2 by rfl, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (by simp) (by simp), ← ENNReal.rpow_intCast]
      congr 2; norm_num; ring
    _ ≤ _ := by
      gcongr
      · norm_num
      simp only [Int.reduceNeg, tsub_le_iff_right, le_neg_add_iff_add_le]
      norm_cast
      calc
      4 + (9 * a + 6)
      _ = 9 * a + 10 := by ring
      _ ≤ 3 * 4 * a + 4 * 4 := by lia
      _ ≤ 3 * a * a + a * a := by gcongr <;> linarith [four_le_a X]
      _ = 4 * a ^ 2 := by ring
      _ ≤ 𝕔 * a ^ 2 := by
        gcongr
        linarith [seven_le_c]

/-- Lemma 5.1.1 -/
lemma exceptional_set : volume (G' : Set X) ≤ 2 ^ (-1 : ℤ) * volume G :=
  calc volume G'
    _ ≤ volume G₁ + volume G₂ + volume G₃ :=
      le_add_of_le_add_right (measure_union_le _ G₃) (measure_union_le _ _)
    _ ≤ 2 ^ (- 4 : ℤ) * volume G + 2 ^ (- 2 : ℤ) * volume G + 2 ^ (- 4 : ℤ) * volume G :=
      add_le_add_three first_exception second_exception third_exception
    _ = ((2 : ℝ≥0∞) * 2 ^ (-4 : ℤ) + 2 ^ (- 2 : ℤ)) * volume G := by ring
    _ ≤ 2 ^ (- 1 : ℤ) * volume G := by
      gcongr
      change ((2 : ℝ≥0) : ℝ≥0∞) * (2 : ℝ≥0) ^ (-4 : ℤ) + (2 : ℝ≥0) ^ (-2 : ℤ) ≤
        (2 : ℝ≥0) ^ (-1 : ℤ)
      repeat rw [← ENNReal.coe_zpow (show (2 : ℝ≥0) ≠ 0 by norm_num)]
      rw_mod_cast [← NNReal.coe_le_coe]; norm_num
