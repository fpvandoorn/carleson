import Carleson.Discrete.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
open Classical -- We use quite some `Finset.filter`
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

variable {k n j l : ℕ} {p p' u u' : 𝔓 X} {x : X}

/-! ## Section 5.5 and Lemma 5.1.3 -/

/-- The set 𝔓_{G\G'} in the blueprint -/
def 𝔓pos : Set (𝔓 X) := { p : 𝔓 X | 0 < volume (𝓘 p ∩ G ∩ G'ᶜ) }

lemma exists_mem_aux𝓒 {i : Grid X} (hi : 0 < volume (G ∩ i)) : ∃ k, i ∈ aux𝓒 (k + 1) := by
  have vlt : volume (i : Set X) < ⊤ := volume_coeGrid_lt_top
  have one_le_quot : 1 ≤ volume (i : Set X) / volume (G ∩ i) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hi.ne') (Or.inr vlt.ne), one_mul]
    exact measure_mono inter_subset_right
  have quot_ne_top : volume (i : Set X) / volume (G ∩ i) ≠ ⊤ := by
    rw [Ne, ENNReal.div_eq_top, not_or, not_and_or, not_and_or]
    exact ⟨Or.inr hi.ne', Or.inl vlt.ne⟩
  have ornz : 0 < (volume (i : Set X) / volume (G ∩ i)).toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le one_le_quot).ne' quot_ne_top
  let k : ℝ := Real.logb 2 (volume (i : Set X) / volume (G ∩ i)).toReal
  use ⌊k⌋₊, i, le_rfl
  nth_rw 1 [← ENNReal.mul_lt_mul_left (show 2 ^ (⌊k⌋₊ + 1) ≠ 0 by simp) (by simp), ← mul_assoc,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_intCast, ← ENNReal.rpow_add _ _ (by simp) (by simp)]
  rw [Int.cast_neg, Int.cast_natCast, add_neg_cancel, ENNReal.rpow_zero, one_mul,
    ← ENNReal.div_lt_iff (Or.inl hi.ne') (Or.inr vlt.ne), ← ENNReal.ofReal_toReal quot_ne_top,
    ← @ENNReal.ofReal_toReal (2 ^ (⌊k⌋₊ + 1)) (by simp), ENNReal.ofReal_lt_ofReal_iff (by simp),
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← Real.rpow_natCast,
    ← Real.logb_lt_iff_lt_rpow one_lt_two ornz]
  exact Nat.lt_succ_floor k

lemma exists_k_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : ∃ k, p ∈ TilesAt k := by
  let C : Set ℕ := {k | 𝓘 p ∈ aux𝓒 k}
  have Cn : C.Nonempty := by
    rw [𝔓pos, mem_setOf] at h
    have vpos : 0 < volume (G ∩ 𝓘 p) := by
      rw [inter_comm]; exact h.trans_le (measure_mono inter_subset_left)
    obtain ⟨k, hk⟩ := exists_mem_aux𝓒 vpos; exact ⟨_, hk⟩
  let s : ℕ := WellFounded.min wellFounded_lt _ Cn
  have s_mem : s ∈ C := WellFounded.min_mem ..
  have s_min : ∀ t ∈ C, s ≤ t := fun t mt ↦ WellFounded.min_le _ mt _
  have s_pos : 0 < s := by
    by_contra! h; rw [nonpos_iff_eq_zero] at h
    simp_rw [h, C, aux𝓒, mem_setOf] at s_mem; apply absurd s_mem; push_neg; intro _ _
    rw [Int.neg_ofNat_zero, zpow_zero, one_mul]; exact measure_mono inter_subset_right
  use s - 1; rw [TilesAt, mem_preimage, 𝓒, mem_diff, Nat.sub_add_cancel s_pos]
  have : ∀ t < s, t ∉ C := fun t mt ↦ by contrapose! mt; exact s_min t mt
  exact ⟨s_mem, this (s - 1) (Nat.sub_one_lt_of_lt s_pos)⟩

lemma dens'_le_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : dens' k {p} ≤ 2 ^ (-k : ℤ) := by
  simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left, iSup_le_iff]; intro l hl p' mp' sl
  have vpos : 0 < volume (𝓘 p' : Set X) := by
    refine lt_of_lt_of_le ?_ (measure_mono sl.1.1)
    rw [𝔓pos, mem_setOf, inter_assoc] at h; exact h.trans_le (measure_mono inter_subset_left)
  rw [ENNReal.div_le_iff vpos.ne' volume_coeGrid_lt_top.ne]
  calc
    _ ≤ volume (E₂ l p') := by
      nth_rw 2 [← one_mul (volume _)]; apply mul_le_mul_right'
      rw [show 1 = (l : ℝ≥0∞) ^ (0 : ℤ) by simp]; apply ENNReal.zpow_le_of_le
      · rw [ENNReal.one_le_coe_iff]; exact one_le_two.trans hl
      · linarith [four_le_a X]
    _ ≤ _ := by
      have E : E₂ l p' ⊆ 𝓘 p' ∩ G := inter_subset_left
      rw [TilesAt, mem_preimage, 𝓒, mem_diff] at mp'; replace mp' := mp'.2
      rw [aux𝓒, mem_setOf] at mp'; push_neg at mp'; specialize mp' (𝓘 p') le_rfl
      rw [inter_comm] at E; exact (measure_mono E).trans mp'

lemma exists_E₂_volume_pos_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : ∃ r : ℕ, 0 < volume (E₂ r p) := by
  apply exists_measure_pos_of_not_measure_iUnion_null
  change volume (⋃ n : ℕ, 𝓘 p ∩ G ∩ Q ⁻¹' ball_(p) (𝒬 p) n) ≠ 0
  rw [← inter_iUnion]
  suffices ⋃ i : ℕ, Q ⁻¹' ball_(p) (𝒬 p) i = univ by
    rw [this, inter_univ, ← pos_iff_ne_zero]
    rw [𝔓pos, mem_setOf] at h; exact h.trans_le (measure_mono inter_subset_left)
  simp_rw [iUnion_eq_univ_iff, mem_preimage, mem_ball]
  exact fun x ↦ exists_nat_gt (dist_(p) (Q x) (𝒬 p))

lemma dens'_pos_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) (hp : p ∈ TilesAt k) : 0 < dens' k {p} := by
  simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left, lt_iSup_iff]
  obtain ⟨l, hl⟩ := exists_E₂_volume_pos_of_mem_𝔓pos h
  use max 2 l, le_max_left .., p, hp, le_rfl
  simp_rw [ENNReal.div_pos_iff, ne_eq, mul_eq_zero, not_or, ← ne_eq, ← pos_iff_ne_zero]
  refine ⟨⟨ENNReal.zpow_pos (by simp) (by simp) _, ?_⟩, volume_coeGrid_lt_top.ne⟩
  refine hl.trans_le <| measure_mono <| inter_subset_inter_right _ <| preimage_mono ?_
  change ball_(p) (𝒬 p) _ ⊆ ball_(p) (𝒬 p) _
  exact ball_subset_ball (by simp)

lemma exists_k_n_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : ∃ k n, p ∈ ℭ k n ∧ k ≤ n := by
  obtain ⟨k, mp⟩ := exists_k_of_mem_𝔓pos h; use k
  have dens'_pos : 0 < dens' k {p} := dens'_pos_of_mem_𝔓pos h mp
  have dens'_le : dens' k {p} ≤ 2 ^ (-k : ℤ) := dens'_le_of_mem_𝔓pos h
  have dens'_lt_top : dens' k {p} < ⊤ :=
    dens'_le.trans_lt (ENNReal.zpow_lt_top (by simp) (by simp) _)
  have dens'_toReal_pos : 0 < (dens' k {p}).toReal :=
    ENNReal.toReal_pos dens'_pos.ne' dens'_lt_top.ne
  -- 2 ^ (4 * a - n) < dens' k {p} ≤ 2 ^ (4 * a - n + 1)
  -- 4 * a - n < log_2 dens' k {p} ≤ 4 * a - n + 1
  -- -n < log_2 dens' k {p} - 4 * a ≤ -n + 1
  -- n - 1 ≤ 4 * a - log_2 dens' k {p} < n
  -- n ≤ 4 * a - log_2 dens' k {p} + 1 < n + 1
  -- n = 4 * a + ⌊-log_2 dens' k {p}⌋ + 1
  let v : ℝ := -Real.logb 2 (dens' k {p}).toReal
  have klv : k ≤ v := by
    rw [le_neg, Real.logb_le_iff_le_rpow one_lt_two dens'_toReal_pos,
      show (2 : ℝ) = (2 : ℝ≥0∞).toReal by rfl, ENNReal.toReal_rpow,
      ENNReal.toReal_le_toReal dens'_lt_top.ne (by simp)]
    exact_mod_cast dens'_le
  have klq : k ≤ ⌊v⌋₊ := Nat.le_floor klv
  let n : ℕ := 4 * a + ⌊v⌋₊ + 1; use n; refine ⟨⟨mp, ?_⟩, by omega⟩
  rw [show 4 * (a : ℤ) - (4 * a + ⌊v⌋₊ + 1 : ℕ) = (-⌊v⌋₊ - 1 : ℤ) by omega, sub_add_cancel, mem_Ioc,
    ← ENNReal.ofReal_toReal dens'_lt_top.ne, ← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast,
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_cast,
    ENNReal.ofReal_rpow_of_pos zero_lt_two, ENNReal.ofReal_rpow_of_pos zero_lt_two,
    ENNReal.ofReal_lt_ofReal_iff dens'_toReal_pos, ENNReal.ofReal_le_ofReal_iff (by positivity),
    ← Real.logb_le_iff_le_rpow one_lt_two dens'_toReal_pos,
    ← Real.lt_logb_iff_rpow_lt one_lt_two dens'_toReal_pos,
    Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_sub_left, neg_lt, le_neg]
  constructor
  · rw [add_comm]; exact_mod_cast Nat.lt_succ_floor _
  · exact Nat.floor_le ((Nat.cast_nonneg' k).trans klv)

private lemma two_mul_n_add_six_lt : 2 * n + 6 < 2 ^ (n + 3) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      _ = 2 * n + 6 + 2 := by ring
      _ < 2 ^ (n + 3) + 2 := by gcongr
      _ < 2 ^ (n + 3) + 2 ^ (n + 3) := by omega
      _ = _ := by ring

lemma exists_k_n_j_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) :
    ∃ k n, k ≤ n ∧ (p ∈ 𝔏₀ k n ∨ ∃ j ≤ 2 * n + 3, p ∈ ℭ₁ k n j) := by
  obtain ⟨k, n, mp, hkn⟩ := exists_k_n_of_mem_𝔓pos h; use k, n, hkn
  rw [𝔓pos, mem_setOf, inter_comm _ G'ᶜ, ← inter_assoc] at h
  replace h : 0 < volume (G'ᶜ ∩ (𝓘 p : Set X)) := h.trans_le (measure_mono inter_subset_left)
  rw [inter_comm, G', compl_union, compl_union, inter_comm G₁ᶜ, ← inter_assoc, ← inter_assoc] at h
  replace h : 0 < volume ((𝓘 p : Set X) ∩ G₂ᶜ) :=
    h.trans_le (measure_mono (inter_subset_left.trans inter_subset_left))
  obtain ⟨x, mx, nx⟩ := nonempty_of_measure_ne_zero h.ne'
  simp_rw [G₂, mem_compl_iff, mem_iUnion] at nx; push_neg at nx; specialize nx n k hkn
  let B : ℕ := Finset.card { q | q ∈ 𝔅 k n p }
  have Blt : B < 2 ^ (2 * n + 4) := by
    calc
      _ ≤ Finset.card { m | m ∈ 𝔐 k n ∧ x ∈ 𝓘 m } :=
        Finset.card_le_card (Finset.monotone_filter_right _ (Pi.le_def.mpr fun m ⟨m₁, m₂⟩ ↦
          ⟨m₁, m₂.1.1 mx⟩))
      _ = stackSize (𝔐 k n) x := by
        simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
          Finset.filter_filter]; rfl
      _ ≤ (2 * n + 6) * 2 ^ (n + 1) := by rwa [setA, mem_setOf, not_lt] at nx
      _ < _ := by
        rw [show 2 * n + 4 = (n + 3) + (n + 1) by omega, pow_add _ (n + 3)]
        exact mul_lt_mul_of_pos_right two_mul_n_add_six_lt (by positivity)
  rcases B.eq_zero_or_pos with Bz | Bpos
  · simp_rw [B, filter_mem_univ_eq_toFinset, Finset.card_eq_zero, toFinset_eq_empty] at Bz
    exact Or.inl ⟨mp, Bz⟩
  · right; use Nat.log 2 B; rw [Nat.lt_pow_iff_log_lt one_lt_two Bpos.ne'] at Blt
    refine ⟨by omega, (?_ : _ ∧ _ ≤ B), (?_ : ¬(_ ∧ _ ≤ B))⟩
    · exact ⟨mp, Nat.pow_log_le_self 2 Bpos.ne'⟩
    · rw [not_and, not_le]; exact fun _ ↦ Nat.lt_pow_succ_log_self one_lt_two _

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₀ -/
def ℜ₀ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n), 𝔏₀ k n

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₁ -/
def ℜ₁ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3) (l ≤ Z * (n + 1)), 𝔏₁ k n j l

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₂ -/
def ℜ₂ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3), 𝔏₂ k n j

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₃ -/
def ℜ₃ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3) (l ≤ Z * (n + 1)), 𝔏₃ k n j l

/-- Lemma allowing to peel `⋃ (n : ℕ) (k ≤ n)` from unions in the proof of Lemma 5.5.1. -/
lemma mem_iUnion_iff_mem_of_mem_ℭ {f : ℕ → ℕ → Set (𝔓 X)} (hp : p ∈ ℭ k n ∧ k ≤ n)
    (hf : ∀ k n, f k n ⊆ ℭ k n) : p ∈ ⋃ (n : ℕ) (k ≤ n), f k n ↔ p ∈ f k n := by
  simp_rw [mem_iUnion]; constructor <;> intro h
  · obtain ⟨n', k', _, mp⟩ := h
    have e := pairwiseDisjoint_ℭ (X := X).elim (mem_univ (k, n)) (mem_univ (k', n'))
      (not_disjoint_iff.mpr ⟨p, hp.1, hf k' n' mp⟩)
    rw [Prod.mk.inj_iff] at e
    exact e.1 ▸ e.2 ▸ mp
  · use n, k, hp.2

/-- Lemma allowing to peel `⋃ (j ≤ 2 * n + 3)` from unions in the proof of Lemma 5.5.1. -/
lemma mem_iUnion_iff_mem_of_mem_ℭ₁ {f : ℕ → Set (𝔓 X)} (hp : p ∈ ℭ₁ k n j ∧ j ≤ 2 * n + 3)
    (hf : ∀ j, f j ⊆ ℭ₁ k n j) : p ∈ ⋃ (j ≤ 2 * n + 3), f j ↔ p ∈ f j := by
  simp_rw [mem_iUnion]; constructor <;> intro h
  · obtain ⟨j', _, mp⟩ := h
    have e := pairwiseDisjoint_ℭ₁ (X := X).elim (mem_univ j) (mem_univ j')
      (not_disjoint_iff.mpr ⟨p, hp.1, hf j' mp⟩)
    exact e ▸ mp
  · use j, hp.2

/-- Lemma 5.5.1 -/
lemma antichain_decomposition : 𝔓pos (X := X) ∩ 𝔓₁ᶜ = ℜ₀ ∪ ℜ₁ ∪ ℜ₂ ∪ ℜ₃ := by
  unfold ℜ₀ ℜ₁ ℜ₂ ℜ₃ 𝔓₁; simp_rw [← inter_union_distrib_left]; ext p
  simp_rw [mem_inter_iff, and_congr_right_iff, mem_compl_iff, mem_union]; intro h
  obtain ⟨k, n, hkn, split⟩ := exists_k_n_j_of_mem_𝔓pos h
  have pc : p ∈ ℭ k n := by
    rcases split with ml0 | ⟨_, _, mc1⟩
    · exact 𝔏₀_subset_ℭ ml0
    · exact ℭ₁_subset_ℭ mc1
  iterate 5 rw [mem_iUnion_iff_mem_of_mem_ℭ ⟨pc, hkn⟩]
  pick_goal 5; · exact fun _ _ ↦ 𝔏₀_subset_ℭ
  pick_goal 4; · exact fun _ _ ↦ iUnion₂_subset fun _ _ ↦ iUnion₂_subset fun _ _ ↦ 𝔏₁_subset_ℭ
  pick_goal 3; · exact fun _ _ ↦ iUnion₂_subset fun _ _ ↦ 𝔏₂_subset_ℭ
  pick_goal 2; · exact fun _ _ ↦ iUnion₂_subset fun _ _ ↦ iUnion₂_subset fun _ _ ↦ 𝔏₃_subset_ℭ
  pick_goal -1; · exact fun _ _ ↦ iUnion₂_subset fun _ _ ↦ ℭ₅_subset_ℭ
  by_cases ml0 : p ∈ 𝔏₀ k n
  · simp_rw [ml0, true_or, iff_true, mem_iUnion₂]; push_neg; intros
    exact fun a ↦ disjoint_left.mp 𝔏₀_disjoint_ℭ₁ ml0 (ℭ₅_subset_ℭ₁ a)
  simp_rw [ml0, false_or] at split ⊢
  obtain ⟨j, hj, mc1⟩ := split
  iterate 4 rw [mem_iUnion_iff_mem_of_mem_ℭ₁ ⟨mc1, hj⟩]
  pick_goal 4; · exact fun _ ↦ iUnion₂_subset fun _ _ ↦ 𝔏₁_subset_ℭ₁
  pick_goal 3; · exact fun _ ↦ 𝔏₂_subset_ℭ₁
  pick_goal 2; · exact fun _ ↦ iUnion₂_subset fun _ _ ↦ 𝔏₃_subset_ℭ₁
  pick_goal -1; · exact fun _ ↦ ℭ₅_subset_ℭ₁
  by_cases mc2 : p ∉ ℭ₂ k n j
  all_goals
    have mc2' := mc2
    simp_rw [ℭ₂, layersAbove, mem_diff, not_and, mc1, true_implies, not_not_mem] at mc2'
  · change p ∈ ⋃ (l ≤ Z * (n + 1)), 𝔏₁ k n j l at mc2'
    simp_rw [mc2', true_or, iff_true]; contrapose! mc2
    exact ℭ₅_subset_ℭ₄.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂ mc2
  change p ∉ ⋃ (l ≤ Z * (n + 1)), 𝔏₁ k n j l at mc2'; simp_rw [mc2', false_or]
  rw [not_not_mem] at mc2; by_cases ml2 : p ∈ 𝔏₂ k n j
  · simp_rw [ml2, true_or, iff_true]
    exact fun a ↦ disjoint_left.mp 𝔏₂_disjoint_ℭ₃ ml2 (ℭ₅_subset_ℭ₄.trans ℭ₄_subset_ℭ₃ a)
  simp_rw [ml2, false_or]
  have mc3 : p ∈ ℭ₃ k n j := ⟨mc2, ml2⟩
  by_cases mc4 : p ∉ ℭ₄ k n j
  all_goals
    have mc4' := mc4
    simp_rw [ℭ₄, layersBelow, mem_diff, not_and, mc3, true_implies, not_not_mem] at mc4'
  · change p ∈ ⋃ (l ≤ Z * (n + 1)), 𝔏₃ k n j l at mc4'
    simp_rw [mc4', iff_true]; contrapose! mc4
    exact ℭ₅_subset_ℭ₄ mc4
  change p ∉ ⋃ (l ≤ Z * (n + 1)), 𝔏₃ k n j l at mc4'
  simp_rw [mc4', iff_false, ℭ₅]; rw [not_not_mem] at mc4 ⊢; simp_rw [mem_diff, mc4, true_and]
  have nG₃ : ¬(𝓘 p : Set X) ⊆ G₃ := by
    suffices ¬(𝓘 p : Set X) ⊆ G' by contrapose! this; exact subset_union_of_subset_right this _
    by_contra hv
    rw [𝔓pos, mem_setOf, inter_comm _ G'ᶜ, ← inter_assoc, ← diff_eq_compl_inter,
      diff_eq_empty.mpr hv] at h
    simp at h
  contrapose! nG₃
  exact le_iSup₂_of_le n k <| le_iSup₂_of_le hkn j <|
    le_iSup₂_of_le hj p <| le_iSup_of_le nG₃ subset_rfl

/-- The subset `𝔏₀(k, n, l)` of `𝔏₀(k, n)`, given in Lemma 5.5.3.
  We use the name `𝔏₀'` in Lean. The indexing is off-by-one w.r.t. the blueprint -/
def 𝔏₀' (k n l : ℕ) : Set (𝔓 X) := (𝔏₀ k n).minLayer l

/-- Logarithmic inequality used in the proof of Lemma 5.5.2. -/
lemma ceil_log2_le_floor_four_add_log2 {l : ℝ} (hl : 2 ≤ l) :
    ⌈Real.logb 2 ((l + 6 / 5) / 5⁻¹)⌉₊ ≤ ⌊4 + Real.logb 2 l⌋₊ := by
  have : 2 ≤ Real.logb 2 (l + 6 / 5) + Real.logb 2 5 :=
    calc
      _ ≥ Real.logb 2 (2 ^ (0 : ℝ)) + Real.logb 2 (2 ^ (2 : ℝ)) :=
        add_le_add
          (Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith))
          (Real.logb_le_logb_of_le one_lt_two (by positivity) (by norm_num))
      _ ≥ _ := by simp_rw [Real.logb_rpow zero_lt_two one_lt_two.ne']; norm_num
  rw [div_inv_eq_mul, Real.logb_mul (by positivity) (by positivity), Nat.le_floor_iff']
  · calc
      _ ≤ 1 + Real.logb 2 (l + 6 / 5) + Real.logb 2 5 := by
        rw [add_rotate]; exact (Nat.ceil_lt_add_one (zero_le_two.trans this)).le
      _ ≤ 1 + Real.logb 2 (8 / 5 * l) + Real.logb 2 5 := by
        gcongr
        · exact one_lt_two
        · linarith
      _ = _ := by
        rw [add_assoc, ← Real.logb_mul (by positivity) (by positivity), ← mul_rotate,
          show (5 : ℝ) * (8 / 5) = 2 ^ 3 by norm_num,
          Real.logb_mul (by positivity) (by positivity), ← Real.rpow_natCast,
          Real.logb_rpow zero_lt_two one_lt_two.ne', ← add_assoc]
        norm_num
  · exact (zero_lt_one.trans_le (Nat.one_le_ceil_iff.mpr (zero_lt_two.trans_le this))).ne'

/-- The set `𝔒` in the proof of Lemma 5.5.2. -/
def 𝔒 (p' : 𝔓 X) (l : ℝ≥0) : Finset (𝔓 X) :=
  {p'' | 𝓘 p'' = 𝓘 p' ∧ ¬Disjoint (ball_(p') (𝒬 p') l) (Ω p'')}

lemma card_𝔒 (p' : 𝔓 X) {l : ℝ≥0} (hl : 2 ≤ l) : (𝔒 p' l).card ≤ ⌊2 ^ (4 * a) * l ^ a⌋₊ := by
  have djO : (𝔒 p' l).toSet.PairwiseDisjoint fun p'' ↦ ball_(p') (𝒬 p'') 5⁻¹ :=
    fun p₁ mp₁ p₂ mp₂ hn ↦ by
      simp_rw [𝔒, Finset.coe_filter, mem_setOf, Finset.mem_univ, true_and] at mp₁ mp₂
      change Disjoint (ball_{𝓘 p'} (𝒬 p₁) 5⁻¹) (ball_{𝓘 p'} (𝒬 p₂) 5⁻¹)
      conv => enter [1]; rw [← mp₁.1]
      conv => enter [2]; rw [← mp₂.1]
      exact cball_disjoint hn (mp₁.1.trans mp₂.1.symm)
  have tO : ∀ p'' ∈ 𝔒 p' l,
      ball_(p') (𝒬 p'') 5⁻¹ ⊆ ball_(p') (𝒬 p') (l + 6 / 5) := fun p'' mp'' ↦ by
    apply ball_subset_ball'
    simp_rw [𝔒, Finset.mem_filter, Finset.mem_univ, true_and] at mp''
    obtain ⟨x, mx₁, mx₂⟩ := not_disjoint_iff.mp mp''.2
    replace mx₂ := _root_.subset_cball mx₂
    rw [@mem_ball] at mx₁ mx₂
    calc
      _ ≤ 5⁻¹ + (dist_{𝓘 p'} x (𝒬 p'') + dist_{𝓘 p'} x (𝒬 p')) :=
        add_le_add_left (dist_triangle_left ..) _
      _ ≤ 5⁻¹ + (1 + l) := by gcongr; rw [← mp''.1]; exact mx₂.le
      _ = _ := by rw [inv_eq_one_div, ← add_assoc, add_comm _ l.toReal]; norm_num
  have vO : CoveredByBalls (ball_(p') (𝒬 p') (l + 6 / 5)) ⌊2 ^ (4 * a) * l ^ a⌋₊ 5⁻¹ := by
    apply (ballsCoverBalls_iterate (show 0 < l.toReal + 6 / 5 by positivity)
      (show 0 < 5⁻¹ by positivity) (𝒬 p')).mono_nat
    calc
      _ ≤ (defaultA a) ^ ⌊4 + Real.logb 2 l⌋₊ :=
        pow_le_pow_right₀ Nat.one_le_two_pow (ceil_log2_le_floor_four_add_log2 hl)
      _ ≤ ⌊(defaultA a : ℝ) ^ (4 + Real.logb 2 l)⌋₊ := by
        apply Nat.le_floor; rw [Nat.cast_npow, ← Real.rpow_natCast]
        refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_two_pow)
          (Nat.floor_le ?_)
        calc
          _ ≥ 4 + Real.logb 2 2 :=
            add_le_add_left (Real.logb_le_logb_of_le one_lt_two zero_lt_two hl) _
          _ ≥ _ := by rw [Real.logb_self_eq_one one_lt_two]; norm_num
      _ = _ := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
          mul_comm, add_mul, Real.rpow_add zero_lt_two, show (4 : ℝ) * a = (4 * a : ℕ) by simp,
          Real.rpow_natCast, Real.rpow_mul zero_le_two, Real.rpow_natCast,
          Real.rpow_logb zero_lt_two one_lt_two.ne']
        congr 1; exact zero_lt_two.trans_le hl
  obtain ⟨(T : Finset (Θ X)), cT, uT⟩ := vO
  refine (Finset.card_le_card_of_forall_subsingleton (fun p'' t ↦ 𝒬 p'' ∈ ball_(p') t 5⁻¹)
      (fun p'' mp'' ↦ ?_) (fun t _ o₁ mo₁ o₂ mo₂ ↦ ?_)).trans cT
  · have := (tO _ mp'').trans uT (mem_ball_self (by positivity))
    rwa [mem_iUnion₂, bex_def] at this
  · simp_rw [mem_setOf_eq] at mo₁ mo₂; rw [@mem_ball_comm] at mo₁ mo₂
    exact djO.elim mo₁.1 mo₂.1 (not_disjoint_iff.mpr ⟨t, mo₁.2, mo₂.2⟩)

section

variable {p' : 𝔓 X} {l : ℝ≥0} (hl : 2 ≤ l)
  (qp' : 2 ^ (4 * a - n : ℤ) < l ^ (-a : ℤ) * volume (E₂ l p') / volume (𝓘 p' : Set X))
include hl qp'

lemma lt_quotient_rearrange :
    (2 ^ (4 * a) * l ^ a : ℝ≥0) * 2 ^ (-n : ℤ) < volume (E₂ l p') / volume (𝓘 p' : Set X) := by
  rw [mul_div_assoc] at qp'; convert ENNReal.div_lt_of_lt_mul' qp' using 1
  rw [ENNReal.div_eq_inv_mul,
    ← ENNReal.zpow_neg (by exact_mod_cast (zero_lt_two.trans_le hl).ne') ENNReal.coe_ne_top,
    neg_neg, ENNReal.coe_mul, mul_rotate, mul_assoc, ENNReal.coe_pow, zpow_natCast]
  congr 1
  rw [ENNReal.coe_pow, ENNReal.coe_ofNat, ← zpow_natCast,
    ← ENNReal.zpow_add two_ne_zero ENNReal.two_ne_top]
  congr 1; omega

lemma l_upper_bound : l < 2 ^ n := by
  have ql1 : volume (E₂ l p') / volume (𝓘 p' : Set X) ≤ 1 := by
    apply ENNReal.div_le_of_le_mul; rw [one_mul]; exact measure_mono (E₂_subset ..)
  replace qp' := (lt_quotient_rearrange hl qp').trans_le ql1
  rw [← ENNReal.mul_lt_mul_right (c := 2 ^ (n : ℤ)) (by simp) (by simp), one_mul, mul_assoc,
    ← ENNReal.zpow_add two_ne_zero ENNReal.two_ne_top, neg_add_cancel, zpow_zero, mul_one,
    show (2 ^ (n : ℤ) : ℝ≥0∞) = (2 ^ (n : ℤ) : ℝ≥0) by simp, ENNReal.coe_lt_coe,
    zpow_natCast] at qp'
  calc
    _ ≤ l ^ a := le_self_pow₀ (one_le_two.trans hl) (by linarith [four_le_a X])
    _ ≤ 2 ^ (4 * a) * l ^ a := by
      nth_rw 1 [← one_mul (l ^ a)]; gcongr; exact_mod_cast Nat.one_le_two_pow
    _ < _ := qp'

lemma exists_𝔒_with_le_quotient :
    ∃ b ∈ 𝔒 p' l, 2 ^ (-n : ℤ) < volume (E₁ b) / volume (𝓘 b : Set X) := by
  have cO : (𝔒 p' l).card ≤ ⌊2 ^ (4 * a) * l ^ a⌋₊ := card_𝔒 _ hl
  have ltq : (2 ^ (4 * a) * l ^ a : ℝ≥0) * 2 ^ (-n : ℤ) <
      ∑ p'' ∈ 𝔒 p' l, volume (E₁ p'') / volume (𝓘 p'' : Set X) :=
    calc
      _ < volume (E₂ l p') / volume (𝓘 p' : Set X) := lt_quotient_rearrange hl qp'
      _ ≤ volume (⋃ p'' ∈ 𝔒 p' l, E₁ p'') / volume (𝓘 p' : Set X) := by
        gcongr; simp_rw [E₁, E₂, smul, toTileLike, TileLike.toSet]; intro x mx
        have rsub := biUnion_Ω (i := 𝓘 p'); rw [range_subset_iff] at rsub; specialize rsub x
        simp_rw [mem_iUnion₂, mem_preimage, mem_singleton_iff, exists_prop] at rsub
        obtain ⟨(ps : 𝔓 X), (ips : 𝓘 ps = 𝓘 p'), mps⟩ := rsub; rw [← mem_preimage] at mps
        rw [mem_iUnion₂]; refine ⟨ps, ?_, ?_⟩
        · simp_rw [𝔒, Finset.mem_filter, Finset.mem_univ, ips, true_and, not_disjoint_iff]
          use Q x, mem_preimage.mp mx.2, mem_preimage.mp mps
        · exact ⟨⟨ips.symm ▸ mx.1.1, mx.1.2⟩, mps⟩
      _ ≤ (∑ p'' ∈ 𝔒 p' l, volume (E₁ p'')) / volume (𝓘 p' : Set X) :=
        ENNReal.div_le_div_right (measure_biUnion_finset_le _ _) _
      _ = ∑ p'' ∈ 𝔒 p' l, volume (E₁ p'') / volume (𝓘 p' : Set X) := by
        simp_rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
      _ = _ := by
        refine Finset.sum_congr rfl fun p'' mp'' ↦ ?_
        rw [𝔒, Finset.mem_filter] at mp''; rw [mp''.2.1]
  by_contra! h
  have : ∑ p'' ∈ 𝔒 p' l, volume (E₁ p'') / volume (𝓘 p'' : Set X) ≤
      (2 ^ (4 * a) * l ^ a : ℝ≥0) * 2 ^ (-n : ℤ) :=
    calc
      _ ≤ ∑ _ ∈ 𝔒 p' l, (2 : ℝ≥0∞) ^ (-n : ℤ) := by
        refine Finset.sum_le_sum h
      _ = (𝔒 p' l).card * (2 : ℝ≥0∞) ^ (-n : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        refine mul_le_mul_right' ?_ _
        rw [show ((𝔒 p' l).card : ℝ≥0∞) = ((𝔒 p' l).card : ℝ≥0) by simp, ENNReal.coe_le_coe]
        rw [← Nat.cast_le (α := ℝ≥0)] at cO
        exact cO.trans (Nat.floor_le (by positivity))
  exact (ltq.trans_le this).false

end

/-- Main part of Lemma 5.5.2. -/
lemma iUnion_L0' : ⋃ (l ≤ n), 𝔏₀' (X := X) k n l = 𝔏₀ k n := by
  refine iUnion_minLayer_iff_bounded_series.mpr fun p ↦ ?_
  suffices ¬∃ s : LTSeries (𝔏₀ (X := X) k n), s.length = n + 1 by
    rcases lt_or_le p.length (n + 1) with c | c
    · exact Nat.le_of_lt_succ c
    · exact absurd ⟨p.take ⟨n + 1, by omega⟩, by rw [RelSeries.take_length]⟩ this
  by_contra h; obtain ⟨s, hs⟩ := h; let sl := s.last; have dsl := sl.2.1.2.1
  simp_rw [dens', lt_iSup_iff, mem_singleton_iff, exists_prop, exists_eq_left] at dsl
  obtain ⟨l, hl, p', mp', sp', qp'⟩ := dsl
  obtain ⟨b, mb, qb⟩ := exists_𝔒_with_le_quotient hl qp'
  have 𝓘p'b : 𝓘 p' = 𝓘 b := by rw [𝔒, Finset.mem_filter] at mb; exact mb.2.1.symm
  replace qb := ENNReal.mul_lt_of_lt_div qb
  have mba : b ∈ (aux𝔐 k n).toFinset := by
    simp_rw [mem_toFinset, aux𝔐, mem_setOf, qb, and_true]; rw [TilesAt, mem_preimage] at mp' ⊢
    exact 𝓘p'b ▸ mp'
  obtain ⟨m, lm, maxm⟩ := (aux𝔐 k n).toFinset.exists_le_maximal mba
  replace maxm : m ∈ 𝔐 k n := by simpa only [mem_toFinset] using maxm
  -- We will now show a contradiction. As a member of `𝔏₀ k n` the _first_ element `s₀` of the
  -- `LTSeries s` satisfies `𝔅 k n s₀ = ∅`. But we will show that `m ∈ 𝔅 k n s₀`,
  -- i.e. `smul 100 s₀ ≤ smul 1 m`.
  let s₀ := s.head; apply absurd s₀.2.2; rw [← ne_eq, ← nonempty_iff_ne_empty]; use m, maxm
  constructor
  · have l1 : 𝓘 s₀.1 ≤ 𝓘 sl.1 := s.head_le_last.1
    have l2 : 𝓘 sl.1 ≤ 𝓘 b := 𝓘p'b ▸ sp'.1
    have l3 : 𝓘 b ≤ 𝓘 m := lm.1
    exact (l1.trans l2).trans l3
  change ball_(m) (𝒬 m) 1 ⊆ ball_(s₀.1) (𝒬 s₀.1) 100; intro (θ : Θ X) mθ; rw [@mem_ball] at mθ ⊢
  have aux : dist_(sl.1) (𝒬 sl.1) θ < 2 * l + 3 :=
    calc
      _ ≤ dist_(sl.1) (𝒬 sl.1) (𝒬 p') + dist_(sl.1) (𝒬 p') θ := dist_triangle ..
      _ < l + dist_(sl.1) (𝒬 p') θ := by
        apply add_lt_add_right
        have : 𝒬 p' ∈ ball_(p') (𝒬 p') l := by convert mem_ball_self (zero_lt_two.trans_le hl)
        exact mem_ball'.mp (sp'.2 this)
      _ ≤ l + dist_(p') (𝒬 p') θ := add_le_add_left (Grid.dist_mono sp'.1) _
      _ ≤ l + dist_(p') (𝒬 p') (𝒬 b) + dist_(p') (𝒬 b) θ := by
        rw [add_assoc]; apply add_le_add_left; exact dist_triangle ..
      _ ≤ l + (l + 1) + dist_(b) (𝒬 b) θ := by
        gcongr
        · rw [𝔒, Finset.mem_filter] at mb
          obtain ⟨(x : Θ X), x₁, x₂⟩ := not_disjoint_iff.mp mb.2.2
          replace x₂ := _root_.subset_cball x₂
          rw [@mem_ball] at x₁ x₂
          calc
            _ ≤ dist_(p') x (𝒬 p') + dist_(p') x (𝒬 b) := dist_triangle_left ..
            _ ≤ _ := by
              apply add_le_add x₁.le
              change dist_{𝓘 p'} x (𝒬 b) ≤ 1; rw [𝓘p'b]; exact x₂.le
        · change dist_{𝓘 p'} (𝒬 b) θ ≤ dist_{𝓘 b} (𝒬 b) θ; rw [𝓘p'b]
      _ ≤ l + (l + 1) + (dist_(b) (𝒬 m) (𝒬 b) + dist_(b) (𝒬 m) θ) :=
        add_le_add_left (dist_triangle_left ..) _
      _ ≤ l + (l + 1) + (1 + dist_(m) (𝒬 m) θ) := by
        gcongr
        · exact (dist_𝒬_lt_one_of_le lm).le
        · exact Grid.dist_mono lm.1
      _ < l + (l + 1) + (1 + 1) := by gcongr; exact mem_ball'.mp mθ
      _ = _ := by ring
  calc
    _ ≤ dist_(s₀.1) (𝒬 sl.1) θ + dist_(s₀.1) (𝒬 sl.1) (𝒬 s₀.1) := dist_triangle_left ..
    _ < 1 + dist_(s₀.1) (𝒬 sl.1) θ := by
      rw [add_comm]; exact add_lt_add_right (dist_𝒬_lt_one_of_le s.head_le_last) _
    _ ≤ 1 + C2_1_2 a ^ (n + 1) * dist_(sl.1) (𝒬 sl.1) θ := add_le_add_left (dist_LTSeries hs) _
    _ < 1 + C2_1_2 a ^ (n + 1) * (2 * l + 3) := by gcongr; rw [C2_1_2]; positivity
    _ ≤ 1 + (1 / 512) ^ (n + 1) * (2 ^ (n + 1) + 3) := by
      gcongr
      · rw [C2_1_2]; positivity
      · exact C2_1_2_le_inv_512 X
      · rw [pow_succ']
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (l_upper_bound hl qp').le) zero_le_two
    _ = 1 + (2 / 512) ^ (n + 1) + (1 / 512) ^ (n + 1) * 3 := by
      rw [mul_add, ← add_assoc, ← mul_pow]; norm_num
    _ ≤ 1 + (2 / 512) ^ 1 + (1 / 512) ^ 1 * 3 := by
      gcongr 1 + ?_ + ?_ * 3 <;>
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ < _ := by norm_num

/-- Part of Lemma 5.5.2 -/
lemma pairwiseDisjoint_L0' : univ.PairwiseDisjoint (𝔏₀' (X := X) k n) := pairwiseDisjoint_minLayer

/-- Part of Lemma 5.5.2 -/
lemma antichain_L0' : IsAntichain (· ≤ ·) (𝔏₀' (X := X) k n l) := isAntichain_minLayer

section L2Antichain

/-- Type synonym of `ℭ₁` to apply the `Preorder` of the proof of Lemma 5.5.3 on. -/
private def ℭ₁' (k n j : ℕ) : Type _ := ℭ₁ (X := X) k n j

private instance : Fintype (ℭ₁' (X := X) k n j) := inferInstanceAs (Fintype (ℭ₁ k n j))

private instance : Preorder (ℭ₁' (X := X) k n j) where
  le x y := smul 200 x.1 ≤ smul 200 y.1
  le_refl := by simp
  le_trans _ _ _ xy yz := by
    change smul _ _ ≤ smul _ _ at xy yz ⊢
    exact xy.trans yz

/-- Lemma 5.5.3 -/
lemma antichain_L2 : IsAntichain (· ≤ ·) (𝔏₂ (X := X) k n j) := by
  by_contra h; rw [isAntichain_iff_forall_not_lt] at h; push_neg at h
  obtain ⟨p', mp', p, mp, l⟩ := h
  have p200 : smul 2 p' ≤ smul 200 p := by
    calc
      _ ≤ smul (11 / 10 + C2_1_2 a * 200) p' := by
        apply smul_mono_left
        calc
          _ ≤ 11 / 10 + 1 / 512 * (200 : ℝ) := by gcongr; exact C2_1_2_le_inv_512 X
          _ ≤ _ := by norm_num
      _ ≤ _ := by
        refine smul_C2_1_2 _ (by norm_num) ?_ (wiggle_order_11_10 l.le (C5_3_3_le (X := X)))
        exact (𝓘_strictMono l).ne
  have cp : p ∈ ℭ₁ k n j := (𝔏₂_subset_ℭ₂.trans ℭ₂_subset_ℭ₁) mp
  let C : Finset (LTSeries (ℭ₁' k n j)) := { s | s.head = ⟨p, cp⟩ }
  have Cn : C.Nonempty := by
    use RelSeries.singleton _ ⟨p, cp⟩
    simp_rw [C, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  obtain ⟨z, mz, maxz⟩ := C.exists_max_image (·.length) Cn
  simp_rw [C, Finset.mem_filter, Finset.mem_univ, true_and] at mz
  by_cases mu : z.last.1 ∈ 𝔘₁ k n j
  · have px : z.head ≤ z.last := z.monotone (Fin.zero_le _)
    rw [mz] at px
    apply absurd mp'; rw [𝔏₂, mem_setOf, not_and_or, not_not]; right; use z.last.1, mu
    have : 𝓘 p' < 𝓘 p := 𝓘_strictMono l
    exact ⟨(this.trans_le px.1).ne, (p200.trans px).trans (smul_mono_left (by norm_num))⟩
  · simp_rw [𝔘₁, mem_setOf, not_and, z.last.2, true_implies, not_forall, exists_prop] at mu
    obtain ⟨q, mq, lq, ndjq⟩ := mu; rw [not_disjoint_iff] at ndjq; obtain ⟨ϑ, mϑ₁, mϑ₂⟩ := ndjq
    have cpos : 0 < C2_1_2 a := by rw [C2_1_2]; positivity
    have s200 : smul 200 z.last.1 ≤ smul 200 q := by
      refine ⟨lq.le, (?_ : ball_(q) (𝒬 q) 200 ⊆ ball_(z.last.1) (𝒬 z.last.1) 200)⟩
      intro (r : Θ X) mr
      rw [@mem_ball] at mr mϑ₁ mϑ₂ ⊢
      calc
        _ ≤ dist_(z.last.1) r (𝒬 q) + dist_(z.last.1) (𝒬 q) ϑ + dist_(z.last.1) ϑ (𝒬 z.last.1) :=
          dist_triangle4 ..
        _ ≤ C2_1_2 a * dist_(q) r (𝒬 q) + C2_1_2 a * dist_(q) (𝒬 q) ϑ + 100 := by
          gcongr <;> exact Grid.dist_strictMono lq
        _ ≤ C2_1_2 a * (200 + 100) + 100 := by rw [mul_add]; gcongr; rw [dist_comm]; exact mϑ₂.le
        _ ≤ (1 / 512) * 300 + 100 := by
          rw [show (200 : ℝ) + 100 = 300 by norm_num]; gcongr
          exact C2_1_2_le_inv_512 X
        _ < _ := by norm_num
    have : z.last < ⟨q, mq⟩ := by
      refine ⟨s200, (?_ : ¬(smul 200 q ≤ smul 200 z.last.1))⟩
      rw [TileLike.le_def, not_and_or]; exact Or.inl (not_le_of_gt lq)
    apply absurd maxz; push_neg; use z.snoc ⟨q, mq⟩ this, by simp [C, mz], by simp

end L2Antichain

/-- Part of Lemma 5.5.4 -/
lemma antichain_L1 : IsAntichain (· ≤ ·) (𝔏₁ (X := X) k n j l) := isAntichain_minLayer

/-- Part of Lemma 5.5.4 -/
lemma antichain_L3 : IsAntichain (· ≤ ·) (𝔏₃ (X := X) k n j l) := isAntichain_maxLayer

/-- The constant used in Lemma 5.1.3, with value `2 ^ (210 * a ^ 3) / (q - 1) ^ 5` -/
-- todo: redefine in terms of other constants
def C5_1_3 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (210 * a ^ 3) / (q - 1) ^ 5

lemma C5_1_3_pos : C5_1_3 a nnq > 0 := sorry

lemma forest_complement {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
  ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖₊ ≤
    C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  sorry
