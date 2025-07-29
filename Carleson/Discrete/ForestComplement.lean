import Carleson.Antichain.AntichainOperator
import Carleson.Discrete.Defs
import Carleson.Discrete.SumEstimates
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Complex.ExponentialBounds

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
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

lemma exists_j_of_mem_𝔓pos_ℭ (h : p ∈ 𝔓pos (X := X)) (mp : p ∈ ℭ k n) (hkn : k ≤ n) :
    p ∈ 𝔏₀ k n ∨ ∃ j ≤ 2 * n + 3, p ∈ ℭ₁ k n j := by
  classical
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

lemma exists_k_n_j_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) :
    ∃ k n, k ≤ n ∧ (p ∈ 𝔏₀ k n ∨ ∃ j ≤ 2 * n + 3, p ∈ ℭ₁ k n j) := by
  obtain ⟨k, n, mp, hkn⟩ := exists_k_n_of_mem_𝔓pos h
  exact ⟨k, n, hkn, exists_j_of_mem_𝔓pos_ℭ h mp hkn⟩

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
    rw [Prod.mk_inj] at e
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

lemma notMem_ℭ₅_iff_mem_𝔏₃ (hkn : k ≤ n) (hj : j ≤ 2 * n + 3)
    (h : p ∈ 𝔓pos) (mc2 : p ∈ ℭ₂ k n j) (ml2 : p ∉ 𝔏₂ k n j) :
    p ∉ ℭ₅ k n j ↔ p ∈ ⋃ l, ⋃ (_ : l ≤ Z * (n + 1)), 𝔏₃ k n j l := by
  have mc3 : p ∈ ℭ₃ k n j := ⟨mc2, ml2⟩
  by_cases mc4 : p ∉ ℭ₄ k n j
  all_goals
    have mc4' := mc4
    simp_rw [ℭ₄, layersBelow, mem_diff, not_and, mc3, true_implies, not_notMem] at mc4'
  · change p ∈ ⋃ (l ≤ Z * (n + 1)), 𝔏₃ k n j l at mc4'
    simp_rw [mc4', iff_true]; contrapose! mc4
    exact ℭ₅_subset_ℭ₄ mc4
  change p ∉ ⋃ (l ≤ Z * (n + 1)), 𝔏₃ k n j l at mc4'
  simp_rw [mc4', iff_false, ℭ₅]; rw [not_notMem] at mc4 ⊢; simp_rw [mem_diff, mc4, true_and]
  have nG₃ : ¬(𝓘 p : Set X) ⊆ G₃ := by
    suffices ¬(𝓘 p : Set X) ⊆ G' by contrapose! this; exact subset_union_of_subset_right this _
    by_contra hv
    rw [𝔓pos, mem_setOf, inter_comm _ G'ᶜ, ← inter_assoc, ← diff_eq_compl_inter,
      diff_eq_empty.mpr hv] at h
    simp at h
  contrapose! nG₃
  exact le_iSup₂_of_le n k <| le_iSup₂_of_le hkn j <|
    le_iSup₂_of_le hj p <| le_iSup_of_le nG₃ Subset.rfl


/-- Lemma 5.5.1.

We will not use the lemma in this form, as to decompose the Carleson sum it is also crucial that
the union is disjoint. This is easier to formalize by decomposing into successive terms, taking
advantage of disjointess at each step, instead of doing everything in one go. Still, we keep this
lemma as it corresponds to the blueprint, and the key steps of its proof will also be the key steps
when doing the successive decompositions.
-/
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
    simp_rw [ℭ₂, layersAbove, mem_diff, not_and, mc1, true_implies, not_notMem] at mc2'
  · change p ∈ ⋃ (l ≤ Z * (n + 1)), 𝔏₁ k n j l at mc2'
    simp_rw [mc2', true_or, iff_true]; contrapose! mc2
    exact ℭ₅_subset_ℭ₄.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂ mc2
  change p ∉ ⋃ (l ≤ Z * (n + 1)), 𝔏₁ k n j l at mc2'; simp_rw [mc2', false_or]
  rw [not_notMem] at mc2; by_cases ml2 : p ∈ 𝔏₂ k n j
  · simp_rw [ml2, true_or, iff_true]
    exact fun a ↦ disjoint_left.mp 𝔏₂_disjoint_ℭ₃ ml2 (ℭ₅_subset_ℭ₄.trans ℭ₄_subset_ℭ₃ a)
  simp_rw [ml2, false_or]
  exact notMem_ℭ₅_iff_mem_𝔏₃ hkn hj h mc2 ml2

/-- The subset `𝔏₀(k, n, l)` of `𝔏₀(k, n)`, given in Lemma 5.5.3.
  We use the name `𝔏₀'` in Lean. -/
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

open scoped Classical in
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
    simp_rw [𝔒, Finset.mem_filter_univ] at mp''
    obtain ⟨x, mx₁, mx₂⟩ := not_disjoint_iff.mp mp''.2
    replace mx₂ := _root_.subset_cball mx₂
    rw [@mem_ball] at mx₁ mx₂
    calc
      _ ≤ 5⁻¹ + (dist_{𝓘 p'} x (𝒬 p'') + dist_{𝓘 p'} x (𝒬 p')) :=
        add_le_add_left (dist_triangle_left ..) _
      _ ≤ 5⁻¹ + (1 + l) := by gcongr; rw [← mp''.1]; exact mx₂.le
      _ = _ := by rw [inv_eq_one_div, ← add_assoc, add_comm _ l.toReal]; norm_num
  have vO : CoveredByBalls (ball_(p') (𝒬 p') (l + 6 / 5)) ⌊2 ^ (4 * a) * l ^ a⌋₊ 5⁻¹ := by
    apply (ballsCoverBalls_iterate (show 0 < 5⁻¹ by positivity) (𝒬 p')).mono_nat
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
    ← ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top]
  congr 1; omega

lemma l_upper_bound : l < 2 ^ n := by
  have ql1 : volume (E₂ l p') / volume (𝓘 p' : Set X) ≤ 1 := by
    apply ENNReal.div_le_of_le_mul; rw [one_mul]; exact measure_mono (E₂_subset ..)
  replace qp' := (lt_quotient_rearrange hl qp').trans_le ql1
  rw [← ENNReal.mul_lt_mul_right (c := 2 ^ (n : ℤ)) (by simp) (by simp), one_mul, mul_assoc,
    ← ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top, neg_add_cancel, zpow_zero, mul_one,
    show (2 ^ (n : ℤ) : ℝ≥0∞) = (2 ^ (n : ℤ) : ℝ≥0) by simp, ENNReal.coe_lt_coe,
    zpow_natCast] at qp'
  calc
    _ ≤ l ^ a := le_self_pow₀ (one_le_two.trans hl) (by linarith [four_le_a X])
    _ ≤ 2 ^ (4 * a) * l ^ a := by
      nth_rw 1 [← one_mul (l ^ a)]; gcongr; exact_mod_cast Nat.one_le_two_pow
    _ < _ := qp'

lemma exists_𝔒_with_le_quotient :
    ∃ b ∈ 𝔒 p' l, 2 ^ (-n : ℤ) < volume (E₁ b) / volume (𝓘 b : Set X) := by
  classical
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
lemma iUnion_L0' : ⋃ (l < n), 𝔏₀' (X := X) k n l = 𝔏₀ k n := by
  classical
  refine iUnion_lt_minLayer_iff_bounded_series.mpr fun p ↦ ?_
  suffices ¬∃ s : LTSeries (𝔏₀ (X := X) k n), s.length = n by
    rcases lt_or_ge p.length n with c | c
    · exact c
    · exact absurd ⟨p.take ⟨n, by omega⟩, by rw [RelSeries.take_length]⟩ this
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
    _ ≤ 1 + C2_1_2 a ^ n * dist_(sl.1) (𝒬 sl.1) θ := add_le_add_left (dist_LTSeries hs) _
    _ < 1 + C2_1_2 a ^ n * (2 * l + 3) := by gcongr; rw [C2_1_2]; positivity
    _ ≤ 1 + (1 / 256) ^ n * (2 * 2 ^ n + 3) := by
      gcongr
      · rw [C2_1_2]; positivity
      · exact C2_1_2_le_inv_256 X
      · exact_mod_cast (l_upper_bound hl qp').le
    _ = 1 + 2 * (2 / 256) ^ n + (1 / 256) ^ n * 3 := by
      simp [div_pow]; ring
    _ ≤ 1 + 2 * (2 / 256) ^ 0 + (1 / 256) ^ 0 * 3 := by
      gcongr 1 + 2 * ?_ + ?_ * 3 <;>
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ < _ := by norm_num

/-- Part of Lemma 5.5.2 -/
lemma pairwiseDisjoint_L0' : univ.PairwiseDisjoint (𝔏₀' (X := X) k n) := pairwiseDisjoint_minLayer

/-- Part of Lemma 5.5.2 -/
lemma antichain_L0' : IsAntichain (· ≤ ·) (𝔏₀' (X := X) k n l) := isAntichain_minLayer

section L2Antichain

/-- Type synonym of `ℭ₁` to apply the `Preorder` of the proof of Lemma 5.5.3 on. -/
private def ℭ₁' (k n j : ℕ) : Type _ := ℭ₁ (X := X) k n j

open scoped Classical in
private instance : Fintype (ℭ₁' (X := X) k n j) := inferInstanceAs (Fintype (ℭ₁ k n j))

private instance : Preorder (ℭ₁' (X := X) k n j) where
  le x y := smul 200 x.1 ≤ smul 200 y.1
  le_refl := by simp
  le_trans _ _ _ xy yz := by
    change smul _ _ ≤ smul _ _ at xy yz ⊢
    exact xy.trans yz

/-- Lemma 5.5.3 -/
lemma antichain_L2 : IsAntichain (· ≤ ·) (𝔏₂ (X := X) k n j) := by
  classical
  by_contra h; rw [isAntichain_iff_forall_not_lt] at h; push_neg at h
  obtain ⟨p', mp', p, mp, l⟩ := h
  have p200 : smul 2 p' ≤ smul 200 p := by
    calc
      _ ≤ smul (11 / 10 + C2_1_2 a * 200) p' := by
        apply smul_mono_left
        calc
          _ ≤ 11 / 10 + 1 / 256 * (200 : ℝ) := by gcongr; exact C2_1_2_le_inv_256 X
          _ ≤ _ := by norm_num
      _ ≤ _ := by
        refine smul_C2_1_2 _ (by norm_num) ?_ (wiggle_order_11_10 l.le (C5_3_3_le (X := X)))
        exact (𝓘_strictMono l).ne
  have cp : p ∈ ℭ₁ k n j := (𝔏₂_subset_ℭ₂.trans ℭ₂_subset_ℭ₁) mp
  let C : Finset (LTSeries (ℭ₁' k n j)) := { s | s.head = ⟨p, cp⟩ }
  have Cn : C.Nonempty := by
    use RelSeries.singleton _ ⟨p, cp⟩
    rw [Finset.mem_filter_univ]; rfl
  obtain ⟨z, mz, maxz⟩ := C.exists_max_image (·.length) Cn
  rw [Finset.mem_filter_univ] at mz
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
        _ ≤ (1 / 256) * 300 + 100 := by
          rw [show (200 : ℝ) + 100 = 300 by norm_num]; gcongr
          exact C2_1_2_le_inv_256 X
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

/- Our goal is now to estimate `∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ` by decomposing `𝔓₁ᶜ` as a
union of disjoint antichains. For this, we proceed step by step, isolating some antichains and
some sets that remain to be decomposed. After 4 steps, we will get a sum of integrals corresponding
to the (disjoint) decomposition in Lemma 5.5.1.
-/

/-- The Carleson sum over `𝔓₁ᶜ` and `𝔓pos ∩ 𝔓₁ᶜ` coincide at ae every point of `G \ G'`. -/
lemma carlesonSum_𝔓₁_compl_eq_𝔓pos_inter (f : X → ℂ) :
    ∀ᵐ x, x ∈ G \ G' → carlesonSum 𝔓₁ᶜ f x = carlesonSum (𝔓pos (X := X) ∩ 𝔓₁ᶜ) f x := by
  have A p (hp : p ∈ (𝔓pos (X := X))ᶜ) : ∀ᵐ x, x ∈ G \ G' → x ∉ 𝓘 p := by
    simp only [𝔓pos, mem_compl_iff, mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hp
    filter_upwards [measure_zero_iff_ae_notMem.mp hp] with x hx h'x (h''x : x ∈ (𝓘 p : Set X))
    simp [h''x, h'x.1, h'x.2] at hx
  rw [← ae_ball_iff (to_countable 𝔓posᶜ)] at A
  filter_upwards [A] with x hx h'x
  simp only [carlesonSum]
  symm
  apply Finset.sum_subset
  · intro p hp
    simp_rw [Finset.mem_filter_univ] at hp ⊢
    exact hp.2
  · intro p hp h'p
    simp_rw [Finset.mem_filter_univ] at hp h'p
    simp only [mem_inter_iff, hp, and_true] at h'p
    have : x ∉ 𝓘 p := hx _ h'p h'x
    have : x ∉ E p := by simp at this; simp [E, this]
    simp [carlesonOn, this]

/-- The Carleson sum over `𝔓pos ∩ 𝔓₁ᶜ` can be decomposed as a sum over the intersections of this
set with various `ℭ k n`. -/
lemma carlesonSum_𝔓pos_eq_sum {f : X → ℂ} {x : X} :
    carlesonSum (𝔓pos (X := X) ∩ 𝔓₁ᶜ) f x =
      ∑ n ≤ maxℭ X, ∑ k ≤ n, carlesonSum (𝔓pos (X := X) ∩ 𝔓₁ᶜ ∩ ℭ k n) f x := by
  simp only [Finset.sum_sigma']
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · rintro ⟨n, k⟩ - ⟨n', k'⟩ - h
    simp only [ne_eq, Sigma.mk.inj_iff, heq_eq_eq] at h
    simp only [Function.onFun, disjoint_iff_forall_ne]
    have W := pairwiseDisjoint_ℭ (X := X) (mem_univ ⟨k, n⟩) (mem_univ ⟨k', n'⟩)
      (by simp [-not_and]; tauto)
    intro x hx y hy
    exact (disjoint_iff_forall_ne.1 W) hx.2 hy.2
  congr
  ext p
  simp only [mem_inter_iff, mem_compl_iff, Finset.mem_sigma,
    Finset.mem_Iic, mem_iUnion, exists_and_left, exists_prop, Sigma.exists, iff_self_and, and_imp]
  intro hp h'p
  rcases exists_k_n_of_mem_𝔓pos hp with ⟨k, n, h'p, hkn⟩
  exact ⟨n, k, ⟨le_maxℭ_of_nonempty ⟨p, h'p⟩ , hkn⟩, h'p⟩

/-- In each set `ℭ k n`, the Carleson sum can be decomposed as a sum over `𝔏₀ k n` and over
various `ℭ₁ k n j`. -/
lemma carlesonSum_𝔓pos_inter_ℭ_eq_add_sum {f : X → ℂ} {x : X} (hkn : k ≤ n) :
    carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ k n) f x =
      carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀ k n) f x
      + ∑ j ≤ 2 * n + 3, carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₁ k n j) f x := by
  conv_lhs => rw [← carlesonSum_inter_add_inter_compl _ (𝔏₀ k n)]
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · apply PairwiseDisjoint.subset _ (subset_univ _)
    apply (pairwiseDisjoint_ℭ₁ (k := k) (n := n)).mono
    intro j
    exact inter_subset_right
  congr 2
  · ext p
    simp only [mem_inter_iff, mem_compl_iff, and_congr_left_iff, and_iff_left_iff_imp, and_imp]
    intro hp
    simp [𝔏₀_subset_ℭ hp]
  · apply Subset.antisymm
    · rintro p ⟨⟨hp, Hp⟩, h'p⟩
      rcases exists_j_of_mem_𝔓pos_ℭ hp.1 Hp hkn with H
      simp only [mem_compl_iff] at h'p
      simp only [h'p, false_or] at H
      simp only [Finset.mem_Iic, mem_iUnion, mem_inter_iff, hp, true_and, exists_prop]
      exact H
    · intro p hp
      simp only [Finset.mem_Iic, mem_iUnion, exists_prop] at hp
      rcases hp with ⟨i, hi, h'i, h''i⟩
      exact ⟨⟨h'i, ℭ₁_subset_ℭ h''i⟩, disjoint_left.1 𝔏₀_disjoint_ℭ₁.symm h''i⟩

lemma carlesonSum_𝔓pos_inter_𝔏₀_eq_sum {f : X → ℂ} {x : X} :
    carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀ k n) f x =
      ∑ l < n, carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x := by
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · apply PairwiseDisjoint.subset _ (subset_univ _)
    apply (pairwiseDisjoint_L0' (k := k) (n := n)).mono
    intro j
    exact inter_subset_right
  congr
  rw [← iUnion_L0']
  ext p
  simp

/-- In each set `ℭ₁ k n j`, the Carleson sum can be decomposed as a sum over `ℭ₂ k n j` and over
various `𝔏₁ k n j l`. -/
lemma carlesonSum_𝔓pos_inter_ℭ₁_eq_add_sum {f : X → ℂ} {x : X} :
    carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₁ k n j) f x =
      carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₂ k n j) f x
      + ∑ l ≤ Z * (n + 1), carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x := by
  classical
  conv_lhs => rw [← carlesonSum_inter_add_inter_compl _ (ℭ₂ k n j)]
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · apply PairwiseDisjoint.subset _ (subset_univ _)
    have : univ.PairwiseDisjoint fun l ↦ 𝔏₁ (X := X) k n j l := pairwiseDisjoint_minLayer
    apply this.mono
    intro j
    exact inter_subset_right
  congr 2
  · ext p
    simp only [mem_inter_iff, mem_compl_iff, and_congr_left_iff, and_iff_left_iff_imp, and_imp]
    intro hp
    simp [ℭ₂_subset_ℭ₁ hp]
  · ext p
    simp only [ℭ₂, layersAbove, mem_inter_iff, mem_compl_iff, mem_diff, mem_iUnion, exists_prop,
      not_exists, not_and, not_forall, Decidable.not_not, Finset.mem_Iic, 𝔏₁]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simpa [h.1.1] using h.2 h.1.2
    · rcases h with ⟨i, hi, h'i⟩
      simp only [h'i.1, not_false_eq_true, and_self, minLayer_subset h'i.2, forall_const, true_and]
      exact ⟨i, hi, h'i.2⟩

/-- In each set `ℭ₂ k n j`, the Carleson sum can be decomposed as a sum over `𝔏₂ k n j` and over
various `𝔏₃ k n j l`. -/
lemma carlesonSum_𝔓pos_inter_ℭ₂_eq_add_sum {f : X → ℂ} {x : X} (hkn : k ≤ n) (hj : j ≤ 2 * n + 3) :
    carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₂ k n j) f x =
      carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₂ k n j) f x
      + ∑ l ≤ Z * (n + 1), carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₃ k n j l) f x := by
  conv_lhs => rw [← carlesonSum_inter_add_inter_compl _ (𝔏₂ k n j)]
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · apply PairwiseDisjoint.subset _ (subset_univ _)
    have : univ.PairwiseDisjoint fun l ↦ 𝔏₃ (X := X) k n j l := pairwiseDisjoint_minLayer
    apply this.mono
    intro j
    exact inter_subset_right
  congr 2
  · ext p
    simp only [mem_inter_iff, mem_compl_iff, and_congr_left_iff, and_iff_left_iff_imp, and_imp]
    intro hp
    simp [𝔏₂_subset_ℭ₂ hp]
  · ext p
    simp only [mem_inter_iff, mem_compl_iff,
      Finset.mem_Iic, mem_iUnion, exists_and_left, exists_prop]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · refine ⟨h.1.1, ?_⟩
      simp only [𝔓₁, mem_iUnion, exists_prop, not_exists, not_and] at h
      have : p ∉ ℭ₅ k n j := h.1.1.2 n k hkn j hj
      simpa using (notMem_ℭ₅_iff_mem_𝔏₃ (X := X) hkn hj h.1.1.1 h.1.2 h.2).1 this
    · rcases h.2 with ⟨l, lZ, hl⟩
      exact ⟨⟨h.1, ℭ₃_subset_ℭ₂ (maxLayer_subset hl)⟩,
        disjoint_right.1 𝔏₂_disjoint_ℭ₃ (maxLayer_subset hl)⟩




/-- Putting together all the previous decomposition lemmas, one gets an estimate of the integral
of `‖carlesonSum 𝔓₁ᶜ f x‖ₑ` by a sum of integrals of the same form over various subsets of `𝔓`,
which are all antichains by design. -/
lemma lintegral_carlesonSum_𝔓₁_compl_le_sum_lintegral {f : X → ℂ} (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ ≤
        (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n,
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₂ k n j) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₃ k n j l) f x‖ₑ) := calc
  ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ
  _ = ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ) f x‖ₑ := by
    apply lintegral_congr_ae
    apply (ae_restrict_iff' (measurableSet_G.diff measurable_G')).2
    filter_upwards [carlesonSum_𝔓₁_compl_eq_𝔓pos_inter f] with x hx h'x
    simp [hx h'x]
  _ ≤ ∑ n ≤ maxℭ X, ∑ k ≤ n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ k n) f x‖ₑ := by
    simp only [Finset.sum_sigma']
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    simp only [Finset.sum_sigma', carlesonSum_𝔓pos_eq_sum]
    apply enorm_sum_le
  _ ≤ ∑ n ≤ maxℭ X, ∑ k ≤ n, ((∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀ k n) f x‖ₑ)
      + ∑ j ≤ 2 * n + 3, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₁ k n j) f x‖ₑ) := by
    gcongr with n hn k hkn
    simp only [Finset.mem_Iic] at hkn
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    rw [← lintegral_add_left']; swap
    · exact h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    rw [carlesonSum_𝔓pos_inter_ℭ_eq_add_sum hkn]
    apply (enorm_add_le _ _).trans
    gcongr
    apply enorm_sum_le
  _ = (∑ n ≤ maxℭ X, ∑ k ≤ n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀ k n) f x‖ₑ)
      + ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
        ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₁ k n j) f x‖ₑ := by
    simp only [Finset.sum_add_distrib]
  _ ≤ (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
        ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₁ k n j) f x‖ₑ := by
    gcongr with n hn k hk
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    rw [carlesonSum_𝔓pos_inter_𝔏₀_eq_sum]
    apply enorm_sum_le
  _ ≤ (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
      ((∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₂ k n j) f x‖ₑ)
        + ∑ l ≤ Z * (n + 1), ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x‖ₑ) := by
    gcongr with n hn k hk j hj
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    rw [← lintegral_add_left']; swap
    · exact h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    rw [carlesonSum_𝔓pos_inter_ℭ₁_eq_add_sum]
    apply (enorm_add_le _ _).trans
    gcongr
    apply enorm_sum_le
  _ = (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x‖ₑ)
      + ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ ℭ₂ k n j) f x‖ₑ := by
    simp only [Finset.sum_add_distrib]
    abel
  _ ≤ (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x‖ₑ)
      + ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
        ((∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₂ k n j) f x‖ₑ)
          + ∑ l ≤ Z * (n + 1), ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₃ k n j l) f x‖ₑ) := by
    gcongr with n hn k hkn j hj
    simp only [Finset.mem_Iic] at hkn hj
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    rw [← lintegral_add_left']; swap
    · exact h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    rw [carlesonSum_𝔓pos_inter_ℭ₂_eq_add_sum hkn hj]
    apply (enorm_add_le _ _).trans
    gcongr
    apply enorm_sum_le
  _ = (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₂ k n j) f x‖ₑ)
      + ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₃ k n j l) f x‖ₑ := by
    simp only [Finset.sum_add_distrib]
    abel

/-- Custom version of the antichain operator theorem, in the specific form we need to handle
the various terms in the previous statement. -/
lemma lintegral_enorm_carlesonSum_le_of_isAntichain_subset_ℭ
    {f : X → ℂ} {𝔄 : Set (𝔓 X)} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f)
    (hA : IsAntichain (· ≤ ·) 𝔄) (h'A : 𝔄 ⊆ ℭ k n) :
    ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔄) f x‖ₑ
    ≤ C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ (q⁻¹)
      * 2 ^ (- ((q - 1) / (8 * a ^ 4) * n)) := by
  have I : 0 ≤ q - 1 := by linarith [one_lt_q X]
  have J : 0 ≤ q⁻¹ - 2⁻¹ := inv_q_sub_half_nonneg X
  apply (antichain_operator_le_volume (hA.subset inter_subset_right) h'f hf diff_subset).trans
  simp only [mul_assoc]
  apply mul_le_mul_left'
  have : dens₁ (𝔓pos (X := X) ∩ 𝔓₁ᶜ ∩ 𝔄) ≤ 2 ^ (4 * a - n + 1 : ℝ) :=
    dens1_le (inter_subset_right.trans h'A)
  have : dens₂ (𝔓pos (X := X) ∩ 𝔓₁ᶜ ∩ 𝔄) ≤ 2 ^ (2 * a + 5) * volume F / volume G := by
    rw [dens₂_eq_biSup_dens₂]
    simp only [iSup_le_iff]
    intro p hp
    have : ¬ (𝓘 p : Set X) ⊆ G₁ := by
      have W := hp.1.1
      contrapose! W
      have : ↑(𝓘 p) ∩ G ∩ G'ᶜ = ∅ := by
        simp only [G', compl_union]
        apply eq_empty_of_subset_empty
        intro x hx
        exact (hx.2.1.1 (W hx.1.1)).elim
      simp only [𝔓pos, mem_setOf_eq, this, measure_empty, lt_self_iff_false, not_false_eq_true]
    contrapose! this
    have : p ∈ highDensityTiles := by simp [highDensityTiles, this]
    apply subset_biUnion_of_mem this
  calc
  dens₁ (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔄) ^ ((q - 1) / (8 * ↑a ^ 4)) *
    (dens₂ (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔄) ^ (q⁻¹ - 2⁻¹) * (volume F ^ (1 / 2 : ℝ) * volume G ^ (1 / 2 : ℝ)))
  _ ≤ (2 ^ (4 * a - n + 1 : ℝ)) ^ ((q - 1) / (8 * ↑a ^ 4)) *
    ((2 ^ (2 * a + 5) * volume F / volume G) ^ (q⁻¹ - 2⁻¹)
      * ((volume F ^ (1 / 2 : ℝ) * volume G ^ (1 / 2 : ℝ)))) := by gcongr
  _ = (2 ^ ((4 * a + 1) * (q - 1) / (8 * ↑a ^ 4)) * 2 ^ (- ((q - 1) / (8 * ↑a ^ 4) * n))) *
    ((2 ^ ((2 * a + 5) * (q⁻¹ - 2⁻¹)) * volume F ^ (q⁻¹ - 2⁻¹) / volume G ^ (q⁻¹ - 2⁻¹))
      * ((volume F ^ (1 / 2 : ℝ) * volume G ^ (1 / 2 : ℝ)))) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ J, ENNReal.mul_rpow_of_nonneg _ _ J,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ (NeZero.ne 2) ENNReal.ofNat_ne_top]
    congr
    · ring
    · simp
  _ = 2 ^ ((4 * a + 1) * (q - 1) / (8 * ↑a ^ 4)) * 2 ^ ((2 * a + 5) * (q⁻¹ - 2⁻¹)) *
      (volume G ^ (1 - q⁻¹) * (volume F ^ q⁻¹ * 2 ^ (- ((q - 1) / (8 * ↑a ^ 4) * n)))) := by
    rcases eq_or_ne (volume G) 0 with vG | vG
    · have : 0 < 1 - q⁻¹ := by rw [sub_pos, inv_lt_one_iff₀]; exact .inr (one_lt_q X)
      rw [vG, ENNReal.zero_rpow_of_pos (show 0 < (1 / 2 : ℝ) by positivity),
        ENNReal.zero_rpow_of_pos this]
      simp only [zero_mul, mul_zero]
    · have IF : (volume F) ^ (q⁻¹) = (volume F) ^ ((q ⁻¹ - 2⁻¹) + 2⁻¹) := by congr; abel
      have IG : (volume G) ^ (1 - q⁻¹) = (volume G) ^ (2⁻¹ - (q⁻¹ - 2⁻¹)) := by
        congr 1
        simp only [sub_sub_eq_add_sub, sub_left_inj]
        norm_num
      rw [IF, IG, ENNReal.rpow_sub (2⁻¹) _ vG volume_G_ne_top,
        ENNReal.rpow_add_of_nonneg (x := volume F) _ _ (inv_q_sub_half_nonneg X) (by norm_num),
        ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ring_nf
  _ ≤ 2 ^ ((2 : ℝ)⁻¹ + (a + 5/2)) *
      (volume G ^ (1 - q⁻¹) * (volume F ^ q⁻¹ * 2 ^ (- ((q - 1) / (8 * ↑a ^ 4) * n)))) := by
    rw [← ENNReal.rpow_add _ _ (NeZero.ne 2) ENNReal.ofNat_ne_top]
    have : (4 : ℝ) ≤ a := mod_cast (four_le_a X)
    gcongr
    · exact one_le_two
    · calc
      (4 * a + 1) * (q - 1) / (8 * a ^ 4 : ℝ)
      _ ≤ (4 * a + a) * (2 - 1) / (8 * a ^ 4) := by
         gcongr
         · norm_cast
           linarith [four_le_a X]
         · exact q_le_two X
      _ = 5 / (8 * a ^ 3) := by field_simp; ring
      _ ≤ 5 / (8 * (4 : ℝ) ^ 3) := by gcongr
      _ ≤ 2⁻¹ := by norm_num
    · calc
      (2 * ↑a + 5) * (q⁻¹ - 2⁻¹)
      _ ≤ (2 * ↑a + 5) * (1⁻¹ - 2⁻¹) := by gcongr; exact (one_lt_q X).le
      _ = a + 5/2 := by ring
  _ = 2 ^ (a + 3) *
      (volume G ^ (1 - q⁻¹) * (volume F ^ q⁻¹ * 2 ^ (- ((q - 1) / (8 * ↑a ^ 4) * n)))) := by
    congr 1
    rw [← ENNReal.rpow_natCast]
    congr
    simp
    ring

open scoped Nat

omit [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o] in
lemma lintegral_carlesonSum_𝔓₁_compl_le_sum_aux1 [ProofData a q K σ₁ σ₂ F G] {N : ℕ} :
    ∑ x ≤ N,
      (((12 + 8 * Z) * x ^ 0 + (19 + 20 * Z) * x ^ 1 + (7 + 16 * Z) * x ^ 2 + (4 * Z) * x ^ 3) *
        (2 : ℝ) ^ (-((q - 1) / (8 * ↑a ^ 4) * x : ℝ))) ≤ 2 ^ (28 * a + 20) / (q - 1) ^ 4 := by
  simp only [add_mul _ _ ((2 : ℝ) ^ (_ : ℝ)), Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [← mul_assoc]
  have : 0 < q - 1 := by linarith [one_lt_q X]
  have : 0 < a := a_pos X
  have : q ≤ 2 := q_le_two X
  have : (4 : ℝ) ≤ a := mod_cast (four_le_a X)
  have P : 0 < (q - 1) / (8 * ↑a ^ 4) := by positivity
  have : 0.69 ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have : (1 : ℝ) ≤ Z / 2 ^ 48 := by
    rw [one_le_div (by positivity)]
    simp only [defaultZ, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    · exact one_le_two
    · linarith [four_le_a X]
  calc
  (12 + 8 * ↑Z) * ∑ i ≤ N, ↑i ^ 0 * (2 : ℝ) ^ (-((q - 1) / (8 * a ^ 4) * i)) +
      (19 + 20 * ↑Z) * ∑ i ≤ N, ↑i ^ 1 * 2 ^ (-((q - 1) / (8 * a ^ 4) * i)) +
      (7 + 16 * ↑Z) * ∑ i ≤ N, ↑i ^ 2 * 2 ^ (-((q - 1) / (8 * a ^ 4) * i)) +
      (4 * ↑Z) * ∑ i ≤ N, ↑i ^ 3 * 2 ^ (-((q - 1) / (8 * a ^ 4) * i))
  _ ≤ (12 + 8 * ↑Z) * ((2 : ℝ) ^ ((q - 1) / (8 * a ^ 4)) *
        0 ! / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ (0 + 1)) +
      (19 + 20 * ↑Z) * ((2 : ℝ) ^ ((q - 1) / (8 * a ^ 4)) *
        1 ! / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ (1 + 1)) +
      (7 + 16 * ↑Z) * ((2 : ℝ) ^ ((q - 1) / (8 * a ^ 4)) *
        2 ! / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ (2 + 1)) +
      (4 * ↑Z) * ((2 : ℝ) ^ ((q - 1) / (8 * a ^ 4)) *
        3 ! / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ (3 + 1)) := by
    gcongr <;> apply sum_Iic_pow_mul_two_pow_neg_le P
  _ = (2 : ℝ) ^ ((q - 1) / (8 * a ^ 4)) *
      ( (12 + 8 * ↑Z) / (Real.log 2 * ((q - 1) / (8 * a ^ 4)))
      + (19 + 20 * ↑Z)  / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 2
      + (14 + 32 * ↑Z) / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 3
      + (24 * ↑Z) /  (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 4) := by
    simp only [Nat.cast_ofNat, Nat.factorial, Nat.cast_one, mul_one, zero_add, pow_one,
      Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul]
    ring
  _ ≤ (2 : ℝ) ^ (1 : ℝ) *
      ( (12 + 8 * ↑Z) / (Real.log 2 * ((q - 1) / (8 * a ^ 4)))
      + (19 + 20 * ↑Z)  / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 2
      + (14 + 32 * ↑Z) / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 3
      + (24 * ↑Z) /  (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 4) := by
    gcongr
    · exact one_le_two
    · apply div_le_one_of_le₀ _ (by positivity)
      have : 8 * (4 : ℝ) ^ 4 ≤ 8 * a ^ 4 := by gcongr
      linarith
  _ = (24 + 16 * ↑Z) / (Real.log 2 * ((q - 1) / (8 * a ^ 4)))
      + (38 + 40 * ↑Z)  / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 2
      + (28 + 64 * ↑Z) / (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 3
      + (48 * ↑Z) /  (Real.log 2 * ((q - 1) / (8 * a ^ 4))) ^ 4 := by
    simp only [Real.rpow_one]
    ring
  _ = ((8 * a ^ 4) / (q - 1)) ^ 4 *
     (((q - 1) / (8 * a ^ 4)) ^ 3 * (24 * 1 + 16 * ↑Z) / Real.log 2
      + ((q - 1) / (8 * a ^ 4)) ^ 2 * (38 * 1 + 40 * ↑Z)  / (Real.log 2) ^ 2
      + ((q - 1) / (8 * a ^ 4)) * (28 * 1 + 64 * ↑Z) / (Real.log 2) ^ 3
      + (48 * ↑Z) /  (Real.log 2) ^ 4) := by
    field_simp only
    ring
  _ ≤ ((8 * a ^ 4) / (q - 1)) ^ 4 *
     (((2 - 1) / (8 * 4 ^ 4)) ^ 3 * (24 * (Z / 2 ^ 48) + 16 * ↑Z) / 0.69
      + ((2 - 1) / (8 * 4 ^ 4)) ^ 2 * (38 * (Z / 2 ^ 48) + 40 * ↑Z)  / 0.69 ^ 2
      + ((2 - 1) / (8 * 4 ^ 4)) * (28 * (Z / 2 ^ 48) + 64 * ↑Z) / 0.69 ^ 3
      + (48 * ↑Z) / 0.69 ^ 4) := by gcongr
  _ = a ^ 16 / (q - 1) ^ 4 * Z * (8 ^ 4 *
      (((2 - 1) / (8 * 4 ^ 4)) ^ 3 * (24 * (1 / 2 ^ 48) + 16) / 0.69
      + ((2 - 1) / (8 * 4 ^ 4)) ^ 2 * (38 * (1 / 2 ^ 48) + 40)  / 0.69 ^ 2
      + ((2 - 1) / (8 * 4 ^ 4)) * (28 * (1 / 2 ^ 48) + 64) / 0.69 ^ 3
      + 48 / 0.69 ^ 4)) := by
    rw [div_pow]; ring
  _ ≤ a ^ 16 / (q - 1) ^ 4 * Z * 2 ^ 20 := by gcongr; norm_num
  _ ≤ (2 ^ a) ^ 16 / (q - 1) ^ 4 * Z * 2 ^ 20 := by
    gcongr
    exact_mod_cast (Nat.lt_pow_self one_lt_two).le
  _ = (2 ^ (16 * a) * 2 ^ (12 * a) * 2 ^ 20) / (q - 1) ^ 4 := by
    simp [← pow_mul, mul_comm a]
    ring
  _ = 2 ^ (28 * a + 20) / (q - 1) ^ 4 := by
    simp only [← pow_add]
    congr
    omega

omit [TileStructure Q D κ S o] in
lemma lintegral_carlesonSum_𝔓₁_compl_le_sum_aux2 {N : ℕ} :
    ∑ x ≤ N, (((12 + 8 * Z) + (19 + 20 * Z) * x + (7 + 16 * Z) * x ^ 2 + (4 * Z) * x ^ 3) *
        (2 : ℝ≥0∞) ^ (-((q - 1) / (8 * ↑a ^ 4) * x : ℝ)))
    ≤ (2 : ℝ≥0∞) ^ (28 * a + 20) / (nnq - 1) ^ 4 := by
  have : 0 < q - 1 := by linarith [one_lt_q X]
  have A : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
  simp_rw [A, ENNReal.ofReal_rpow_of_pos zero_lt_two]
  calc
  ∑ x ≤ N, (((12 + 8 * ↑Z) + (19 + 20 * ↑Z) * x + (7 + 16 * ↑Z) * x ^ 2 + (4 * ↑Z) * x ^ 3)
      * ENNReal.ofReal (2 ^ (-((q - 1) / (8 * ↑a ^ 4) * x : ℝ))))
  _ = ∑ x ≤ N, ENNReal.ofReal
      (((12 + 8 * Z) + (19 + 20 * Z) * x + (7 + 16 * Z) * x ^ 2 + (4 * Z) * x ^ 3) *
        2 ^ (-((q - 1) / (8 * ↑a ^ 4) * x : ℝ))) := by
    congr with i
    rw [ENNReal.ofReal_mul (by positivity)]
    congr
    norm_cast
  _ = ENNReal.ofReal (∑ x ≤ N,
      (((12 + 8 * Z) + (19 + 20 * Z) * x + (7 + 16 * Z) * x ^ 2 + (4 * Z) * x ^ 3) *
        2 ^ (-((q - 1) / (8 * ↑a ^ 4) * x : ℝ)))) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i hi
    positivity
  _ ≤ ENNReal.ofReal (2 ^ (28 * a + 20) / (q - 1) ^ 4) := by
    apply ENNReal.ofReal_le_ofReal
    simpa using lintegral_carlesonSum_𝔓₁_compl_le_sum_aux1 (X := X)
  _ = 2 ^ (28 * a + 20) / (ENNReal.ofReal (q - 1)) ^ 4 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    congr
    · norm_cast
    · rw [ENNReal.ofReal_pow]
      linarith
  _ = (ENNReal.ofReal 2) ^ (28 * a + 20) / (nnq - 1) ^ 4 := by
    rw [← A]
    rfl

/-- An optimized constant for Lemma 5.1.3. -/
def C5_1_3_optimized (a : ℕ) (q : ℝ≥0) := C2_0_3 a q * 2 ^ (29 * a + 23) / (q - 1) ^ 4

/-- The constant used in Lemma 5.1.3.
Has value `2 ^ (120 * a ^ 3) / (q - 1) ^ 5` in the blueprint. -/
def C5_1_3 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ ((𝕔 + 8 + 𝕔 / 8) * a ^ 3) / (q - 1) ^ 5

omit [TileStructure Q D κ S o] in
lemma C5_1_3_pos : 0 < C5_1_3 a nnq := by
  have : 0 < nnq - 1 := tsub_pos_of_lt (one_lt_nnq X)
  simp only [C5_1_3]
  positivity

omit [TileStructure Q D κ S o] in
lemma C5_1_3_optimized_le_C5_1_3 : C5_1_3_optimized a nnq ≤ C5_1_3 a nnq := by
  simp only [C5_1_3_optimized, C5_1_3, C2_0_3]
  calc
    _ ≤ 2 ^ ((𝕔 + 5 + 𝕔 / 8) * a ^ 3) / (nnq - 1) * 2 ^ (3 * a ^ 3) / (nnq - 1) ^ 4 := by
      have := four_le_a X
      gcongr; · exact one_le_two
      calc
        _ ≤ 3 * 4 * 4 * a := by omega
        _ ≤ 3 * a * a * a := by gcongr
        _ = _ := by ring
    _ = 2 ^ ((𝕔 + 5 + 𝕔 / 8) * a ^ 3 + 3 * a ^ 3) / (nnq - 1) ^ (4 + 1) := by
      rw [pow_add, pow_add, div_mul_eq_div_div]
      simp only [div_eq_inv_mul, pow_one]
      ring
    _ = _ := by congr; ring

lemma forest_complement_optimized
    {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ ≤
      C5_1_3_optimized a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := calc
  ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ
  _ ≤ (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n, ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₀' k n l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₁ k n j l) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₂ k n j) f x‖ₑ)
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          ∫⁻ x in G \ G', ‖carlesonSum (𝔓pos ∩ 𝔓₁ᶜ ∩ 𝔏₃ k n j l) f x‖ₑ) :=
    lintegral_carlesonSum_𝔓₁_compl_le_sum_lintegral h'f
  _ ≤   (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ l < n,
          C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ (q⁻¹)
          * 2 ^ (- ((q - 1) / (8 * a^4) * n)))
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ (q⁻¹)
          * 2 ^ (- ((q - 1) / (8 * a^4) * n)))
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
          C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ (q⁻¹)
          * 2 ^ (- ((q - 1) / (8 * a^4) * n)))
      + (∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l ≤ Z * (n + 1),
          C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ (q⁻¹)
          * 2 ^ (- ((q - 1) / (8 * a^4) * n))) := by
      gcongr
      · apply lintegral_enorm_carlesonSum_le_of_isAntichain_subset_ℭ hf h'f antichain_L0'
        exact minLayer_subset.trans 𝔏₀_subset_ℭ
      · apply lintegral_enorm_carlesonSum_le_of_isAntichain_subset_ℭ hf h'f antichain_L1
        exact 𝔏₁_subset_ℭ
      · apply lintegral_enorm_carlesonSum_le_of_isAntichain_subset_ℭ hf h'f antichain_L2
        exact 𝔏₂_subset_ℭ
      · apply lintegral_enorm_carlesonSum_le_of_isAntichain_subset_ℭ hf h'f antichain_L3
        exact 𝔏₃_subset_ℭ
  _ = C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ *
    ∑ x ≤ maxℭ X,
      (((↑x + 1) * ↑x + (↑x + 1) * (2 * ↑x + 3 + 1) * (↑Z * (↑x + 1) + 1)
      + (↑x + 1) * (2 * ↑x + 3 + 1)  + (↑x + 1) * (2 * ↑x + 3 + 1) * (↑Z * (↑x + 1) + 1))
        * 2 ^ (-((q - 1) / (8 * ↑a ^ 4) * ↑x))) := by
    simp only [← Finset.mul_sum, ← mul_add]
    simp only [Finset.sum_const, Nat.card_Iic, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat, Nat.card_Iio]
    simp only [← Finset.sum_add_distrib]
    congr with x
    ring
  _ = C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ *
    ∑ x ≤ maxℭ X,
      (((12 + 8 * Z) + (19 + 20 * Z) * x + (7 + 16 * Z) * x ^ 2 + (4 * Z) * x ^ 3) *
        (2 : ℝ≥0∞) ^ (-((q - 1) / (8 * ↑a ^ 4) * x : ℝ))) := by
    congr with x
    ring
  _ ≤ C2_0_3 a nnq * 2 ^ (a + 3) * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ *
       (2 ^ (28 * a + 20) / (nnq - 1) ^ 4) := by
    gcongr
    apply lintegral_carlesonSum_𝔓₁_compl_le_sum_aux2
  _ = (C2_0_3 a nnq * (2 ^ (a + 3) * 2 ^ (28 * a + 20)) / (nnq - 1) ^ 4) *
      volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by simp only [ENNReal.div_eq_inv_mul]; ring
  _ = (C2_0_3 a nnq * 2 ^ (29 * a + 23) / (nnq - 1) ^ 4) *
      volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
    rw [← pow_add]
    congr 4
    ring
  _ = C5_1_3_optimized a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
    congr
    simp only [C5_1_3_optimized]
    norm_cast
    rw [ENNReal.coe_div]
    have : 0 < nnq - 1 := tsub_pos_of_lt (one_lt_nnq X)
    exact ne_of_gt (by positivity)

/-- Lemma 5.1.3, proving the bound on the integral of the Carleson sum over all leftover tiles
which do not fit in a forest. It follows from a careful grouping of these tiles into finitely
many antichains. -/
lemma forest_complement {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ ≤
    C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  apply (forest_complement_optimized hf h'f).trans
  gcongr
  exact C5_1_3_optimized_le_C5_1_3
