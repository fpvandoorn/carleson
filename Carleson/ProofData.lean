import Carleson.DoublingMeasure

open MeasureTheory Measure Metric Complex Set TopologicalSpace Bornology Function ENNReal
open scoped NNReal
noncomputable section

/-! # ProofData.

This file introduces the class `ProofData`, used to bundle data common through most of
chapters 2-7 (except 3), and provides API for it.

-/

/-- Data common through most of chapters 2-7 (except 3). -/
class ProofData {X : Type*} (a : outParam ℕ) (q : outParam ℝ) (K : outParam (X → X → ℂ))
  (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X] extends
    KernelProofData a K where
  c : IsCancellative X (defaultτ a)
  q_mem_Ioc : q ∈ Ioc 1 2
  isBounded_F : IsBounded F
  isBounded_G : IsBounded G
  measurableSet_F : MeasurableSet F
  measurableSet_G : MeasurableSet G
  measurable_σ₁ : Measurable σ₁
  measurable_σ₂ : Measurable σ₂
  finite_range_σ₁ : Finite (range σ₁)
  finite_range_σ₂ : Finite (range σ₂)
  σ₁_le_σ₂ : σ₁ ≤ σ₂
  Q : SimpleFunc X (Θ X)
  BST_T_Q (θ : Θ X) : HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
    2 2 volume volume (C_Ts a)

export ProofData (q_mem_Ioc isBounded_F isBounded_G measurableSet_F measurableSet_G
  measurable_σ₁ measurable_σ₂ finite_range_σ₁ finite_range_σ₂ σ₁_le_σ₂ Q BST_T_Q)
attribute [instance] ProofData.c

section ProofData

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

include a q K σ₁ σ₂ F G

variable (X) in
lemma S_spec : ∃ n : ℕ, (∀ x, -n ≤ σ₁ x ∧ σ₂ x ≤ n) ∧
    F ⊆ ball (cancelPt X) (defaultD a ^ n / 4) ∧
    G ⊆ ball (cancelPt X) (defaultD a ^ n / 4) ∧ 0 < n := by
  obtain ⟨l₁, hl₁⟩ := bddBelow_def.mp (Finite.bddBelow (finite_range_σ₁ (X := X)))
  obtain ⟨u₂, hu₂⟩ := bddAbove_def.mp (Finite.bddAbove (finite_range_σ₂ (X := X)))
  simp_rw [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hl₁ hu₂
  have one_lt_D := one_lt_realD X
  obtain ⟨rF, rFpos, hrF⟩ : ∃ r > 0, F ⊆ ball (cancelPt X) r := by
    obtain ⟨r, hr⟩ := isBounded_F.subset_ball (cancelPt X)
    rcases lt_or_ge 0 r with lr | lr
    · use r
    · use 1, zero_lt_one, hr.trans (ball_subset_ball (lr.trans zero_le_one))
  let nF := ⌈Real.logb (defaultD a) (4 * rF)⌉
  obtain ⟨rG, rGpos, hrG⟩ : ∃ r > 1, G ⊆ ball (cancelPt X) r := by
    obtain ⟨r, hr⟩ := isBounded_G.subset_ball (cancelPt X)
    rcases lt_or_ge 0 r with lr | lr
    · use r + 1, by linarith, subset_trans hr (ball_subset_ball (by simp))
    · use 2, one_lt_two, hr.trans (ball_subset_ball (lr.trans zero_le_two))
  let nG := ⌈Real.logb (defaultD a) (4 * rG)⌉
  refine ⟨(max (max (-l₁) u₂) (max nF nG)).toNat, ⟨fun x ↦ ?_, ?_, ?_, ?_⟩⟩
  · simp only [Int.ofNat_toNat, ← min_neg_neg, neg_neg, min_le_iff, le_max_iff]
    exact ⟨.inl (.inl (.inl (hl₁ x))), .inl (.inl (.inr (hu₂ x)))⟩
  · refine hrF.trans (ball_subset_ball ?_)
    trans (defaultD a : ℝ) ^ nF / 4
    · rw [le_div_iff₀' zero_lt_four, ← Real.rpow_intCast,
          ← Real.logb_le_iff_le_rpow one_lt_D (by positivity)]
      exact Int.le_ceil _
    rw [← Real.rpow_natCast, ← Real.rpow_intCast]
    gcongr
    · exact one_lt_D.le
    norm_cast
    apply Int.self_le_toNat nF |>.trans
    exact_mod_cast Int.toNat_le_toNat <| (le_max_left ..).trans <| le_max_right ..
  · refine hrG.trans (ball_subset_ball ?_)
    trans (defaultD a : ℝ) ^ nG / 4
    · rw [le_div_iff₀' zero_lt_four, ← Real.rpow_intCast,
          ← Real.logb_le_iff_le_rpow one_lt_D (by positivity)]
      exact Int.le_ceil _
    rw [← Real.rpow_natCast, ← Real.rpow_intCast]
    gcongr
    · exact one_lt_D.le
    norm_cast
    apply Int.self_le_toNat nG |>.trans
    exact_mod_cast Int.toNat_le_toNat <| (le_max_right ..).trans <| le_max_right ..
  · apply Int.pos_iff_toNat_pos.mp <| lt_of_lt_of_le _ <| (le_max_right ..).trans <| le_max_right ..
    exact Int.ceil_pos.mpr (Real.logb_pos one_lt_D (by linarith))

variable (X) in
open Classical in
def defaultS : ℕ := Nat.find (S_spec X)

lemma range_σ₁_subset : range σ₁ ⊆ Icc (-defaultS X) (defaultS X) := by
  classical
  rw [range_subset_iff]
  have := (Nat.find_spec (S_spec X)).1
  exact fun x ↦ ⟨(this x).1, (σ₁_le_σ₂ x).trans (this x).2⟩

lemma range_σ₂_subset : range σ₂ ⊆ Icc (-defaultS X) (defaultS X) := by
  classical
  rw [range_subset_iff]
  have := (Nat.find_spec (S_spec X)).1
  exact fun x ↦ ⟨(this x).1.trans (σ₁_le_σ₂ x), (this x).2⟩

lemma F_subset : F ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4) := by
  classical exact (Nat.find_spec (S_spec X)).2.1

lemma G_subset : G ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4) := by
  classical exact (Nat.find_spec (S_spec X)).2.2.1

lemma defaultS_pos : 0 < defaultS X := by
  classical exact (Nat.find_spec (S_spec X)).2.2.2

lemma Icc_σ_subset_Icc_S {x : X} : Icc (σ₁ x) (σ₂ x) ⊆ Icc (-defaultS X) (defaultS X) :=
  fun _ h ↦ ⟨(range_σ₁_subset ⟨x, rfl⟩).1.trans h.1, h.2.trans (range_σ₂_subset ⟨x, rfl⟩).2⟩

variable (X)

lemma one_lt_q : 1 < q := (q_mem_Ioc X).1
lemma q_le_two : q ≤ 2 := (q_mem_Ioc X).2
lemma q_pos : 0 < q := zero_lt_one.trans (one_lt_q X)
lemma q_nonneg : 0 ≤ q := (q_pos X).le
lemma inv_q_sub_half_nonneg : 0 ≤ q⁻¹ - 2⁻¹ := by
  simp [inv_le_inv₀ zero_lt_two (q_pos X), q_le_two X]

-- Note: For exponent computations it is usually cleaner to argue in terms
-- of `q⁻¹` rather than `q`, both on paper and in Lean.
lemma inv_q_mem_Ico : q⁻¹ ∈ Ico 2⁻¹ 1 := ⟨by linarith only [inv_q_sub_half_nonneg X],
  inv_one (G := ℝ) ▸ inv_lt_inv₀ (q_pos X) zero_lt_one |>.mpr <| one_lt_q X⟩

/-- `q` as an element of `ℝ≥0`. -/
def nnq : ℝ≥0 := ⟨q, q_nonneg X⟩

lemma one_lt_nnq : 1 < nnq X := one_lt_q X
lemma nnq_le_two : nnq X ≤ 2 := q_le_two X
lemma nnq_pos : 0 < nnq X := q_pos X
lemma nnq_mem_Ioc : nnq X ∈ Ioc 1 2 :=
  ⟨NNReal.coe_lt_coe.mp (q_mem_Ioc X).1, NNReal.coe_le_coe.mp (q_mem_Ioc X).2⟩

end ProofData

namespace ShortVariables
-- open this section to get shorter 1-letter names for a bunch of variables

set_option hygiene false
scoped notation "nnq" => nnq X

end ShortVariables

open scoped ShortVariables

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

/-- Used in `third_exception` (Lemma 5.2.10). -/
lemma two_le_κZ [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 2 ≤ κ * Z := by
  rw [defaultκ, defaultZ, Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 by rfl,
    show (2 : ℝ) ^ (12 * a) = 2 ^ (12 * a : ℝ) by norm_cast, ← Real.rpow_add zero_lt_two,
    show (-10 * a + 12 * a : ℝ) = 2 * a by ring]
  norm_cast; change 2 ^ 1 ≤ _
  exact Nat.pow_le_pow_of_le one_lt_two (by linarith [four_le_a X])

/-- Used in `third_exception` (Lemma 5.2.10). -/
lemma DκZ_le_two_rpow_100 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    (D : ℝ≥0∞) ^ (-κ * Z) ≤ 2 ^ (-100 : ℝ) := by
  rw [defaultD, Nat.cast_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ≥0∞) = 2 by rfl]
  apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
  rw [defaultκ, defaultZ, Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 by rfl, neg_mul,
    show (2 : ℝ) ^ (12 * a) = 2 ^ (12 * a : ℝ) by norm_cast, mul_neg,
    ← Real.rpow_add zero_lt_two, show (-10 * a + 12 * a : ℝ) = 2 * a by ring,
    neg_le_neg_iff]
  norm_cast
  have : 1 ≤ 𝕔 := by linarith [seven_le_c]
  have := four_le_a X
  calc
    _ ≤ 1 * 4 ^ 2 * 2 ^ (2 * 4) := by norm_num
    _ ≤ _ := by
      gcongr
      norm_num

lemma four_le_Z [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 4 ≤ Z := by
  rw [defaultZ, show 4 = 2 ^ 2 by rfl]
  exact Nat.pow_le_pow_right zero_lt_two (by linarith [four_le_a X])

section PseudoMetricSpace

variable [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma volume_F_lt_top : volume F < ⊤ := isBounded_F.measure_lt_top
lemma volume_F_ne_top : volume F ≠ ⊤ := volume_F_lt_top.ne
lemma volume_G_lt_top : volume G < ⊤ := isBounded_G.measure_lt_top
lemma volume_G_ne_top : volume G ≠ ⊤ := volume_G_lt_top.ne

/-! Lemma 2.1.1 -/

def C2_1_1 (k : ℕ) (a : ℕ) : ℕ := 2 ^ (k * a)

lemma Θ.finite_and_mk_le_of_le_dist {x₀ : X} {r R : ℝ} {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : 𝓩.PairwiseDisjoint (ball_{x₀, R} · r)) :
    𝓩.Finite ∧ Cardinal.mk 𝓩 ≤ C2_1_1 k a := by
  obtain ⟨𝓩', c𝓩', u𝓩'⟩ := ballsCoverBalls_iterate_nat (x := x₀) (n := k) (r := r) (d := R) f
  rw [mul_comm] at u𝓩'
  classical
    let g : Θ X → Finset (Θ X) := fun z ↦ 𝓩'.filter (z ∈ ball_{x₀, R} · r)
    have g_pd : 𝓩.PairwiseDisjoint g := fun z hz z' hz' hne ↦ by
      refine Finset.disjoint_filter.mpr fun c _ mz mz' ↦ ?_
      rw [mem_ball_comm (α := WithFunctionDistance x₀ R)] at mz mz'
      exact Set.disjoint_left.mp (h2𝓩 hz hz' hne) mz mz'
  have g_ne : ∀ z, z ∈ 𝓩 → (g z).Nonempty := fun z hz ↦ by
    obtain ⟨c, hc⟩ := mem_iUnion.mp <| mem_of_mem_of_subset hz (h𝓩.trans u𝓩')
    simp only [mem_iUnion, exists_prop] at hc
    use c; simpa only [g, Finset.mem_filter]
  have g_injOn : 𝓩.InjOn g := fun z hz z' hz' e ↦ by
    have : z ≠ z' → Disjoint (g z) (g z') := g_pd hz hz'
    rw [← e, Finset.disjoint_self_iff_empty] at this
    exact not_ne_iff.mp <| this.mt <| Finset.nonempty_iff_ne_empty.mp (g_ne z hz)
  have g_subset : g '' 𝓩 ⊆ 𝓩'.powerset.toSet := fun gz hgz ↦ by
    rw [mem_image] at hgz
    obtain ⟨z, hz⟩ := hgz
    simp_rw [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset, ← hz.2, g,
      Finset.filter_subset]
  have f𝓩 : (g '' 𝓩).Finite := Finite.subset 𝓩'.powerset.finite_toSet g_subset
  rw [Set.finite_image_iff g_injOn] at f𝓩
  refine ⟨f𝓩, ?_⟩
  lift 𝓩 to Finset (Θ X) using f𝓩
  simp_rw [Cardinal.mk_fintype, Finset.coe_sort_coe, Fintype.card_coe]
  norm_cast
  classical calc
    _ = ∑ _ ∈ 𝓩, 1 := by simp
    _ ≤ ∑ u ∈ 𝓩, (g u).card := Finset.sum_le_sum fun z hz ↦ Finset.card_pos.mpr (g_ne z hz)
    _ = (𝓩.biUnion g).card := (Finset.card_biUnion (fun z hz z' hz' ↦ g_pd hz hz')).symm
    _ ≤ 𝓩'.card := by
      refine Finset.card_le_card fun _ h ↦ ?_
      rw [Finset.mem_biUnion] at h
      exact Finset.mem_of_subset (by simp [g]) h.choose_spec.2
    _ ≤ (2 ^ a) ^ k := c𝓩'
    _ ≤ _ := by rw [C2_1_1, mul_comm, pow_mul]

lemma Θ.card_le_of_le_dist {x₀ : X} {r R : ℝ} {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : 𝓩.PairwiseDisjoint (ball_{x₀, R} · r)) :
    Nat.card 𝓩 ≤ C2_1_1 k a := by
  obtain ⟨f𝓩, c𝓩⟩ := finite_and_mk_le_of_le_dist h𝓩 h2𝓩
  lift 𝓩 to Finset (Θ X) using f𝓩
  simpa using c𝓩

end PseudoMetricSpace
