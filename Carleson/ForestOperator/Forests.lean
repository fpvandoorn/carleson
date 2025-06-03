import Carleson.ForestOperator.LargeSeparation
import Carleson.ForestOperator.RemainingTiles
import Carleson.ToMathlib.MeasureTheory.Function.L1Integrable
import Carleson.ToMathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Carleson.ToMathlib.Order.Chain

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

/-! ## Lemma 7.4.4 -/

lemma estimate_C7_4_5 {a : ℕ} (n : ℕ) (ha : 4 ≤ a) :
    C7_4_5 a n ≤ 2 ^ (533 * a ^ 3) * 2 ^ (-(4 * n : ℝ)) := by
  simp_rw [C7_4_5, neg_div, NNReal.rpow_neg, ← div_eq_mul_inv]
  gcongr _ / 2 ^ ?_
  · norm_cast; positivity
  · exact one_le_two
  · rw [mul_div_right_comm]; gcongr
    rw [le_div_iff₀ (by positivity), defaultZ]; norm_cast
    calc
      _ = 8 * a * a * (a + 2) := by ring
      _ ≤ 8 * a * a * (a + a) := by gcongr; omega
      _ = 2 ^ 4 * a * a * a := by ring
      _ ≤ 2 ^ a * 2 ^ a * 2 ^ a * 2 ^ a := by
        gcongr; · exact one_le_two
        all_goals exact Nat.lt_two_pow_self.le
      _ ≤ _ := by simp_rw [← pow_add]; exact pow_le_pow_right' one_le_two (by linarith)

lemma estimate_C7_4_6 {a : ℕ} (n : ℕ) (ha : 4 ≤ a) :
    C7_4_6 a n ≤ 2 ^ (258 * a ^ 3) * 2 ^ (-(4 * n : ℝ)) := by
  simp_rw [C7_4_6, C7_2_1, C7_6_2, C2_1_3, ← mul_assoc]
  conv_lhs => enter [1, 1, 1, 2]; norm_cast
  conv_lhs => enter [1, 1, 2, 2]; norm_cast
  rw [NNReal.rpow_natCast, NNReal.rpow_natCast, ← pow_add, ← pow_add,
    show 152 * a ^ 3 + 102 * a ^ 3 + (21 * a + 5) = 254 * a ^ 3 + 21 * a + 5 by ring]
  simp_rw [NNReal.rpow_neg, ← div_eq_mul_inv]
  gcongr 2 ^ ?_ / 2 ^ ?_
  · norm_cast; positivity
  · exact one_le_two
  · calc
      _ ≤ 254 * a ^ 3 + 2 * 4 * 4 * a + 2 * 1 * 1 * 4 := by gcongr <;> norm_num
      _ ≤ 254 * a ^ 3 + 2 * a * a * a + 2 * a * a * a := by gcongr <;> omega
      _ = _ := by ring
  · exact one_le_two
  · rw [← mul_rotate]; gcongr
    rw [← mul_assoc, ← mul_rotate, ← mul_div_assoc, le_div_iff₀ (by positivity),
      defaultκ, defaultZ, Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_ofNat,
      ← Real.rpow_add zero_lt_two, Nat.cast_mul, Nat.cast_ofNat, ← add_mul,
      show 12 + -10 = (2 : ℝ) by norm_num]; norm_cast
    induction a, ha using Nat.le_induction with
    | base => norm_num -- 1616 ≤ 6400
    | succ k lk ih =>
      rw [mul_add_one, mul_add, mul_add_one, pow_add, show 2 ^ 2 = 3 + 1 by norm_num, mul_add_one,
        add_mul, add_comm]
      gcongr ?_ + ?_
      calc
        _ ≤ 2 ^ (2 * 4) * 3 * 25 := by norm_num
        _ ≤ _ := by gcongr; exact one_le_two

/-- The constant used in `correlation_separated_trees`. -/
irreducible_def C7_4_4 (a n : ℕ) : ℝ≥0 :=
  (2 ^ (533 * a ^ 3) + 2 ^ (258 * a ^ 3)) * 2 ^ (-(4 * n : ℝ))

lemma correlation_separated_trees_of_subset (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hg₁ : BoundedCompactSupport g₁) (hg₂ : BoundedCompactSupport g₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖ₑ ≤
    C7_4_4 a n *
    eLpNorm ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) ·) 2 volume *
    eLpNorm ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) ·) 2 volume := by
  calc
    _ = ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x) +
        adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) g₂ x)‖ₑ := by
      congr! 3 with x; rw [← mul_add, ← map_add]; congr 2
      rw [adjointCarlesonSum_inter, sub_add_cancel]
    _ = ‖(∫ x, adjointCarlesonSum (t u₁) g₁ x *
          conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)) +
        ∫ x, adjointCarlesonSum (t u₁) g₁ x *
          conj (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) g₂ x)‖ₑ := by
      congr 1; apply integral_add
      · exact (integrable_adjointCarlesonSum (t u₁) hg₁).mul_conj
          hg₁.adjointCarlesonSum (integrable_adjointCarlesonSum _ hg₂)
      · exact (integrable_adjointCarlesonSum (t u₁) hg₁).mul_conj
          hg₁.adjointCarlesonSum (integrable_adjointCarlesonSum _ hg₂)
    _ ≤ ‖∫ x, adjointCarlesonSum (t u₁) g₁ x *
          conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)‖ₑ +
        ‖∫ x, adjointCarlesonSum (t u₁) g₁ x *
          conj (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) g₂ x)‖ₑ := enorm_add_le _ _
    _ ≤ (C7_4_5 a n + C7_4_6 a n) *
        eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) ·) 2 volume *
        eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) ·) 2 volume := by
      simp_rw [add_mul]; gcongr
      · exact correlation_distant_tree_parts hu₁ hu₂ hu h2u hg₁ hg₂
      · exact correlation_near_tree_parts hu₁ hu₂ hu h2u hg₁ hg₂
    _ ≤ _ := by
      rw [inter_eq_self_of_subset_left h2u.1, ← ENNReal.coe_add]; gcongr
      calc
        _ ≤ _ := add_le_add (estimate_C7_4_5 n (four_le_a X)) (estimate_C7_4_6 n (four_le_a X))
        _ = _ := by rw [C7_4_4, add_mul]

lemma cst_disjoint (hd : Disjoint (𝓘 u₁ : Set X) (𝓘 u₂)) (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (x : X) :
    adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x) = 0 := by
  rw [disjoint_iff_inter_eq_empty] at hd
  rw [adjoint_tile_support2_sum hu₁, adjoint_tile_support2_sum hu₂,
    ← comp_apply (f := conj) (g := indicator _ _), ← indicator_comp_of_zero (by simp),
    ← inter_indicator_mul, hd, indicator_empty]

/-- Lemma 7.4.4 -/
lemma correlation_separated_trees (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (hg₁ : BoundedCompactSupport g₁) (hg₂ : BoundedCompactSupport g₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖ₑ ≤
    C7_4_4 a n *
    eLpNorm ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) ·) 2 volume *
    eLpNorm ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) ·) 2 volume := by
  by_cases hd : Disjoint (𝓘 u₁ : Set X) (𝓘 u₂)
  · simp [cst_disjoint hd hu₁ hu₂]
  wlog h2u : 𝓘 u₁ ≤ 𝓘 u₂ generalizing u₁ u₂ g₁ g₂
  · have hl := (le_or_ge_or_disjoint.resolve_left h2u).resolve_right hd
    rw [disjoint_comm] at hd
    convert this hu₂ hu₁ hu.symm hg₂ hg₁ hd hl using 1
    · rw [← RCLike.enorm_conj, ← integral_conj]; congr! 3
      rw [map_mul, conj_conj, mul_comm]
    · rw [inter_comm]; ring
  exact correlation_separated_trees_of_subset hu₁ hu₂ hu h2u hg₁ hg₂

/-! ## Section 7.7 -/

def rowDecomp_zornset (s : Set (𝔓 X)) :=
  { x : Set (𝔓 X) | x ⊆ s} ∩ {x : Set (𝔓 X) | x.PairwiseDisjoint (𝓘 ·: _ → Set X)} ∩
    {x : Set (𝔓 X) | x ⊆ {u | Maximal (· ∈ 𝓘 '' s) (𝓘 u)}}

lemma mem_rowDecomp_zornset_iff (s s' : Set (𝔓 X)) :
    s' ∈ rowDecomp_zornset s ↔ (s' ⊆ s ∧ s'.PairwiseDisjoint (𝓘 ·: _ → Set X) ∧
      ∀ u ∈ s', Maximal (· ∈ 𝓘 '' s) (𝓘 u)) := by
  simp_rw [rowDecomp_zornset, mem_inter_iff, mem_setOf, and_assoc]
  nth_rw 2 [subset_def]
  simp_rw [mem_setOf]

lemma rowDecomp_zornset_chain_Union_bound (s' : Set (𝔓 X)) {c : Set (Set (𝔓 X))} (hc : c ⊆ rowDecomp_zornset s')
    (hc_chain : IsChain (· ⊆ ·) c) :
    (⋃ s ∈ c,s) ∈ rowDecomp_zornset s' ∧ ∀ s ∈ c, s ⊆ ⋃ s'' ∈ c, s'' := by
  simp_rw [rowDecomp_zornset,subset_inter_iff] at hc ⊢
  obtain ⟨⟨hc₁,hc₂⟩,hc₃⟩ := hc
  simp_rw [mem_inter_iff,mem_setOf]
  repeat constructor
  · exact iUnion₂_subset_iff.mpr hc₁
  · exact hc_chain.pairwiseDisjoint_iUnion₂ _ _ hc₂
  · exact iUnion₂_subset_iff.mpr hc₃
  · exact fun s a_1 ↦ subset_iUnion₂_of_subset s a_1 fun ⦃a_2⦄ a ↦ a

def rowDecomp_𝔘 (t : Forest X n) (j : ℕ) : Set (𝔓 X) :=
  (zorn_subset (rowDecomp_zornset (t \ ⋃ i < j, rowDecomp_𝔘 t i))
  (fun _ hc => Exists.intro _ ∘ rowDecomp_zornset_chain_Union_bound _ hc)).choose

lemma rowDecomp_𝔘_def (t : Forest X n) (j : ℕ) :
    Maximal (fun x ↦ x ∈ rowDecomp_zornset (t \ ⋃ i < j, rowDecomp_𝔘 t i)) (rowDecomp_𝔘 t j) := by
  rw [rowDecomp_𝔘]
  apply Exists.choose_spec

lemma rowDecomp_𝔘_mem_zornset (t : Forest X n) (j : ℕ) :
    t.rowDecomp_𝔘 j ∈ rowDecomp_zornset (t \ ⋃ i < j, rowDecomp_𝔘 t i) :=
  (rowDecomp_𝔘_def t j).prop

lemma rowDecomp_𝔘_subset (t : Forest X n) (j : ℕ) :
    t.rowDecomp_𝔘 j ⊆ t \ ⋃ i < j, rowDecomp_𝔘 t i := by
  have := rowDecomp_𝔘_mem_zornset t j
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.left

lemma rowDecomp_𝔘_pairwiseDisjoint (t : Forest X n) (j : ℕ) :
    (t.rowDecomp_𝔘 j).PairwiseDisjoint (𝓘 ·: _ → Set X) := by
  have := rowDecomp_𝔘_mem_zornset t j
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.right.left

lemma mem_rowDecomp_𝔘_maximal (t : Forest X n) (j : ℕ) :
    ∀ x ∈ (t.rowDecomp_𝔘 j), Maximal (· ∈ 𝓘 '' (t \ ⋃ i < j, rowDecomp_𝔘 t i)) (𝓘 x) := by
  have := rowDecomp_𝔘_mem_zornset t j
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.right.right

lemma rowDecomp_𝔘_subset_forest (t : Forest X n) (j : ℕ) :
  rowDecomp_𝔘 t j ⊆ t := subset_trans (rowDecomp_𝔘_subset t j) diff_subset

/-- The row-decomposition of a tree, defined in the proof of Lemma 7.7.1.
The indexing is off-by-one compared to the blueprint. -/
def rowDecomp (t : Forest X n) (j : ℕ) : Row X n where
  𝔘 := rowDecomp_𝔘 t j
  𝔗 := t
  nonempty' hu := t.nonempty (rowDecomp_𝔘_subset_forest t j hu)
  ordConnected' hu:= t.ordConnected' (rowDecomp_𝔘_subset_forest t j hu)
  𝓘_ne_𝓘' hu := t.𝓘_ne_𝓘' (rowDecomp_𝔘_subset_forest t j hu)
  smul_four_le' hu := t.smul_four_le' (rowDecomp_𝔘_subset_forest t j hu)
  stackSize_le' := le_trans
    (stackSize_mono (rowDecomp_𝔘_subset_forest t j))
    t.stackSize_le'
  dens₁_𝔗_le' hu := t.dens₁_𝔗_le' (rowDecomp_𝔘_subset_forest t j hu)
  lt_dist' hu hu' := t.lt_dist' (rowDecomp_𝔘_subset_forest t j hu) (rowDecomp_𝔘_subset_forest t j hu')
  ball_subset' hu := t.ball_subset' (rowDecomp_𝔘_subset_forest t j hu)
  pairwiseDisjoint' := rowDecomp_𝔘_pairwiseDisjoint t j

lemma mem_forest_of_mem {t: Forest X n} {j : ℕ} {x : 𝔓 X} (hx : x ∈ t.rowDecomp j) : x ∈ t :=
  rowDecomp_𝔘_subset_forest t j hx

lemma rowDecomp_𝔘_eq (t : Forest X n) (j : ℕ) :
  (t.rowDecomp j).𝔘 = rowDecomp_𝔘 t j := rfl

lemma stackSize_remainder_ge_one_of_exists (t : Forest X n) (j : ℕ) (x:X)
    (this : ∃ 𝔲' ∈ (t.rowDecomp j).𝔘, x ∈ 𝓘 𝔲') :
    1 ≤ stackSize ((t \ ⋃ i < j, t.rowDecomp i) ∩ t.rowDecomp j: Set _) x := by
  classical
  obtain ⟨𝔲',h𝔲'⟩ := this
  dsimp [stackSize]
  rw [← Finset.sum_erase_add _ (a := 𝔲')]
  · rw [indicator_apply,← Grid.mem_def,if_pos h𝔲'.right,Pi.one_apply]
    simp only [le_add_iff_nonneg_left, zero_le]
  simp only [mem_inter_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨t.rowDecomp_𝔘_subset j h𝔲'.left,h𝔲'.left⟩

lemma remainder_stackSize_le (t : Forest X n) (j : ℕ) :
  ∀ x:X, stackSize (t \ ⋃ i < j, t.rowDecomp i : Set _) x ≤ 2 ^ n - j := by
    intro x
    induction j with
    | zero =>
      simp only [not_lt_zero', iUnion_of_empty, iUnion_empty, diff_empty, tsub_zero]
      exact t.stackSize_le'
    | succ j hinduct =>
      if h: ∃ 𝔲 ∈ (t \ ⋃ i < j + 1, t.rowDecomp i : Set _), x ∈ 𝓘 𝔲 then
        have : ∃ s, Maximal (· ∈ (𝓘 '' (t \ ⋃ i < j, t.rowDecomp i : Set _))) s ∧ x ∈ s := by
          obtain ⟨𝔲,h𝔲⟩ := h
          rw [biUnion_lt_succ,← diff_diff,mem_diff] at h𝔲
          exact (((toFinite _).image 𝓘).exists_le_maximal ⟨𝔲,h𝔲.left.left,rfl⟩).imp
            fun _ hz => ⟨hz.right, Grid.mem_mono hz.left h𝔲.right⟩
        obtain ⟨𝔲,h𝔲⟩ := h
        simp only [biUnion_lt_succ, ← diff_diff] at h𝔲 ⊢
        rw [stackSize_sdiff_eq,← Nat.sub_sub]
        apply tsub_le_tsub hinduct (stackSize_remainder_ge_one_of_exists t j x _)
        rw [mem_diff] at h𝔲
        apply (or_not).elim id
        push_neg
        intro h
        apply this.elim
        intro _ ⟨hmax,hz⟩
        obtain ⟨u,hu,rfl⟩ := hmax.prop
        use u
        rw [mem_𝔘]
        refine ⟨?_,hz⟩
        apply (t.rowDecomp_𝔘_def j).mem_of_prop_insert
        rw [mem_rowDecomp_zornset_iff]
        simp only [mem_insert_iff, mem_diff,
          mem_𝔘, mem_iUnion, not_and, forall_eq_or_imp]
        constructor
        · rw [insert_subset_iff]
          simp_rw [rowDecomp_𝔘_eq] at hu
          exact ⟨hu, rowDecomp_𝔘_subset _ _⟩
        constructor
        · rw [pairwiseDisjoint_insert]
          use t.rowDecomp_𝔘_pairwiseDisjoint j
          intro k hk hne
          have : 𝓘 u = 𝓘 k → u = k := by
            specialize h k hk
            intro heq
            rw [← heq] at h
            contradiction
          obtain (h|h|h) := le_or_ge_or_disjoint (i := 𝓘 u) (j := 𝓘 k)
          case inr.inr => exact h
          · have heq : 𝓘 u = 𝓘 k := by
              apply le_antisymm h
              exact hmax.le_of_ge ⟨k,rowDecomp_𝔘_subset t j hk,rfl⟩ h
            exact (hne (this heq)).elim
          · have heq : 𝓘 u = 𝓘 k := by
              apply le_antisymm _ h
              exact (mem_rowDecomp_𝔘_maximal t j k hk).le_of_ge ⟨u,hu,rfl⟩ h
            exact (hne (this heq)).elim
        · exact ⟨hmax, mem_rowDecomp_𝔘_maximal t j⟩
      else
        dsimp [stackSize]
        push_neg at h
        rw [Finset.sum_congr rfl (g := fun _ => 0) (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, indicator_apply_eq_zero,
            Pi.one_apply, one_ne_zero] at h ⊢
          exact h)]
        rw [Finset.sum_eq_zero (fun _ _ => rfl)]
        exact zero_le _

/-- Part of Lemma 7.7.1 -/
@[simp]
lemma biUnion_rowDecomp : ⋃ j < 2 ^ n, t.rowDecomp j = (t : Set (𝔓 X)) := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff,rowDecomp_𝔘_eq]
    exact fun i _ => rowDecomp_𝔘_subset_forest t i
  · rw [← diff_eq_empty]
    exact eq_empty_of_forall_stackSize_zero _ fun x =>
      Nat.eq_zero_of_le_zero ((Nat.sub_self _).symm ▸ remainder_stackSize_le t (2 ^ n) x)

/-- Part of Lemma 7.7.1 -/
lemma pairwiseDisjoint_rowDecomp :
    (Iio (2 ^ n)).PairwiseDisjoint (rowDecomp t · : ℕ → Set (𝔓 X)) := by
  intro i hi j hj hne
  rw [onFun_apply,Set.disjoint_iff]
  wlog hij : i < j
  · rw [Set.inter_comm]
    apply this hj hi hne.symm
    omega
  intro x hx
  obtain ⟨hx₁,hx₂⟩ := hx
  revert hx₁
  simp only [mem_𝔘, mem_empty_iff_false, imp_false]
  rw [rowDecomp_𝔘_eq t j] at hx₂
  have := ((rowDecomp_𝔘_subset t j) hx₂).right
  simp_rw [mem_iUnion, exists_prop, not_exists, not_and] at this
  exact this i hij

@[simp] lemma rowDecomp_apply : t.rowDecomp j u = t u := rfl

open scoped Classical in
/-- The definition of `T_{ℜ_j}*f(x)`, defined at the start of Proposition 2.0.4's proof. -/
def rowCarlesonSum (t : Forest X n) (j : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ u with u ∈ rowDecomp t j, adjointCarlesonSum (t u) f x

/-- The constant used in `row_bound`.
Has value `2 ^ (156 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_1 (a n : ℕ) : ℝ≥0 := 2 ^ (156 * (a : ℝ) ^ 3 - n / 2)

/-- The constant used in `indicator_row_bound`.
Has value `2 ^ (257 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_2 (a n : ℕ) : ℝ≥0 := 2 ^ (257 * (a : ℝ) ^ 3 - n / 2)

/-- Part of Lemma 7.7.2. -/
lemma row_bound (hj : j < 2 ^ n) (hf : BoundedCompactSupport f)
    (h2f : ∀ x, ‖f x‖ ≤ G.indicator 1 x) :
    eLpNorm (rowCarlesonSum t j f) 2 volume ≤ C7_7_2_1 a n * eLpNorm f 2 volume := by
  sorry

/-- Part of Lemma 7.7.2. -/
lemma indicator_row_bound (hj : j < 2 ^ n) (hf : BoundedCompactSupport f)
    (h2f : ∀ x, ‖f x‖ ≤ G.indicator 1 x) :
    eLpNorm (F.indicator (rowCarlesonSum t j f)) 2 volume ≤
    C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  sorry

open Classical in
lemma row_correlation_aux (t : Forest X n) (lj : j < 2 ^ n) (lj' : j' < 2 ^ n) (hn : j ≠ j')
    (nf : ∀ x, ‖f x‖ ≤ G.indicator 1 x) :
    (∑ u with u ∈ t.rowDecomp j, ∑ u' with u' ∈ t.rowDecomp j',
    eLpNorm ((𝓘 u ∩ 𝓘 u' : Set X).indicator
      (adjointBoundaryOperator t u f) ·) 2 volume ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤
    C7_4_3 a * eLpNorm f 2 volume := by
  set U : Finset (𝔓 X) := {u | u ∈ t.rowDecomp j}
  set U' : Finset (𝔓 X) := {u' | u' ∈ t.rowDecomp j'}
  calc
    _ = (∑ u ∈ U, ∑ u' ∈ U', ∫⁻ x in 𝓘 u',
        (𝓘 u : Set X).indicator (adjointBoundaryOperator t u f · ^ 2) x) ^ (2 : ℝ)⁻¹ := by
      congr! with u mu u' mu'
      rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
        ← ENNReal.rpow_mul, div_mul_cancel₀ _ two_ne_zero, ENNReal.rpow_one,
        show (2 : ℝ) = (2 : ℕ) by rfl]
      simp_rw [ENNReal.rpow_natCast, enorm_eq_self]
      rw [← lintegral_indicator coeGrid_measurable]; congr with x
      simp_rw [sq, ← inter_indicator_mul, inter_self, indicator_indicator, inter_comm]
    _ = (∑ u ∈ U, ∫⁻ x in ⋃ u' ∈ U', 𝓘 u',
        (𝓘 u : Set X).indicator (adjointBoundaryOperator t u f · ^ 2) x) ^ (2 : ℝ)⁻¹ := by
      congr! with u mu; refine (lintegral_biUnion_finset ?_ (fun _ _ ↦ coeGrid_measurable) _).symm
      convert rowDecomp_𝔘_pairwiseDisjoint t j'
      simp_rw [U', Finset.coe_filter, Finset.mem_univ, true_and]; rfl
    _ ≤ (∑ u ∈ U, ∫⁻ x in 𝓘 u, adjointBoundaryOperator t u f x ^ 2) ^ (2 : ℝ)⁻¹ := by
      simp_rw [← lintegral_indicator coeGrid_measurable]
      gcongr with u mu; exact setLIntegral_le_lintegral _ _
    _ ≤ _ := by
      sorry

/-- The constant used in `row_correlation`. -/
irreducible_def C7_7_3 (a n : ℕ) : ℝ≥0 := C7_4_3 a ^ 2 * C7_4_4 a n

/-- Lemma 7.7.3. -/
lemma row_correlation (lj : j < 2 ^ n) (lj' : j' < 2 ^ n) (hn : j ≠ j')
    (hf₁ : BoundedCompactSupport f₁) (nf₁ : ∀ x, ‖f₁ x‖ ≤ G.indicator 1 x)
    (hf₂ : BoundedCompactSupport f₂) (nf₂ : ∀ x, ‖f₂ x‖ ≤ G.indicator 1 x) :
    ‖∫ x, rowCarlesonSum t j f₁ x * conj (rowCarlesonSum t j' f₂ x)‖ₑ ≤
    C7_7_3 a n * eLpNorm f₁ 2 volume * eLpNorm f₂ 2 volume := by
  classical
  let W := ({u | u ∈ t.rowDecomp j} : Finset _) ×ˢ ({u' | u' ∈ t.rowDecomp j'} : Finset _)
  let N₁ (w : 𝔓 X × 𝔓 X) :=
    eLpNorm ((𝓘 w.1 ∩ 𝓘 w.2 : Set X).indicator (adjointBoundaryOperator t w.1 f₁) ·) 2 volume
  let N₂ (w : 𝔓 X × 𝔓 X) :=
    eLpNorm ((𝓘 w.1 ∩ 𝓘 w.2 : Set X).indicator (adjointBoundaryOperator t w.2 f₂) ·) 2 volume
  have N₁_bound : (∑ w ∈ W, N₁ w ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤ C7_4_3 a * eLpNorm f₁ 2 volume := by
    unfold W N₁; rw [Finset.sum_product]
    exact row_correlation_aux t lj lj' hn nf₁
  have N₂_bound : (∑ w ∈ W, N₂ w ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤ C7_4_3 a * eLpNorm f₂ 2 volume := by
    unfold W N₂; rw [Finset.sum_product, Finset.sum_comm]; dsimp only
    conv_lhs => enter [1, 2, u', 2, u]; rw [inter_comm]
    exact row_correlation_aux t lj' lj hn.symm nf₂
  calc
    _ = ‖∫ x, ∑ u with u ∈ rowDecomp t j, ∑ u' with u' ∈ rowDecomp t j',
        adjointCarlesonSum (t u) f₁ x * conj (adjointCarlesonSum (t u') f₂ x)‖ₑ := by
      congr! with x; unfold rowCarlesonSum
      rw [Finset.sum_mul]; congr! with u mu; rw [← Finset.mul_sum, map_sum]
    _ = ‖∑ u with u ∈ rowDecomp t j, ∫ x, ∑ u' with u' ∈ rowDecomp t j',
        adjointCarlesonSum (t u) f₁ x * conj (adjointCarlesonSum (t u') f₂ x)‖ₑ := by
      congr
      exact integral_finset_sum _ fun u mu ↦
        (BoundedCompactSupport.finset_sum fun u' mu' ↦
          hf₁.adjointCarlesonSum.mul hf₂.adjointCarlesonSum.conj).integrable
    _ = ‖∑ u with u ∈ rowDecomp t j, ∑ u' with u' ∈ rowDecomp t j', ∫ x,
        adjointCarlesonSum (t u) f₁ x * conj (adjointCarlesonSum (t u') f₂ x)‖ₑ := by
      congr! with u mu
      exact integral_finset_sum _ fun u' mu' ↦
        (hf₁.adjointCarlesonSum.mul hf₂.adjointCarlesonSum.conj).integrable
    _ ≤ ∑ u with u ∈ rowDecomp t j, ‖∑ u' with u' ∈ rowDecomp t j', ∫ x,
        adjointCarlesonSum (t u) f₁ x * conj (adjointCarlesonSum (t u') f₂ x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ u with u ∈ rowDecomp t j, ∑ u' with u' ∈ rowDecomp t j',
        ‖∫ x, adjointCarlesonSum (t u) f₁ x * conj (adjointCarlesonSum (t u') f₂ x)‖ₑ := by
      gcongr with u mu; exact enorm_sum_le _ _
    _ ≤ ∑ u with u ∈ rowDecomp t j, ∑ u' with u' ∈ rowDecomp t j',
        C7_4_4 a n *
        eLpNorm ((𝓘 u ∩ 𝓘 u' : Set X).indicator (adjointBoundaryOperator t u f₁) ·) 2 volume *
        eLpNorm ((𝓘 u ∩ 𝓘 u' : Set X).indicator (adjointBoundaryOperator t u' f₂) ·) 2 volume := by
      gcongr with u mu u' mu'
      simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mu mu'
      refine correlation_separated_trees (mem_forest_of_mem mu) (mem_forest_of_mem mu') ?_ hf₁ hf₂
      exact (pairwiseDisjoint_rowDecomp lj lj' hn).ne_of_mem mu mu'
    _ = C7_4_4 a n * ∑ w ∈ W, N₁ w * N₂ w := by
      rw [← Finset.sum_product', Finset.mul_sum]; congr! 1 with w mw; rw [mul_assoc]
    _ ≤ C7_4_4 a n *
        (∑ w ∈ W, N₁ w ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ * (∑ w ∈ W, N₂ w ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
      rw [← one_div, mul_assoc]; gcongr
      exact ENNReal.inner_le_Lp_mul_Lq _ _ _ Real.HolderConjugate.two_two
    _ ≤ C7_4_4 a n * (C7_4_3 a * eLpNorm f₁ 2 volume) * (C7_4_3 a * eLpNorm f₂ 2 volume) := by
      gcongr
    _ = _ := by rw [C7_7_3, sq, ENNReal.coe_mul, ENNReal.coe_mul]; ring

variable (t) in
/-- The definition of `Eⱼ` defined above Lemma 7.7.4. -/
def rowSupport (j : ℕ) : Set X := ⋃ (u ∈ rowDecomp t j) (p ∈ t u), E p

lemma disjoint_impl {p p' : 𝔓 X} : Disjoint (Ω p) (Ω p') → Disjoint (E p) (E p') := by
  simp_rw [Set.disjoint_iff,subset_def]
  intro h x hx
  exact h (Q x) ⟨Q_mem_Ω hx.left, Q_mem_Ω hx.right⟩

lemma disjoint_of_ne_of_mem {i j : ℕ} {u u' : 𝔓 X} (hne : u ≠ u') (hu : u ∈ t.rowDecomp i) (hu' : u' ∈ t.rowDecomp j)
  {p p' : 𝔓 X} (hp : p ∈ t u) (hp' : p' ∈ t u') : Disjoint (E p) (E p') := by
  classical
  wlog hsle : 𝔰 p ≤ 𝔰 p'
  · exact (this hne.symm hu' hu hp' hp (Int.le_of_not_le hsle)).symm
  -- if x is in the inter, both `Disjoint (Ω p) (Ω p')` and `Q x ∈ Ω p ∩ Ω p'`
  refine _root_.not_imp_self.mp (fun h => disjoint_impl ?_)
  simp only [Set.disjoint_iff, subset_def, mem_inter_iff, mem_empty_iff_false, imp_false, not_and,
    not_forall, Decidable.not_not] at h
  obtain ⟨x,hxp, hxp'⟩ := h
  rw [← rowDecomp_apply (j := j)] at hp'
  have 𝓘_p_le : 𝓘 p ≤ 𝓘 p' := by
    exact ⟨(fundamental_dyadic hsle).resolve_right <|
      Set.Nonempty.not_disjoint <|
      Set.nonempty_of_mem ⟨E_subset_𝓘 hxp,E_subset_𝓘 hxp'⟩, hsle⟩
  have : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u') := lt_dist t
    (mem_forest_of_mem hu') (mem_forest_of_mem hu) hne.symm hp
    <| le_trans 𝓘_p_le (𝓘_le_𝓘 _ hu' hp')
  have := calc 2 ^ (Z * (n + 1)) - 4
    _ < dist_(p) (𝒬 p) (𝒬 u') - dist_(p) (𝒬 p') (𝒬 u') :=
      sub_lt_sub this <| lt_of_le_of_lt (Grid.dist_mono 𝓘_p_le) <| dist_lt_four _ hu' hp'
    _ ≤ dist_(p) (𝒬 p) (𝒬 p') := by
      exact le_trans (le_abs_self _) <|
        abs_dist_sub_le (α := WithFunctionDistance (𝔠 p) (↑D ^ 𝔰 p / 4)) _ _ _
  have : 𝒬 p' ∉ ball_(p) (𝒬 p) 1 := by
    rw [mem_ball (α := WithFunctionDistance (𝔠 p) (↑D ^ 𝔰 p / 4)),dist_comm]
    exact not_lt_of_le <| le_trans (calculation_7_7_4 (X := X)) this.le
  have : ¬(Ω p' ⊆ Ω p) := (fun hx => this <| subset_cball <| hx 𝒬_mem_Ω)
  exact (relative_fundamental_dyadic 𝓘_p_le).resolve_right this

/-- Lemma 7.7.4 -/
lemma pairwiseDisjoint_rowSupport : (Iio (2 ^ n)).PairwiseDisjoint (rowSupport t) := by
  intro i hi j hj hne
  have rowDecomp_disjoint : Disjoint (α := Set (𝔓 X)) (t.rowDecomp i) (t.rowDecomp j) := by
    exact (pairwiseDisjoint_rowDecomp (t := t) hi hj hne)
  clear hi hj hne
  dsimp [onFun, rowSupport]
  simp only [disjoint_iUnion_right, disjoint_iUnion_left]
  intro u hu p hp u' hu' p' hp'
  exact disjoint_of_ne_of_mem (rowDecomp_disjoint.ne_of_mem hu' hu) hu' hu hp' hp

end TileStructure.Forest

/-! ## Proposition 2.0.4 -/

irreducible_def C2_0_4_base (a : ℝ) : ℝ≥0 := 2 ^ (432 * a ^ 3)

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := C2_0_4_base a * 2 ^ (- (q - 1) / q * n)

open scoped Classical in
theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

open scoped Classical in
/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function. -/
theorem forest_operator' {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖ₑ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * (volume A) ^ (1/2 : ℝ) := by
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  rw [← enorm_integral_starRingEnd_mul_eq_lintegral_enorm]; swap
  · apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.finset_sum (fun i hi ↦ ?_)
    apply BoundedCompactSupport.restrict
    apply BoundedCompactSupport.carlesonSum
    have : BoundedCompactSupport (F.indicator 1 : X → ℝ) :=
      BoundedCompactSupport.indicator_of_isCompact_closure (memLp_top_const _)
        isBounded_F.isCompact_closure measurableSet_F
    exact BoundedCompactSupport.mono_norm this hf.aestronglyMeasurable h2f
  rw [← integral_indicator hA]
  simp_rw [indicator_mul_left, ← comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  apply (forest_operator 𝔉 hf h2f ?_ ?_).trans; rotate_left
  · apply Measurable.indicator _ hA
    fun_prop
  · apply h'A.subset support_indicator_subset
  gcongr
  · simp only [sub_nonneg, ge_iff_le, inv_le_inv₀ zero_lt_two (q_pos X)]
    exact (q_mem_Ioc (X := X)).2
  · exact le_rfl
  calc
  _ ≤ eLpNorm (A.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    simp only [indicator, coe_algebraMap, Pi.one_apply, Real.norm_eq_abs]
    split_ifs
    · have A (x : ℝ) : x / x ≤ 1 := by
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · simp [hx]
      simpa using A _
    · simp
  _ ≤ _ := by
    rw [eLpNorm_indicator_const hA (by norm_num) (by norm_num)]
    simp

open scoped Classical in
/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function, and with the upper bound in terms
of `volume F` and `volume G`. -/
theorem forest_operator_le_volume {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖ₑ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    (volume F) ^ (1/2 : ℝ) * (volume A) ^ (1/2 : ℝ) := by
  apply (forest_operator' 𝔉 hf h2f hA h'A).trans
  gcongr
  calc
  _ ≤ eLpNorm (F.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    exact (h2f x).trans (le_abs_self _)
  _ ≤ _ := by
    rw [eLpNorm_indicator_const measurableSet_F (by norm_num) (by norm_num)]
    simp
