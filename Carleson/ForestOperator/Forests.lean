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
  rw [← pow_add, ← pow_add,
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

lemma mem_forest_of_mem {t : Forest X n} {j : ℕ} {x : 𝔓 X} (hx : x ∈ t.rowDecomp j) : x ∈ t :=
  rowDecomp_𝔘_subset_forest t j hx

lemma rowDecomp_𝔘_eq (t : Forest X n) (j : ℕ) :
  (t.rowDecomp j).𝔘 = rowDecomp_𝔘 t j := rfl

lemma mem_rowDecomp_iff_mem_rowDecomp_𝔘 (t : Forest X n) (j : ℕ) : ∀ x,
  x ∈ t.rowDecomp j ↔ x ∈ t.rowDecomp_𝔘 j := by intros; rfl

lemma stackSize_remainder_ge_one_of_exists (t : Forest X n) (j : ℕ) (x : X)
    (this : ∃ 𝔲' ∈ (t.rowDecomp j).𝔘, x ∈ 𝓘 𝔲') :
    1 ≤ stackSize ((t \ ⋃ i < j, t.rowDecomp i) ∩ t.rowDecomp j: Set _) x := by
  classical
  obtain ⟨𝔲',h𝔲'⟩ := this
  dsimp [stackSize]
  rw [← Finset.sum_erase_add _ (a := 𝔲')]
  · rw [indicator_apply,← Grid.mem_def,if_pos h𝔲'.right,Pi.one_apply]
    simp only [le_add_iff_nonneg_left, zero_le]
  simp_rw [Finset.mem_filter_univ, mem_inter_iff]
  exact ⟨t.rowDecomp_𝔘_subset j h𝔲'.1, h𝔲'.1⟩

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
        simp only [mem_insert_iff, forall_eq_or_imp]
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
          simp_rw [Finset.mem_filter_univ, indicator_apply_eq_zero,
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
/-- The definition of `T_{ℜ_j}f(x)`, defined above Lemma 7.7.2. -/
def carlesonRowSum (t : Forest X n) (j : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ u with u ∈ rowDecomp t j, carlesonSum (t u) f x

open scoped Classical in
/-- The definition of `T_{ℜ_j}*f(x)`, defined above Lemma 7.7.2. -/
def adjointCarlesonRowSum (t : Forest X n) (j : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ u with u ∈ rowDecomp t j, adjointCarlesonSum (t u) f x

/-- `adjointCarlesonRowSum` is the adjoint of `carlesonRowSum`. -/
lemma adjointCarlesonRowSum_adjoint
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (j : ℕ) :
    ∫ x, conj (g x) * carlesonRowSum t j f x = ∫ x, conj (adjointCarlesonRowSum t j g x) * f x := by
  classical calc
    _ = ∫ x, ∑ u with u ∈ rowDecomp t j, conj (g x) * carlesonSum (t u) f x := by
      unfold carlesonRowSum; simp_rw [Finset.mul_sum]
    _ = ∑ u with u ∈ rowDecomp t j, ∫ x, conj (g x) * carlesonSum (t u) f x := by
      apply integral_finset_sum; intro p _
      exact hg.conj.mul hf.carlesonSum |>.integrable
    _ = ∑ u with u ∈ rowDecomp t j, ∫ y, conj (adjointCarlesonSum (t u) g y) * f y := by
      simp_rw [adjointCarlesonSum_adjoint hf hg]
    _ = ∫ y, ∑ u with u ∈ rowDecomp t j, conj (adjointCarlesonSum (t u) g y) * f y := by
      symm; apply integral_finset_sum; intro p _
      refine BoundedCompactSupport.mul ?_ hf |>.integrable
      exact hg.adjointCarlesonSum.conj
    _ = _ := by congr!; rw [← Finset.sum_mul, ← map_sum]; rfl

/-- The constant used in `row_bound`.
Has value `2 ^ (156 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: edit blueprint to update w/r/t new value of C7_3_1_1
irreducible_def C7_7_2_1 (a n : ℕ) : ℝ≥0 := (C7_3_1_1 a : ℝ≥0) * 2 ^ (a ^ 3 - n/2:ℝ)

lemma C7_7_2_1_eq : C7_7_2_1 a n = 2 ^ (203.5 * a ^3 - n/2: ℝ) := by
  rw [C7_7_2_1,C7_3_1_1, ← NNReal.rpow_add (by norm_num)]
  ring_nf

/--
The approximation being used here should also depend on the constant used to bound the
dens₁ operator found in `Forest.dens₁_𝔗_le`, which is equation 2.0.35 in the blueprint.
As is, for the purposes of 7.7.2 the approximation
`dens₁ (t.𝔗 u) ≤ 2 ^ (2 * a ^ 3 - n)` is good enough, but we assume
`dens₁ (t.𝔗 u) ≤ 2 ^ (4 * a + 1 - n)` in the definition of `Forest`
We get to the first bound by assuming `2 ≤ a`. This is the strictest bound on naturals that works.
-/
lemma C7_7_2_1_bounds (a n : ℕ) (ha : 2 ≤ a) : (C7_3_1_1 a : ℝ≥0∞) * 2 ^ ((4 * a + 1-n)/2 : ℝ) ≤ C7_7_2_1 a n := by
  rw [C7_7_2_1_def,ENNReal.coe_mul]
  gcongr
  rw [ENNReal.coe_rpow_of_ne_zero (by norm_num),ENNReal.coe_ofNat]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [sub_div, add_div, mul_div_right_comm]
  norm_num
  have : 2 ≤ (a:ℝ) := by simpa
  calc (2:ℝ) * a + 1/2
  _ ≤ 2 * a + 2 * 2 := by
    gcongr
    norm_num
  _ ≤ 2 * a + 2 * a := by gcongr
  _ ≤ (a:ℝ) ^ 3 := by
    rw [← left_distrib,← two_mul, pow_three]
    gcongr


/-- The constant used in `indicator_row_bound`.
Has value `2 ^ (257 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: edit blueprint to update w/r/t new value of C7_3_1_2
irreducible_def C7_7_2_2 (a n : ℕ) : ℝ≥0 := (C7_3_1_2 a : ℝ≥0) * 2 ^ (a ^ 3 - n/2:ℝ)

lemma C7_7_2_2_eq (a n : ℕ) : C7_7_2_2 a n = 2 ^ (304 * a ^ 3 - n/2: ℝ) := by
  rw [C7_7_2_2,C7_3_1_2,← NNReal.rpow_add (by norm_num)]
  ring_nf

/--
The approximation being used here should also depend on the constant used to bound the
dens₁ operator found in `Forest.dens₁_𝔗_le`, which is equation 2.0.35 in the blueprint.
As is, for the purposes of 7.2.2 the approximation
`dens₁ (t.𝔗 u) ≤ 2 ^ (2 * a ^ 3 - n)` is good enough, but we assume
`dens₁ (t.𝔗 u) ≤ 2 ^ (4 * a + 1 - n)` in the definition of `Forest`.
We get to the first bound by assuming `2 ≤ a`. This is the strictest bound on naturals that works.
-/
lemma C7_7_2_2_bounds (a n : ℕ) (ha : 2 ≤ a) : (C7_3_1_2 a : ℝ≥0∞) * 2 ^ ((4 * a + 1-n)/2 : ℝ) ≤ C7_7_2_2 a n := by
  rw [C7_7_2_2_def,ENNReal.coe_mul]
  gcongr
  rw [ENNReal.coe_rpow_of_ne_zero (by norm_num),ENNReal.coe_ofNat]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [sub_div, add_div, mul_div_right_comm]
  norm_num
  have : 2 ≤ (a:ℝ) := by simpa
  calc (2:ℝ) * a + 1/2
  _ ≤ 2 * a + 2 * 2 := by
    gcongr
    norm_num
  _ ≤ 2 * a + 2 * a := by gcongr
  _ ≤ (a:ℝ) ^ 3 := by
    rw [← left_distrib,← two_mul, pow_three]
    gcongr

-- move
lemma _root_.ENNReal.sq_le_mul_right {a : ℝ≥0∞} (htop : a ≠ ⊤) (b : ℝ≥0∞) : a ^ 2 ≤ b * a ↔ a ≤ b := by
  if hzero : (a = 0) then
    subst hzero
    simp
  else
    rw [pow_two]
    exact ENNReal.mul_le_mul_right hzero htop

-- move
lemma _root_.ENNReal.le_of_pow_le_pow {a b : ℝ≥0∞} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n → a ≤ b := by
  contrapose!
  exact (ENNReal.pow_right_strictMono hn ·)

-- move to mathlib, check name
@[to_additive]
lemma _root_.MonoidHomClass.map_mulIndicator {F X A B: Type*} [Monoid A] [Monoid B] [FunLike F A B]
    [MonoidHomClass F A B] {s : Set X} (f : F) (x : X) (g : X → A) :
    f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  exact (MonoidHomClass.toMonoidHom f).map_mulIndicator s g x

lemma adjoint_density_tree_bound1
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
    (hg2 : g.support ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖₊ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  simp_rw [← adjointCarlesonSum_adjoint hf hg]
  exact density_tree_bound1 hf hg hg2 hu

lemma adjoint_refined_density_tree_bound1 (hu : u ∈ t) (hf : BoundedCompactSupport f) (hf2 : f.support ⊆ G):
    eLpNorm (adjointCarlesonSum (t u) f) 2 volume ≤
      C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  have hf_indicator : BoundedCompactSupport ((adjointCarlesonSum (t u) f)) :=
    hf.adjointCarlesonSum
  rw [← ENNReal.sq_le_mul_right (hf_indicator.memLp 2).eLpNorm_ne_top,
    eLpNorm_two_eq_enorm_integral_mul_conj (hf_indicator.memLp 2)]
  simp_rw [Complex.mul_conj', ← Complex.conj_mul']
  trans
  · exact adjoint_density_tree_bound1 (X := X) hf_indicator (hf) hf2 hu
  ring_nf
  rfl

lemma adjoint_density_tree_bound2
    (hf : BoundedCompactSupport f) (h2f : support f ⊆ F)
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  simp_rw [← adjointCarlesonSum_adjoint hf hg]
  exact density_tree_bound2 hf h2f hg h2g hu

lemma adjoint_refined_density_tree_bound2 (hu : u ∈ t) (hf : BoundedCompactSupport f) (h2f : f.support ⊆ G):
    eLpNorm (F.indicator <| adjointCarlesonSum (t u) f) 2 volume ≤
      ↑(C7_3_1_2 a) * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (f) 2 volume := by
  have hf_indicator : BoundedCompactSupport (F.indicator (adjointCarlesonSum (t u) (f))) :=
    hf.adjointCarlesonSum.indicator measurableSet_F
  rw [← ENNReal.sq_le_mul_right (hf_indicator.memLp 2).eLpNorm_ne_top,
    eLpNorm_two_eq_enorm_integral_mul_conj (hf_indicator.memLp 2)]
  simp_rw [Complex.mul_conj', ← Complex.conj_mul']
  simp_rw [AddMonoidHomClass.map_indicator, ← indicator_mul]
  eta_expand
  simp_rw [indicator_mul_right]
  trans
  · exact adjoint_density_tree_bound2 hf_indicator support_indicator_subset hf h2f hu
  · ring_nf
    rfl


lemma adjoint_C7_7_2_bound1 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (adjointCarlesonSum (t u) (G.indicator f)) 2 volume ≤
      C7_7_2_1 a n * eLpNorm f 2 volume := by
  calc eLpNorm (adjointCarlesonSum (t u) (G.indicator f)) 2 volume
  _ ≤ C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (G.indicator f) 2 volume := by
    exact adjoint_refined_density_tree_bound1 hu (hf.indicator measurableSet_G)
      support_indicator_subset
  _ ≤ C7_3_1_1 a * 2 ^ ((4 * a + 1 - n) / 2 : ℝ) * eLpNorm f 2 volume := by
    rw [div_eq_mul_inv _ (2:ℝ),ENNReal.rpow_mul]
    gcongr
    · rw [add_sub_right_comm]
      exact t.dens₁_𝔗_le hu
    · exact eLpNorm_indicator_le f
  _ ≤ C7_7_2_1 a n * eLpNorm f 2 volume := by
    gcongr
    exact C7_7_2_1_bounds a n ((show 2 ≤ 4 from by norm_num).trans (four_le_a X))


lemma adjoint_C7_7_2_bound2 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (F.indicator <| adjointCarlesonSum (t u) (G.indicator f)) 2 volume ≤
      C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  calc eLpNorm (F.indicator <| adjointCarlesonSum (t u) (G.indicator f)) 2 volume
  _ ≤ C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (G.indicator f) 2 volume := by
    exact adjoint_refined_density_tree_bound2 hu (hf.indicator measurableSet_G)
      support_indicator_subset
  _ ≤ C7_3_1_2 a * 2 ^ ((4 * a + 1 - n) / 2 : ℝ) * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    rw [div_eq_mul_inv _ (2:ℝ),ENNReal.rpow_mul]
    gcongr
    · rw [add_sub_right_comm]
      exact t.dens₁_𝔗_le hu
    · exact eLpNorm_indicator_le f
  _ ≤ C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    gcongr
    -- it suffices that 2 ≤ a. this can be improved, but involves solving a cubic inequality.
    -- 1 is not enough
    exact C7_7_2_2_bounds a n ((show 2 ≤ 4 from by norm_num).trans (four_le_a X))

open Classical in
lemma part_1' (j : ℕ) {A : Set X} :
    (eLpNorm (A.indicator <|
      ∑ u with u ∈ rowDecomp t j, adjointCarlesonSum (t u) g) 2 volume) ^ 2
    = (eLpNorm (A.indicator <| ∑ u with u ∈ rowDecomp t j,
      ((𝓘 u: Set X).indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g))) 2 volume) ^ 2 := by
  congr! 4 with u hu'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
  ext x
  rw [adjoint_tile_support2_sum (mem_forest_of_mem hu')]

open Classical in
lemma part_2' (hg : BoundedCompactSupport g) {A : Set X} (hA : MeasurableSet A) (j : ℕ) :
    (eLpNorm (A.indicator <| ∑ u with u ∈ rowDecomp t j,
      ((𝓘 u: Set X).indicator <|
        adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator g))) 2 volume) ^ 2
    ≤ ∑ u with u ∈ rowDecomp t j, (eLpNorm (A.indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) 2 volume) ^ 2:= by
  calc _
  _ = (eLpNorm (fun x => ∑ u with u ∈ rowDecomp t j,
      A.indicator ((𝓘 u: Set X).indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) x) 2 volume) ^ 2 := by
    simp_rw [Finset.indicator_sum, ← Finset.sum_apply]
  _ ≤ ∑ u with u ∈ rowDecomp t j, (eLpNorm (A.indicator <| (𝓘 u: Set X).indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) 2 volume) ^ 2 +
      ∑ u with u ∈ rowDecomp t j, ∑ u' ∈ {p | p ∈ rowDecomp t j} with u ≠ u',
        ‖∫ (x:X),((A.indicator ((𝓘 u: Set X).indicator
        <| adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) x) * conj (A.indicator ((𝓘 u': Set X).indicator
        <| adjointCarlesonSum (t u') ((𝓘 u':Set X).indicator g)) x)) ‖ₑ := by
    -- eta_expand
    refine MeasureTheory.BoundedCompactSupport.sq_eLpNorm_le_sums (fun _ => ?_)
    apply BoundedCompactSupport.indicator _ hA
    apply BoundedCompactSupport.indicator _ coeGrid_measurable
    apply BoundedCompactSupport.adjointCarlesonSum
    exact hg.indicator coeGrid_measurable
  _ = ∑ u with u ∈ rowDecomp t j, (eLpNorm (fun x => A.indicator ((𝓘 u: Set X).indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) x) 2 volume) ^ 2 := by
    nth_rw 3 [← add_zero (Finset.sum _ _)]
    congr
    simp only [Finset.sum_eq_zero_iff,
      Finset.mem_filter, Finset.mem_univ, true_and, enorm_eq_zero, and_imp]
    rw [← integral_zero X ℂ (μ := volume)]
    intro u hu u' hu' hne
    congr with x
    simp only [mul_eq_zero,map_eq_zero]
    simp only [indicator_apply_eq_zero, ← imp_or]
    intro hxA
    if hxu: x ∈ (𝓘 u : Set X) then
      right
      intro hxu'
      by_contra
      rw [mem_rowDecomp_iff_mem_rowDecomp_𝔘] at hu hu'
      exact (hne ((rowDecomp_𝔘_pairwiseDisjoint t j).elim_set hu hu' x hxu hxu')).elim
    else
      left
      intro
      contradiction
  _ ≤ _ := by
    gcongr
    simp_rw [Set.indicator_indicator,Set.inter_comm A, ← Set.indicator_indicator]
    apply eLpNorm_indicator_le

open Classical in
lemma part_1_and_2 (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) {A : Set X}
    (ha : MeasurableSet A) (j : ℕ):
  (eLpNorm (A.indicator <| ∑ u with u ∈ rowDecomp t j, adjointCarlesonSum (t u) g) 2 volume) ^ 2
  ≤ ∑ u with u ∈ rowDecomp t j, (eLpNorm (A.indicator
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2 := by
  rw [part_1']
  convert part_2' hg ha j using 4
  congr! 2
  ext x
  simp only [defaultA, defaultD.eq_1, defaultκ.eq_1, indicator_apply_eq_self,
    indicator_apply_eq_zero]
  intro hxG _
  exact Function.notMem_support.mp (hxG <| h2g ·)

omit [MetricSpace X] in
lemma support_subset_of_norm_le_indicator {g : X → ℝ} {A : Set X} (h2f : ∀ x, ‖f x‖ ≤ A.indicator g x) :
    f.support ⊆ A := by
  intro x hx
  contrapose! hx
  simp only [mem_support, ne_eq, Decidable.not_not]
  specialize h2f x
  simp only [indicator_of_notMem hx,norm_le_zero_iff] at h2f
  exact h2f

open Classical in
/-- Part of Lemma 7.7.2. -/
lemma row_bound (_ : j < 2 ^ n) (hg : BoundedCompactSupport g)
    (h2g : g.support ⊆ G) :
    eLpNorm (adjointCarlesonRowSum t j g) 2 volume ≤ C7_7_2_1 a n * eLpNorm g 2 volume := by
  eta_expand
  simp_rw [adjointCarlesonRowSum, ← Finset.sum_apply]
  eta_reduce
  rw [Finset.sum_apply]
  calc
    eLpNorm (∑ u with u ∈ rowDecomp t j, adjointCarlesonSum (t u) g) 2 volume
    = eLpNorm (Set.univ.indicator <|
      ∑ u  with u ∈ rowDecomp t j, adjointCarlesonSum (t u) g) 2 volume := by
      rw [indicator_univ]
  _ ≤ (∑ u with u ∈ rowDecomp t j, (eLpNorm (Set.univ.indicator
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
      apply ENNReal.le_of_pow_le_pow (by norm_num : 2 ≠ 0)
      simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
        ENNReal.rpow_one]
      simp_rw [ENNReal.rpow_two]
      exact part_1_and_2 (t := t) hg h2g (.univ) j
  _ ≤ (∑ u with u ∈ rowDecomp t j, (C7_7_2_1 a n *
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
    simp only [indicator_univ]
    gcongr
    rename_i u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact adjoint_C7_7_2_bound1 (mem_forest_of_mem hu) (hg.indicator coeGrid_measurable)
  _ = C7_7_2_1 a n * (∑ u with u ∈ rowDecomp t j, (
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2) ^ (2⁻¹ : ℝ) := by
    simp_rw [mul_pow (C7_7_2_1 _ _ : ℝ≥0∞), ← Finset.mul_sum,ENNReal.mul_rpow_of_nonneg (_ ^ _) _
      (by positivity : (0:ℝ) ≤ 2⁻¹)]
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num),ENNReal.rpow_one]
  _ ≤ C7_7_2_1 a n * ((eLpNorm g 2 volume) ^2) ^(2⁻¹:ℝ) := by
    gcongr
    apply sum_sq_eLpNorm_indicator_le_of_pairwiseDisjoint (fun _ => coeGrid_measurable)
    simp only [mem_rowDecomp_iff_mem_rowDecomp_𝔘, Finset.coe_filter, Finset.mem_univ, true_and,
      setOf_mem_eq]
    exact rowDecomp_𝔘_pairwiseDisjoint t j
  _ = C7_7_2_1 a n * (eLpNorm g 2 volume) := by
    simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
      ENNReal.rpow_one]

open Classical in
/-- Part of Lemma 7.7.2. -/
lemma indicator_row_bound (_ : j < 2 ^ n) (hg : BoundedCompactSupport g)
    (h2g : g.support ⊆ G) :
    eLpNorm (F.indicator (adjointCarlesonRowSum t j g)) 2 volume ≤
    C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 volume := by
  calc eLpNorm (F.indicator (adjointCarlesonRowSum t j g)) 2 volume
  _ = eLpNorm (F.indicator <| ∑ u with u ∈ rowDecomp t j, (adjointCarlesonSum (t u) g)) 2 volume := by
    eta_expand
    simp_rw [adjointCarlesonRowSum, ← Finset.sum_apply]
    eta_reduce
    rw [Finset.sum_apply]
  _ ≤ (∑ u with u ∈ rowDecomp t j, (eLpNorm (F.indicator <|
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
      apply ENNReal.le_of_pow_le_pow (by norm_num : 2 ≠ 0)
      simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
        ENNReal.rpow_one]
      simp_rw [ENNReal.rpow_two,]
      exact part_1_and_2 (t := t) hg h2g (measurableSet_F) j
  _ ≤ (∑ u with u ∈ rowDecomp t j, (C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
    gcongr
    rename_i u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact adjoint_C7_7_2_bound2 (mem_forest_of_mem hu) (hg.indicator coeGrid_measurable)
  _ ≤ (∑ u ∈ {p | p ∈ rowDecomp t j}, (C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) *
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
    gcongr
    rename_i u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    apply le_biSup _ hu
  _ = C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) *
      (∑ u ∈ {p | p ∈ rowDecomp t j},
      (eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2) ^ (2⁻¹ : ℝ) := by
    simp_rw [mul_pow (_ * _), ← Finset.mul_sum,
      ENNReal.mul_rpow_of_nonneg (_ ^ _) _ (by positivity : (0:ℝ) ≤ 2⁻¹)]
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num),ENNReal.rpow_one]
  _ ≤ C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) *
      ((eLpNorm g 2 volume) ^2) ^(2⁻¹:ℝ) := by
    gcongr
    apply sum_sq_eLpNorm_indicator_le_of_pairwiseDisjoint (fun _ => coeGrid_measurable)
    simp only [mem_rowDecomp_iff_mem_rowDecomp_𝔘, Finset.coe_filter, Finset.mem_univ, true_and,
      setOf_mem_eq]
    exact rowDecomp_𝔘_pairwiseDisjoint t j
  _ = C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) * (eLpNorm g 2 volume) := by
    simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
      ENNReal.rpow_one]
  _ ≤ C7_7_2_2 a n * ((⨆ u' ∈ t, dens₂ (t u')) ^ (2 : ℝ)⁻¹) * (eLpNorm g 2 volume) := by
    gcongr _ * ?_ ^ _ * _
    apply biSup_mono
    exact fun _ => mem_forest_of_mem
  _ = C7_7_2_2 a n * dens₂ (⋃ u ∈ t, (fun x ↦ t.𝔗 x) u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 volume := by
    congr 3
    rw [dens₂_eq_biSup_dens₂]
    simp_rw [dens₂_eq_biSup_dens₂ (⇑t _), iSup_iUnion]


open Classical in
lemma row_correlation_aux (hf : BoundedCompactSupport f) (nf : f.support ⊆ G) :
    (∑ u with u ∈ t.rowDecomp j, ∑ u' with u' ∈ t.rowDecomp j',
    eLpNorm ((𝓘 u ∩ 𝓘 u' : Set X).indicator
      (adjointBoundaryOperator t u ((𝓘 u : Set X).indicator f)) ·) 2 volume ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤
    C7_4_3 a * eLpNorm f 2 volume := by
  set U : Finset (𝔓 X) := {u | u ∈ t.rowDecomp j}
  set U' : Finset (𝔓 X) := {u' | u' ∈ t.rowDecomp j'}
  calc
    _ = (∑ u ∈ U, ∑ u' ∈ U', ∫⁻ x in 𝓘 u', (𝓘 u : Set X).indicator
        (adjointBoundaryOperator t u ((𝓘 u : Set X).indicator f) · ^ 2) x) ^ (2 : ℝ)⁻¹ := by
      congr! with u mu u' mu'
      rw [show (2 : ℝ) = (2 : ℕ) by rfl, ENNReal.rpow_natCast, sq_eLpNorm_two]
      simp_rw [enorm_eq_self]
      rw [← lintegral_indicator coeGrid_measurable]; congr with x
      simp_rw [sq, ← inter_indicator_mul, inter_self, indicator_indicator, inter_comm]
    _ = (∑ u ∈ U, ∫⁻ x in ⋃ u' ∈ U', 𝓘 u', (𝓘 u : Set X).indicator
        (adjointBoundaryOperator t u ((𝓘 u : Set X).indicator f) · ^ 2) x) ^ (2 : ℝ)⁻¹ := by
      congr! with u mu; refine (lintegral_biUnion_finset ?_ (fun _ _ ↦ coeGrid_measurable) _).symm
      convert rowDecomp_𝔘_pairwiseDisjoint t j'
      simp_rw [U', Finset.coe_filter, Finset.mem_univ, true_and]; rfl
    _ ≤ (∑ u ∈ U, ∫⁻ x in 𝓘 u,
        adjointBoundaryOperator t u ((𝓘 u : Set X).indicator f) x ^ 2) ^ (2 : ℝ)⁻¹ := by
      simp_rw [← lintegral_indicator coeGrid_measurable]
      gcongr with u mu; exact setLIntegral_le_lintegral _ _
    _ ≤ (∑ u ∈ U, eLpNorm (adjointBoundaryOperator t u
        ((𝓘 u : Set X).indicator f)) 2 volume ^ 2) ^ (2 : ℝ)⁻¹ := by
      gcongr with u mu; rw [sq_eLpNorm_two]; simp_rw [enorm_eq_self]
      exact setLIntegral_le_lintegral _ _
    _ ≤ (∑ u ∈ U, (C7_4_3 a * eLpNorm ((𝓘 u : Set X).indicator f) 2 volume) ^ 2) ^ (2 : ℝ)⁻¹ := by
      gcongr with u mu
      rw [Finset.mem_filter_univ] at mu
      apply adjoint_tree_control (mem_forest_of_mem mu) (hf.indicator coeGrid_measurable)
      rw [Set.support_indicator]
      exact inter_subset_right.trans nf
    _ ≤ C7_4_3 a * (eLpNorm f 2 volume ^ 2) ^ (2 : ℝ)⁻¹ := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul, show (2 : ℕ) * (2 : ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
      gcongr with u mu
      apply sum_sq_eLpNorm_indicator_le_of_pairwiseDisjoint fun _ ↦ coeGrid_measurable
      convert rowDecomp_𝔘_pairwiseDisjoint t j
      simp_rw [U, Finset.coe_filter, Finset.mem_univ, true_and]; rfl
    _ = _ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, show (2 : ℕ) * (2 : ℝ)⁻¹ = 1 by norm_num,
        ENNReal.rpow_one]

/-- The constant used in `row_correlation`. -/
irreducible_def C7_7_3 (a n : ℕ) : ℝ≥0 := C7_4_3 a ^ 2 * C7_4_4 a n

/-- Lemma 7.7.3. -/
lemma row_correlation (lj : j < 2 ^ n) (lj' : j' < 2 ^ n) (hn : j ≠ j')
    (hf₁ : BoundedCompactSupport f₁) (nf₁ : f₁.support ⊆ G)
    (hf₂ : BoundedCompactSupport f₂) (nf₂ : f₂.support ⊆ G) :
    ‖∫ x, adjointCarlesonRowSum t j f₁ x * conj (adjointCarlesonRowSum t j' f₂ x)‖ₑ ≤
    C7_7_3 a n * eLpNorm f₁ 2 volume * eLpNorm f₂ 2 volume := by
  classical
  let W := ({u | u ∈ t.rowDecomp j} : Finset _) ×ˢ ({u' | u' ∈ t.rowDecomp j'} : Finset _)
  let N₁ (w : 𝔓 X × 𝔓 X) := eLpNorm ((𝓘 w.1 ∩ 𝓘 w.2 : Set X).indicator
    (adjointBoundaryOperator t w.1 ((𝓘 w.1 : Set X).indicator f₁)) ·) 2 volume
  let N₂ (w : 𝔓 X × 𝔓 X) := eLpNorm ((𝓘 w.1 ∩ 𝓘 w.2 : Set X).indicator
    (adjointBoundaryOperator t w.2 ((𝓘 w.2 : Set X).indicator f₂)) ·) 2 volume
  have N₁_bound : (∑ w ∈ W, N₁ w ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤ C7_4_3 a * eLpNorm f₁ 2 volume := by
    unfold W N₁; rw [Finset.sum_product]
    exact row_correlation_aux hf₁ nf₁
  have N₂_bound : (∑ w ∈ W, N₂ w ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤ C7_4_3 a * eLpNorm f₂ 2 volume := by
    unfold W N₂; rw [Finset.sum_product, Finset.sum_comm]; dsimp only
    conv_lhs => enter [1, 2, u', 2, u]; rw [inter_comm]
    exact row_correlation_aux hf₂ nf₂
  calc
    _ = ‖∫ x, ∑ u with u ∈ rowDecomp t j, ∑ u' with u' ∈ rowDecomp t j',
        adjointCarlesonSum (t u) f₁ x * conj (adjointCarlesonSum (t u') f₂ x)‖ₑ := by
      congr! with x; unfold adjointCarlesonRowSum
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
        ‖∫ x, adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator f₁) x *
        conj (adjointCarlesonSum (t u') ((𝓘 u' : Set X).indicator f₂) x)‖ₑ := by
      congr! 5 with u mu u' mu' x
      rw [Finset.mem_filter_univ] at mu mu'
      rw [adjoint_tile_support2_sum_partial (mem_forest_of_mem mu),
        adjoint_tile_support2_sum_partial (mem_forest_of_mem mu')]
    _ ≤ ∑ u with u ∈ rowDecomp t j, ∑ u' with u' ∈ rowDecomp t j',
        C7_4_4 a n *
        eLpNorm ((𝓘 u ∩ 𝓘 u' : Set X).indicator
          (adjointBoundaryOperator t u ((𝓘 u : Set X).indicator f₁)) ·) 2 volume *
        eLpNorm ((𝓘 u ∩ 𝓘 u' : Set X).indicator
          (adjointBoundaryOperator t u' ((𝓘 u' : Set X).indicator f₂)) ·) 2 volume := by
      gcongr with u mu u' mu'
      rw [Finset.mem_filter_univ] at mu mu'
      refine correlation_separated_trees (mem_forest_of_mem mu) (mem_forest_of_mem mu') ?_
        (hf₁.indicator coeGrid_measurable) (hf₂.indicator coeGrid_measurable)
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
    exact not_lt_of_ge <| le_trans (calculation_7_7_4 (X := X)) this.le
  have : ¬(Ω p' ⊆ Ω p) := (fun hx => this <| subset_cball <| hx 𝒬_mem_Ω)
  exact (relative_fundamental_dyadic 𝓘_p_le).resolve_right this

lemma measurableSet_rowSupport : MeasurableSet (rowSupport t j) :=
  (rowDecomp t j).𝔘.toFinite.measurableSet_biUnion fun v _ ↦
    (t v).toFinite.measurableSet_biUnion fun _ _ ↦ measurableSet_E

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

section FinalProp

open scoped Classical in
lemma forest_operator_g_prelude
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ ≤
    eLpNorm f 2 * eLpNorm (∑ u with u ∈ t, adjointCarlesonSum (t u) g ·) 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf h2f
  have bg := bcs_of_measurable_of_le_indicator_g hg h2g
  calc
    _ = ‖∑ u with u ∈ t, ∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ := by
      congr; rw [← integral_finset_sum]; swap
      · exact fun _ _ ↦ (bg.conj.mul bf.carlesonSum).integrable
      simp_rw [Finset.mul_sum]
    _ = ‖∑ u with u ∈ t, ∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖ₑ := by
      congr! 2 with u mu; exact adjointCarlesonSum_adjoint bf bg _
    _ = ‖∫ x, f x * ∑ u with u ∈ t, conj (adjointCarlesonSum (t u) g x)‖ₑ := by
      congr; rw [← integral_finset_sum]; swap
      · exact fun _ _ ↦ (bg.adjointCarlesonSum.conj.mul bf).integrable
      simp_rw [Finset.mul_sum, mul_comm (f _)]
    _ ≤ ∫⁻ x, ‖f x‖ₑ * ‖∑ u with u ∈ t, conj (adjointCarlesonSum (t u) g x)‖ₑ := by
      simp_rw [← enorm_mul]; exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      simp_rw [← map_sum, RCLike.enorm_conj]
      conv_rhs => rw [← eLpNorm_enorm]; enter [2]; rw [← eLpNorm_enorm]
      exact ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance
        bf.enorm.aestronglyMeasurable.aemeasurable
        (BoundedCompactSupport.finset_sum fun _ _ ↦
          bg.adjointCarlesonSum).enorm.aestronglyMeasurable.aemeasurable

lemma adjointCarlesonRowSum_rowSupport :
    adjointCarlesonRowSum t j f = adjointCarlesonRowSum t j ((rowSupport t j).indicator f) := by
  ext x; unfold adjointCarlesonRowSum adjointCarlesonSum; congr! 2 with u mu p mp
  simp_rw [Finset.mem_filter_univ] at mu mp
  refine setIntegral_congr_ae measurableSet_E (.of_forall fun y my ↦ ?_)
  congr; refine (indicator_of_mem ?_ _).symm
  simp_rw [rowSupport, mem_iUnion₂]; exact ⟨_, mu, _, mp, my⟩

/-- The constant on the `g` side of Proposition 2.0.4. -/
def G2_0_4 (a n : ℕ) : ℝ≥0 := 2 ^ (470 * a ^ 3) * 2 ^ (-(n / 2 : ℝ))

lemma le_sq_G2_0_4 (a4 : 4 ≤ a) : C7_7_2_1 a n ^ 2 + C7_7_3 a n * 2 ^ n ≤ G2_0_4 a n ^ 2 :=
  calc
    _ ≤ 2 ^ (407 * (a : ℝ) ^ 3 - n) + (2 ^ (203 * a ^ 3)) ^ 2 * C7_4_4 a n * 2 ^ n := by
      rw [C7_7_2_1_eq, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, C7_7_3,
        show (203.5 * (a : ℝ) ^ 3 - n / 2) * (2 : ℕ) = 407 * a ^ 3 - n by ring]
      gcongr; exact C7_4_3_le a4
    _ ≤ 2 ^ (407 * a ^ 3) * 2 ^ (-n : ℝ) +
        2 ^ (406 * a ^ 3) * (2 ^ (533 * a ^ 3 + 1) * 2 ^ (-(4 * n : ℝ))) * 2 ^ n := by
      rw [sub_eq_add_neg, NNReal.rpow_add two_ne_zero]
      conv_lhs => enter [1, 1, 2]; norm_cast
      rw [NNReal.rpow_natCast, ← pow_mul, show 203 * a ^ 3 * 2 = 406 * a ^ 3 by ring, C7_4_4,
        pow_succ _ (533 * a ^ 3), mul_two]
      gcongr <;> norm_num
    _ = 2 ^ (407 * a ^ 3) * 2 ^ (-n : ℝ) +
        2 ^ (939 * a ^ 3 + 1) * 2 ^ (-(2 * n : ℝ)) * 2 ^ (-n : ℝ) := by
      rw [← mul_assoc, ← pow_add, show 406 * a ^ 3 + (533 * a ^ 3 + 1) = 939 * a ^ 3 + 1 by ring,
        mul_assoc, mul_assoc]; congr 2
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_add two_ne_zero, ← NNReal.rpow_add two_ne_zero]
      congr 1; ring
    _ ≤ 2 ^ (939 * a ^ 3 + 1) * 2 ^ (-n : ℝ) + 2 ^ (939 * a ^ 3 + 1) * 1 * 2 ^ (-n : ℝ) := by
      gcongr
      · exact one_le_two
      · omega
      · exact NNReal.rpow_le_one_of_one_le_of_nonpos one_le_two (by simp)
    _ ≤ 2 ^ (940 * a ^ 3) * 2 ^ (-n : ℝ) := by
      rw [mul_one, ← two_mul, ← mul_assoc, ← pow_succ']; gcongr
      · exact one_le_two
      · rw [show 940 = 939 + 1 by norm_num, add_one_mul, add_assoc]; gcongr
        calc
          _ ≤ 4 * 1 * 1 := by norm_num
          _ ≤ a * a * a := by gcongr <;> omega
          _ = _ := by ring
    _ = _ := by
      rw [G2_0_4, mul_pow, ← pow_mul, ← NNReal.rpow_natCast _ 2, ← NNReal.rpow_mul]
      congr 2 <;> ring

open Classical in
lemma forest_operator_g_main (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    eLpNorm (∑ u with u ∈ t, adjointCarlesonSum (t u) g ·) 2 ^ 2 ≤
    (G2_0_4 a n * eLpNorm g 2) ^ 2 := by
  have bg := bcs_of_measurable_of_le_indicator_g hg h2g
  let TR (j : ℕ) (x : X) := adjointCarlesonRowSum t j ((rowSupport t j).indicator g) x
  have bcsrsi (j : ℕ) : BoundedCompactSupport ((t.rowSupport j).indicator g) volume :=
    bg.indicator measurableSet_rowSupport
  have bcsTR (j : ℕ) : BoundedCompactSupport (TR j) :=
    BoundedCompactSupport.finset_sum fun _ _ ↦
      BoundedCompactSupport.finset_sum fun _ _ ↦ (bcsrsi j).adjointCarleson
  calc
    _ = eLpNorm (∑ j ∈ Finset.range (2 ^ n), adjointCarlesonRowSum t j g ·) 2 ^ 2 := by
      congr; ext x
      have dc : ({u | u ∈ t} : Finset _) =
          (Finset.range (2 ^ n)).biUnion (fun j ↦ {u | u ∈ rowDecomp t j}) := by
        rw [← Finset.toFinset_coe ({u | u ∈ t} : Finset _),
          ← Finset.toFinset_coe (Finset.biUnion ..), toFinset_inj]
        simp_rw [Finset.coe_biUnion, Finset.coe_range, mem_Iio, Finset.coe_filter, Finset.mem_univ,
          true_and]
        exact biUnion_rowDecomp.symm
      rw [dc, Finset.sum_biUnion]; swap
      · rw [Finset.coe_range]; intro j mj j' mj' hn
        simp_rw [← Finset.disjoint_coe, Finset.coe_filter, Finset.mem_univ, true_and]
        exact pairwiseDisjoint_rowDecomp mj mj' hn
      rfl
    _ = eLpNorm (∑ j ∈ Finset.range (2 ^ n), TR j ·) 2 ^ 2 := by
      congr! 4 with x j mj; rw [adjointCarlesonRowSum_rowSupport]
    _ ≤ ∑ j ∈ Finset.range (2 ^ n), eLpNorm (TR j) 2 ^ 2 +
        ∑ j ∈ Finset.range (2 ^ n), ∑ j' ∈ Finset.range (2 ^ n) with j ≠ j',
          ‖∫ x, TR j x * conj (TR j' x)‖ₑ := by
      convert BoundedCompactSupport.sq_eLpNorm_le_sums bcsTR
    _ ≤ ∑ j ∈ Finset.range (2 ^ n), (C7_7_2_1 a n * eLpNorm ((rowSupport t j).indicator g) 2) ^ 2 +
        ∑ j ∈ Finset.range (2 ^ n), ∑ j' ∈ Finset.range (2 ^ n) with j ≠ j',
          C7_7_3 a n * eLpNorm ((rowSupport t j).indicator g) 2 *
          eLpNorm ((rowSupport t j').indicator g) 2 := by
      have nleg {j : ℕ} (x : X) : ‖(t.rowSupport j).indicator g x‖ ≤ G.indicator 1 x := by
        by_cases mx : x ∈ t.rowSupport j
        · rw [indicator_of_mem mx]; exact h2g x
        · rw [indicator_of_notMem mx, norm_zero]; exact indicator_apply_nonneg fun _ ↦ by simp
      gcongr with j mj j mj j' mj'
      · simp_rw [Finset.mem_range] at mj
        exact row_bound mj (bcsrsi j) (support_subset_of_norm_le_indicator nleg)
      · simp_rw [Finset.mem_filter, Finset.mem_range] at mj mj'
        exact row_correlation mj mj'.1 mj'.2 (bcsrsi j) (support_subset_of_norm_le_indicator nleg)
          (bcsrsi j') (support_subset_of_norm_le_indicator nleg)
    _ ≤ C7_7_2_1 a n ^ 2 *
        ∑ j ∈ Finset.range (2 ^ n), eLpNorm ((rowSupport t j).indicator g) 2 ^ 2 +
        C7_7_3 a n * ∑ j ∈ Finset.range (2 ^ n), ∑ j' ∈ Finset.range (2 ^ n),
          eLpNorm ((rowSupport t j).indicator g) 2 *
          eLpNorm ((rowSupport t j').indicator g) 2 := by
      simp_rw [Finset.mul_sum, ← mul_pow, mul_assoc]
      gcongr with j mj; exact Finset.filter_subset ..
    _ ≤ C7_7_2_1 a n ^ 2 *
        ∑ j ∈ Finset.range (2 ^ n), eLpNorm ((rowSupport t j).indicator g) 2 ^ 2 +
        C7_7_3 a n * 2 ^ n *
        ∑ j ∈ Finset.range (2 ^ n), eLpNorm ((rowSupport t j).indicator g) 2 ^ 2 := by
      conv_lhs => enter [2, 2, 2, j]; rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← sq, mul_assoc]; gcongr
      have := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.range (2 ^ n))
        (fun j ↦ eLpNorm ((t.rowSupport j).indicator g) 2 volume) one_le_two
      simp_rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, Finset.card_range,
        show (2 : ℝ) = (2 : ℕ) by rfl, ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] at this
      exact this
    _ ≤ (C7_7_2_1 a n ^ 2 + C7_7_3 a n * 2 ^ n) * eLpNorm g 2 ^ 2 := by
      rw [← add_mul]; gcongr
      apply sum_sq_eLpNorm_indicator_le_of_pairwiseDisjoint fun _ ↦ measurableSet_rowSupport
      rw [Finset.coe_range]; exact pairwiseDisjoint_rowSupport
    _ ≤ _ := by
      rw [mul_pow]; gcongr; norm_cast
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact le_sq_G2_0_4 (four_le_a X)

open Classical in
/-- The `g` side of Proposition 2.0.4. -/
lemma forest_operator_g (t : Forest X n)
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ ≤
    G2_0_4 a n * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  calc
    _ ≤ _ := forest_operator_g_prelude hf h2f hg h2g
    _ ≤ _ := by
      rw [mul_comm _ (eLpNorm f 2 volume), mul_assoc]; gcongr
      rw [← ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < (2 : ℕ) by norm_num),
        ENNReal.rpow_natCast, ENNReal.rpow_natCast]
      exact forest_operator_g_main hg h2g

lemma carlesonRowSum_rowSupport :
    carlesonRowSum t j f = (rowSupport t j).indicator (carlesonRowSum t j f) := by
  symm; rw [indicator_eq_self, support_subset_iff']
  refine fun x nx ↦ Finset.sum_eq_zero fun u mu ↦ Finset.sum_eq_zero fun p mp ↦ ?_
  simp_rw [Finset.mem_filter_univ] at mu mp
  simp only [rowSupport, mem_iUnion, exists_prop, not_exists, not_and] at nx
  exact indicator_of_notMem (nx _ mu _ mp) _

open Classical in
lemma forest_operator_f_prelude
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ ≤
    eLpNorm g 2 * eLpNorm (fun x ↦ G.indicator (∑ u with u ∈ t, carlesonSum (t u) f ·) x) 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf h2f
  have bg := bcs_of_measurable_of_le_indicator_g hg h2g
  calc
    _ ≤ ∫⁻ x, ‖g x‖ₑ * ‖∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ := by
      conv_rhs => enter [2, x]; rw [← RCLike.enorm_conj, ← enorm_mul]
      exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x, ‖g x‖ₑ * ‖G.indicator (∑ u with u ∈ t, carlesonSum (t u) f ·) x‖ₑ := by
      congr! 2 with x; rw [indicator_eq_indicator_one_mul, enorm_mul, ← mul_assoc]
      nth_rw 2 [← enorm_mul]; congr 2
      by_cases hx : x ∈ G
      · simp [indicator_of_mem hx]
      · specialize h2g x
        rw [indicator_of_notMem hx, norm_le_zero_iff] at h2g
        rw [h2g, zero_mul]
    _ ≤ _ :=
      ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance
        bg.enorm.aestronglyMeasurable.aemeasurable
        ((BoundedCompactSupport.finset_sum fun _ _ ↦
          bf.carlesonSum).indicator measurableSet_G).enorm.aestronglyMeasurable.aemeasurable

/-- https://leanprover.zulipchat.com/#narrow/channel/442935-Carleson/topic/Problems.20in.20the.20forest.20operator.20proposition/near/522771057 -/
lemma forest_operator_f_inner
    (hj : j < 2 ^ n) (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    eLpNorm (G.indicator (carlesonRowSum t j f)) 2 ≤
    C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf h2f
  set IGTf := G.indicator (carlesonRowSum t j f)
  have bIGTf : BoundedCompactSupport IGTf :=
    (BoundedCompactSupport.finset_sum fun _ _ ↦ bf.carlesonSum).indicator measurableSet_G
  suffices eLpNorm IGTf 2 ^ 2 ≤
      C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm IGTf 2 * eLpNorm f 2 by
    rcases eq_or_ne (eLpNorm IGTf 2) 0 with he | he
    · simp [he]
    · have nt : eLpNorm IGTf 2 ≠ ⊤ := (bIGTf.memLp _).eLpNorm_ne_top
      rwa [mul_assoc _ (eLpNorm IGTf 2 volume), mul_comm (eLpNorm IGTf 2 volume), ← mul_assoc, sq,
        ENNReal.mul_le_mul_right he nt] at this
  calc
    _ = ‖∫ x, conj (IGTf x) * carlesonRowSum t j f x‖ₑ := by
      rw [eLpNorm_two_eq_enorm_integral_mul_conj (bIGTf.memLp _)]; congr! 3 with x
      unfold IGTf
      rw [indicator_eq_indicator_one_mul, map_mul, conj_indicator, map_one, mul_mul_mul_comm,
        ← inter_indicator_mul, inter_self, mul_comm (carlesonRowSum ..), ← mul_assoc]
      simp_rw [Pi.one_apply, mul_one]; rfl
    _ = ‖∫ x, conj (F.indicator (adjointCarlesonRowSum t j IGTf) x) * f x‖ₑ := by
      rw [adjointCarlesonRowSum_adjoint bf bIGTf]; congr! 3 with x
      rw [indicator_eq_indicator_one_mul, map_mul, conj_indicator, map_one, mul_rotate, mul_assoc]
      congr 1
      by_cases hx : x ∈ F
      · simp [indicator_of_mem hx]
      · specialize h2f x
        rw [indicator_of_notMem hx, norm_le_zero_iff] at h2f
        rw [h2f, zero_mul]
    _ ≤ ∫⁻ x, ‖F.indicator (adjointCarlesonRowSum t j IGTf) x‖ₑ * ‖f x‖ₑ := by
      conv_rhs => enter [2, x]; rw [← RCLike.enorm_conj, ← enorm_mul]
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ eLpNorm (F.indicator (adjointCarlesonRowSum t j IGTf)) 2 * eLpNorm f 2 := by
      apply ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance
      · exact ((BoundedCompactSupport.finset_sum fun _ _ ↦ bIGTf.adjointCarlesonSum).indicator
          measurableSet_F).enorm.aestronglyMeasurable.aemeasurable
      · exact bf.enorm.aestronglyMeasurable.aemeasurable
    _ ≤ _ := by
      exact mul_le_mul_right' (indicator_row_bound hj bIGTf support_indicator_subset) _

open Classical in
lemma forest_operator_f_main (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    eLpNorm (fun x ↦ G.indicator (∑ u with u ∈ t, carlesonSum (t u) f ·) x) 2 volume ^ 2 ≤
    (2 ^ (304 * a ^ 3) * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume) ^ 2 := by
  have bf := bcs_of_measurable_of_le_indicator_f hf h2f
  let TR (j : ℕ) (x : X) := G.indicator ((rowSupport t j).indicator (carlesonRowSum t j f)) x
  have bcsTR (j : ℕ) : BoundedCompactSupport (TR j) :=
    ((BoundedCompactSupport.finset_sum fun _ _ ↦ bf.carlesonSum).indicator
      measurableSet_rowSupport).indicator measurableSet_G
  calc
    _ = eLpNorm (fun x ↦ G.indicator 1 x *
        ∑ u with u ∈ t, carlesonSum (t u) f x) 2 volume ^ 2 := by
      congr! 3 with x; rw [indicator_eq_indicator_one_mul]
    _ = eLpNorm (fun x ↦ G.indicator 1 x *
        ∑ j ∈ Finset.range (2 ^ n), carlesonRowSum t j f x) 2 volume ^ 2 := by
      congr! with x
      have dc : ({u | u ∈ t} : Finset _) =
          (Finset.range (2 ^ n)).biUnion (fun j ↦ {u | u ∈ rowDecomp t j}) := by
        rw [← Finset.toFinset_coe ({u | u ∈ t} : Finset _),
          ← Finset.toFinset_coe (Finset.biUnion ..), toFinset_inj]
        simp_rw [Finset.coe_biUnion, Finset.coe_range, mem_Iio, Finset.coe_filter, Finset.mem_univ,
          true_and]
        exact biUnion_rowDecomp.symm
      rw [dc, Finset.sum_biUnion]; swap
      · rw [Finset.coe_range]; intro j mj j' mj' hn
        simp_rw [← Finset.disjoint_coe, Finset.coe_filter, Finset.mem_univ, true_and]
        exact pairwiseDisjoint_rowDecomp mj mj' hn
      rfl
    _ = eLpNorm (fun x ↦ ∑ j ∈ Finset.range (2 ^ n), TR j x) 2 ^ 2 := by
      congr! 3 with x; rw [Finset.mul_sum]; congr! 2 with j mj
      unfold TR; nth_rw 1 [carlesonRowSum_rowSupport, ← indicator_eq_indicator_one_mul]
    _ ≤ ∑ j ∈ Finset.range (2 ^ n), eLpNorm (TR j) 2 ^ 2 +
        ∑ j ∈ Finset.range (2 ^ n), ∑ j' ∈ Finset.range (2 ^ n) with j ≠ j',
        ‖∫ x, TR j x * conj (TR j' x)‖ₑ := by
      convert BoundedCompactSupport.sq_eLpNorm_le_sums bcsTR
    _ = ∑ j ∈ Finset.range (2 ^ n), eLpNorm (TR j) 2 ^ 2 := by
      conv_rhs => rw [← add_zero (Finset.sum ..)]
      congr 1; refine Finset.sum_eq_zero fun j mj ↦ Finset.sum_eq_zero fun j' mj' ↦ ?_
      rw [enorm_eq_zero]; refine integral_eq_zero_of_ae (.of_forall fun x ↦ ?_)
      simp only [Finset.mem_filter, Finset.mem_range] at mj mj'
      have : rowSupport t j ∩ rowSupport t j' = ∅ :=
        (pairwiseDisjoint_rowSupport mj mj'.1 mj'.2).inter_eq
      simp_rw [TR, indicator_indicator, conj_indicator, ← inter_indicator_mul]
      rw [inter_inter_inter_comm, this, inter_empty, indicator_empty, Pi.zero_apply]
    _ ≤ ∑ j ∈ Finset.range (2 ^ n), eLpNorm (G.indicator (carlesonRowSum t j f) ·) 2 ^ 2 := by
      gcongr with j mj; refine eLpNorm_mono_enorm fun x ↦ ?_
      unfold TR
      rw [indicator_eq_indicator_one_mul, indicator_eq_indicator_one_mul (rowSupport t j),
        ← mul_assoc, mul_comm (G.indicator 1 x), mul_assoc, ← indicator_eq_indicator_one_mul]
      nth_rw 2 [← one_mul ‖_‖ₑ]; rw [enorm_mul]; gcongr
      by_cases hx : x ∈ rowSupport t j
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    _ ≤ ∑ j ∈ Finset.range (2 ^ n),
        (C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2) ^ 2 := by
      gcongr with j mj; rw [Finset.mem_range] at mj
      exact forest_operator_f_inner mj hf h2f
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        ← ENNReal.rpow_natCast, ← div_mul_cancel₀ (n : ℝ) (show ((2 : ℕ) : ℝ) ≠ 0 by norm_num),
        ENNReal.rpow_mul, ENNReal.rpow_natCast, ← mul_pow]
      congr 1; simp_rw [← mul_assoc]
      rw [C7_7_2_2_eq, ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_ofNat,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, Nat.cast_ofNat, add_sub_cancel]
      conv_lhs => enter [1, 1, 2]; norm_cast
      rw [ENNReal.rpow_natCast]

open Classical in
/-- The `f` side of Proposition 2.0.4. -/
lemma forest_operator_f (t : Forest X n)
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ ≤
    2 ^ (304 * a ^ 3) * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  calc
    _ ≤ _ := forest_operator_f_prelude hf h2f hg h2g
    _ ≤ _ := by
      rw [← mul_rotate, mul_assoc]; gcongr
      rw [← ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < (2 : ℕ) by norm_num),
        ENNReal.rpow_natCast, ENNReal.rpow_natCast]
      exact forest_operator_f_main hf h2f

end FinalProp

end TileStructure.Forest

/-! ## Proposition 2.0.4 -/

irreducible_def C2_0_4_base (a : ℕ) : ℝ≥0 := 2 ^ (470 * a ^ 3)

/-- The constant used in `forest_operator`.
Has value `2 ^ (470 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
irreducible_def C2_0_4 (a : ℕ) (q : ℝ) (n : ℕ) : ℝ≥0 := C2_0_4_base a * 2 ^ (-(q - 1) / q * n)

open scoped Classical in
theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f x‖ₑ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have g_part := 𝔉.forest_operator_g hf h2f hg h2g -- ^ (2 - 2 / q)
  have f_part := 𝔉.forest_operator_f hf h2f hg h2g -- ^ (2 / q - 1)
  rcases (q_le_two X).eq_or_lt with rfl | hq
  · rw [sub_self, ENNReal.rpow_zero, mul_one, C2_0_4, C2_0_4_base]
    rw [Forest.G2_0_4] at g_part; convert g_part using 6; ring
  have egpos : 0 < 2 - 2 / q := by
    rw [sub_pos]; nth_rw 2 [show 2 = (2 : ℝ) / 1 by norm_num]
    exact div_lt_div_of_pos_left zero_lt_two zero_lt_one (one_lt_q X)
  have efpos : 0 < 2 / q - 1 := by rwa [sub_pos, one_lt_div (zero_lt_one.trans (one_lt_q X))]
  rw [← ENNReal.rpow_le_rpow_iff egpos] at g_part
  rw [← ENNReal.rpow_le_rpow_iff efpos] at f_part
  have key := mul_le_mul' g_part f_part
  have esum : 2 - 2 / q + (2 / q - 1) = 1 := by ring
  rw [← ENNReal.rpow_add_of_nonneg _ _ egpos.le efpos.le, esum, ENNReal.rpow_one, mul_assoc,
    mul_assoc _ (eLpNorm f 2 volume), ENNReal.mul_rpow_of_nonneg _ _ egpos.le,
    ENNReal.mul_rpow_of_nonneg _ _ efpos.le, mul_mul_mul_comm,
    ← ENNReal.rpow_add_of_nonneg _ _ egpos.le efpos.le, esum, ENNReal.rpow_one, ← mul_assoc,
    ENNReal.mul_rpow_of_nonneg _ _ efpos.le, ← mul_assoc, ← ENNReal.rpow_mul,
    show 2⁻¹ * (2 / q - 1) = q⁻¹ - 2⁻¹ by ring] at key
  apply key.trans; gcongr
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ (470 * a ^ 3)) ^ (2 - 2 / q) * (2 ^ (-(n / 2 : ℝ))) ^ (2 - 2 / q) *
        (2 ^ (470 * a ^ 3)) ^ (2 / q - 1) := by
      rw [Forest.G2_0_4, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_rpow_of_ne_zero two_ne_zero]
      simp only [ENNReal.coe_ofNat]
      rw [ENNReal.mul_rpow_of_nonneg _ _ egpos.le]; gcongr <;> norm_num
    _ = _ := by
      rw [← mul_rotate, ← ENNReal.rpow_add_of_nonneg _ _ efpos.le egpos.le, add_comm, esum,
        ENNReal.rpow_one, ← ENNReal.rpow_mul, C2_0_4, C2_0_4_base, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_rpow_of_ne_zero two_ne_zero, neg_div,
        show -(n / 2) * (2 - 2 / q) = -(1 - 1 / q) * n by ring]
      congr; rw [sub_div, div_self (q_pos X).ne']

open scoped Classical in
/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function. -/
theorem forest_operator' {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A) (sA : A ⊆ G) :
    ∫⁻ x in A, ‖∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f x‖ₑ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * (volume A) ^ (1/2 : ℝ) := by
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  have bf := bcs_of_measurable_of_le_indicator_f hf h2f
  rw [← enorm_integral_starRingEnd_mul_eq_lintegral_enorm]; swap
  · exact (BoundedCompactSupport.finset_sum (fun i hi ↦ bf.carlesonSum.restrict)).integrable
  rw [← integral_indicator hA]
  simp_rw [indicator_mul_left, ← comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  have bAi (x : X) : ‖A.indicator (fun y ↦ (∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f y) /
      ‖∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f y‖) x‖ ≤ A.indicator 1 x := by
    rw [norm_indicator_eq_indicator_norm]; apply indicator_le_indicator
    rw [Complex.norm_div, norm_real, norm_norm, Pi.one_apply]
    rcases eq_or_ne ‖∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f x‖ 0 with hnorm | hnorm
    · rw [hnorm]; norm_num
    · rw [div_self hnorm]
  apply (forest_operator 𝔉 hf h2f ?_ fun x ↦ ?_).trans; rotate_left
  · refine Measurable.indicator ?_ hA
    suffices Measurable (∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f ·) by
      exact this.div (measurable_ofReal.comp this.norm)
    exact Finset.measurable_sum _ fun _ _ ↦ measurable_carlesonSum hf
  · exact (bAi _).trans (indicator_le_indicator_apply_of_subset sA (by simp))
  gcongr
  · simp only [sub_nonneg, inv_le_inv₀ zero_lt_two (q_pos X)]
    exact (q_mem_Ioc (X := X)).2
  · exact le_rfl
  calc
  _ ≤ eLpNorm (A.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    simp only [indicator, coe_algebraMap, Real.norm_eq_abs]
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
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A) (sA : A ⊆ G) :
    ∫⁻ x in A, ‖∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f x‖ₑ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    (volume F) ^ (1/2 : ℝ) * (volume A) ^ (1/2 : ℝ) := by
  apply (forest_operator' 𝔉 hf h2f hA sA).trans
  gcongr
  calc
  _ ≤ eLpNorm (F.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    exact (h2f x).trans (le_abs_self _)
  _ ≤ _ := by
    rw [eLpNorm_indicator_const measurableSet_F (by norm_num) (by norm_num)]
    simp
