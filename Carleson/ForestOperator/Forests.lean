import Carleson.ForestOperator.LargeSeparation
import Carleson.ForestOperator.RemainingTiles
import Carleson.ToMathlib.MeasureTheory.Integral.SetIntegral
import Carleson.ToMathlib.Order.Chain

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

/-! ## Lemmas 7.4.4 -/

/-- The constant used in `correlation_separated_trees`.
Has value `2 ^ (550 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_4 (a n : ℕ) : ℝ≥0 := 2 ^ (550 * (a : ℝ) ^ 3 - 3 * n)

lemma correlation_separated_trees_of_subset (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-- Lemma 7.4.4. -/
lemma correlation_separated_trees (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-! ## Section 7.7 -/

def rowDecomp_zornset (t : Forest X n) (s : Set (𝔓 X)) :=
  { x : Set (𝔓 X)
    | x ⊆ s
    ∧ x.PairwiseDisjoint t
    ∧ ∀ u ∈ x, Maximal (· ∈ ((fun x => 𝓘 x : 𝔓 X → Set X) '' s)) (𝓘 u : Set X) }

lemma mem_rowDecomp_zornset_iff (t : Forest X n) (s s' : Set (𝔓 X)) :
    s' ∈ rowDecomp_zornset t s ↔ (s' ⊆ s ∧ s'.PairwiseDisjoint t ∧
      ∀ u ∈ s', Maximal (· ∈ (fun x => 𝓘 x : 𝔓 X → Set X) '' s) (𝓘 u : Set X)) := by
  rw [rowDecomp_zornset,mem_setOf]

lemma rowDecomp_zornset_chain_Union_bound (s' : Set (𝔓 X)) (c : Set (Set (𝔓 X))) (hc : c ⊆ t.rowDecomp_zornset s')
    (hc_chain : IsChain (· ⊆ ·) c) :
    (⋃ s ∈ c,s) ∈ t.rowDecomp_zornset s' ∧ ∀ s ∈ c, s ⊆ ⋃ s'' ∈ c, s'' := by
  have hc' := fun a (h : a ∈ c) => hc h
  simp_rw [mem_rowDecomp_zornset_iff] at hc ⊢
  repeat' constructor
  · simp_rw [iUnion_subset_iff]
    intro s hs
    specialize hc' s hs
    exact hc'.left
  · apply hc_chain.pairwiseDisjoint_iUnion₂
    exact fun s hs => (hc' s hs).right.left
  · simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
    exact fun u s hs => (hc' s hs).right.right u
  · exact fun s a_1 ↦ subset_iUnion₂_of_subset s a_1 fun ⦃a_2⦄ a ↦ a

def rowDecomp_𝔘 (t : Forest X n) (j : ℕ) : Set (𝔓 X) :=
  (zorn_subset
  (rowDecomp_zornset t (t \ ⋃ i < j, rowDecomp_𝔘 t i))
  (fun c hc hc_chain => ⟨⋃ s ∈ c, s, rowDecomp_zornset_chain_Union_bound _ c hc hc_chain⟩
  )).choose

lemma rowDecomp_𝔘_def (t : Forest X n) (j : ℕ) :
    Maximal (fun x ↦ x ∈ rowDecomp_zornset t (t \ ⋃ i < j, rowDecomp_𝔘 t i)) (rowDecomp_𝔘 t j) := by
  rw [rowDecomp_𝔘]
  apply Exists.choose_spec

lemma rowDecomp_𝔘_mem_zornset (t : Forest X n) (j : ℕ) :
    t.rowDecomp_𝔘 j ∈ rowDecomp_zornset t (t \ ⋃ i < j, rowDecomp_𝔘 t i) :=
  (rowDecomp_𝔘_def t j).prop

lemma rowDecomp_𝔘_subset (t : Forest X n) (j : ℕ) :
    t.rowDecomp_𝔘 j ⊆ t \ ⋃ i < j, rowDecomp_𝔘 t i := by
  have := (rowDecomp_𝔘_def t j).prop
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.left

lemma rowDecomp_𝔘_pairwiseDisjoint (t : Forest X n) (j : ℕ) :
    (t.rowDecomp_𝔘 j).PairwiseDisjoint t := by
  have := (rowDecomp_𝔘_def t j).prop
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.right.left

lemma mem_rowDecomp_𝔘_maximal (t : Forest X n) (j : ℕ) :
    ∀ x ∈ (t.rowDecomp_𝔘 j), Maximal (· ∈ (fun x => 𝓘 x : 𝔓 X → Set X) '' (t \ ⋃ i < j, rowDecomp_𝔘 t i)) (𝓘 x : Set X) := by
  have := (rowDecomp_𝔘_def t j).prop
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.right.right

-- maybe not important?
lemma rowDecomp_𝔘_maximal (t : Forest X n) (j : ℕ) :
    ∀ s ∈ rowDecomp_zornset t (t \ ⋃ i < j, rowDecomp_𝔘 t i),
    rowDecomp_𝔘 t j ⊆ s → s ⊆ rowDecomp_𝔘 t j :=
  fun _ => (rowDecomp_𝔘_def t j).le_of_ge

lemma rowDecomp_𝔘_subset_tree (t : Forest X n) (j : ℕ) :
  rowDecomp_𝔘 t j ⊆ t := fun x hx => ((mem_diff x).mp (rowDecomp_𝔘_subset t j hx)).left

lemma rowDecomp_𝔘_stackSize_le' (t : Forest X n) (j : ℕ) :
    ∀ {x}, stackSize (rowDecomp_𝔘 t j) x ≤ 2 ^ n := by
  intro x
  trans
  · exact stackSize_mono (rowDecomp_𝔘_subset_tree t j)
  · exact t.stackSize_le'

-- #print Row
/-- The row-decomposition of a tree, defined in the proof of Lemma 7.7.1.
The indexing is off-by-one compared to the blueprint. -/
def rowDecomp (t : Forest X n) (j : ℕ) : Row X n where
  𝔘 := rowDecomp_𝔘 t j
  𝔗 := t
  nonempty' hu := t.nonempty (rowDecomp_𝔘_subset_tree t j hu)
  ordConnected' hu:= t.ordConnected' (rowDecomp_𝔘_subset_tree t j hu)
  𝓘_ne_𝓘' hu := t.𝓘_ne_𝓘' (rowDecomp_𝔘_subset_tree t j hu)
  smul_four_le' hu := t.smul_four_le' (rowDecomp_𝔘_subset_tree t j hu)
  stackSize_le' := rowDecomp_𝔘_stackSize_le' t j
  dens₁_𝔗_le' hu := t.dens₁_𝔗_le' (rowDecomp_𝔘_subset_tree t j hu)
  lt_dist' hu hu' := t.lt_dist' (rowDecomp_𝔘_subset_tree t j hu) (rowDecomp_𝔘_subset_tree t j hu')
  ball_subset' hu := t.ball_subset' (rowDecomp_𝔘_subset_tree t j hu)
  pairwiseDisjoint' := rowDecomp_𝔘_pairwiseDisjoint t j

lemma rowDecomp_𝔘_eq (t : Forest X n) (j : ℕ) :
  (t.rowDecomp j).𝔘 = rowDecomp_𝔘 t j := rfl

lemma Set.Finite.exists_maximal_and_mem {α : Type*} {s : Set (Set α)} (hs : s.Finite)
    {b : Set α} (hb : b ∈ s) {x : α} (hx : x ∈ b) : ∃ m, Maximal (· ∈ s) m ∧ x ∈ m :=
  (hs.inter_of_left _ |>.exists_le_maximal (s := s ∩ {y' | x ∈ y'}) ⟨hb,hx⟩).elim
    fun m ⟨_,hm⟩ =>
      ⟨m,⟨⟨hm.prop.left,fun _ hm' hle => hm.le_of_ge ⟨hm',hle hm.prop.right⟩ hle⟩,hm.prop.right⟩⟩

lemma remainder_stackSize_le (t : Forest X n) (j : ℕ) :
  ∀ x:X, stackSize (t \ ⋃ i < j, t.rowDecomp i : Set _) x ≤ 2 ^ n - j := by
    intro x
    induction j with
    | zero =>
      simp only [not_lt_zero', iUnion_of_empty, iUnion_empty, diff_empty, tsub_zero]
      exact t.stackSize_le'
    | succ j hinduct =>
      if h: ∃ 𝔲 ∈ (t \ ⋃ i < j + 1, t.rowDecomp i : Set _), x ∈ 𝓘 𝔲 then
        have : ∃ s, Maximal (· ∈ ((𝓘 · : 𝔓 X → Set X) '' (t \ ⋃ i < j, t.rowDecomp i : Set _))) s ∧ x ∈ (s:Set X) := by
          obtain ⟨𝔲,h𝔲⟩ := h
          rw [biUnion_lt_succ,← diff_diff,mem_diff] at h𝔲
          apply Set.Finite.exists_maximal_and_mem (Set.Finite.image _ (toFinite _))
            ⟨𝔲,h𝔲.left.left,rfl⟩ h𝔲.right
        obtain ⟨𝔲,h𝔲⟩ := h
        simp only [biUnion_lt_succ, ← diff_diff] at h𝔲 ⊢
        rw [stackSize_sdiff_eq,← Nat.sub_sub]
        gcongr
        dsimp [stackSize]
        suffices ∃ 𝔲' ∈ (t.rowDecomp j).𝔘, x ∈ (𝓘 𝔲' : Set _) by
          obtain ⟨𝔲',h𝔲'⟩ := this
          rw [← Finset.sum_erase_add _ (a := 𝔲')]
          simp only [exists_prop, not_exists, not_and, ge_iff_le]
          rw [indicator_apply,if_pos h𝔲'.right,Pi.one_apply]
          simp only [le_add_iff_nonneg_left, zero_le]
          simp only [Finset.mem_filter, Finset.mem_univ,
            true_and,mem_inter_iff]
          exact ⟨t.rowDecomp_𝔘_subset j h𝔲'.left,h𝔲'.left⟩
        rw [mem_diff] at h𝔲
        apply this.elim
        intro _ ⟨hmax,hz⟩
        obtain ⟨u,hu,rfl⟩ := hmax.prop
        use u
        rw [mem_𝔘]
        refine ⟨?_,hz⟩
        apply (t.rowDecomp_𝔘_def j).mem_of_prop_insert
        rw [mem_rowDecomp_zornset_iff t]
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
          sorry
        refine ⟨?_, mem_rowDecomp_𝔘_maximal t j⟩
        exact hmax
      else
        dsimp [stackSize]
        push_neg at h
        rw [Finset.sum_congr rfl (g := fun _ => 0) (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, indicator_apply_eq_zero,
            Pi.one_apply, one_ne_zero] at h ⊢
          exact h)]
        rw [Finset.sum_eq_zero (fun _ _ => rfl)]
        exact zero_le _

lemma empty_of_forall_stackSize_zero (s : Set (𝔓 X)) :
  (∀ x, stackSize s x = 0) → s = ∅ := by
  intro h
  dsimp [stackSize] at h
  simp only [Finset.sum_eq_zero_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false] at h
  ext 𝔲
  simp only [mem_empty_iff_false, iff_false]
  obtain ⟨x,hx⟩ := (𝓘 𝔲).nonempty
  exact fun h𝔲 => h x 𝔲 h𝔲 hx


/-- Part of Lemma 7.7.1 -/
@[simp]
lemma biUnion_rowDecomp : ⋃ j < 2 ^ n, t.rowDecomp j = (t : Set (𝔓 X)) := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff,rowDecomp_𝔘_eq]
    exact fun i _ => rowDecomp_𝔘_subset_tree t i
  · rw [← diff_eq_empty]
    apply empty_of_forall_stackSize_zero
    intro x
    apply Nat.eq_zero_of_le_zero ((Nat.sub_self _).symm ▸ remainder_stackSize_le t (2 ^ n) x)

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

/-- The constant used in `row_bound`.
Has value `2 ^ (156 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_1 (a n : ℕ) : ℝ≥0 := 2 ^ (156 * (a : ℝ) ^ 3 - n / 2)

/-- The constant used in `indicator_row_bound`.
Has value `2 ^ (257 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_2 (a n : ℕ) : ℝ≥0 := 2 ^ (257 * (a : ℝ) ^ 3 - n / 2)

/-- Part of Lemma 7.7.2. -/
lemma row_bound (hj : j < 2 ^ n) (hf : BoundedCompactSupport f) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) f) 2 volume ≤
    C7_7_2_1 a n * eLpNorm f 2 volume := by
  sorry

/-- Part of Lemma 7.7.2. -/
lemma indicator_row_bound (hj : j < 2 ^ n) (hf : BoundedCompactSupport f) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, F.indicator <| adjointCarlesonSum (t u) f) 2 volume ≤
    C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  sorry

/-- The constant used in `row_correlation`.
Has value `2 ^ (862 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_3 (a n : ℕ) : ℝ≥0 := 2 ^ (862 * (a : ℝ) ^ 3 - 2 * n)

/-- Lemma 7.7.3. -/
lemma row_correlation (hjj' : j < j') (hj' : j' < 2 ^ n)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) f₁ x) *
    (∑ u ∈ {p | p ∈ rowDecomp t j'}, adjointCarlesonSum (t u) f₂ x)‖₊ ≤
    C7_7_3 a n * eLpNorm f₁ 2 volume * eLpNorm f₂ 2 volume := by
  sorry

variable (t) in
/-- The definition of `Eⱼ` defined above Lemma 7.7.4. -/
def rowSupport (j : ℕ) : Set X := ⋃ (u ∈ rowDecomp t j) (p ∈ t u), E p

/-- Lemma 7.7.4 -/
lemma pairwiseDisjoint_rowSupport :
    (Iio (2 ^ n)).PairwiseDisjoint (rowSupport t) := by
  sorry

end TileStructure.Forest

/-! ## Proposition 2.0.4 -/

irreducible_def C2_0_4_base (a : ℝ) : ℝ≥0 := 2 ^ (432 * a ^ 3)

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := C2_0_4_base a * 2 ^ (- (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function. -/
theorem forest_operator' {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * (volume A) ^ (1/2 : ℝ) := by
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  rw [← ennnorm_integral_starRingEnd_mul_eq_lintegral_ennnorm]; swap
  · apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.finset_sum (fun i hi ↦ ?_)
    apply BoundedCompactSupport.carlesonSum
    have : BoundedCompactSupport (F.indicator 1 : X → ℝ) := by
      apply BoundedCompactSupport.indicator_of_isBounded_range _ stronglyMeasurable_one _
        measurableSet_F
      · exact isBounded_range_iff_forall_norm_le.2 ⟨1, fun x ↦ by simp⟩
      · exact isBounded_F
    apply BoundedCompactSupport.mono this hf.stronglyMeasurable h2f
  rw [← integral_indicator hA]
  simp_rw [indicator_mul_left, ← comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  apply (forest_operator 𝔉 hf h2f ?_ ?_).trans; rotate_left
  · apply Measurable.indicator _ hA
    fun_prop
  · apply h'A.subset support_indicator_subset
  gcongr
  · have := (q_mem_Ioc (X := X)).2
    simp only [sub_nonneg, ge_iff_le, inv_le_inv₀ zero_lt_two (q_pos X)]
    exact (q_mem_Ioc (X := X)).2
  · exact le_rfl
  calc
  _ ≤ eLpNorm (A.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    simp only [indicator, norm_eq_abs, coe_algebraMap, Pi.one_apply, Real.norm_eq_abs]
    split_ifs
    · have A (x : ℝ) : x / x ≤ 1 := by
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · simp [hx]
      simpa using A _
    · simp
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact hA
    · norm_num
    · norm_num

/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function, and with the upper bound in terms
of `volume F` and `volume G`.  -/
theorem forest_operator_le_volume {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    (volume F) ^ (1/2 : ℝ) * (volume A) ^ (1/2 : ℝ) := by
  apply (forest_operator' 𝔉 hf h2f hA h'A).trans
  gcongr
  calc
  _ ≤ eLpNorm (F.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    apply (h2f x).trans (le_abs_self _)
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact measurableSet_F
    · norm_num
    · norm_num
