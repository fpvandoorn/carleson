import Carleson.ForestOperator.AlmostOrthogonality

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


/-! ## Section 7.6 and Lemma 7.4.6 -/

variable (t u₁) in
/-- The definition `𝓙'` at the start of Section 7.6.
We use a different notation to distinguish it from the 𝓙' used in Section 7.5 -/
def 𝓙₆ : Set (Grid X) := 𝓙 (t u₁) ∩ Iic (𝓘 u₁) -- or {J | (J : Set X) ⊆ 𝓘 u₁}

/-- Part of Lemma 7.6.1. -/
-- Very similar to Lemma 7.5.1. Todo: simplify
lemma union_𝓙₆ (hu₁ : u₁ ∈ t) :
    ⋃ J ∈ 𝓙₆ t u₁, (J : Set X) = 𝓘 u₁ := by
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · refine iUnion₂_subset_iff.mpr <| fun _ hJ ↦ hJ.2.1
  · have existsCube : x ∈ ⋃ J ∈ 𝓙 (t u₁), (J : Set X) := by
      suffices (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙 (t u₁), (J : Set X) from this hx
      rw [biUnion_𝓙 (𝔖 := t u₁)]
      apply subset_iUnion_of_subset (𝓘 u₁)
      rfl
    simp only [mem_iUnion, exists_prop] at existsCube
    rcases existsCube with ⟨cube, cube_in_𝓙, xInCube⟩
    simp only [mem_iUnion, exists_prop]
    have notDisjoint := Set.not_disjoint_iff.mpr ⟨x, xInCube, hx⟩
    have cubeIn𝓙₀ : cube ∈ 𝓙₀ (t u₁) := mem_of_mem_inter_left cube_in_𝓙
    simp only [mem_setOf_eq] at cubeIn𝓙₀
    cases cubeIn𝓙₀ with
    | inl west =>
      refine ⟨cube, ?_, xInCube⟩
      unfold 𝓙₆
      rw [inter_def, mem_setOf_eq]
      refine ⟨cube_in_𝓙, ?_⟩
      simp only [mem_Iic, Grid.le_def]
      have smaller := calc s cube
        _ = -S := west
        _ ≤ s (𝓘 u₁) := (mem_Icc.mp (scale_mem_Icc (i := 𝓘 u₁))).left
      refine ⟨?_, smaller⟩
      cases GridStructure.fundamental_dyadic' smaller with
      | inl subset => exact subset
      | inr disjoint => exact False.elim (notDisjoint disjoint)
    | inr east =>
      obtain ⟨p, belongs⟩ := t.nonempty' hu₁
      by_contra! contr
      have white := calc (𝓘 p : Set X)
        _ ⊆ 𝓘 u₁ := if_descendant_then_subset t hu₁ belongs
        _ ⊆ cube := by
          apply subset_of_nmem_Iic_of_not_disjoint cube
          · have notIn : cube ∉ t.𝓙₆ u₁ := λ a => contr cube a xInCube
            rw [𝓙₆, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
            exact Or.resolve_left notIn (Set.not_not_mem.mpr cube_in_𝓙)
          · exact notDisjoint
        _ ⊆ ball (c cube) (4 * ↑D ^ s cube) := by
          exact Grid_subset_ball (i := cube)
        _ ⊆ ball (c cube) (100 * ↑D ^ (s cube + 1)) := by
          unfold ball
          intro y xy
          rw [mem_setOf_eq] at xy ⊢
          have numbers : 4 * (D : ℝ) ^ s cube < 100 * D ^ (s cube + 1) := by
            gcongr
            linarith
            exact one_lt_D (X := X)
            linarith
          exact gt_trans numbers xy
      have black : ¬↑(𝓘 p) ⊆ ball (c cube) (100 * ↑D ^ (s cube + 1)) := by
        refine east p belongs
      contradiction

/-- Part of Lemma 7.6.1. -/
lemma pairwiseDisjoint_𝓙₆ :
    (𝓙₆ t u₁).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  have ss : (𝓙 (t u₁) ∩ Iic (𝓘 u₁)) ⊆ 𝓙 (t u₁) := inter_subset_left
  exact PairwiseDisjoint.subset (pairwiseDisjoint_𝓙 (𝔖 := t u₁)) ss


/-- The constant used in `thin_scale_impact`. This is denoted `s₁` in the proof of Lemma 7.6.3.
Has value `Z * n / (202 * a ^ 3) - 2` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_3 (a n : ℕ) : ℝ := Z * n / (202 * a ^ 3) - 2

-- if needed
lemma C7_6_3_pos [ProofData a q K σ₁ σ₂ F G] (h : 1 ≤ n) : 0 < C7_6_3 a n := by
  sorry

/-- Lemma 7.6.3. -/
lemma thin_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) :
    𝔰 p ≤ s J - C7_6_3 a n := by
  sorry

/-- The constant used in `square_function_count`. -/
irreducible_def C7_6_4 (a : ℕ) (s : ℤ) : ℝ≥0 := 2 ^ (14 * (a : ℝ) + 1) * (8 * D ^ (- s)) ^ κ

set_option linter.flexible false in -- Addressing the linter makes the code less readable.
/-- Lemma 7.6.4. -/
lemma square_function_count (hJ : J ∈ 𝓙₆ t u₁) (s' : ℤ) :
    ⨍⁻ x in J, (∑ I ∈ {I : Grid X | s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
    ¬ Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)) },
    (ball (c I) (8 * D ^ s I)).indicator 1 x) ^ 2 ∂volume ≤ C7_6_4 a s' := by
  cases' lt_or_ge (↑S + s J) s' with hs' hs'
  · suffices ({I : Grid X | s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
        ¬ Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)) } : Finset (Grid X)) = ∅ by
      rw [this]
      simp
    simp only [Nat.cast_pow, Nat.cast_ofNat, Finset.filter_eq_empty_iff, Finset.mem_univ,
      not_and, Decidable.not_not, true_implies]
    intros I hI
    have : -S ≤ s I := (range_s_subset ⟨I, rfl⟩).1
    linarith
  have : NeZero (volume.restrict (J : Set X) univ) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact ((measure_ball_pos _ _ (by simp; positivity)).trans_le
      (measure_mono (μ := volume) (ball_subset_Grid (i := J)))).ne'⟩
  have : IsFiniteMeasure (volume.restrict (J : Set X)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact volume_coeGrid_lt_top⟩
  let 𝒟 (s₀ x) : Set (Grid X) := { I | x ∈ ball (c I) (8 * D ^ s I) ∧ s I = s₀ }
  let supp : Set X := { x ∈ J | EMetric.infEdist x Jᶜ ≤ 8 * (D ^ (s J - s')) }
  have hsupp : supp ⊆ J := fun x hx ↦ hx.1
  have vsupp : volume.real supp ≤ 2 * (↑8 * ↑D ^ (-s')) ^ κ * volume.real (J : Set X) := by
    simp only [supp, sub_eq_neg_add, ENNReal.zpow_add (x := D) (by simp) (by finiteness),
      ← mul_assoc]
    convert small_boundary (i := J) (t := 8 * ↑D ^ (-s')) ?_
    · simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      rw [ENNReal.coe_zpow (by simp)]
      norm_num
    · rw [show (8 : ℝ≥0) = 2 ^ 3 by norm_num]
      simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultA,
        ← zpow_neg, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (show (2 : ℝ≥0) ≠ 0 by norm_num)]
      -- #adaptation note(2024-11-02): this line was `gcongr`
      -- This was probably broken by mathlib4#19626 and friends, see
      -- https://leanprover.zulipchat.com/#narrow/channel/428973-nightly-testing/topic/.2319314.20adaptations.20for.20nightly-2024-11-20
      -- for details.
      refine zpow_le_zpow_right₀ ?ha ?hmn
      · norm_num
      · simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_neg,
        le_add_neg_iff_add_le, ← mul_add]
        refine (Int.mul_nonpos_of_nonneg_of_nonpos (by simp) ?_).trans (by norm_num)
        rwa [ge_iff_le, ← sub_nonpos, sub_eq_neg_add, neg_add] at hs'
  have vsupp : volume supp ≤ ENNReal.ofReal (2 * (↑8 * ↑D ^ (-s')) ^ κ) * volume (J : Set X) := by
    apply ENNReal.ofReal_le_ofReal at vsupp
    rwa [Measure.real, Measure.real, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (volume_coeGrid_lt_top.ne),
      ENNReal.ofReal_toReal ((measure_mono hsupp).trans_lt volume_coeGrid_lt_top).ne] at vsupp
  have est₁ (s₀ x) : (𝒟 s₀ x).toFinset.card ≤ (defaultA a) ^ 7 := by
    apply Nat.cast_le (α := ℝ).mp
    have : 0 < volume.real (ball x (9 * ↑D ^ s₀)) :=
      ENNReal.toReal_pos (measure_ball_pos _ _ (by simp; positivity)).ne' (by finiteness)
    refine le_of_mul_le_mul_right (a := volume.real (ball x (9 * D ^ s₀))) ?_ this
    transitivity (defaultA a) ^ 7 * ∑ I ∈ 𝒟 s₀ x, volume.real (ball (c I) (D ^ s I / 4))
    · rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun I hI ↦ ?_
      simp only [mem_toFinset] at hI
      apply le_trans _ (measure_ball_le_pow_two (μ := volume) (x := c I) (r := D ^ s I / 4))
      refine measureReal_mono ?_ (by finiteness)
      apply ball_subset_ball'
      refine (add_le_add le_rfl hI.1.le).trans ?_
      rw [div_eq_mul_one_div, mul_comm _ (1 / 4), hI.2, ← add_mul, ← mul_assoc]
      gcongr
      linarith
    have disj : (𝒟 s₀ x).PairwiseDisjoint fun I : Grid X ↦ ball (c I) (D ^ s I / 4) := by
      intros I₁ hI₁ I₂ hI₂ e
      exact disjoint_of_subset ball_subset_Grid ball_subset_Grid
        ((eq_or_disjoint (hI₁.2.trans hI₂.2.symm)).resolve_left e)
    rw [← measureReal_biUnion_finset (by simpa only [coe_toFinset] using disj)
      (fun _ _ ↦ measurableSet_ball) (by finiteness)]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    · finiteness
    · simp only [mem_toFinset, iUnion_subset_iff]
      intro I hI
      apply ball_subset_ball'
      rw [dist_comm, div_eq_mul_one_div, mul_comm]
      refine (add_le_add le_rfl hI.1.le).trans ?_
      rw [← add_mul, hI.2]
      gcongr
      linarith
  simp_rw [← Nat.cast_le (α := ℝ≥0∞)] at est₁
  have est₂ (x) (hx : x ∈ J) : (∑ I ∈ {I : Grid X | s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
      ¬ Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)) },
      (ball (c I) (8 * D ^ s I)).indicator (1 : X → ℝ≥0∞) x) ≤
      if x ∈ supp then (defaultA a) ^ 7 else 0 := by
    split_ifs with hx'
    · rw [Finset.sum_indicator_eq_sum_filter]
      simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
      refine le_trans ?_ (est₁ (s J - s') x)
      gcongr
      intro I
      simp only [Nat.cast_pow, Nat.cast_ofNat, mem_ball, Finset.mem_filter,
        Finset.mem_univ, true_and, mem_toFinset, 𝒟]
      exact fun H ↦ ⟨H.2, H.1.1⟩
    · have (I : Grid X) : ball (c I) (8 * D ^ s I) = EMetric.ball (c I) (8 * D ^ s I) := by
        trans EMetric.ball (c I) (show ℝ≥0 from ⟨8 * D ^ s I, by positivity⟩)
        · rw [emetric_ball_nnreal]; rfl
        · congr!
          simp only [ENNReal.coe_nnreal_eq, ← Real.rpow_intCast]
          erw [ENNReal.ofReal_mul (by norm_num)]
          rw [← ENNReal.ofReal_rpow_of_pos (by simp), ENNReal.ofReal_natCast]
          norm_num
      simp_rw [this]
      simp only [CharP.cast_eq_zero, nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_filter,
        Finset.mem_univ, true_and, indicator_apply_eq_zero, EMetric.mem_ball, Pi.one_apply,
        one_ne_zero, imp_false, not_lt, and_imp]
      intro I e hI₁ _
      simp only [Grid.mem_def, mem_setOf_eq, not_and, not_le, supp, ← e] at hx'
      exact (hx' hx).le.trans (iInf₂_le (c I)
        fun h ↦ Set.disjoint_iff.mp hI₁ ⟨Grid.c_mem_Grid, hJ.2.1 h⟩)
  have est₂' (x) (hx : x ∈ J) : _ ≤ supp.indicator (fun _ ↦ (↑(defaultA a ^ 7 : ℕ) : ℝ≥0∞) ^ 2) x :=
    (pow_left_mono 2 <| est₂ x hx).trans (by simp [Set.indicator_apply])
  refine (setLaverage_mono' coeGrid_measurable est₂').trans ?_
  rw [laverage_eq, ENNReal.div_le_iff (NeZero.ne _) (by finiteness)]
  refine (lintegral_indicator_const_le _ _).trans ?_
  rw [Measure.restrict_apply' coeGrid_measurable, Measure.restrict_apply_univ,
    Set.inter_eq_left.mpr (fun x hx ↦ hx.1)]
  refine ((ENNReal.mul_le_mul_left (by simp) (ne_of_beq_false rfl).symm).mpr vsupp).trans ?_
  rw [← mul_assoc, ENNReal.ofReal, ← ENNReal.coe_natCast, ← ENNReal.coe_pow, ← ENNReal.coe_mul]
  gcongr
  rw [Real.toNNReal_mul (by positivity), Real.toNNReal_rpow_of_nonneg (by positivity),
    Real.toNNReal_mul (by positivity), ← Real.rpow_intCast,
    Real.toNNReal_rpow_of_nonneg (by positivity), NNReal.toNNReal_coe_nat]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.toNNReal_ofNat, Int.cast_neg, ← pow_mul]
  rw [← mul_assoc, ← pow_succ, C7_6_4, ← NNReal.rpow_natCast, ← NNReal.rpow_intCast, Int.cast_neg]
  congr!
  simp [mul_assoc, mul_comm (G := ℝ) 14]

/-- The constant used in `bound_for_tree_projection`.
Has value `2 ^ (118 * a ^ 3 - 100 / (202 * a) * Z * n * κ)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_2 (a n : ℕ) : ℝ≥0 := 2 ^ (118 * (a : ℝ) ^ 3 - 100 / (202 * a) * Z * n * κ)

/-- Lemma 7.6.2. Todo: add needed hypothesis to LaTeX -/
lemma bound_for_tree_projection (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume ≤
    C7_6_2 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) · |>.toReal)) 2 volume := by
  sorry

/-- The constant used in `correlation_near_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_6 (a n : ℕ) : ℝ≥0 := 2 ^ (222 * (a : ℝ) ^ 3 - Z * n * 2 ^ (-10 * (a : ℝ)))

/-- Lemma 7.4.6 -/
lemma correlation_near_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_6 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

end TileStructure.Forest
