import Carleson.Calculations
import Carleson.ForestOperator.AlmostOrthogonality

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


/-! ## Section 7.6 and Lemma 7.4.6 -/

variable (t u₁) in
/-- The definition `𝓙'` at the start of Section 7.6.
We use a different notation to distinguish it from the 𝓙' used in Section 7.5 -/
def 𝓙₆ : Set (Grid X) := 𝓙 (t u₁) ∩ Iic (𝓘 u₁)

/-- Part of Lemma 7.6.1. -/
-- Very similar to Lemma 7.5.1. Todo: simplify
lemma union_𝓙₆ (hu₁ : u₁ ∈ t) : ⋃ J ∈ 𝓙₆ t u₁, (J : Set X) = 𝓘 u₁ := by
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
        _ ⊆ 𝓘 u₁ := (𝓘_le_𝓘 t hu₁ belongs).1
        _ ⊆ cube := by
          apply subset_of_notMem_Iic_of_not_disjoint cube
          · have notIn : cube ∉ t.𝓙₆ u₁ := fun a ↦ contr cube a xInCube
            rw [𝓙₆, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
            exact Or.resolve_left notIn (Set.not_notMem.mpr cube_in_𝓙)
          · exact notDisjoint
        _ ⊆ ball (c cube) (4 * ↑D ^ s cube) := by
          exact Grid_subset_ball (i := cube)
        _ ⊆ ball (c cube) (100 * ↑D ^ (s cube + 1)) := by
          unfold ball
          intro y xy
          rw [mem_setOf_eq] at xy ⊢
          have numbers : 4 * (D : ℝ) ^ s cube < 100 * D ^ (s cube + 1) := by
            gcongr
            · linarith
            · exact one_lt_realD X
            · linarith
          exact gt_trans numbers xy
      have black : ¬↑(𝓘 p) ⊆ ball (c cube) (100 * ↑D ^ (s cube + 1)) := by
        refine east p belongs
      contradiction

/-- Part of Lemma 7.6.1. -/
lemma pairwiseDisjoint_𝓙₆ : (𝓙₆ t u₁).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  have ss : (𝓙 (t u₁) ∩ Iic (𝓘 u₁)) ⊆ 𝓙 (t u₁) := inter_subset_left
  exact PairwiseDisjoint.subset (pairwiseDisjoint_𝓙 (𝔖 := t u₁)) ss

/-- The constant used in `thin_scale_impact`. This is denoted `s₁` in the proof of Lemma 7.6.3.
Has value `Z * n / (202 * a ^ 3) - 2` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_3 (a n : ℕ) : ℝ := Z * n / ((2 * 𝕔 + 2) * a ^ 3) - 2

lemma nonneg_C7_6_3_add_two : 0 ≤ C7_6_3 a n + 2 := by
  simp_rw [C7_6_3, sub_add_cancel]; positivity

/-- Some preliminary relations for Lemma 7.6.3. -/
lemma thin_scale_impact_prelims (hu₁ : u₁ ∈ t) (hJ : J ∈ 𝓙₆ t u₁)
    (hd : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)))
    (h : s J - C7_6_3 a n < 𝔰 p) :
    dist (𝔠 p) (c J) < 16 * D ^ (𝔰 p + C7_6_3 a n + 2) ∧
    ∃ J', J < J' ∧ s J' = s J + 1 ∧
      ∃ p ∈ t u₁, ↑(𝓘 p) ⊆ ball (c J') (100 * D ^ (s J' + 1)) := by
  have b1 : dist (𝔠 p) (c J) < 16 * D ^ (𝔰 p + C7_6_3 a n + 2) := by
    calc
      _ < 8 * (D : ℝ) ^ 𝔰 p + 8 * D ^ s J := dist_lt_of_not_disjoint_ball hd
      _ ≤ 8 * D ^ (𝔰 p + C7_6_3 a n + 2) + 8 * D ^ (𝔰 p + C7_6_3 a n + 2) := by
        simp_rw [← Real.rpow_intCast]; gcongr (8 : ℝ) * D ^ ?_ + 8 * D ^ ?_
        · exact one_le_realD _
        · rw [add_assoc, le_add_iff_nonneg_right]; exact nonneg_C7_6_3_add_two
        · exact one_le_realD _
        · linarith
      _ ≤ _ := by rw [← two_mul, ← mul_assoc]; norm_num
  obtain ⟨q, mq⟩ := t.nonempty hu₁
  have qlt : 𝓘 q < 𝓘 u₁ := lt_of_le_of_ne (t.smul_four_le hu₁ mq).1 (t.𝓘_ne_𝓘 hu₁ mq)
  have u₁nm : 𝓘 u₁ ∉ 𝓙₆ t u₁ := by
    simp_rw [𝓙₆, mem_inter_iff, mem_Iic, le_rfl, and_true, 𝓙, mem_setOf, Maximal, not_and_or]; left
    rw [𝓙₀, mem_setOf]; push Not; rw [Grid.lt_def] at qlt
    refine ⟨(scale_mem_Icc.1.trans_lt qlt.2).ne',
      ⟨q, mq, qlt.1.trans <| Grid_subset_ball.trans <| ball_subset_ball ?_⟩⟩
    change 4 * (D : ℝ) ^ (𝔰 u₁) ≤ 100 * D ^ (𝔰 u₁ + 1); gcongr
    exacts [by norm_num, one_le_realD _, by lia]
  have Jlt : J < 𝓘 u₁ := by apply lt_of_le_of_ne hJ.2; by_contra hh; subst hh; exact u₁nm hJ
  rw [Grid.lt_def] at Jlt; obtain ⟨J', lJ', sJ'⟩ := Grid.exists_scale_succ Jlt.2
  replace lJ' : J < J' := Grid.lt_def.mpr ⟨lJ'.1, by lia⟩
  have J'nm : J' ∉ 𝓙₀ (t u₁) := by
    by_contra hh; apply absurd hJ.1.2; push Not; use J', hh, lJ'.le, not_le_of_gt lJ'
  rw [𝓙₀, mem_setOf] at J'nm; push Not at J'nm; obtain ⟨p', mp', sp'⟩ := J'nm.2
  exact ⟨b1, ⟨J', lJ', sJ', ⟨p', mp', sp'⟩⟩⟩

/-- The key relation of Lemma 7.6.3, which will eventually be shown to lead to a contradiction. -/
lemma thin_scale_impact_key (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁)
    (hd : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)))
    (h : s J - C7_6_3 a n < 𝔰 p) :
    (2 : ℝ) ^ (Z * (n + 1) - 1) <
    2 ^ (a * (𝕔 * a ^ 2 * (C7_6_3 a n + 2 + 1) + 9)) * 2 ^ ((Z : ℝ) * n / 2) := by
  obtain ⟨b1, ⟨J', lJ', sJ', ⟨p', mp', sp'⟩⟩⟩ := thin_scale_impact_prelims hu₁ hJ hd h
  have bZn : 4 ≤ Z * (n + 1) := by
    rw [← mul_one 4]; gcongr
    · exact four_le_Z (X := X)
    · exact Nat.le_add_left ..
  calc
    _ ≤ (2 : ℝ) ^ (Z * (n + 1)) - 4 := by
      nth_rw 2 [← Nat.sub_add_cancel (show 1 ≤ Z * (n + 1) by lia)]
      rw [pow_succ, mul_two, add_sub_assoc, ← neg_add_le_iff_le_add, neg_add_cancel, sub_nonneg,
        show (4 : ℝ) = 2 ^ 2 by norm_num]
      apply pow_le_pow_right₀ one_le_two; lia
    _ < dist_(p') (𝒬 u₁) (𝒬 u₂) := by
      refine (sub_lt_sub (t.lt_dist hu₂ hu₁ hu.symm mp' ((t.𝓘_le_𝓘 hu₁ mp').trans h2u))
        (t.dist_lt_four hu₁ mp')).trans_le ((le_abs_self _).trans ?_)
      simp_rw [dist_comm, abs_sub_comm]; exact abs_dist_sub_le ..
    _ ≤ dist_{𝔠 p, 128 * D ^ (𝔰 p + C7_6_3 a n + 2)} (𝒬 u₁) (𝒬 u₂) := by
      refine cdist_mono (ball_subset_Grid.trans sp' |>.trans (ball_subset_ball' ?_))
      calc
        _ ≤ (100 : ℝ) * D ^ (s J' + 1) + dist (c J') (c J) + dist (𝔠 p) (c J) := by
          rw [add_assoc]; gcongr; exact dist_triangle_right ..
        _ ≤ (100 : ℝ) * D ^ (s J' + 1) + 4 * D ^ s J' + 16 * D ^ (𝔰 p + C7_6_3 a n + 2) := by
          gcongr; · exact (mem_ball'.mp (Grid_subset_ball (lJ'.1.1 Grid.c_mem_Grid))).le
        _ ≤ (100 : ℝ) * D ^ (𝔰 p + C7_6_3 a n + 2) + 4 * D ^ (𝔰 p + C7_6_3 a n + 2) +
            16 * D ^ (𝔰 p + C7_6_3 a n + 2) := by
          rw [← sub_eq_iff_eq_add] at sJ'
          rw [← sJ', Int.cast_sub, Int.cast_one, sub_lt_iff_lt_add, sub_lt_iff_lt_add] at h
          simp_rw [← Real.rpow_intCast, Int.cast_add, Int.cast_one]
          gcongr 100 * (D : ℝ) ^ ?_ + 4 * D ^ ?_ + _
          exacts [one_le_realD _, by linarith only [h], one_le_realD _, by linarith only [h]]
        _ ≤ _ := by rw [← add_mul, ← add_mul]; gcongr; norm_num
    _ ≤ dist_{𝔠 p, 2 ^ (𝕔 * a ^ 2 * ⌈C7_6_3 a n + 2⌉₊ + 9) * (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
      refine cdist_mono (ball_subset_ball ?_)
      rw [add_assoc, Real.rpow_add (by simp), Real.rpow_intCast,
        show (128 : ℝ) * (D ^ 𝔰 p * D ^ (C7_6_3 a n + 2)) =
          D ^ (C7_6_3 a n + 2) * 2 ^ 9 * (D ^ 𝔰 p / 4) by ring]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [pow_add, pow_mul _ (𝕔 * a ^ 2), defaultD, ← Real.rpow_natCast _ ⌈_⌉₊, Nat.cast_pow,
        Nat.cast_ofNat]; gcongr
      · exact_mod_cast Nat.one_le_two_pow
      · exact Nat.le_ceil _
    _ ≤ (defaultA a) ^ (𝕔 * a ^ 2 * ⌈C7_6_3 a n + 2⌉₊ + 9) * dist_(p) (𝒬 u₁) (𝒬 u₂) :=
      cdist_le_iterate (by unfold defaultD; positivity) ..
    _ ≤ _ := by
      obtain ⟨hp₁, hp₂⟩ := hp
      simp_rw [𝔖₀, mem_setOf, not_and_or, mem_union, hp₁, or_true, not_true_eq_false,
        false_or, not_le] at hp₂
      simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← Real.rpow_natCast 2]
      push_cast; gcongr
      · exact one_le_two
      · exact (Nat.ceil_lt_add_one nonneg_C7_6_3_add_two).le

/-- Lemma 7.6.3. -/
lemma thin_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁)
    (hd : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) :
    𝔰 p ≤ s J - C7_6_3 a n := by
  by_contra! h
  have bZn : 4 ≤ Z * (n + 1) := by
    rw [← mul_one 4]; gcongr
    · exact four_le_Z (X := X)
    · exact Nat.le_add_left ..
  have key := thin_scale_impact_key hu₁ hu₂ hu h2u hp hJ hd h
  rw [← Real.rpow_natCast, ← Real.rpow_add zero_lt_two,
    Real.rpow_lt_rpow_left_iff one_lt_two, Nat.cast_sub (by lia), Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_add_one] at key
  nth_rw 1 [← add_halves ((Z : ℝ) * n)] at key
  rw [add_rotate, ← sub_add_eq_add_sub, add_lt_add_iff_right, C7_6_3, sub_add_cancel] at key
  have : (2 * 𝕔 + 2 : ℝ) ≠ 0 := by norm_cast
  have : (a : ℝ) ≠ 0 := by norm_cast; linarith [four_le_a X]
  have rearr : (a : ℝ) * (𝕔 * a ^ 2 * (Z * n / ((2 * 𝕔 + 2) * a ^ 3) + 1) + 9) =
      Z * n / 2 * (𝕔 / (𝕔 + 1)) * a ^ 3 / a ^ 3 + 𝕔 * a ^ 3 + 9 * a := by
        field_simp
  have fla := four_le_a X
  rw [rearr, mul_div_cancel_right₀ _ (by norm_cast; positivity), add_assoc,
    ← sub_lt_iff_lt_add', sub_right_comm, add_sub_right_comm, ← mul_one_sub, div_mul_comm,
    show (1 - 𝕔 / (𝕔 + 1)) / (2 : ℝ) = 1 / (2 * 𝕔 + 2) by field_simp; ring,
    sub_lt_iff_lt_add] at key
  apply absurd key; rw [not_lt]
  suffices 𝕔 * a ^ 3 + 9 * a + 1 ≤ (Z : ℝ) by
    apply this.trans; nth_rw 1 [← zero_add (Z : ℝ)]; gcongr; positivity
  norm_cast; rw [defaultZ]
  calc
    _ = 𝕔 * a ^ 3 + 9 * a * 1 * 1 + 1 * 1 * 1 * 1 := by norm_num
    _ ≤ 𝕔 * a ^ 3 + 9 * a * a * a + 1 * a * a * a := by gcongr <;> lia
    _ = (𝕔 + 10) * a ^ 3 := by ring
    _ ≤ 2 ^ (7 + 3 * a) := by
      rw [pow_add, pow_mul']; gcongr; exacts [by linarith [c_le_100], Nat.lt_two_pow_self.le]
    _ ≤ _ := by gcongr <;> lia

/-- Lemma 7.6.3 with a floor on the constant to avoid casting. -/
lemma thin_scale_impact' (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁)
    (hd : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) :
    𝔰 p ≤ s J - ⌊C7_6_3 a n⌋ := by
  rw [← Int.cast_le (R := ℝ), Int.cast_sub]
  apply (thin_scale_impact hu₁ hu₂ hu h2u hp hJ hd).trans; gcongr; exact Int.floor_le _

/-- The constant used in `square_function_count`. -/
irreducible_def C7_6_4 (a : ℕ) (s : ℤ) : ℝ≥0 := 2 ^ (14 * (a : ℝ) + 1) * (8 * D ^ (- s)) ^ κ

open Classical in
/-- Lemma 7.6.4. -/
lemma square_function_count (hJ : J ∈ 𝓙₆ t u₁) {s' : ℤ} :
    ⨍⁻ x in J, (∑ I with s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
    ¬Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)),
    (ball (c I) (8 * D ^ s I)).indicator 1 x) ^ 2 ∂volume ≤ C7_6_4 a s' := by
  rcases lt_or_ge (↑S + s J) s' with hs' | hs'
  · suffices ({I : Grid X | s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
        ¬Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)) } : Finset (Grid X)) = ∅ by
      rw [this]
      simp only [Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, laverage_zero, zero_le]
    simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, not_and, Decidable.not_not,
      true_implies]
    intros I hI
    have : -S ≤ s I := (range_s_subset ⟨I, rfl⟩).1
    linarith
  have : NeZero (volume.restrict (J : Set X) univ) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact ((measure_ball_pos _ _ (by simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultA,
      defaultD.eq_1, defaultκ.eq_1, Nat.ofNat_pos, div_pos_iff_of_pos_right]; positivity)).trans_le
      (measure_mono (μ := volume) (ball_subset_Grid (i := J)))).ne'⟩
  have : IsFiniteMeasure (volume.restrict (J : Set X)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact volume_coeGrid_lt_top⟩
  let 𝒟 (s₀ x) : Set (Grid X) := { I | x ∈ ball (c I) (8 * D ^ s I) ∧ s I = s₀ }
  let supp : Set X := { x ∈ J | Metric.infEDist x Jᶜ ≤ 8 * (D ^ (s J - s')) }
  have hsupp : supp ⊆ J := fun x hx ↦ hx.1
  have vsupp : volume.real supp ≤ 2 * (↑8 * ↑D ^ (-s')) ^ κ * volume.real (J : Set X) := by
    simp only [supp, sub_eq_neg_add, ENNReal.zpow_add (x := D) (by simp) (by finiteness),
      ← mul_assoc]
    convert small_boundary (i := J) (t := 8 * ↑D ^ (-s')) ?_
    · simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      rw [ENNReal.coe_zpow (by simp)]
      norm_num
    · rw [show (8 : ℝ≥0) = 2 ^ 3 by norm_num]
      simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultA, ← zpow_natCast, ← zpow_mul,
        ← zpow_add₀ (show (2 : ℝ≥0) ≠ 0 by norm_num)]
      gcongr
      · norm_num
      · simp only [Nat.cast_mul, Nat.cast_pow, mul_neg,
        le_add_neg_iff_add_le, ← mul_add]
        refine (Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_).trans (by norm_num)
        rwa [← sub_nonpos, sub_eq_neg_add, neg_add] at hs'
  have vsupp : volume supp ≤ ENNReal.ofReal (2 * (↑8 * ↑D ^ (-s')) ^ κ) * volume (J : Set X) := by
    apply ENNReal.ofReal_le_ofReal at vsupp
    rwa [Measure.real, Measure.real, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (volume_coeGrid_lt_top.ne),
      ENNReal.ofReal_toReal ((measure_mono hsupp).trans_lt volume_coeGrid_lt_top).ne] at vsupp
  have est₁ (s₀ x) : (𝒟 s₀ x).toFinset.card ≤ (defaultA a) ^ 7 := by
    apply Nat.cast_le (α := ℝ).mp
    have : 0 < volume.real (ball x (9 * ↑D ^ s₀)) :=
      ENNReal.toReal_pos (measure_ball_pos _ _ (by simpa using by positivity)).ne' (by finiteness)
    refine le_of_mul_le_mul_right (a := volume.real (ball x (9 * D ^ s₀))) ?_ this
    transitivity (defaultA a) ^ 7 * ∑ I ∈ 𝒟 s₀ x, volume.real (ball (c I) (D ^ s I / 4))
    · rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun I hI ↦ ?_
      simp only [mem_toFinset] at hI
      apply le_trans _ (measureReal_ball_two_le_same_iterate (μ := volume) (c I) (D ^ s I / 4) 7)
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
  have est₂ (x) (hx : x ∈ J) : (∑ I with s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
      ¬Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)),
      (ball (c I) (8 * D ^ s I)).indicator (1 : X → ℝ≥0∞) x) ≤
      if x ∈ supp then (defaultA a) ^ 7 else 0 := by
    split_ifs with hx'
    · rw [Finset.sum_indicator_eq_sum_filter]
      simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
      refine le_trans ?_ (est₁ (s J - s') x)
      gcongr
      intro I
      simp_rw [Finset.filter_filter, Finset.mem_filter_univ, mem_toFinset]
      exact fun H ↦ ⟨H.2, H.1.1⟩
    · have (I : Grid X) : ball (c I) (8 * D ^ s I) = Metric.eball (c I) (8 * D ^ s I) := by
        trans Metric.eball (c I) (show ℝ≥0 from ⟨8 * D ^ s I, by positivity⟩)
        · rw [Metric.eball_coe]; rfl
        · congr!
          simp only [ENNReal.coe_nnreal_eq, ← Real.rpow_intCast]
          erw [ENNReal.ofReal_mul (by norm_num)]
          rw [← ENNReal.ofReal_rpow_of_pos (by simp), ENNReal.ofReal_natCast]
          norm_num
      simp_rw [this]
      simp only [CharP.cast_eq_zero, nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_filter,
        Finset.mem_univ, true_and, indicator_apply_eq_zero, Metric.mem_eball, Pi.one_apply,
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
  refine ((ENNReal.mul_le_mul_iff_right (by simp) (ne_of_beq_false rfl).symm).mpr vsupp).trans ?_
  rw [← mul_assoc, ENNReal.ofReal, ← ENNReal.coe_natCast, ← ENNReal.coe_pow, ← ENNReal.coe_mul]
  gcongr
  rw [Real.toNNReal_mul (by positivity), Real.toNNReal_rpow_of_nonneg (by positivity),
    Real.toNNReal_mul (by positivity), ← Real.rpow_intCast,
    Real.toNNReal_rpow_of_nonneg (by positivity), Real.toNNReal_coe_nat]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.toNNReal_ofNat, Int.cast_neg, ← pow_mul]
  rw [← mul_assoc, ← pow_succ, C7_6_4, ← NNReal.rpow_natCast, ← NNReal.rpow_intCast, Int.cast_neg]
  congr!
  simp [mul_assoc, mul_comm (G := ℝ) 14]

open Classical in
lemma sum_𝓙₆_indicator_sq_eq {f : Grid X → X → ℝ≥0∞} :
    (∑ J ∈ (𝓙₆ t u₁).toFinset, (J : Set X).indicator (f J) x) ^ 2 =
    ∑ J ∈ (𝓙₆ t u₁).toFinset, (J : Set X).indicator (f J · ^ 2) x := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have dsub : (𝓙₆ t u₁).toFinset.diag ⊆ (𝓙₆ t u₁).toFinset ×ˢ (𝓙₆ t u₁).toFinset := by
    rw [Finset.diag_eq_filter]
    exact Finset.filter_subset ..
  rw [← Finset.sum_subset dsub]; swap
  · intro p mp np
    simp_rw [Finset.mem_product, Finset.mem_diag, mem_toFinset, not_and] at mp np
    specialize np mp.1
    rw [← inter_indicator_mul, (pairwiseDisjoint_𝓙₆ mp.1 mp.2 np).inter_eq]
    simp
  simp_rw [Finset.sum_diag, ← inter_indicator_mul, inter_self, ← sq]

open Classical in
lemma btp_expansion (hf : BoundedCompactSupport f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume =
    (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
    (∫⁻ y in J, ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
  have Vpos {J : Grid X} : 0 < volume (J : Set X) := volume_coeGrid_pos (defaultD_pos a)
  have Vlt {J : Grid X} : volume (J : Set X) < ⊤ := volume_coeGrid_lt_top
  calc
    _ = (∫⁻ x, ∑ J ∈ (𝓙₆ t u₁).toFinset, (J : Set X).indicator (fun _ ↦
        ‖⨍ y in J, ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f y‖‖ₑ ^ 2) x) ^ (2 : ℝ)⁻¹ := by
      unfold approxOnCube
      simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat, one_div]
      congr! with x; rw [ENNReal.enorm_sum_eq_sum_enorm]; swap
      · refine fun J mJ ↦ indicator_nonneg (fun y my ↦ ?_) _
        rw [average_eq, smul_eq_mul]
        exact mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _)
      rw [show (2 : ℝ) = (2 : ℕ) by rfl, ENNReal.rpow_natCast, filter_mem_univ_eq_toFinset]
      simp_rw [enorm_indicator_eq_indicator_enorm, sum_𝓙₆_indicator_sq_eq]
    _ = (∑ J ∈ (𝓙₆ t u₁).toFinset, ∫⁻ x in (J : Set X), (fun _ ↦
        ‖⨍ y in J, ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f y‖‖ₑ ^ 2) x) ^ (2 : ℝ)⁻¹ := by
      congr 1; simp_rw [← lintegral_indicator coeGrid_measurable]
      exact lintegral_finset_sum _ fun J mJ ↦ measurable_const.indicator coeGrid_measurable
    _ = (∑ J ∈ (𝓙₆ t u₁).toFinset, ∫⁻ x in (J : Set X),
        (⨍⁻ y in J, ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f y‖ₑ ∂volume) ^ 2) ^ (2 : ℝ)⁻¹ := by
      simp only [lintegral_const]; congr! with J mJ
      have vn0 : volume.real (J : Set X) ≠ 0 := by
        rw [measureReal_def, ENNReal.toReal_ne_zero]; exact ⟨Vpos.ne', Vlt.ne⟩
      rw [setLAverage_eq, setAverage_eq, smul_eq_mul, enorm_mul, enorm_inv vn0,
        ← ENNReal.div_eq_inv_mul, measureReal_def, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal Vlt.ne]; congr
      rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable.adjointCarlesonSum.restrict]
      apply enorm_toReal
      rw [← lt_top_iff_ne_top, ← eLpNorm_one_eq_lintegral_enorm]
      exact (hf.adjointCarlesonSum.restrict.memLp 1).2
    _ = _ := by
      congr! with J mJ
      rw [setLIntegral_const, setLAverage_eq, ENNReal.div_eq_inv_mul, mul_pow, ← mul_rotate, sq,
        ← mul_assoc, ENNReal.mul_inv_cancel Vpos.ne' Vlt.ne, one_mul]

open Classical in
/-- Equation (7.6.3) of Lemma 7.6.2. -/
lemma e763 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf : BoundedCompactSupport f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume ≤
    ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
    (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
    (∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
      ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝔰 p = s J - k,
    ‖adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
  calc
    _ = _ := btp_expansion hf
    _ = (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ * (∫⁻ y in J,
        ‖∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)),
          adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
      congr! 4 with J mJ
      refine setLIntegral_congr_fun coeGrid_measurable fun y my ↦ ?_
      unfold adjointCarlesonSum; congr 1
      rw [filter_mem_univ_eq_toFinset]; refine (Finset.sum_filter_of_ne fun p mp hd ↦ ?_).symm
      rw [adjoint_tile_support1] at hd
      exact not_disjoint_iff.mpr ⟨_, my,
        ball_subset_ball (by gcongr; norm_num) (mem_of_indicator_ne_zero hd)⟩
    _ = (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ * (∫⁻ y in J,
        ‖∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ s J - 𝔰 p = k,
        adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
      congr! with J mJ y; simp_rw [← Finset.filter_filter]
      refine (Finset.sum_fiberwise_of_maps_to (fun p mp ↦ ?_) _).symm
      rw [Finset.mem_filter] at mp; rw [mem_toFinset] at mp mJ; obtain ⟨mp, dp⟩ := mp
      have dpJ : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) := by
        contrapose! dp; refine dp.symm.mono_left (Grid_subset_ball.trans (ball_subset_ball ?_))
        change (4 : ℝ) * D ^ s J ≤ _; gcongr; norm_num
      rw [Finset.mem_Icc]
      constructor
      · have := thin_scale_impact' hu₁ hu₂ hu h2u mp mJ dpJ
        lia
      · have : s J ≤ S := scale_mem_Icc.2
        have : -S ≤ 𝔰 p := scale_mem_Icc.1
        lia
    _ ≤ (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∫⁻ y in J, ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ s J - 𝔰 p = k,
        ‖adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by -- Triangle inequality
      gcongr with J mJ y
      exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k mk ↦ enorm_sum_le _ _)
    _ = (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S), ∫⁻ y in J,
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ s J - 𝔰 p = k,
        ‖adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
      congr! with J mJ
      exact lintegral_finset_sum' _ fun k mk ↦ Finset.aemeasurable_fun_sum _ fun p mp ↦
        hf.aestronglyMeasurable.adjointCarleson.aemeasurable.enorm.restrict
    _ = (∑ J ∈ (𝓙₆ t u₁).toFinset, (∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        volume (J : Set X) ^ (-2 : ℝ)⁻¹ * ∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝔰 p = s J - k,
        ‖adjointCarleson p f y‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [one_div]; congr! with J mJ
      rw [← ENNReal.rpow_neg_one, show (-1 : ℝ) = (-2)⁻¹ * (2 : ℕ) by norm_num, ENNReal.rpow_mul,
        ENNReal.rpow_natCast, ← mul_pow, show (2 : ℝ) = (2 : ℕ) by rfl, ENNReal.rpow_natCast,
        Finset.mul_sum]
      congr! 9 with k mk y p; lia
    _ ≤ ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X) ^ (-2 : ℝ)⁻¹ *
        ∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝔰 p = s J - k,
        ‖adjointCarleson p f y‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := -- Minkowski inequality
      ENNReal.Lp_add_le_sum one_le_two
    _ = _ := by
      rw [one_div]; congr! with k mk J mJ
      nth_rw 2 [show (2 : ℝ) = (2 : ℕ) by rfl]
      rw [ENNReal.rpow_natCast, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        show (-2)⁻¹ * (2 : ℕ) = (-1 : ℝ) by norm_num, ENNReal.rpow_neg_one]

open Classical in
/-- The critical bound on the integral in Equation (7.6.3). It holds for _any_ cubes `I, J`. -/
lemma btp_integral_bound :
    ∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
      ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝓘 p = I, ‖adjointCarleson p f y‖ₑ ≤
    C2_1_3 a * 2 ^ (4 * a) * ∫⁻ y in J, (ball (c I) (8 * D ^ s I)).indicator 1 y *
      MB volume 𝓑 c𝓑 r𝓑 f y := by
  calc
    _ ≤ ∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
        ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝓘 p = I,
          C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * (∫⁻ y in E p, ‖f y‖ₑ) *
          (ball (𝔠 p) (8 * D ^ 𝔰 p)).indicator 1 y := by
      gcongr with y p mp; exact enorm_adjointCarleson_le_mul_indicator
    _ = ∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
        ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)) ∧ 𝓘 p = I,
          C2_1_3 a * 2 ^ (4 * a) * (volume (ball (c I) (8 * D ^ s I)))⁻¹ * (∫⁻ y in E p, ‖f y‖ₑ) *
          (ball (c I) (8 * D ^ s I)).indicator 1 y := by
      congr! 3 with y p mp
      · ext p; simp_rw [Finset.mem_filter, and_congr_right_iff, and_congr_left_iff]
        intro _ he; rw [← he]; rfl
      · simp_rw [Finset.mem_filter] at mp
        simp_rw [← mp.2.2]; rfl
    _ = C2_1_3 a * 2 ^ (4 * a) * ∫⁻ y in J,
        (ball (c I) (8 * D ^ s I)).indicator 1 y * ((volume (ball (c I) (8 * D ^ s I)))⁻¹ *
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)) ∧ 𝓘 p = I,
          ∫⁻ y in E p, ‖f y‖ₑ) := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]; congr! with y
      simp_rw [Finset.mul_sum]; congr! 1 with p mp; ring
    _ = C2_1_3 a * 2 ^ (4 * a) * ∫⁻ y in J,
        (ball (c I) (8 * D ^ s I)).indicator 1 y * ((volume (ball (c I) (8 * D ^ s I)))⁻¹ *
        ∫⁻ y in ⋃ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (¬Disjoint ↑J (ball (c I) (8 * D ^ s I)) ∧ 𝓘 · = I), E p, ‖f y‖ₑ) := by
      congr! with y
      refine (lintegral_biUnion_finset (fun p₁ mp₁ p₂ mp₂ hn ↦ ?_)
        (fun p mp ↦ measurableSet_E) _).symm
      rw [Finset.coe_filter, mem_setOf_eq] at mp₁ mp₂
      exact disjoint_E hn (mp₂.2.2.symm ▸ mp₁.2.2)
    _ ≤ C2_1_3 a * 2 ^ (4 * a) * ∫⁻ y in J, (ball (c I) (8 * D ^ s I)).indicator 1 y *
        ⨍⁻ y in ball (c I) (8 * D ^ s I), ‖f y‖ₑ ∂volume := by
      gcongr with y; rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
      refine mul_le_mul_right (lintegral_mono_set (iUnion₂_subset fun p mp ↦ ?_)) _
      rw [Finset.mem_filter] at mp
      convert (E_subset_𝓘.trans Grid_subset_ball).trans (ball_subset_ball _)
      · exact mp.2.2.symm
      · change (4 : ℝ) * D ^ s (𝓘 p) ≤ _
        rw [mp.2.2]; gcongr; norm_num
    _ ≤ _ := by
      refine mul_le_mul_right (lintegral_mono fun y ↦ ?_) _
      by_cases my : y ∈ ball (c I) (8 * D ^ s I)
      · refine mul_le_mul_right ?_ _; rw [MB_def]
        have : (3, 0, I) ∈ 𝓑 := by
          simp only [𝓑, Set.mem_prod, mem_Iic, Set.mem_univ, and_true]
          omega
        refine le_of_eq_of_le ?_ (le_biSup _ this)
        have : y ∈ ball (c I) (2 ^ 3 * (D : ℝ) ^ s I) := by rwa [show (2 : ℝ) ^ 3 = 8 by norm_num]
        simp_rw [c𝓑, r𝓑, Nat.cast_zero, add_zero, indicator_of_mem this, enorm_eq_nnnorm]
        norm_num
      · rw [indicator_of_notMem my, zero_mul]; exact zero_le _

attribute [fun_prop] AEMeasurable.restrict

open Classical in
/-- Equation (7.6.4) of Lemma 7.6.2 (before applying Cauchy–Schwarz). -/
lemma e764_preCS (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf : BoundedCompactSupport f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume ≤
    C2_1_3 a * 2 ^ (4 * a) * ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
    (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
    (∑ I with s I = s J - k ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
      ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)),
    ∫⁻ y in J, (ball (c I) (8 * D ^ s I)).indicator 1 y *
      MB volume 𝓑 c𝓑 r𝓑 f y) ^ 2) ^ (2 : ℝ)⁻¹ := by
  calc
    _ ≤ _ := e763 hu₁ hu₂ hu h2u hf
    _ = ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∫⁻ y in J, ∑ I, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝔰 p = s J - k ∧ 𝓘 p = I,
        ‖adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
      congr! with k mk J mJ y
      conv_rhs => enter [2, I, 1, 1, p]; rw [← and_assoc]
      conv_rhs => enter [2, I]; rw [← Finset.filter_filter]
      exact (Finset.sum_fiberwise _ _ _).symm
    _ ≤ ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∫⁻ y in J, ∑ I with
          s I = s J - k ∧ Disjoint (I : Set X) (𝓘 u₁) ∧ ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝓘 p = I,
        ‖adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
      gcongr with k mk J mJ y
      nth_rw 1 [← Finset.filter_true (@Finset.univ (Grid X) _) (h := fun _ ↦ instDecidableTrue)]
      simp_rw [Finset.sum_finset_product_filter_right]
      refine Finset.sum_le_sum_of_subset fun r hr ↦ ?_
      obtain ⟨I, p⟩ := r
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hr ⊢
      obtain ⟨mp, h₁, h₂, h₃⟩ := hr; dsimp only [𝔠, 𝔰] at h₁ h₂ h₃ ⊢; rw [h₃] at h₁ h₂ ⊢
      refine ⟨mp, ⟨h₂, ?_, h₁⟩, ⟨h₁, rfl⟩⟩
      rw [mem_toFinset, mem_diff] at mp; obtain ⟨mp₁, mp₂⟩ := mp; contrapose! mp₂
      exact overlap_implies_distance hu₁ hu₂ hu h2u (.inr mp₁) (h₃.symm ▸ mp₂)
    _ = ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∑ I with s I = s J - k ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
          ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)),
        ∫⁻ y in J, ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset with
          ¬Disjoint ↑J (ball (𝔠 p) (8 * D ^ 𝔰 p)) ∧ 𝓘 p = I,
        ‖adjointCarleson p f y‖ₑ) ^ 2) ^ (2 : ℝ)⁻¹ := by
      congr! with k mk J mJ
      exact lintegral_finset_sum' _ fun k mk ↦ Finset.aemeasurable_fun_sum _ fun p mp ↦
        hf.aestronglyMeasurable.adjointCarleson.aemeasurable.enorm.restrict
    _ ≤ ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∑ I with s I = s J - k ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
          ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)),
        C2_1_3 a * 2 ^ (4 * a) * ∫⁻ y in J, (ball (c I) (8 * D ^ s I)).indicator 1 y *
          MB volume 𝓑 c𝓑 r𝓑 f y) ^ 2) ^ (2 : ℝ)⁻¹ := by
      gcongr with k mk J mJ; exact btp_integral_bound
    _ = _ := by
      nth_rw 2 [← ENNReal.rpow_one (C2_1_3 a * 2 ^ (4 * a))]
      rw [show (1 : ℝ) = (2 : ℕ) * 2⁻¹ by norm_num, ENNReal.rpow_mul, Finset.mul_sum]
      congr! with k mk
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), Finset.mul_sum]
      congr! 2 with J mJ
      rw [← mul_assoc, mul_comm _ (volume (J : Set X))⁻¹, ENNReal.rpow_natCast, mul_assoc,
        ← mul_pow, Finset.mul_sum]

/-- Equation (7.6.4) of Lemma 7.6.2 (after applying Cauchy–Schwarz and simplification). -/
lemma e764_postCS (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf : BoundedCompactSupport f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume ≤
    C2_1_3 a * 2 ^ (11 * a + 2) *
    (∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S), (D : ℝ≥0∞) ^ (-k * κ / 2)) *
    eLpNorm ((𝓘 u₁ : Set X).indicator (MB volume 𝓑 c𝓑 r𝓑 f ·)) 2 volume := by
  have aem_MB : AEMeasurable (MB volume 𝓑 c𝓑 r𝓑 f) volume :=
    (AEStronglyMeasurable.maximalFunction 𝓑.to_countable).aemeasurable
  classical
  calc
    _ ≤ _ := e764_preCS hu₁ hu₂ hu h2u hf
    _ = C2_1_3 a * 2 ^ (4 * a) * ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (volume (J : Set X))⁻¹ *
        (∫⁻ y in J, MB volume 𝓑 c𝓑 r𝓑 f y *
        ∑ I with s I = s J - k ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
          ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)),
        (ball (c I) (8 * D ^ s I)).indicator 1 y) ^ 2) ^ (2 : ℝ)⁻¹ := by
      congr! with k mk J mJ
      rw [← lintegral_finset_sum']; swap
      · fun_prop (discharger := measurability)
      congr with y; rw [mul_comm, Finset.sum_mul]
    _ ≤ C2_1_3 a * 2 ^ (4 * a) * ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset, (∫⁻ y in J, MB volume 𝓑 c𝓑 r𝓑 f y ^ 2) *
        (⨍⁻ y in J, (∑ I : Grid X with s I = s J - k ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
          ¬Disjoint ↑J (ball (c I) (8 * D ^ s I)),
        (ball (c I) (8 * D ^ s I)).indicator 1 y) ^ 2 ∂volume)) ^ (2 : ℝ)⁻¹ := by
      gcongr _ * ∑ k ∈ _, (∑ J ∈ _, ?_) ^ _ with k mk J mJ
      rw [setLAverage_eq, ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm _ _⁻¹, mul_assoc]
      gcongr; apply ENNReal.sq_lintegral_mul_le_mul_lintegral_sq aem_MB.restrict -- Cauchy–Schwarz
      fun_prop (discharger := measurability)
    _ ≤ C2_1_3 a * 2 ^ (4 * a) * ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        (∑ J ∈ (𝓙₆ t u₁).toFinset,
        (∫⁻ y in J, MB volume 𝓑 c𝓑 r𝓑 f y ^ 2) * C7_6_4 a k) ^ (2 : ℝ)⁻¹ := by
      gcongr with k mk J mJ; rw [mem_toFinset] at mJ; exact square_function_count mJ
    _ ≤ C2_1_3 a * 2 ^ (4 * a) *
        ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S),
        2 ^ (7 * a + 2) * D ^ (-k * κ / 2) * (∑ J ∈ (𝓙₆ t u₁).toFinset,
        ∫⁻ y in J, MB volume 𝓑 c𝓑 r𝓑 f y ^ 2) ^ (2 : ℝ)⁻¹ := by
      gcongr with k mk
      rw [← Finset.sum_mul, mul_comm _ (C7_6_4 a k : ℝ≥0∞),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      gcongr
      rw [C7_6_4, NNReal.mul_rpow, show (8 : ℝ≥0) = 2 ^ (3 : ℝ) by norm_num, ← NNReal.rpow_mul,
        ← mul_assoc, ← NNReal.rpow_intCast, ← NNReal.rpow_mul,
        ENNReal.rpow_ofNNReal (by positivity), NNReal.mul_rpow, ← NNReal.rpow_mul,
        ← NNReal.rpow_add two_ne_zero, ← NNReal.rpow_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_ne_zero two_ne_zero, ← show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl,
        ENNReal.coe_rpow_of_ne_zero (by norm_cast; unfold defaultD; positivity),
        show ((D : ℝ≥0) : ℝ≥0∞) = (D : ℝ≥0∞) by rfl, Int.cast_neg, div_eq_mul_inv,
        ← ENNReal.rpow_natCast]
      gcongr
      · exact one_le_two
      · rw [add_assoc, add_mul, Nat.cast_add, Nat.cast_mul, show (14 * a * 2⁻¹ : ℝ) = 7 * a by ring,
          Nat.cast_ofNat]
        gcongr
        calc
          _ ≤ (1 + 3 * 1) * (2 : ℝ)⁻¹ := by gcongr; exact κ_le_one
          _ = _ := by norm_num
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← mul_assoc, ← mul_assoc, mul_assoc _ (_ ^ _) (_ ^ _),
        ← pow_add, show 4 * a + (7 * a + 2) = 11 * a + 2 by lia]
      congr; rw [← lintegral_biUnion_finset _ fun _ _ ↦ coeGrid_measurable]; swap
      · rw [coe_toFinset]; exact pairwiseDisjoint_𝓙₆
      simp_rw [mem_toFinset, union_𝓙₆ hu₁, ← lintegral_indicator coeGrid_measurable,
        eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat, one_div, show (2 : ℝ) = (2 : ℕ) by rfl, ENNReal.rpow_natCast,
        enorm_eq_self]
      congr! with x
      simp_rw [sq, ← inter_indicator_mul, inter_self]

/-- The constant used in `bound_for_tree_projection`. -/
irreducible_def C7_6_2 (a n : ℕ) : ℝ≥0 :=
  C2_1_3 a * 2 ^ (21 * a + 5) * 2 ^ (-(𝕔 / ((4 * 𝕔 + 4) * a) * Z * n * κ))

omit [TileStructure Q D κ S o] in
lemma btp_constant_bound :
    C2_1_3 a * 2 ^ (11 * a + 2) *
    ∑ k ∈ Finset.Icc ⌊C7_6_3 a n⌋ (2 * S), (D : ℝ≥0∞) ^ (-k * κ / 2) ≤ C7_6_2 a n := by
  calc
    _ = C2_1_3 a * 2 ^ (11 * a + 2) * D ^ (-⌊C7_6_3 a n⌋ * κ / 2) *
        ∑ k ∈ Finset.range (2 * S + 1 - ⌊C7_6_3 a n⌋).toNat, ((D : ℝ≥0∞) ^ (-(κ / 2))) ^ k := by
      conv_rhs => rw [mul_assoc, Finset.mul_sum]
      congr 1; change ∑ k ∈ Finset.Ico _ _, _ = _
      rcases le_or_gt (2 * S + 1 : ℤ) ⌊C7_6_3 a n⌋ with hb | hb
      · rw [Finset.Ico_eq_empty (not_lt.mpr hb)]; rw [← sub_nonpos] at hb
        rw [Int.toNat_of_nonpos hb]; simp
      refine Finset.sum_bij
        (fun (k : ℤ) (_ : k ∈ Finset.Ico ⌊C7_6_3 a n⌋ (2 * S + 1)) ↦ (k - ⌊C7_6_3 a n⌋).toNat)
        (fun k mk ↦ ?_) (fun k₁ mk₁ k₂ mk₂ he ↦ ?_) (fun k mk ↦ ?_) (fun k mk ↦ ?_)
      · rw [Finset.mem_Ico] at mk; simp [mk]
      · rw [Finset.mem_Ico] at mk₁ mk₂
        simp_rw [← Int.ofNat_inj, Int.toNat_sub_of_le mk₁.1, Int.toNat_sub_of_le mk₂.1] at he
        simpa using he
      · use k + ⌊C7_6_3 a n⌋, ?_, by simp
        rw [Finset.mem_range, ← Nat.cast_lt (α := ℤ), Int.toNat_sub_of_le hb.le] at mk
        rw [Finset.mem_Ico]; lia
      · rw [Finset.mem_Ico] at mk
        simp_rw [← ENNReal.rpow_natCast,
          show ((k - ⌊C7_6_3 a n⌋).toNat : ℝ) = ((k - ⌊C7_6_3 a n⌋).toNat : ℤ) by rfl,
          Int.toNat_sub_of_le mk.1, ← ENNReal.rpow_mul, Int.cast_sub]
        rw [← ENNReal.rpow_add _ _ (by norm_cast; unfold defaultD; positivity)
          (ENNReal.natCast_ne_top D)]
        congr; ring
    _ ≤ C2_1_3 a * 2 ^ (11 * a + 2) * 2 ^ (-𝕔 * a ^ 2 * (Z * n / ((2 * 𝕔 + 2) * a ^ 3) - 3)
         * κ / 2) * 2 ^ (10 * a + 2) := by
      gcongr with k
      · rw [defaultD, Nat.cast_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, neg_mul, neg_div,
          ← neg_mul_comm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← neg_mul,
          ← mul_div_assoc, ← mul_assoc]
        gcongr _ ^ (?_ * _ / _)
        · exact one_le_two
        · exact κ_nonneg
        · apply mul_le_mul_of_nonpos_left
          · rw [show (3 : ℝ) = 2 + 1 by norm_num, ← sub_sub, ← C7_6_3_def, sub_le_iff_le_add]
            exact (Int.lt_floor_add_one _).le
          · rw [neg_mul, Left.neg_nonpos_iff, mul_nonneg_iff_of_pos_left
              (by norm_cast; linarith [seven_le_c])]
            positivity
      · exact calculation_7_6_2 (X := X)
    _ = C2_1_3 a * 2 ^ (21 * a + 4) *
        2 ^ ((𝕔 * (3 / 2)) * a ^ 2 * κ - 𝕔 / ((4 * 𝕔 + 4) * a) * Z * n * κ) := by
      rw [← mul_rotate]; congr 1
      · rw [← mul_assoc, ← mul_rotate, ← pow_add, mul_comm]
        congr 2; lia
      · congr 1
        rw [mul_sub, neg_mul, neg_mul, neg_mul, sub_neg_eq_add, ← sub_eq_neg_add, sub_mul, sub_div]
        congr
        · ring
        · have a4 := four_le_a X
          have : 2 * 𝕔 + (2 : ℝ) ≠ 0 := by norm_cast
          field_simp
          ring
    _ ≤ C2_1_3 a * 2 ^ (21 * a + 4) * 2 ^ (1 - 𝕔 / ((4 * 𝕔 + 4) * a) * Z * n * κ) := by
      gcongr; exacts [one_le_two, calculation_150 (X := X)]
    _ = _ := by
      rw [sub_eq_add_neg, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.rpow_one,
        ← mul_assoc, mul_assoc _ _ 2, ← pow_succ, C7_6_2, ENNReal.coe_mul, ← div_div,
        ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_mul, ENNReal.coe_pow]
      rfl

/-- Lemma 7.6.2. -/
lemma bound_for_tree_projection (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf : BoundedCompactSupport f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume ≤
    C7_6_2 a n * eLpNorm ((𝓘 u₁ : Set X).indicator (MB volume 𝓑 c𝓑 r𝓑 f ·)) 2 volume :=
  (e764_postCS hu₁ hu₂ hu h2u hf).trans (mul_le_mul_left btp_constant_bound _)

lemma cntp_approxOnCube_eq (hu₁ : u₁ ∈ t) :
    approxOnCube (𝓙 (t u₁))
      (‖(𝓘 u₁ : Set X).indicator (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂) ·‖) =
    approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂ ·‖) := by
  set U := (𝓘 u₁ : Set X)
  ext x; simp only [approxOnCube]
  classical
  calc
    _ = ∑ p with p ∈ 𝓙₆ t u₁, (p : Set X).indicator (fun x ↦ ⨍ y in p,
        ‖U.indicator (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂) y‖) x := by
      apply (Finset.sum_subset (fun p mp ↦ ?_) (fun p mp np ↦ ?_)).symm
      · rw [Finset.mem_filter_univ] at mp ⊢
        exact mp.1
      · rw [Finset.mem_filter_univ] at mp np
        rw [indicator_apply_eq_zero]; intro mx
        rw [show (0 : ℝ) = ⨍ y in (p : Set X), 0 by simp]
        refine setAverage_congr_fun coeGrid_measurable (.of_forall fun y my ↦ ?_)
        suffices Disjoint (p : Set X) U by
          rw [indicator_of_notMem (this.notMem_of_mem_left my), norm_zero]
        -- There has to be a cube `I ∈ 𝓙₆` (the one containing `c (𝓘 u₁)`)
        have cm : c (𝓘 u₁) ∈ (𝓘 u₁ : Set X) := Grid.c_mem_Grid
        rw [← union_𝓙₆ hu₁, mem_iUnion₂] at cm; obtain ⟨I, mI, hI⟩ := cm
        -- Obviously `I ≠ p`
        have nIp : I ≠ p := ne_of_mem_of_not_mem mI np
        -- If `U` intersected `p`, `U ≤ p` since `p ∉ 𝓙₆`
        by_contra! h
        rw [𝓙₆, mem_inter_iff, not_and, mem_Iic] at np; specialize np mp
        have Ulp := le_or_ge_or_disjoint.resolve_left np |>.resolve_right h
        -- `I`, being in `𝓙₆`, should be a maximal cube in `𝓙₀ 𝔖`,
        -- but `p` is above it and also in `𝓙₀ 𝔖`; contradiction
        rw [𝓙₆, mem_inter_iff, mem_Iic] at mI
        rw [𝓙, mem_setOf] at mp mI
        exact nIp <| le_antisymm (mI.2.trans Ulp) (mI.1.2 mp.1 (mI.2.trans Ulp))
    _ = _ := by
      congr! 3 with p mp
      refine setAverage_congr_fun coeGrid_measurable (.of_forall fun y my ↦ ?_)
      rw [Finset.mem_filter_univ, 𝓙₆, mem_inter_iff, mem_Iic] at mp
      rw [indicator_of_mem (mp.2.1 my)]

/-- The constant used in `correlation_near_tree_parts`.
Has value `2 ^ (232 * a ^ 3 + 21 * a + 5- 25/(101a) * Z n κ)` in the blueprint. -/
irreducible_def C7_4_6 (a n : ℕ) : ℝ≥0 := C7_2_1 a * C7_6_2 a n

/-- Lemma 7.4.6 -/
lemma correlation_near_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) f₁ x * conj (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂ x)‖ₑ ≤
    C7_4_6 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ f₁) ·) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ f₂) ·) 2 volume := by
  set U := (𝓘 u₁ : Set X)
  calc
    _ = ‖∫ x, conj (adjointCarlesonSum (t u₁) f₁ x) *
        adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂ x‖ₑ := by
      erw [← RCLike.enorm_conj, ← integral_conj]
      congr! 3 with x
      rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    _ = ‖∫ x, conj (U.indicator (adjointCarlesonSum (t u₁) (U.indicator f₁)) x) *
        adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂ x‖ₑ := by
      congr! 5 with x; rw [adjoint_tile_support2_sum hu₁]
    _ = ‖∫ x, conj (adjointCarlesonSum (t u₁) (U.indicator f₁) x) *
        (U.indicator (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂) x)‖ₑ := by
      congr! 3 with x
      rw [indicator_eq_indicator_one_mul, map_mul, conj_indicator, map_one, mul_comm _ (conj _),
        mul_assoc, ← indicator_eq_indicator_one_mul]
    _ = ‖∫ x, conj (U.indicator f₁ x) *
        carlesonSum (t u₁) (U.indicator (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂)) x‖ₑ := by
      rw [← adjointCarlesonSum_adjoint (hf₂.adjointCarlesonSum.indicator coeGrid_measurable)
        (hf₁.indicator coeGrid_measurable)]
    _ ≤ C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u₁))
          (‖U.indicator (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f₂) ·‖)) 2 volume *
        eLpNorm (approxOnCube (𝓛 (t u₁)) (‖U.indicator f₁ ·‖)) 2 volume :=
      tree_projection_estimate (hf₂.adjointCarlesonSum.indicator coeGrid_measurable)
        (hf₁.indicator coeGrid_measurable) hu₁
    _ ≤ C7_2_1 a *
        (C7_6_2 a n * eLpNorm ((𝓘 u₁ : Set X).indicator (MB volume 𝓑 c𝓑 r𝓑 f₂ ·)) 2 volume) *
        eLpNorm (U.indicator f₁ ·) 2 volume := by
      rw [cntp_approxOnCube_eq hu₁]; gcongr
      · exact bound_for_tree_projection hu₁ hu₂ hu h2u hf₂
      · exact eLpNorm_approxOnCube_two_le_self (hf₁.indicator coeGrid_measurable) pairwiseDisjoint_𝓛
    _ ≤ _ := by
      conv_rhs => rw [mul_comm (C7_4_6 a n : ℝ≥0∞), mul_rotate]
      rw [C7_4_6, ENNReal.coe_mul, ← mul_assoc]; gcongr
      all_goals
        refine eLpNorm_mono_enorm fun x ↦ ?_
        simp only [enorm_eq_self, enorm_indicator_eq_indicator_enorm, adjointBoundaryOperator]
        apply indicator_le_indicator
      · rw [← add_rotate]; exact le_add_self
      · exact le_add_self

end TileStructure.Forest
