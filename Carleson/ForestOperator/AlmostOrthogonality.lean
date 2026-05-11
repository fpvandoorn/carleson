module

public import Carleson.ForestOperator.QuantativeEstimate

@[expose] public section

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

/-! ## Section 7.4 except Lemmas 4-6 -/

variable (t) in
/-- The operator `S_{2,𝔲} f(x)`, given above Lemma 7.4.3. -/
def adjointBoundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ‖adjointCarlesonSum (t u) f x‖ₑ + maximalFunction volume 𝓑 c𝓑 r𝓑 1 f x + ‖f x‖ₑ

variable (t u₁ u₂) in
/-- The set `𝔖` defined in the proof of Lemma 7.4.4.
We append a subscript 0 to distinguish it from the section variable. -/
def 𝔖₀ : Set (𝔓 X) := { p ∈ t u₁ ∪ t u₂ | 2 ^ ((Z : ℝ) * n / 2) ≤ dist_(p) (𝒬 u₁) (𝒬 u₂) }

/-- Part 1 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support1 : adjointCarleson p f =
    (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (adjointCarleson p ((𝓘 p : Set X).indicator f)) := by
  rw [adjoint_eq_adjoint_indicator E_subset_𝓘]; ext x
  rcases eq_or_ne (adjointCarleson p ((𝓘 p : Set X).indicator f) x) 0 with h0 | hn
  · exact (indicator_apply_eq_self.mpr fun _ ↦ h0).symm
  refine (indicator_of_mem ?_ _).symm
  obtain ⟨y, my, Ky⟩ : ∃ y ∈ 𝓘 p, Ks (𝔰 p) y x ≠ 0 := by
    contrapose! hn
    refine setIntegral_eq_zero_of_forall_eq_zero fun y my ↦ ?_
    simp only [defaultA, defaultD.eq_1, defaultκ.eq_1, mul_eq_zero, map_eq_zero, exp_ne_zero,
      or_false, indicator_apply_eq_zero]
    left
    exact hn _ (E_subset_𝓘 my)
  rw [mem_ball]
  calc
    _ ≤ dist y x + dist y (𝔠 p) := dist_triangle_left ..
    _ < D ^ 𝔰 p / 2 + 4 * (D : ℝ) ^ 𝔰 p :=
      add_lt_add_of_le_of_lt (dist_mem_Icc_of_Ks_ne_zero Ky).2 (mem_ball.mpr (Grid_subset_ball my))
    _ ≤ _ := by rw [div_eq_mul_inv, mul_comm, ← add_mul]; gcongr; norm_num

/-- Part 2 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support2 (hu : u ∈ t) (hp : p ∈ t u) : adjointCarleson p f =
    (𝓘 u : Set X).indicator (adjointCarleson p ((𝓘 u : Set X).indicator f)) := by
  rw [← adjoint_eq_adjoint_indicator (E_subset_𝓘.trans (t.smul_four_le hu hp).1.1),
    adjoint_tile_support1, indicator_indicator, ← right_eq_inter.mpr]
  exact (ball_subset_ball (by gcongr; norm_num)).trans (t.ball_subset hu hp)

lemma adjoint_tile_support2_sum (hu : u ∈ t) :
    adjointCarlesonSum (t u) f =
    (𝓘 u : Set X).indicator (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator f)) := by
  unfold adjointCarlesonSum
  classical
  calc
    _ = ∑ p with p ∈ t u,
        (𝓘 u : Set X).indicator (adjointCarleson p ((𝓘 u : Set X).indicator f)) := by
      ext x; simp only [Finset.sum_apply]; congr! 1 with p mp
      rw [Finset.mem_filter_univ] at mp; rw [adjoint_tile_support2 hu mp]
    _ = _ := by simp_rw [← Finset.indicator_sum, ← Finset.sum_apply]

/-- A partially applied variant of `adjoint_tile_support2_sum`, used to prove Lemma 7.7.3. -/
lemma adjoint_tile_support2_sum_partial (hu : u ∈ t) :
    adjointCarlesonSum (t u) f = (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator f)) := by
  unfold adjointCarlesonSum
  ext x; congr! 1 with p mp; classical rw [Finset.mem_filter_univ] at mp
  rw [← adjoint_eq_adjoint_indicator (E_subset_𝓘.trans (t.smul_four_le hu mp).1.1)]

lemma enorm_adjointCarleson_le {x : X} :
    ‖adjointCarleson p f x‖ₑ ≤
    C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
  calc
    _ ≤ ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y‖ₑ := by
      apply enorm_integral_le_lintegral_enorm
    _ = ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr! with y
      rw [enorm_mul, enorm_mul, ← ofReal_sub, enorm_exp_I_mul_ofReal, RCLike.enorm_conj, mul_one]
    _ ≤ C2_1_3 a * ∫⁻ y in E p, (volume (ball y (D ^ 𝔰 p)))⁻¹ * ‖f y‖ₑ := by
      rw [← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_mono fun y ↦ ?_
      rw [← mul_assoc, mul_comm _ _⁻¹, ← ENNReal.div_eq_inv_mul]
      exact mul_le_mul_left enorm_Ks_le _
    _ ≤ _ := by
      rw [mul_assoc _ (_ ^ _), mul_comm (_ ^ _), ← ENNReal.div_eq_inv_mul,
        ← ENNReal.inv_div (.inl (by simp)) (.inl (by simp)), mul_assoc, ← lintegral_const_mul' _⁻¹]
      swap
      · simp_rw [ne_eq, ENNReal.inv_eq_top, ENNReal.div_eq_zero_iff, ENNReal.pow_eq_top_iff,
          ENNReal.ofNat_ne_top, false_and, or_false]
        exact (measure_ball_pos _ _ (by unfold defaultD; positivity)).ne'
      refine mul_le_mul_right (setLIntegral_mono' measurableSet_E fun y my ↦ ?_) _
      exact mul_le_mul_left (ENNReal.inv_le_inv' (volume_xDsp_bound_4 (E_subset_𝓘 my))) _

lemma enorm_adjointCarleson_le_mul_indicator {x : X} :
    ‖adjointCarleson p f x‖ₑ ≤
    C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * (∫⁻ y in E p, ‖f y‖ₑ) *
      (ball (𝔠 p) (8 * D ^ 𝔰 p)).indicator 1 x := by
  rw [adjoint_tile_support1, enorm_indicator_eq_indicator_enorm]
  calc
    _ ≤ (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (fun _ ↦
        C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ *
          ∫⁻ y in E p, ‖(𝓘 p : Set X).indicator f y‖ₑ) x := by
      gcongr; exact enorm_adjointCarleson_le
    _ = C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * (∫⁻ y in E p, ‖f y‖ₑ) *
        (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator 1 x := by
      conv_lhs => enter [2, z]; rw [← mul_one (_ * _ * _ * _)]
      rw [indicator_const_mul]; congr 2
      refine setLIntegral_congr_fun measurableSet_E fun y my ↦ ?_
      rw [indicator_of_mem (E_subset_𝓘 my)]
    _ ≤ _ := by
      gcongr; norm_num

lemma adjoint_density_tree_bound1 (hf : BoundedCompactSupport f)
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖ₑ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  rw [← adjointCarlesonSum_adjoint hf hg]; exact density_tree_bound1 hf hg h2g hu

/-- Part 1 of Lemma 7.4.2. -/
lemma adjoint_tree_estimate
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    eLpNorm (adjointCarlesonSum (t u) g) 2 volume ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 volume := by
  by_cases h : eLpNorm (adjointCarlesonSum (t u) g) 2 = 0
  · rw [h]; exact zero_le
  have bcs : BoundedCompactSupport (adjointCarlesonSum (t u) g) := hg.adjointCarlesonSum
  rw [← ENNReal.mul_le_mul_iff_left h (bcs.memLp 2).eLpNorm_ne_top, ← sq,
    eLpNorm_two_eq_enorm_integral_mul_conj (bcs.memLp 2), mul_assoc _ (eLpNorm g 2 volume),
    mul_comm (eLpNorm g 2 volume), ← mul_assoc]
  conv_lhs => enter [1, 2, x]; rw [mul_comm]
  exact adjoint_density_tree_bound1 bcs hg h2g hu

lemma adjoint_density_tree_bound2
    (hf : BoundedCompactSupport f) (h2f : support f ⊆ F)
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖ₑ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  rw [← adjointCarlesonSum_adjoint hf hg]; exact density_tree_bound2 hf h2f hg h2g hu

/-- Part 2 of Lemma 7.4.2. -/
lemma indicator_adjoint_tree_estimate
    (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) (hu : u ∈ t) :
    eLpNorm (F.indicator (adjointCarlesonSum (t u) g)) 2 ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 := by
  by_cases h : eLpNorm (F.indicator (adjointCarlesonSum (t u) g)) 2 = 0
  · rw [h]; exact zero_le
  have bcs : BoundedCompactSupport (F.indicator (adjointCarlesonSum (t u) g)) :=
    hg.adjointCarlesonSum.indicator measurableSet_F
  rw [← ENNReal.mul_le_mul_iff_left h (bcs.memLp 2).eLpNorm_ne_top, ← sq,
    eLpNorm_two_eq_enorm_integral_mul_conj (bcs.memLp 2), mul_assoc _ (eLpNorm g 2 volume),
    mul_comm (eLpNorm g 2 volume), ← mul_assoc]
  calc
    _ = ‖∫ x, conj (adjointCarlesonSum (t u) g x) *
        F.indicator (adjointCarlesonSum (t u) g) x‖ₑ := by
      congr 2 with x; nth_rw 2 [indicator_eq_indicator_one_mul]
      rw [map_mul, conj_indicator, map_one, ← mul_assoc, mul_comm _ (F.indicator 1 x),
        ← indicator_eq_indicator_one_mul, indicator_indicator, inter_self, mul_comm]
    _ ≤ _ := adjoint_density_tree_bound2 bcs support_indicator_subset hg h2g hu

/-- The constant used in `adjoint_tree_control`.
Has value `2 ^ (182 * a ^ 3)` in the blueprint. -/
irreducible_def C7_4_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 7 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)

lemma le_C7_4_3 (ha : 4 ≤ a) : C7_3_1_1 a + CMB (defaultA a) 2 + 1 ≤ C7_4_3 a := by
  rw [C7_4_3, C7_3_1_1, CMB_defaultA_two_eq]
  calc
    _ ≤ (2 : ℝ≥0) ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)
        + 2 ^ ((a : ℝ) + 3 / 2) + 2 ^ ((a : ℝ) + 3 / 2) := by
      gcongr; exact NNReal.one_le_rpow one_le_two (by linarith)
    _ = 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)  + 2 ^ ((a : ℝ) + 5 / 2) := by
      rw [add_assoc, ← two_mul, ← NNReal.rpow_one_add' (by positivity)]; congr 2; ring
    _ ≤ 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)
        + 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4 : ℕ) * (a : ℝ) ^ 3) := by
      gcongr
      · exact one_le_two
      · calc
          _ ≤ 2 * (a : ℝ) := by
            rw [two_mul]; gcongr; exact (show (5 : ℝ) / 2 ≤ 4 by norm_num).trans (mod_cast ha)
          _ = 2 * a * 1 * 1 := by ring
          _ ≤ (𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4 : ℕ) * a * a * a := by
            gcongr
            · norm_cast
              have := seven_le_c
              lia
            · norm_cast; lia
            · norm_cast; lia
          _ = _ := by ring
    _ ≤ 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4 : ℕ) * (a : ℝ) ^ 3 + 1) := by
      rw [← NNReal.rpow_natCast]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
      rw [← mul_two, ← NNReal.rpow_add_one' (by positivity)]
    _ ≤ _ := by
      rw [← NNReal.rpow_natCast]; gcongr
      · exact one_le_two
      · norm_cast
        have : 1 ≤ a ^ 3 := one_le_pow_of_one_le' (by linarith) _
        grw [this]
        exact le_of_eq (by ring)

/-- Lemma 7.4.3. -/
lemma adjoint_tree_control
    (hu : u ∈ t) (hf : BoundedCompactSupport f) (h2f : f.support ⊆ G) :
    eLpNorm (adjointBoundaryOperator t u f ·) 2 volume ≤ C7_4_3 a * eLpNorm f 2 volume := by
  have m₁ : AEStronglyMeasurable (‖adjointCarlesonSum (t u) f ·‖ₑ) :=
    hf.aestronglyMeasurable.adjointCarlesonSum.enorm.aestronglyMeasurable
  have m₂ : AEStronglyMeasurable (maximalFunction volume 𝓑 c𝓑 r𝓑 1 f) :=
    measurable_maximalFunction.aestronglyMeasurable
  have m₃ : AEStronglyMeasurable (‖f ·‖ₑ) := hf.aestronglyMeasurable.enorm.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x ↦ ‖adjointCarlesonSum (t u) f x‖ₑ + maximalFunction volume 𝓑 c𝓑 r𝓑 1 f x) 2 volume +
        eLpNorm (‖f ·‖ₑ) 2 volume := eLpNorm_add_le (m₁.add m₂) m₃ one_le_two
    _ ≤ eLpNorm (‖adjointCarlesonSum (t u) f ·‖ₑ) 2 volume +
        eLpNorm (maximalFunction volume 𝓑 c𝓑 r𝓑 1 f ·) 2 volume + eLpNorm (‖f ·‖ₑ) 2 volume := by
      gcongr; apply eLpNorm_add_le m₁ m₂ one_le_two
    _ ≤ C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume +
        CMB (defaultA a) 2 * eLpNorm f 2 volume + eLpNorm f 2 volume := by
      gcongr
      · exact adjoint_tree_estimate hf h2f hu
      · exact (hasStrongType_maximalFunction_one one_lt_two) _ (hf.memLp _) |>.2
      · rfl
    _ ≤ (C7_3_1_1 a * 1 ^ (2 : ℝ)⁻¹ + CMB (defaultA a) 2 + 1) * eLpNorm f 2 volume := by
      simp_rw [add_mul, one_mul]; gcongr; exact dens₁_le_one
    _ ≤ _ := by
      gcongr
      simp only [ENNReal.one_rpow, mul_one, defaultA, Nat.cast_pow, Nat.cast_ofNat]
      norm_cast
      apply le_C7_4_3 (four_le_a X)

/-- Part 1 of Lemma 7.4.7. -/
lemma overlap_implies_distance (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₁ ∪ t u₂)
    (hpu₁ : ¬Disjoint (𝓘 p : Set X) (𝓘 u₁)) : p ∈ 𝔖₀ t u₁ u₂ := by
  simp_rw [𝔖₀, mem_setOf, hp, true_and]
  wlog plu₁ : 𝓘 p ≤ 𝓘 u₁ generalizing p
  · have u₁lp : 𝓘 u₁ ≤ 𝓘 p := (le_or_ge_or_disjoint.resolve_left plu₁).resolve_right hpu₁
    obtain ⟨p', mp'⟩ := t.nonempty hu₁
    have p'lu₁ : 𝓘 p' ≤ 𝓘 u₁ := (t.smul_four_le hu₁ mp').1
    obtain ⟨c, mc⟩ := (𝓘 p').nonempty
    specialize this (mem_union_left _ mp') (not_disjoint_iff.mpr ⟨c, mc, p'lu₁.1 mc⟩) p'lu₁
    exact this.trans (Grid.dist_mono (p'lu₁.trans u₁lp))
  have four_Z := four_le_Z (X := X)
  have four_le_Zn : 4 ≤ Z * (n + 1) := by rw [← mul_one 4]; exact mul_le_mul' four_Z (by lia)
  have four_le_two_pow_Zn : 4 ≤ 2 ^ (Z * (n + 1) - 1) := by
    change 2 ^ 2 ≤ _; exact Nat.pow_le_pow_right zero_lt_two (by lia)
  have ha : (2 : ℝ) ^ (Z * (n + 1)) - 4 ≥ 2 ^ (Z * n / 2 : ℝ) :=
    calc
      _ ≥ (2 : ℝ) ^ (Z * (n + 1)) - 2 ^ (Z * (n + 1) - 1) := by gcongr; norm_cast
      _ = 2 ^ (Z * (n + 1) - 1) := by
        rw [sub_eq_iff_eq_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by lia)]
      _ ≥ 2 ^ (Z * n) := by apply pow_le_pow_right₀ one_le_two; rw [mul_add_one]; lia
      _ ≥ _ := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le one_le_two; rw [Nat.cast_mul]
        exact half_le_self (by positivity)
  rcases hp with (c : p ∈ t.𝔗 u₁) | (c : p ∈ t.𝔗 u₂)
  · calc
    _ ≥ dist_(p) (𝒬 p) (𝒬 u₂) - dist_(p) (𝒬 p) (𝒬 u₁) := by
      change _ ≤ _; rw [sub_le_iff_le_add, add_comm]; exact dist_triangle ..
    _ ≥ 2 ^ (Z * (n + 1)) - 4 := by
      gcongr
      · exact (t.lt_dist' hu₂ hu₁ hu.symm c (plu₁.trans h2u)).le
      · have : 𝒬 u₁ ∈ ball_(p) (𝒬 p) 4 :=
          (t.smul_four_le hu₁ c).2 (by convert mem_ball_self zero_lt_one)
        exact (@mem_ball' _ (instPseudoMetricSpaceWithFunctionDistance (x := 𝔠 p) (r := ↑D ^ 𝔰 p / 4)) _ _ _).mp this |>.le
    _ ≥ _ := ha
  · calc
    _ ≥ dist_(p) (𝒬 p) (𝒬 u₁) - dist_(p) (𝒬 p) (𝒬 u₂) := by
      change _ ≤ _; rw [sub_le_iff_le_add, add_comm]; exact dist_triangle_right ..
    _ ≥ 2 ^ (Z * (n + 1)) - 4 := by
      gcongr
      · exact (t.lt_dist' hu₁ hu₂ hu c plu₁).le
      · have : 𝒬 u₂ ∈ ball_(p) (𝒬 p) 4 :=
          (t.smul_four_le hu₂ c).2 (by convert mem_ball_self zero_lt_one)
        exact (@mem_ball' _ (instPseudoMetricSpaceWithFunctionDistance (x := 𝔠 p) (r := ↑D ^ 𝔰 p / 4)) _ _ _).mp this |>.le
    _ ≥ _ := ha

/-- Part 2 of Lemma 7.4.7. -/
lemma 𝔗_subset_𝔖₀ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    t u₁ ⊆ 𝔖₀ t u₁ u₂ := fun p mp ↦ by
  apply overlap_implies_distance hu₁ hu₂ hu h2u (mem_union_left _ mp)
  obtain ⟨c, mc⟩ := (𝓘 p).nonempty
  exact not_disjoint_iff.mpr ⟨c, mc, (t.smul_four_le hu₁ mp).1.1 mc⟩

end TileStructure.Forest
