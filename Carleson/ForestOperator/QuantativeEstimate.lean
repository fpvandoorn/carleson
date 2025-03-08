import Carleson.ForestOperator.L2Estimate
import Carleson.ToMathlib.BoundedCompactSupport

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

/-! ## Section 7.3 and Lemma 7.3.1 -/

/-- The constant used in `local_dens1_tree_bound`.
Has value `2 ^ (101 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_2 (a : ℕ) : ℝ≥0 := 2 ^ (101 * (a : ℝ) ^ 3)

/-- Lemma 7.3.2. -/
lemma local_dens1_tree_bound (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) :
    volume (L ∩ G ∩ ⋃ (p ∈ t u), E p) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) := by
  sorry

/-- The constant used in `local_dens2_tree_bound`.
Has value `2 ^ (200 * a ^ 3 + 19)` in the blueprint, but that appears to be an error. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_3 (a : ℕ) : ℝ≥0 := 2 ^ (201 * (a : ℝ) ^ 3)

private lemma le_C7_3_3_exponent (ha : 4 ≤ a) (b : ℕ) (hb : b ≤ 16) :
    200 * a ^ 3 + b * a ≤ 201 * a ^ 3 := by
  nlinarith [pow_le_pow_left' ha 2]

-- Auxiliary result used to prove `local_dens2_tree_bound`
private lemma local_dens2_tree_bound_aux {p : 𝔓 X} (hpu : p ∈ t u) {r : ℝ}
    (hr : r ≥ 4 * (D : ℝ) ^ (𝔰 p)) (h₁ : (J : Set X) ⊆ ball (𝔠 p) r)
    (h₂ : volume (ball (𝔠 p) r) ≤ C7_3_3 a * volume (J : Set X)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  rw [mul_comm (C7_3_3 a : ℝ≥0∞), mul_assoc, ← ENNReal.div_le_iff]
  · apply le_trans <| ENNReal.div_le_div (measure_mono (inter_subset_inter_right F h₁)) h₂
    exact le_dens₂ (t u) hpu hr
  · refine mul_ne_zero ?_ (volume_coeGrid_pos (defaultD_pos' a)).ne.symm
    rw [C7_3_3]
    exact_mod_cast (pow_pos two_pos _).ne.symm
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (volume_coeGrid_lt_top).ne

-- Special case of `local_dens2_tree_bound_aux` which is used twice
private lemma local_dens2_tree_bound_aux' {p : 𝔓 X} (hpu : p ∈ t u)
    (h₁ : (J : Set X) ⊆ ball (𝔠 p) (4 * (D : ℝ) ^ (𝔰 p)))
    (h₂ : volume (𝓘 p : Set X) ≤ 2 ^ (200 * a ^ 3 + 10 * a) * volume (J : Set X)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  apply local_dens2_tree_bound_aux hpu (le_refl _) h₁
  rw [show 4 * (D : ℝ) ^ 𝔰 p = 2 ^ 4 * (D ^ 𝔰 p / 4) by ring]
  apply le_trans (measure_ball_two_le_same_iterate (𝔠 p) (D ^ 𝔰 p / 4) 4)
  apply le_trans <| mul_le_mul_left' ((measure_mono ball_subset_Grid).trans h₂) _
  simp_rw [defaultA, C7_3_3, ← mul_assoc]
  apply mul_le_mul_right'
  norm_cast
  rw [← pow_mul, ← pow_add]
  apply pow_le_pow_right' one_le_two
  exact le_of_eq_of_le (by ring) <| le_C7_3_3_exponent (four_le_a X) 14 (by norm_num)

/-- Lemma 7.3.3. -/
lemma local_dens2_tree_bound (hu : u ∈ t) (hJ : J ∈ 𝓙 (t u)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  by_cases J_top : J = topCube
  · have ⟨p, hpu⟩ := t.nonempty hu
    have S0 : S = 0 := S_eq_zero_of_topCube_mem_𝓙₀ (t.nonempty hu) (𝓙_subset_𝓙₀ (J_top ▸ hJ))
    have 𝓘p_eq_J : 𝓘 p = J := ((𝓘 p).eq_topCube_of_S_eq_zero S0).trans J_top.symm
    apply local_dens2_tree_bound_aux' hpu (𝓘p_eq_J ▸ Grid_subset_ball)
    exact 𝓘p_eq_J ▸ le_mul_of_one_le_left (zero_le _) (one_le_pow_of_one_le' one_le_two _)
  have ⟨J', hJJ', hsJ'⟩ := J.exists_scale_succ (J.scale_lt_scale_topCube J_top)
  have : J' ∉ 𝓙₀ (t u) := fun h ↦ succ_ne_self (s J) <| hJ.eq_of_le h hJJ' ▸ hsJ'.symm
  rw [𝓙₀, mem_setOf_eq] at this
  push_neg at this
  obtain ⟨p, hpu, hp⟩ := this.2
  have d0 := defaultD_pos a
  have volume_le : volume (ball (c J') (204 * D ^ (s J' + 1))) ≤
                     2 ^ (200 * a ^ 3 + 10 * a) * volume (J : Set X) := calc
    _ ≤ volume (ball (c J) ((204 * D + 4) * D ^ (s J'))) := by
      refine measure_mono <| ball_subset_ball' ?_
      rw [add_mul, mul_assoc, zpow_add₀ d0.ne.symm, mul_comm (D : ℝ), zpow_one]
      apply add_le_add_left (mem_ball'.mp <| Grid_subset_ball <| hJJ'.1 J.c_mem_Grid).le
    _ ≤ volume (ball (c J) (2 ^ (200 * a ^ 2 + 8) * D ^ (s J))) := by
      rw [hsJ', zpow_add₀ d0.ne.symm, mul_comm ((D : ℝ) ^ (s J)), ← mul_assoc, zpow_one]
      refine measure_mono (ball_subset_ball <| mul_le_mul_of_nonneg_right ?_ (zpow_pos d0 (s J)).le)
      calc
          _ ≤ 2 ^ 8 * (D : ℝ) ^ 2   := by nlinarith [one_lt_D (X := X)]
          _ = 2 ^ (200 * a ^ 2 + 8) := by norm_cast; rw [pow_add, defaultD, ← pow_mul]; ring_nf
    _ ≤ (defaultA a) ^ (200 * a ^ 2 + 10) * volume (ball (c J) (D ^ (s J) / 4)) := by
        rw [show 2 ^ (200 * a^2 + 8) * (D : ℝ) ^ s J = 2 ^ (200 * a^2 + 10) * (D ^ s J / 4) by ring]
        apply measure_ball_two_le_same_iterate
    _ ≤ 2 ^ (200 * a ^ 3 + 10 * a) * volume (J : Set X) := by
      apply le_of_le_of_eq <| mul_le_mul_left' (measure_mono ball_subset_Grid) _
      simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul, mul_comm a, add_mul, mul_assoc, show a ^ 2 * a = a ^ 3 by rfl]
  by_cases hJB : (J : Set X) ⊆ ball (𝔠 p) (4 * D ^ (𝔰 p))
  · refine local_dens2_tree_bound_aux' hpu hJB <| (measure_mono ?_).trans volume_le
    exact hp.trans <| ball_subset_ball (by gcongr; norm_num)
  have hcJ' : dist (c J') (𝔠 p) < 100 * (D : ℝ) ^ (s J' + 1) := by
    refine mem_ball'.mp <| hp <| ball_subset_Grid <| mem_ball.mpr ?_
    rw [𝔠, c, dist_self]
    positivity
  have hJp : (J : Set X) ⊆ ball (𝔠 p) (104 * D ^ (s J' + 1)) := by
    rw [show (104 : ℝ) = 4 + 100 by norm_num, add_mul]
    refine (hJJ'.1.trans Grid_subset_ball).trans <| ball_subset_ball' <| add_le_add ?_ hcJ'.le
    exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ one_le_D (Int.le.intro 1 rfl)) four_pos.le
  apply local_dens2_tree_bound_aux hpu (le_of_not_ge (hJB <| hJp.trans <| ball_subset_ball ·)) hJp
  have B_subset : ball (𝔠 p) (104 * D ^ (s J' + 1)) ⊆ ball (c J') (204 * D ^ (s J' + 1)) := by
    apply ball_subset_ball'
    rw [show (204 : ℝ) = 104 + 100 by norm_num, add_mul]
    exact add_le_add_left (dist_comm (c J') (𝔠 p) ▸ hcJ'.le) (104 * (D : ℝ) ^ (s J' + 1))
  refine (measure_mono B_subset).trans <| volume_le.trans <| mul_le_mul_right' ?_ _
  rw [C7_3_3]
  norm_cast
  exact pow_le_pow_right' one_le_two (le_C7_3_3_exponent (four_le_a X) 10 (by norm_num))

/-- The constant used in `density_tree_bound1`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint, but that was based on an incorrect
version of Lemma 7.2.1. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_1 (a : ℕ) : ℝ≥0 := 2 ^ (202.5 * (a : ℝ) ^ 3)

-- Main bound in the proof of Lemma 7.3.1
private lemma eLpNorm_approxOnCube_two_le {C : Set (Grid X)}
    (disj_C : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    {s : Set X} (hs : MeasurableSet s) {c : ℝ≥0∞}
    (hc : ∀ J ∈ C, volume (J ∩ s) ≤ c * volume (J : Set X))
    {f : X → ℂ} (hf : BoundedCompactSupport f) (h2f : ∀ x ∉ s, f x = 0) :
    eLpNorm (approxOnCube C (‖f ·‖)) 2 volume ≤ c ^ (2 : ℝ)⁻¹ * eLpNorm f 2 := by
  simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
    ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div, approxOnCube]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg_of_nonneg two_pos.le)]
  refine ENNReal.rpow_le_rpow ?_ (inv_pos.mpr two_pos).le
  have : ∀ x, ∑ J ∈ Finset.univ.filter (· ∈ C),
      (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x ≥ 0 := by
    intro x
    refine Finset.sum_nonneg (fun J hJ ↦ ?_)
    by_cases hx : x ∈ (J : Set X)
    · rw [indicator_of_mem hx]; exact integral_nonneg (fun _ ↦ by simp)
    · rw [indicator_of_not_mem hx]
  simp_rw [Real.enorm_eq_ofReal (this _)]
  calc
    _ = ∫⁻ x, (∑ J ∈ Finset.univ.filter (· ∈ C),
          ENNReal.ofReal ((J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x)) ^ 2 := by
      congr with x
      congr
      refine ENNReal.ofReal_sum_of_nonneg (fun J hJ ↦ ?_)
      rw [indicator]
      split_ifs
      · exact integral_nonneg (fun _ ↦ norm_nonneg _)
      · exact le_refl 0
    _ = ∫⁻ x, (∑ J ∈ Finset.univ.filter (· ∈ C),
          (J : Set X).indicator (fun _ ↦ ENNReal.ofReal (⨍ y in J, ‖f y‖)) x) ^ 2 := by
      congr with x
      congr with J
      by_cases hx : x ∈ (J : Set X) <;> simp [hx]
    _ = ∫⁻ x, ∑ J ∈ Finset.univ.filter (· ∈ C),
          (J : Set X).indicator (fun _ ↦ (ENNReal.ofReal (⨍ y in J, ‖f y‖)) ^ 2) x := by
      congr with x
      by_cases ex : ∃ J₀ ∈ Finset.univ.filter (· ∈ C), x ∈ (J₀ : Set X)
      · obtain ⟨J₀, hJ₀, hx⟩ := ex
        calc
          _ = ((J₀ : Set X).indicator (fun _ ↦ ENNReal.ofReal (⨍ y in J₀, ‖f y‖)) x) ^ 2 := by
            rw [Finset.sum_eq_single_of_mem _ hJ₀]
            intro J hJ J_ne_J₀
            have := disj_C (Finset.mem_filter.mp hJ).2 (Finset.mem_filter.mp hJ₀).2 J_ne_J₀
            exact indicator_of_not_mem (disjoint_right.mp this hx) _
          _ = (J₀ : Set X).indicator (fun _ ↦ ENNReal.ofReal (⨍ (y : X) in ↑J₀, ‖f y‖) ^ 2) x := by
            rw [indicator]
            split_ifs
            apply (indicator_of_mem hx _).symm
          _ = _ := by
            rw [Finset.sum_eq_single_of_mem _ hJ₀]
            intro J hJ J_ne_J₀
            have := disj_C (Finset.mem_filter.mp hJ).2 (Finset.mem_filter.mp hJ₀).2 J_ne_J₀
            apply indicator_of_not_mem (disjoint_right.mp this hx)
      · push_neg at ex
        rw [Finset.sum_eq_zero fun J h ↦ indicator_of_not_mem (ex J h) _, zero_pow two_pos.ne.symm]
        rw [Finset.sum_eq_zero fun J h ↦ indicator_of_not_mem (ex J h) _]
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C),
          ENNReal.ofReal (⨍ y in J, ‖f y‖) ^ 2 * volume (J : Set X) := by
      rw [lintegral_finset_sum _ (fun _ _ ↦ measurable_const.indicator coeGrid_measurable)]
      simp_rw [lintegral_indicator coeGrid_measurable, setLIntegral_const]
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ y in J, ‖f y‖ₑ) ^ 2 / volume (J : Set X) := by
      congr with J
      rw [ofReal_setAverage hf.norm.integrable.integrableOn (Eventually.of_forall (by simp)),
        div_eq_mul_inv, mul_pow, div_eq_mul_inv, mul_assoc]
      simp_rw [ofReal_norm_eq_enorm]
      by_cases hJ : volume (J : Set X) = 0
      · simp [setLIntegral_measure_zero _ _ hJ]
      congr
      rw [sq, mul_assoc, ENNReal.inv_mul_cancel hJ volume_coeGrid_lt_top.ne, mul_one]
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ y in J ∩ s, ‖f y‖ₑ * 1) ^ 2 / volume (J : Set X) := by
      congr with J
      congr 2
      rw [← lintegral_inter_add_diff _ (J : Set X) hs]
      suffices ∫⁻ x in J \ s, ‖f x‖ₑ = 0 by rw [this, add_zero]; simp_rw [mul_one]
      rw [setLIntegral_eq_zero_iff (coeGrid_measurable.diff hs) hf.stronglyMeasurable.enorm]
      exact Eventually.of_forall (fun x hx ↦ by rw [h2f x hx.2, enorm_zero])
    _ ≤ ∑ J ∈ Finset.univ.filter (· ∈ C),
          ((∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ y in J ∩ s, 1) ^ (1 / 2 : ℝ)) ^ 2 /
          volume (J : Set X) := by
      refine Finset.sum_le_sum fun J hJ ↦ ENNReal.div_le_div_right (pow_le_pow_left' ?_ 2) _
      simpa using ENNReal.lintegral_mul_le_Lp_mul_Lq (f := (‖f ·‖ₑ)) (g := 1)
        (volume.restrict (J ∩ s)) ((Real.isConjExponent_iff 2 2).mpr (by norm_num))
        hf.stronglyMeasurable.aemeasurable.enorm measurable_const.aemeasurable
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) ^ (1 / (2 : ℝ) * 2) *
          volume (J ∩ s) ^ (1 / (2 : ℝ) * 2) / volume (J : Set X) := by
      simp_rw [setLIntegral_one, mul_pow, ENNReal.rpow_mul]; norm_cast
    _ = ∑ J ∈ Finset.univ.filter (· ∈ C),
          (∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) * volume (J ∩ s) / volume (J : Set X) := by
      simp_rw [div_mul_cancel_of_invertible, ENNReal.rpow_one]
    _ ≤ ∑ J ∈ Finset.univ.filter (· ∈ C),
          (∫⁻ y in J ∩ s, ‖f y‖ₑ ^ 2) * (c * volume (J : Set X)) / volume (J : Set X) := by
      refine Finset.sum_le_sum fun J hJ ↦ ENNReal.div_le_div_right ?_ _
      exact mul_le_mul_left' (hc J (Finset.mem_filter.mp hJ).2) (∫⁻ (y : X) in ↑J ∩ s, ‖f y‖ₑ ^ 2)
    _ = c * ∑ J ∈ Finset.univ.filter (· ∈ C), (∫⁻ (y : X) in J ∩ s, ‖f y‖ₑ ^ 2) := by
      simp_rw [mul_div_assoc,
        ENNReal.div_self ((volume_coeGrid_pos (defaultD_pos' a)).ne.symm) volume_coeGrid_lt_top.ne]
      rw [mul_one, ← Finset.sum_mul, mul_comm]
    _ ≤ _ := by
      rw [← setLIntegral_univ]
      have h : (GridStructure.coeGrid · ∩ s) ≤ GridStructure.coeGrid := fun _ ↦ inter_subset_left
      have hC : C = (Finset.univ.filter (· ∈ C) : Set (Grid X)) := by simp
      rw [← lintegral_biUnion_finset (hC ▸ disj_C.mono h) (fun _ _ ↦ coeGrid_measurable.inter hs)]
      exact mul_left_mono <| lintegral_mono_set (subset_univ _)

-- Generalization that implies both parts of Lemma 7.3.1
private lemma density_tree_bound_aux
    (hf : BoundedCompactSupport f)
    {c : ℝ≥0∞} (hc : eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume ≤ c * eLpNorm f 2 volume)
    (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * c * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  let ℰ := ⋃ p ∈ t u, E p
  have hgℰ : BoundedCompactSupport (ℰ.indicator g) :=
    hg.indicator ((t u).toFinite.measurableSet_biUnion (fun _ _ ↦ measurableSet_E))
  calc
    _ = ‖∫ x, conj (ℰ.indicator g x) * carlesonSum (t u) f x‖ₑ := by
      congr with x
      by_cases hx : x ∈ ℰ
      · rw [indicator_of_mem hx]
      suffices carlesonSum (t u) f x = 0 by simp [hx, this]
      refine Finset.sum_eq_zero (fun p hp ↦ indicator_of_not_mem (fun hxp ↦ ?_) _)
      exact hx ⟨E p, ⟨p, by simp [Finset.mem_filter.mp hp]⟩, hxp⟩
    _ ≤ _ := tree_projection_estimate hf hgℰ hu
    _ ≤ (C7_2_1 a) * (c * eLpNorm f 2 volume) *
          (2 ^ (50.5 * (a : ℝ) ^ 3) * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 volume) := by
      refine mul_le_mul' (mul_le_mul_left' hc (C7_2_1 a)) ?_
      have hgℰ' : ∀ x ∉ G ∩ ℰ, ℰ.indicator g x = 0 := by
        intro x hx
        rw [mem_inter_iff] at hx
        push_neg at hx
        by_cases xG : x ∈ G
        · apply indicator_of_not_mem (hx xG)
        · have : g x = 0 := by rw [← norm_le_zero_iff]; simpa [xG] using h2g x
          exact indicator_apply_eq_zero.mpr (fun _ ↦ this)
      have hℰ : MeasurableSet (G ∩ ℰ) :=
        measurableSet_G.inter <| .biUnion (to_countable (t u)) (fun _ _ ↦ measurableSet_E)
      have : ∀ L ∈ 𝓛 (t u), volume (L ∩ (G ∩ ℰ)) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) :=
        fun L ↦ inter_assoc L G ℰ ▸ local_dens1_tree_bound hu
      apply le_trans <| eLpNorm_approxOnCube_two_le pairwiseDisjoint_𝓛 hℰ this hgℰ hgℰ'
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg_of_nonneg two_pos.le)]
      refine mul_le_mul' (mul_le_mul_right' ?_ _) ?_
      · rw [C7_3_2, ENNReal.rpow_ofNNReal (inv_nonneg_of_nonneg two_pos.le)]
        rw [← NNReal.rpow_mul 2 (101 * a ^ 3) 2⁻¹, ← ENNReal.rpow_ofNNReal (by positivity)]
        apply le_of_eq
        congr 1
        ring
      · refine eLpNorm_mono (fun x ↦ ?_)
        rw [indicator]
        split_ifs <;> simp
    _ = C7_2_1 a * 2 ^ ((50.5 : ℝ) * a ^ 3) * dens₁ ((fun x ↦ t.𝔗 x) u) ^ (2 : ℝ)⁻¹ * c *
          eLpNorm f 2 volume * eLpNorm g 2 volume := by ring
    _ = _ := by
      rw [C7_2_1, C7_3_1_1]
      repeat rw [← ENNReal.rpow_ofNNReal (by positivity), ENNReal.coe_ofNat]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
      ring_nf

/-- First part of Lemma 7.3.1. -/
lemma density_tree_bound1
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hc : eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume ≤ 1 * eLpNorm f 2 volume := by
    have : ∀ L ∈ 𝓙 (t u), volume ((L : Set X) ∩ univ) ≤ 1 * volume (L : Set X) := by intros; simp
    apply le_of_le_of_eq <| eLpNorm_approxOnCube_two_le pairwiseDisjoint_𝓙 .univ this hf (by tauto)
    rw [ENNReal.one_rpow]
  simpa using density_tree_bound_aux hf hc hg h2g hu


/-- The constant used in `density_tree_bound2`.
Has value `2 ^ (256 * a ^ 3)` in the blueprint, but that was based on an incorrect
version of Lemma 7.2.1. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (303 * (a : ℝ) ^ 3)

/-- Second part of Lemma 7.3.1. -/
lemma density_tree_bound2
    (hf : BoundedCompactSupport f)
    (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have hc : eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume ≤
      (C7_3_3 a * dens₂ (t u)) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    have h2f : ∀ x ∉ F, f x = 0 := fun x hx ↦ norm_le_zero_iff.mp <| (h2f x).trans (by simp [hx])
    have : ∀ J ∈ 𝓙 (t u), volume (J ∩ F) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) :=
      fun J hJ ↦ by rw [inter_comm]; apply local_dens2_tree_bound hu hJ
    exact eLpNorm_approxOnCube_two_le pairwiseDisjoint_𝓙 measurableSet_F this hf h2f
  apply le_of_le_of_eq (density_tree_bound_aux hf hc hg h2g hu)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_pos_of_pos two_pos).le]
  calc
    _ = (C7_3_1_1 a) * (C7_3_3 a) ^ (2 : ℝ)⁻¹ * dens₁ ((fun x ↦ t.𝔗 x) u) ^ (2 : ℝ)⁻¹ *
          dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by ring
    _ = _ := by
      rw [C7_3_1_1, C7_3_1_2, C7_3_3, ENNReal.rpow_ofNNReal (inv_pos.mpr two_pos).le,
        ← ENNReal.coe_mul, ← NNReal.rpow_mul, ← NNReal.rpow_add two_pos.ne.symm,
        ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_rpow_of_nonneg _ (by positivity)]
      ring_nf

end TileStructure.Forest
