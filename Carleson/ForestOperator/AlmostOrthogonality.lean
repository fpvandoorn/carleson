import Carleson.ForestOperator.QuantativeEstimate
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

/-! ## Section 7.4 except Lemmas 4-6 -/

/-- The definition of `Tₚ*g(x)`, defined above Lemma 7.4.1 -/
def adjointCarleson (p : 𝔓 X) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in E p, conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y
  -- todo: consider changing to `(E p).indicator 1 y`

/-- The definition of `T_ℭ*g(x)`, defined at the bottom of Section 7.4 -/
def adjointCarlesonSum (ℭ : Set (𝔓 X)) (f : X → ℂ) (x : X) : ℂ :=
  ∑ p ∈ {p | p ∈ ℭ}, adjointCarleson p f x

variable (t) in
/-- The operator `S_{2,𝔲} f(x)`, given above Lemma 7.4.3. -/
def adjointBoundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ‖adjointCarlesonSum (t u) f x‖₊ + MB volume 𝓑 c𝓑 r𝓑 f x + ‖f x‖₊

variable (t u₁ u₂) in
/-- The set `𝔖` defined in the proof of Lemma 7.4.4.
We append a subscript 0 to distinguish it from the section variable. -/
def 𝔖₀ : Set (𝔓 X) := { p ∈ t u₁ ∪ t u₂ | 2 ^ ((Z : ℝ) * n / 2) ≤ dist_(p) (𝒬 u₁) (𝒬 u₂) }

lemma _root_.MeasureTheory.StronglyMeasurable.adjointCarleson (hf : StronglyMeasurable f) :
    StronglyMeasurable (adjointCarleson p f) := by
  refine .integral_prod_right'
    (f := fun z ↦ conj (Ks (𝔰 p) z.2 z.1) * exp (Complex.I * (Q z.2 z.2 - Q z.2 z.1)) * f z.2) ?_
  refine .mul (.mul ?_ ?_) ?_
  · exact Complex.continuous_conj.comp_stronglyMeasurable (stronglyMeasurable_Ks.prod_swap)
  · refine Complex.continuous_exp.comp_stronglyMeasurable (.const_mul (.sub ?_ ?_) _)
    · exact Measurable.stronglyMeasurable (by fun_prop)
    · refine continuous_ofReal.comp_stronglyMeasurable ?_
      exact stronglyMeasurable_Q₂ (X := X) |>.prod_swap
  · exact hf.snd

lemma _root_.MeasureTheory.AEStronglyMeasurable.adjointCarleson (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (adjointCarleson p f) := by
  refine .integral_prod_right'
    (f := fun z ↦ conj (Ks (𝔰 p) z.2 z.1) * exp (Complex.I * (Q z.2 z.2 - Q z.2 z.1)) * f z.2) ?_
  refine .mono_ac (.prod .rfl restrict_absolutelyContinuous) ?_
  refine .mul (.mul ?_ ?_) ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable (aestronglyMeasurable_Ks.prod_swap)
  · refine Complex.continuous_exp.comp_aestronglyMeasurable (.const_mul (.sub ?_ ?_) _)
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · refine continuous_ofReal.comp_aestronglyMeasurable ?_
      exact aestronglyMeasurable_Q₂ (X := X) |>.prod_swap
  · exact hf.snd

lemma _root_.MeasureTheory.StronglyMeasurable.adjointCarlesonSum {ℭ : Set (𝔓 X)}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (adjointCarlesonSum ℭ f) :=
  Finset.stronglyMeasurable_sum _ fun _ _ ↦ hf.adjointCarleson

lemma _root_.MeasureTheory.AEStronglyMeasurable.adjointCarlesonSum {ℭ : Set (𝔓 X)}
    (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (adjointCarlesonSum ℭ f) :=
  Finset.aestronglyMeasurable_sum _ fun _ _ ↦ hf.adjointCarleson

lemma adjoint_eq_adjoint_indicator (h : E p ⊆ 𝓘 u) :
    adjointCarleson p f = adjointCarleson p ((𝓘 u : Set X).indicator f) := by
  ext x; refine setIntegral_congr_fun measurableSet_E (fun y my ↦ ?_); congr
  exact (indicator_of_mem (h my) f).symm

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
    simp [hn _ (E_subset_𝓘 my)]
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

theorem _root_.MeasureTheory.BoundedCompactSupport.adjointCarleson
    (hf : BoundedCompactSupport f) : BoundedCompactSupport (adjointCarleson p f) where
  stronglyMeasurable := hf.stronglyMeasurable.adjointCarleson
  isBounded := by
    obtain ⟨CKf, hCKf, hCKf⟩ := hf.hasCompactSupport.isBounded.exists_bound_of_norm_Ks (𝔰 p)
    let C : ℝ := CKf * (eLpNorm f ⊤).toReal * volume.real (E p)
    apply isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
    refine norm_setIntegral_le_of_norm_le_const_ae ?_ ?_
    · exact volume_E_lt_top
    · apply ae_restrict_of_ae
      filter_upwards [hf.ae_le] with y hy
      suffices ‖Ks (𝔰 p) y x‖ * ‖f y‖ ≤ ?C by
        calc
          _ ≤ ‖conj (Ks (𝔰 p) y x) * cexp (I * (↑((Q y) y) - ↑((Q y) x)))‖ * ‖f y‖ :=
            norm_mul_le ..
          _ ≤ ‖conj (Ks (𝔰 p) y x)‖ * 1 * ‖f y‖ := by
            gcongr; convert norm_mul_le _ _; exact (norm_exp_I_mul_sub_ofReal ..).symm
          _ = ‖Ks (𝔰 p) y x‖ * ‖f y‖ := by rw [mul_one, RCLike.norm_conj]
          _ ≤ _ := by convert this
      by_cases hy : y ∈ tsupport f
      · specialize hCKf y x hy; gcongr
      · simp only [norm_eq_abs, image_eq_zero_of_nmem_tsupport hy,
          norm_zero, mul_zero, eLpNorm_exponent_top]; positivity
  hasCompactSupport := by
    obtain x₀ : X := Classical.choice (by infer_instance)
    obtain ⟨r₀, h⟩ := hf.isBoundedSupport.subset_ball x₀
    let C : ℝ := (↑D ^ 𝔰 p / 2) + r₀
    suffices support (TileStructure.Forest.adjointCarleson p f) ⊆ closedBall x₀ C from
      HasCompactSupport.of_support_subset_closedBall this
    intro x hx
    apply mem_support.mp at hx
    have : ∃ y, conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y ≠ 0 := by
      -- mathlib lemma: if integral ne zero, then integrand ne zero at a point
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hx <| setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ hc x
    simp only [ne_eq, mul_eq_zero, map_eq_zero, exp_ne_zero, or_false, not_or] at this
    obtain ⟨y, hKy, hfy⟩ := this
    change _ ≤ C
    apply (dist_triangle _ y _).trans
    unfold C
    gcongr
    · rw [dist_comm]; exact (dist_mem_Icc_of_Ks_ne_zero hKy).2
    · exact le_of_lt <| h hfy

theorem _root_.MeasureTheory.BoundedCompactSupport.adjointCarlesonSum {ℭ : Set (𝔓 X)}
    (hf : BoundedCompactSupport f) : BoundedCompactSupport (adjointCarlesonSum ℭ f) :=
  BoundedCompactSupport.finset_sum fun _ _ ↦ hf.adjointCarleson

/-- `MKD` is short for "modulated kernel times dilated bump". -/
private abbrev MKD (s:ℤ) x y := exp (.I * (Q x y - Q x x)) * K x y * ψ (D ^ (-s) * dist x y)

omit [TileStructure Q D κ S o] in
private lemma norm_MKD_le_norm_Ks {s:ℤ} {x y : X} : ‖MKD s x y‖ ≤ ‖Ks s x y‖ := by
  unfold MKD; rw [mul_assoc, ← Ks_def]
  apply (norm_mul_le ..).trans
  apply le_of_eq
  rw [norm_exp_I_mul_sub_ofReal, one_mul]

/-- `adjointCarleson` is the adjoint of `carlesonOn`. -/
lemma adjointCarleson_adjoint
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (p : 𝔓 X) :
    ∫ x, conj (g x) * carlesonOn p f x = ∫ y, conj (adjointCarleson p g y) * f y := by
  let H := fun x ↦ fun y ↦ conj (g x) * (E p).indicator 1 x * MKD (𝔰 p) x y * f y
  have hH : Integrable (uncurry H) := by
    let H₀ := fun x y ↦ ‖g x‖ * ‖f y‖
    obtain ⟨M₀, hM₀nn, hM₀⟩ := hg.hasCompactSupport.isBounded.exists_bound_of_norm_Ks (𝔰 p)
    have hHleH₀ x y : ‖H x y‖ ≤ M₀ * ‖g x‖ * ‖f y‖ := by
      by_cases h : x ∈ tsupport g
      · specialize hM₀ x y h
        calc
          _ ≤ ‖conj (g x) * (E p).indicator 1 x * MKD (𝔰 p) x y‖ * ‖f y‖ := norm_mul_le ..
          _ ≤ ‖conj (g x) * (E p).indicator 1 x‖ * ‖MKD (𝔰 p) x y‖ * ‖f y‖ := by
            gcongr; exact norm_mul_le ..
          _ ≤ ‖conj (g x)‖ * ‖(E p).indicator 1 x‖ * ‖MKD (𝔰 p) x y‖ * ‖f y‖ := by
            gcongr; exact norm_mul_le ..
          _ ≤ ‖g x‖ * 1 * ‖MKD (𝔰 p) x y‖ * ‖f y‖ := by
            gcongr
            · exact le_of_eq <| RCLike.norm_conj _
            · exact norm_indicator_one_le ..
          _ = ‖MKD (𝔰 p) x y‖ * (‖g x‖ * ‖f y‖) := by rw [mul_one, mul_comm ‖g _‖, mul_assoc]
          _ ≤ M₀ *  (‖g x‖ * ‖f y‖) := by gcongr; exact norm_MKD_le_norm_Ks.trans hM₀
          _ = M₀ *  ‖g x‖ * ‖f y‖ := by rw [mul_assoc]
      · suffices hz : H x y = 0 by rw [hz]; simp only [norm_zero, ge_iff_le]; positivity
        unfold H; simp [image_eq_zero_of_nmem_tsupport h]
    have : Integrable (fun z : X × X ↦ M₀ *  ‖g z.1‖ * ‖f z.2‖) :=
      Integrable.prod_mul (hg.norm.const_mul _).integrable hf.norm.integrable
    refine this.mono ?_ ?_
    · refine .mul ?_ <| .snd hf.aestronglyMeasurable
      refine .mul ?_ ?_
      · refine .mul ?_ ?_
        · exact RCLike.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable.fst
        · have : AEStronglyMeasurable (fun x:X ↦ (E p).indicator (1:X→ℂ) x) :=
            .indicator aestronglyMeasurable_const measurableSet_E
          exact this.fst
      · unfold MKD
        simp_rw [mul_assoc, ← Ks_def]
        refine .mul ?_ aestronglyMeasurable_Ks
        apply Measurable.aestronglyMeasurable
        have : Measurable fun (p : X × X) ↦ (p.1, p.1) :=
          .prod_mk (.fst measurable_id') (.fst measurable_id')
        refine ((Measurable.sub ?_ ?_).const_mul I).cexp <;> apply measurable_ofReal.comp
        · exact measurable_Q₂
        · exact measurable_Q₂.comp this
    · apply ae_of_all
      intro z
      refine trans (hHleH₀ z.1 z.2) ?_
      exact Real.le_norm_self _
  calc
    _ = ∫ x, conj (g x) * ∫ y, (E p).indicator 1 x * MKD (𝔰 p) x y * f y := by
      conv =>
        enter [1, 2, x, 2]; unfold carlesonOn
        rw [indicator_eq_indicator_one_mul, ← integral_mul_left]
        enter [2, y]; rw [← mul_assoc]
    _ = ∫ x, ∫ y, H x y := by unfold H; simp_rw [← integral_mul_left, mul_assoc]
    _ = ∫ y, ∫ x, H x y := integral_integral_swap hH
    _ = ∫ y, (∫ x, conj (g x) * (E p).indicator 1 x * MKD (𝔰 p) x y) * f y := by
      simp_rw [H, integral_mul_right]
    _ = ∫ y, conj (∫ x, g x * (E p).indicator 1 x * conj (MKD (𝔰 p) x y)) * f y := by
      simp_rw [← integral_conj]; congrm (∫ _, (∫ _, ?_) * (f _))
      rw [map_mul, conj_conj, map_mul, conj_indicator, map_one]
    _ = _ := by
      congr; funext y; congrm (conj ?_) * (f _)
      calc
        _ = ∫ x, (E p).indicator 1 x * g x * conj (MKD (𝔰 p) x y) := by
          congr; funext x; rw [mul_comm (g x) _]
        _ = ∫ x, (E p).indicator (fun x ↦ g x * conj (MKD (𝔰 p) x y)) x := by
          congr; funext x; simp only [indicator]; split_ifs <;> simp
        _ = ∫ x in E p, g x * conj (MKD (𝔰 p) x y) := integral_indicator measurableSet_E
        _ = ∫ x in E p, conj (MKD (𝔰 p) x y) * g x := by congr; funext; rw [mul_comm]
        _ = _ := by
          unfold adjointCarleson MKD
          congr; funext; rw [mul_assoc, ← Ks_def, map_mul, ← exp_conj, mul_comm (cexp _)]
          congr; simp; ring

/-- `adjointCarlesonSum` is the adjoint of `carlesonSum`. -/
lemma adjointCarlesonSum_adjoint
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (ℭ : Set (𝔓 X)) :
    ∫ x, conj (g x) * carlesonSum ℭ f x = ∫ x, conj (adjointCarlesonSum ℭ g x) * f x := by
  calc
    _ = ∫ x, ∑ p ∈ {p | p ∈ ℭ}, conj (g x) * carlesonOn p f x := by
      unfold carlesonSum; simp_rw [Finset.mul_sum]
    _ = ∑ p ∈ {p | p ∈ ℭ}, ∫ x, conj (g x) * carlesonOn p f x := by
      apply integral_finset_sum; intro p _
      refine hg.conj.mul hf.carlesonOn |>.integrable
    _ = ∑ p ∈ {p | p ∈ ℭ}, ∫ y, conj (adjointCarleson p g y) * f y := by
      simp_rw [adjointCarleson_adjoint hf hg]
    _ = ∫ y, ∑ p ∈ {p | p ∈ ℭ}, conj (adjointCarleson p g y) * f y := by
      symm; apply integral_finset_sum; intro p _
      refine BoundedCompactSupport.mul ?_ hf |>.integrable
      exact hg.adjointCarleson.conj
    _ = _ := by congr!; rw [← Finset.sum_mul, ← map_sum]; rfl

/-- The constant used in `adjoint_tree_estimate`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
irreducible_def C7_4_2 (a : ℕ) : ℝ≥0 := C7_3_1_1 a

-- unfortunate technicality
lemma _root_._aux_L2NormSq {X : Type*} [MeasureSpace X] {f : X → ℂ}
    (hf : Memℒp f 2): ↑‖∫ x, ofReal (normSq (f x))‖₊ = (eLpNorm f 2)^2 := by
  rw [show ∫ x, ofReal (normSq (f x)) = ofReal (∫ x, normSq (f x)) by exact integral_ofReal]
  rw [nnnorm_real]
  have hnn: 0 ≤ ∫ x, normSq (f x) := by-- todo: adjust `positivity` to handle this
    refine integral_nonneg ?_
    refine Pi.le_def.mpr ?_
    exact fun _ ↦ normSq_nonneg _
  rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal hnn]
  rw [hf.eLpNorm_eq_integral_rpow_norm (NeZero.ne 2) ENNReal.ofNat_ne_top]
  rw [← ENNReal.rpow_natCast, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by simp)]
  rw [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  suffices ∫ x, normSq (f x) = ((∫ x, ‖f x‖ ^ 2) ^ ((2:ℝ)⁻¹)) ^ (2:ℝ) by
    simp_rw [← Real.rpow_two] at this; rw [this]
  have h : ∫ x, normSq (f x) = ∫ x, ‖f x‖ ^ 2 := by congr!; exact normSq_eq_norm_sq _
  rw [← Real.rpow_mul ?_, IsUnit.inv_mul_cancel (by simp), Real.rpow_one]
  · exact h
  · rw [← h]; exact hnn

/-- Lemma 7.4.2. -/
lemma adjoint_tree_estimate (hu : u ∈ t) (hf : BoundedCompactSupport f) :
    eLpNorm (adjointCarlesonSum (t u) f) 2 volume ≤
    C7_4_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  rw [C7_4_2_def]
  set g := adjointCarlesonSum (t u) f
  have hg : BoundedCompactSupport g := hf.adjointCarlesonSum
  have h := density_tree_bound1 hg hf hu
  simp_rw [adjointCarlesonSum_adjoint hg hf] at h
  have : ‖∫ x, conj (adjointCarlesonSum (t u) f x) * g x‖₊ =
      (eLpNorm g 2 volume)^2 := by
    simp_rw [mul_comm, g, Complex.mul_conj]; exact _aux_L2NormSq <| hg.memℒp 2
  rw [this, pow_two, mul_assoc, mul_comm _ (eLpNorm f _ _), ← mul_assoc] at h
  by_cases hgz : eLpNorm g 2 volume = 0
  · simp [hgz]
  · refine ENNReal.mul_le_mul_right hgz ?_ |>.mp h
    exact (hg.memℒp 2).eLpNorm_ne_top

/-- The constant used in `adjoint_tree_control`.
Has value `2 ^ (156 * a ^ 3)` in the blueprint. -/
irreducible_def C7_4_3 (a : ℕ) : ℝ≥0 :=
  C7_4_2 a + CMB (defaultA a) 2 + 1

/-- Lemma 7.4.3. -/
lemma adjoint_tree_control (hu : u ∈ t) (hf : BoundedCompactSupport f) :
    eLpNorm (adjointBoundaryOperator t u f · |>.toReal) 2 volume ≤
    C7_4_3 a * eLpNorm f 2 volume := by
  calc _ ≤ eLpNorm (adjointBoundaryOperator t u f · |>.toReal) 2 volume := by rfl
  _ ≤ eLpNorm
    ((‖adjointCarlesonSum (t u) f ·‖) + (MB volume 𝓑 c𝓑 r𝓑 f · |>.toReal) + (‖f ·‖))
    2 volume := by
      refine MeasureTheory.eLpNorm_mono_real fun x ↦ ?_
      simp_rw [Real.norm_eq_abs, ENNReal.abs_toReal, Pi.add_apply]
      refine ENNReal.toReal_add_le.trans ?_
      gcongr
      · exact ENNReal.toReal_add_le
      · rfl
  _ ≤ eLpNorm (‖adjointCarlesonSum (t u) f ·‖) 2 volume +
    eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f · |>.toReal) 2 volume +
    eLpNorm (‖f ·‖) 2 volume := by
      refine eLpNorm_add_le ?_ ?_ one_le_two |>.trans ?_
      · exact hf.aestronglyMeasurable.adjointCarlesonSum.norm.add
          <| .maximalFunction_toReal 𝓑_finite.countable
      · exact hf.aestronglyMeasurable.norm
      gcongr
      refine eLpNorm_add_le ?_ ?_ one_le_two |>.trans ?_
      · exact hf.aestronglyMeasurable.adjointCarlesonSum.norm
      · exact .maximalFunction_toReal 𝓑_finite.countable
      rfl
  _ ≤ eLpNorm (adjointCarlesonSum (t u) f) 2 volume +
    eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f · |>.toReal) 2 volume +
    eLpNorm f 2 volume := by simp_rw [eLpNorm_norm]; rfl
  _ ≤ C7_4_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume +
    CMB (defaultA a) 2 * eLpNorm f 2 volume +
    eLpNorm f 2 volume := by
      gcongr
      · exact adjoint_tree_estimate hu hf
      · exact (hasStrongType_MB_finite 𝓑_finite one_lt_two).toReal _ (hf.memℒp _) |>.2
  _ ≤ (C7_4_2 a * (1 : ℝ≥0∞) ^ (2 : ℝ)⁻¹ + CMB (defaultA a) 2 + 1) * eLpNorm f 2 volume := by
    simp_rw [add_mul]
    gcongr
    · exact dens₁_le_one
    · simp only [ENNReal.coe_one, one_mul, le_refl]
  _ ≤ C7_4_3 a * eLpNorm f 2 volume := by
    simp_rw [C7_4_3, ENNReal.coe_add, ENNReal.one_rpow, mul_one, ENNReal.coe_one]
    with_reducible rfl

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
  have four_le_Zn : 4 ≤ Z * (n + 1) := by rw [← mul_one 4]; exact mul_le_mul' four_Z (by omega)
  have four_le_two_pow_Zn : 4 ≤ 2 ^ (Z * (n + 1) - 1) := by
    change 2 ^ 2 ≤ _; exact Nat.pow_le_pow_right zero_lt_two (by omega)
  have ha : (2 : ℝ) ^ (Z * (n + 1)) - 4 ≥ 2 ^ (Z * n / 2 : ℝ) :=
    calc
      _ ≥ (2 : ℝ) ^ (Z * (n + 1)) - 2 ^ (Z * (n + 1) - 1) := by gcongr; norm_cast
      _ = 2 ^ (Z * (n + 1) - 1) := by
        rw [sub_eq_iff_eq_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]
      _ ≥ 2 ^ (Z * n) := by apply pow_le_pow_right₀ one_le_two; rw [mul_add_one]; omega
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
        rw [@mem_ball'] at this; exact this.le
    _ ≥ _ := ha
  · calc
    _ ≥ dist_(p) (𝒬 p) (𝒬 u₁) - dist_(p) (𝒬 p) (𝒬 u₂) := by
      change _ ≤ _; rw [sub_le_iff_le_add, add_comm]; exact dist_triangle_right ..
    _ ≥ 2 ^ (Z * (n + 1)) - 4 := by
      gcongr
      · exact (t.lt_dist' hu₁ hu₂ hu c plu₁).le
      · have : 𝒬 u₂ ∈ ball_(p) (𝒬 p) 4 :=
          (t.smul_four_le hu₂ c).2 (by convert mem_ball_self zero_lt_one)
        rw [@mem_ball'] at this; exact this.le
    _ ≥ _ := ha

/-- Part 2 of Lemma 7.4.7. -/
lemma 𝔗_subset_𝔖₀ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    t u₁ ⊆ 𝔖₀ t u₁ u₂ := fun p mp ↦ by
  apply overlap_implies_distance hu₁ hu₂ hu h2u (mem_union_left _ mp)
  obtain ⟨c, mc⟩ := (𝓘 p).nonempty
  exact not_disjoint_iff.mpr ⟨c, mc, (t.smul_four_le hu₁ mp).1.1 mc⟩

end TileStructure.Forest
