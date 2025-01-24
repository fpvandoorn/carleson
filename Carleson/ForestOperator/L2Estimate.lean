import Carleson.ForestOperator.PointwiseEstimate
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.ENorm

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

lemma CMB_defaultA_two_eq {a : ℕ} : CMB (defaultA a) 2 = 2 ^ (a + (3 / 2 : ℝ)) := by
  suffices (2 : ℝ≥0) * 2 ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal |2 - 1|⁻¹).toNNReal ^ (2 : ℝ)⁻¹ *
      ((2 ^ a) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ = 2 ^ (a + 3 / (2 : ℝ)) by
    simpa [CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  rw [← NNReal.rpow_mul, show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
  repeat rw [NNReal.rpow_add two_ne_zero]
  norm_num
  ring

namespace TileStructure.Forest

lemma eLpNorm_MB_le {𝕜 : Type*} [RCLike 𝕜] {f : X → 𝕜} (hf : BoundedCompactSupport f) :
    eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume ≤ (CMB (defaultA a) 2) * eLpNorm f 2 volume := by
  have : HasStrongType (fun (u : X → 𝕜) ↦ (MB volume 𝓑 c𝓑 r𝓑 u · |>.toReal)) 2 2 _ _ _ :=
    hasStrongType_MB_finite 𝓑_finite one_lt_two
  convert this f (hf.memℒp 2) |>.2 using 1
  congr
  ext
  rw [ENNReal.nnorm_toReal]
  refine ENNReal.coe_toNNReal (ne_of_lt ?_) |>.symm
  exact lt_of_le_of_lt MB_le_eLpNormEssSup (hf.memℒp ⊤).2

/-! ## Section 7.2 and Lemma 7.2.1 -/

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (103 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_2 (a : ℕ) : ℝ≥0 := 2 ^ (102 * (a : ℝ) ^ 3)

private def annulus_oo (x : X) (r R : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Ioo r R}
private def annulus_oc (x : X) (r R : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Ioc r R}
private def annulus_co (x : X) (r R : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Ico r R}
private def annulus_cc (x : X) (r R : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Icc r R}
private def annulus_ci (x : X) (r : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Ici r}
private abbrev annulus_oo' (x : X) (r R : ℝ) := annulus_oo x (ENNReal.ofReal r) (ENNReal.ofReal R)
private abbrev annulus_oc' (x : X) (r R : ℝ) := annulus_oc x (ENNReal.ofReal r) (ENNReal.ofReal R)
private abbrev annulus_co' (x : X) (r R : ℝ) := annulus_co x (ENNReal.ofReal r) (ENNReal.ofReal R)
private abbrev annulus_cc' (x : X) (r R : ℝ) := annulus_cc x (ENNReal.ofReal r) (ENNReal.ofReal R)

--private lemma annulus_ci_top (x : X) : annulus_ci x ⊤ = ∅ := by simp [annulus_ci]

private lemma annulus_oc_subset_cc_self (x : X) (r R : ℝ≥0∞) :
    annulus_oc x r R ⊆ annulus_cc x r R := by
  rw [annulus_oc, annulus_cc, setOf_subset_setOf]; intro; apply Ioc_subset_Icc_self

private lemma annulus_co_subset_cc_self (x : X) (r R : ℝ≥0∞) :
    annulus_co x r R ⊆ annulus_cc x r R := by
  rw [annulus_co, annulus_cc, setOf_subset_setOf]; intro; apply Ico_subset_Icc_self

private lemma annulus_oc_union_oo (x : X) {r r' R : ℝ≥0∞} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulus_oc x r r' ∪ annulus_oo x r' R = annulus_oo x r R := by
  ext y
  simp_rw [annulus_oc, annulus_oo, mem_union, mem_setOf_eq, ← mem_union, Ioc_union_Ioo_eq_Ioo h₁ h₂]

private lemma annulus_oc_union_oc (x : X) {r r' R : ℝ≥0∞} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulus_oc x r r' ∪ annulus_oc x r' R = annulus_oc x r R := by
  ext y
  simp_rw [annulus_oc, mem_union, mem_setOf_eq, ← mem_union, Ioc_union_Ioc_eq_Ioc h₁ h₂]

/- private lemma annulus_oo_subset_union_oc_oc_oo (x : X) {r₀ r₁ r₂ r₃ : ℝ≥0∞} :
    annulus_oo x r₀ r₃ ⊆ annulus_oc x r₀ r₁ ∪ annulus_oc x r₁ r₂ ∪ annulus_oo x r₂ r₃ := by
  intro y hy
  rw [annulus_oo, mem_setOf_eq, mem_Ioo] at hy
  by_cases i1 : ENNReal.ofReal (dist x y) ≤ r₁
  · left; left; exact ⟨hy.1, i1⟩
  · by_cases i2 : ENNReal.ofReal (dist x y) ≤ r₂
    · left; right; exact ⟨lt_of_not_ge i1, i2⟩
    · right; exact ⟨lt_of_not_ge i2, hy.2⟩ -/

private lemma annulus_oo'_eq (x : X) (r R : ℝ) (hr : r ≥ 0) :
    annulus_oo' x r R = {y | dist x y ∈ Ioo r R} := by
  simp [annulus_oo, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

-- The assumption `0 ≤ R` could be removed, but that's not necessary for now.
private lemma annulus_oc'_eq (x : X) (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    annulus_oc' x r R = {y | dist x y ∈ Ioc r R} := by
  simp [annulus_oc, ENNReal.ofReal_le_ofReal_iff hR,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr]

-- The assumption `0 ≤ R` could be removed, but that's not necessary for now.
private lemma annulus_cc'_eq (x : X) (r R : ℝ) (hR : 0 ≤ R) :
    annulus_cc' x r R = {y | dist x y ∈ Icc r R} := by
  simp [annulus_cc, ENNReal.ofReal_le_ofReal_iff hR,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]

omit [TileStructure Q D κ S o] in
lemma integrableOn_K_mul_f (x' : X) (hf : BoundedCompactSupport f) (r : ℝ≥0∞) (hr : 0 < r) :
    IntegrableOn (fun y ↦ K x' y * f y) (annulus_ci x' r) := by
  by_cases supp_f : (support f).Nonempty; swap
  · simp [Function.support_eq_empty_iff.mp <| Set.not_nonempty_iff_eq_empty.mp supp_f]
  by_cases r_inf : r = ⊤
  · simp [r_inf, annulus_ci]
  have ⟨x'', hx''⟩ := supp_f
  have ⟨C, hC⟩ := Metric.isBounded_iff.mp hf.isBoundedSupport
  specialize hC hx''
  have : support (fun y ↦ f y * K x' y) ⊆ closedBall x' (dist x' x'' + C) := by
    intro y hy
    rw [mem_closedBall']
    have : y ∈ support f := by contrapose! hy; simp [hy]
    exact (dist_triangle x' x'' y).trans <| add_le_add_left (hC this) _
  simp_rw [mul_comm (K x' _)]
  unfold IntegrableOn
  rw [← integrableOn_iff_integrable_of_support_subset this]
  unfold IntegrableOn
  rw [Measure.restrict_restrict]
  · apply hf.integrable_mul
    have := integrableOn_K_Icc (K := K) x' (ENNReal.toReal r) (dist x' x'' + C)
      (ENNReal.toReal_pos hr.ne.symm r_inf)
    unfold IntegrableOn at this
    convert this using 2
    ext y
    simp [inter_comm (closedBall _ _), dist_comm y, annulus_ci,
      ENNReal.le_ofReal_iff_toReal_le r_inf dist_nonneg]
  · exact measurableSet_closedBall

-- Truncated version of `K` used in proof of `nontangential_pointwise_bound`
private def K' (b : ℤ) (c : ℤ) (x y : X) := ∑ i ∈ (Icc b c).toFinset, Ks i x y

omit [TileStructure Q D κ S o] in
private lemma K'_eq_K (b : ℤ) (c : ℤ) (x y : X)
    (h : dist x y ∈ Icc ((D : ℝ) ^ (b - 1) / 2) (D ^ c / 4)) : K' b c x y = K x y := by
  have hxy : dist x y > 0 := lt_of_lt_of_le (div_pos (defaultD_pow_pos a (b - 1)) two_pos) h.1
  simp_rw [K', Ks, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [← finsum_eq_sum_of_support_subset, finsum_ψ (one_lt_D (X := X)) hxy, ofReal_one, mul_one]
  intro i hi
  simp only [support_ψS (one_lt_D (X := X)) hxy, nonzeroS, Finset.coe_Icc, mem_Icc] at hi
  simp only [toFinset_Icc, Finset.coe_Icc, mem_Icc]
  refine ⟨le_trans ?_ hi.1, le_trans hi.2 ?_⟩
  · rw [← Nat.cast_one, Int.floor_nat_add, Nat.cast_one, ← sub_le_iff_le_add', Int.le_floor,
      Real.le_logb_iff_rpow_le (one_lt_D (X := X)) (mul_pos two_pos hxy), mul_comm]
    exact_mod_cast (div_le_iff₀ two_pos).mp h.1
  · rw [Int.ceil_le, Real.logb_le_iff_le_rpow (one_lt_D (X := X)) (mul_pos four_pos hxy), mul_comm]
    exact_mod_cast (le_div_iff₀ four_pos).mp h.2

omit [TileStructure Q D κ S o] in
private lemma integrableOn_K'_mul_f (x' : X) (hf : BoundedCompactSupport f) (r : ℝ≥0∞) (hr : 0 < r)
    (s₁ s₂ : ℤ) : IntegrableOn (fun y ↦ K' s₁ s₂ x' y * f y) (annulus_ci x' r) := by
  unfold K' Ks
  simp_rw [mul_comm (K x' _) (ψ _), ← Finset.sum_mul, mul_assoc]
  apply Integrable.bdd_mul (integrableOn_K_mul_f x' hf r hr)
  · refine (Finset.aestronglyMeasurable_sum _ (fun i hi ↦ ?_)).restrict
    apply continuous_ofReal.comp_aestronglyMeasurable ∘ continuous_ψ.comp_aestronglyMeasurable
    exact (continuous_const.dist continuous_id').aestronglyMeasurable.const_mul _
  · refine ⟨(s₂ + 1 - s₁).toNat, fun _ ↦ le_trans (norm_sum_le ..) ?_⟩
    simp_rw [norm_eq_abs, abs_ofReal]
    exact le_of_le_of_eq (Finset.sum_le_sum fun _ _ ↦ abs_ψ_le_one _ _) (by simp)

/- omit [TileStructure Q D κ S o] in
private lemma _root_.integrableOn_K_mul_f_ennreal (hf : BoundedCompactSupport f) (r : ℝ≥0∞)
    (hr : r > 0) : IntegrableOn (fun y ↦ K x' y * f y) (annulus_ci x' r) := by
  exact integrableOn_K_mul_f hf r hr -/

private lemma annulus_oo_eq_of_lt_top (x : X) {r R : ℝ≥0∞} (hr : r < ⊤) (hR : R < ⊤) :
    annulus_oo x r R = ball x (ENNReal.toReal R) ∩ (closedBall x (ENNReal.toReal r))ᶜ := by
  ext y
  simp [annulus_oo, dist_comm, and_comm, ENNReal.lt_ofReal_iff_toReal_lt hr.ne (b := dist x y),
    ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg hR.ne]

private lemma annulus_oc_eq_of_lt_top (x : X) {r R : ℝ≥0∞} (hr : r < ⊤) (hR : R < ⊤) :
    annulus_oc x r R = closedBall x (ENNReal.toReal R) ∩ (closedBall x (ENNReal.toReal r))ᶜ := by
  ext y
  simp [annulus_oc, dist_comm, and_comm, ENNReal.lt_ofReal_iff_toReal_lt hr.ne (b := dist x y),
    ENNReal.ofReal_le_iff_le_toReal hR.ne]

private lemma annulus_co_eq_of_lt_top (x : X) {r R : ℝ≥0∞} (hr : r < ⊤) (hR : R < ⊤) :
    annulus_co x r R = ball x (ENNReal.toReal R) ∩ (ball x (ENNReal.toReal r))ᶜ := by
  ext y
  simp [annulus_co, dist_comm, and_comm, ENNReal.le_ofReal_iff_toReal_le hr.ne dist_nonneg,
    ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg hR.ne]

private lemma annulus_cc_eq_of_lt_top (x : X) {r R : ℝ≥0∞} (hr : r < ⊤) (hR : R < ⊤) :
    annulus_cc x r R = closedBall x (ENNReal.toReal R) ∩ (ball x (ENNReal.toReal r))ᶜ := by
  ext y
  simp [annulus_cc, dist_comm, and_comm, ENNReal.le_ofReal_iff_toReal_le hr.ne dist_nonneg,
    ENNReal.ofReal_le_iff_le_toReal hR.ne]

private lemma annulus_oo_eq_of_top (x : X) {r : ℝ≥0∞} (hr : r < ⊤) :
    annulus_oo x r ⊤ = (closedBall x (ENNReal.toReal r))ᶜ := by
  ext; simpa [annulus_oo, dist_comm] using ENNReal.lt_ofReal_iff_toReal_lt hr.ne

private lemma annulus_oc_eq_of_top (x : X) {r : ℝ≥0∞} (hr : r < ⊤) :
    annulus_oc x r ⊤ = (closedBall x (ENNReal.toReal r))ᶜ := by
  ext; simpa [annulus_oc, dist_comm] using ENNReal.lt_ofReal_iff_toReal_lt hr.ne

private lemma annulus_co_eq_of_top (x : X) {r : ℝ≥0∞} (hr : r < ⊤) :
    annulus_co x r ⊤ = (ball x (ENNReal.toReal r))ᶜ := by
  ext; simpa [annulus_co, dist_comm] using ENNReal.le_ofReal_iff_toReal_le hr.ne dist_nonneg

private lemma annulus_cc_eq_of_top (x : X) {r : ℝ≥0∞} (hr : r < ⊤) :
    annulus_cc x r ⊤ = (ball x (ENNReal.toReal r))ᶜ := by
  ext; simpa [annulus_cc, dist_comm] using ENNReal.le_ofReal_iff_toReal_le hr.ne dist_nonneg

-- Generalize these to `r ≥ R`?
private lemma annulus_oo_empty (x : X) (R : ℝ≥0∞) : annulus_oo x ⊤ R = ∅ := by simp [annulus_oo]
private lemma annulus_oc_empty (x : X) (R : ℝ≥0∞) : annulus_oc x ⊤ R = ∅ := by simp [annulus_oc]
private lemma annulus_co_empty (x : X) (R : ℝ≥0∞) : annulus_co x ⊤ R = ∅ := by simp [annulus_co]
private lemma annulus_cc_empty (x : X) (R : ℝ≥0∞) : annulus_cc x ⊤ R = ∅ := by simp [annulus_cc]

private lemma annulus_oc_subset_oo (x : X) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₃ : r₃ ≤ r₁) (h₂₄ : r₂ < r₄) :
    annulus_oc x r₁ r₂ ⊆ annulus_oo x r₃ r₄ := by
  intro
  simp only [annulus_oc, mem_setOf_eq, annulus_oo]
  apply subset_trans (Ioc_subset_Ioc h₁₃ (le_refl r₂)) (Ioc_subset_Ioo_right h₂₄)

private lemma annulus_oo_subset_oo (x : X) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₃ : r₃ ≤ r₁) (h₂₄ : r₂ ≤ r₄) :
    annulus_oo x r₁ r₂ ⊆ annulus_oo x r₃ r₄ := by
  intro
  simp only [mem_setOf_eq, annulus_oo]
  apply Ioo_subset_Ioo h₁₃ h₂₄

private lemma annulus_oo_subset_cc (x : X) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₃ : r₃ ≤ r₁) (h₂₄ : r₂ ≤ r₄) :
    annulus_oo x r₁ r₂ ⊆ annulus_cc x r₃ r₄ := by
  intro
  simp only [mem_setOf_eq, annulus_oo, annulus_cc, mem_Ioo, mem_Icc]
  intro ⟨hr₁, hr₂⟩
  exact ⟨h₁₃.trans hr₁.le, hr₂.le.trans h₂₄⟩

/- private lemma annulus_oo_subset_co (x : X) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₃ : r₃ ≤ r₁) (h₂₄ : r₂ ≤ r₄) :
    annulus_oo x r₁ r₂ ⊆ annulus_co x r₃ r₄ := by
  apply (annulus_oo_subset_oo x h₁₃ h₂₄).trans
  intro y
  simp only [mem_setOf_eq, annulus_oo, annulus_co]
  apply Ioo_subset_Ico_self -/

private lemma annulus_co_subset_oo (x : X) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₃ : r₃ < r₁) (h₂₄ : r₂ ≤ r₄) :
    annulus_co x r₁ r₂ ⊆ annulus_oo x r₃ r₄ := by
  intro y
  simp only [mem_setOf_eq, annulus_oo, annulus_co]
  apply subset_trans (Ico_subset_Ioo_left h₁₃) (Ioo_subset_Ioo_right h₂₄)

private lemma annulus_oo_subset_ci (x : X) {r₁ R r₂ : ℝ≥0∞} (h : r₁ ≥ r₂) :
    annulus_oo x r₁ R ⊆ annulus_ci x r₂ := by
  intro
  simp only [annulus_oo, mem_setOf_eq, annulus_ci, and_imp, mem_Ioo, mem_Ici]
  intro hr₁ _
  exact h.trans hr₁.le

private lemma annulus_cc_subset_ci (x : X) {r₁ R r₂ : ℝ≥0∞} (h : r₁ ≥ r₂) :
    annulus_cc x r₁ R ⊆ annulus_ci x r₂ := by
  intro
  simp only [annulus_cc, mem_setOf_eq, annulus_ci, and_imp, mem_Icc, mem_Ici]
  intro hr₁ _
  exact h.trans hr₁

private lemma annulus_cc_subset_cc (x : X) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₃ : r₁ ≥ r₃) (h₂₄ : r₂ ≤ r₄) :
    annulus_cc x r₁ r₂ ⊆ annulus_cc x r₃ r₄ := by
  intro
  simp only [annulus_cc, mem_setOf_eq, and_imp, mem_Icc]
  intro hr₁ hr₂
  exact ⟨h₁₃.trans hr₁, hr₂.trans h₂₄⟩

omit [TileStructure Q D κ S o] in
@[measurability]
private lemma measurableSet_annulus_oo {x : X} {r R : ℝ≥0∞} : MeasurableSet (annulus_oo x r R) := by
  by_cases hr : r = ⊤
  · simp [hr, annulus_oo_empty x R]
  replace hr : r < ⊤ := Ne.lt_top' fun h ↦ hr h.symm
  by_cases hR : R = ⊤
  · simp [hR, annulus_oo_eq_of_top x hr, measurableSet_closedBall]
  rw [annulus_oo_eq_of_lt_top x hr (Ne.lt_top' fun h ↦ hR h.symm)]
  measurability

omit [TileStructure Q D κ S o] in
@[measurability]
private lemma measurableSet_annulus_oc {x : X} {r R : ℝ≥0∞} : MeasurableSet (annulus_oc x r R) := by
  by_cases hr : r = ⊤
  · simp [hr, annulus_oc_empty x R]
  replace hr : r < ⊤ := Ne.lt_top' fun h ↦ hr h.symm
  by_cases hR : R = ⊤
  · simp [hR, annulus_oc_eq_of_top x hr, measurableSet_closedBall]
  rw [annulus_oc_eq_of_lt_top x hr (Ne.lt_top' fun h ↦ hR h.symm)]
  measurability

omit [TileStructure Q D κ S o] in
@[measurability]
private lemma measurableSet_annulus_co {x : X} {r R : ℝ≥0∞} : MeasurableSet (annulus_co x r R) := by
  by_cases hr : r = ⊤
  · simp [hr, annulus_co_empty x R]
  replace hr : r < ⊤ := Ne.lt_top' fun h ↦ hr h.symm
  by_cases hR : R = ⊤
  · simp [hR, annulus_co_eq_of_top x hr, measurableSet_ball]
  rw [annulus_co_eq_of_lt_top x hr (Ne.lt_top' fun h ↦ hR h.symm)]
  measurability

omit [TileStructure Q D κ S o] in
@[measurability]
private lemma measurableSet_annulus_cc {x : X} {r R : ℝ≥0∞} : MeasurableSet (annulus_cc x r R) := by
  by_cases hr : r = ⊤
  · simp [hr, annulus_cc_empty x R]
  replace hr : r < ⊤ := Ne.lt_top' fun h ↦ hr h.symm
  by_cases hR : R = ⊤
  · simp [hR, annulus_cc_eq_of_top x hr, measurableSet_ball]
  rw [annulus_cc_eq_of_lt_top x hr (Ne.lt_top' fun h ↦ hR h.symm)]
  measurability

-- Bound needed for proof of `nontangential_pointwise_bound`
omit [TileStructure Q D κ S o] in
private lemma annulus_integral_bound (x : X) (g : X → ℂ) {r₁ r₂ r₃ r₄ : ℝ≥0∞} (h₁₂ : r₁ < r₂)
    (h₃₄ : r₃ < r₄) (hg : IntegrableOn g (annulus_cc x r₁ r₄)) :
    ‖∫ y in annulus_cc x r₁ r₄, g y‖ₑ ≤ ‖∫ y in annulus_oo x r₂ r₃, g y‖ₑ +
    ((∫⁻ y in annulus_cc x r₁ r₂, ‖g y‖ₑ) + ∫⁻ y in annulus_cc x r₃ r₄, ‖g y‖ₑ) := calc
  _ = ‖(∫ y in annulus_cc x r₁ r₄ ∩ annulus_oo x r₂ r₃, g y) +
        ∫ y in annulus_cc x r₁ r₄ ∩ (annulus_oo x r₂ r₃)ᶜ, g y‖ₑ := by
    apply congrArg (‖·‖ₑ)
    rw [← setIntegral_union (Set.disjoint_left.mpr (fun _ h₁ h₂ ↦ h₂.2 h₁.2)) (by measurability),
        inter_union_compl] <;>
      exact hg.mono_set inter_subset_left
  _ ≤ ‖∫ y in annulus_cc x r₁ r₄ ∩ annulus_oo x r₂ r₃, g y‖ₑ +
        ‖∫ y in annulus_cc x r₁ r₄ ∩ (annulus_oo x r₂ r₃)ᶜ, g y‖ₑ := by apply enorm_add_le
  _ ≤ _ := by
    gcongr
    · rw [inter_eq_self_of_subset_right <| annulus_oo_subset_cc x h₁₂.le h₃₄.le]
    · calc
        _ ≤ _ := ennnorm_integral_le_lintegral_ennnorm _
        _ ≤ ∫⁻ y in annulus_cc x r₁ r₂ ∪ annulus_cc x r₃ r₄, ‖g y‖ₑ := by
          apply lintegral_mono_set
          intro y
          simp only [annulus_oo, annulus_cc, mem_Ioo, mem_Icc, mem_inter_iff,
            mem_setOf_eq, mem_compl_iff, not_and, not_le, mem_union, and_imp]
          intro hr₁ hr₄ hr₂₃
          by_cases hr₂ : r₂ < ENNReal.ofReal (dist x y)
          · exact Or.inr ⟨le_of_not_gt (hr₂₃ hr₂), hr₄⟩
          · apply Or.inl ⟨hr₁, le_of_not_gt hr₂⟩
        _ ≤ _ := lintegral_union_le _ _ _




/- -- Bound for (7.2.3) in the proof of `nontangential_pointwise_bound`
private lemma nontangential_integral_bound₁ (hf : BoundedCompactSupport f) (θ : Θ X) {x x' : X}
    {I : Grid X} (hx : x ∈ I) (hx' : x' ∈ I) {s₂ : ℤ}
    (hs₂ : ENNReal.ofReal (D ^ (s₂ - 1)) ≤ upperRadius Q θ x') :
    ‖∫ y in annulus_oc' x' (8 * (D : ℝ) ^ s I) (D ^ (s₂ - 1) / 4), K x' y * f y‖ₑ ≤
    2 * linearizedNontangentialOperator Q θ K f x := by
  by_cases R₁_le_R₂ : ENNReal.ofReal (8 * (D : ℝ) ^ (s I)) ≤ ENNReal.ofReal (D ^ (s₂ - 1) / 4); swap
  · simp [-defaultD, annulus_oc, Set.Ioc_eq_empty (fun h ↦ R₁_le_R₂ h.le)]
  have int_Kf : IntegrableOn (K x' * f) (annulus_ci x' (ENNReal.ofReal (8 * D ^ s I))) volume := by
    refine integrableOn_K_mul_f x' hf _ (ENNReal.ofReal_pos.mpr ?_)
    exact mul_pos (by norm_num) (defaultD_pow_pos a (s I))
  have D0 : (D : ℝ) ≠ 0 := (defaultD_pos a).ne.symm
  have R₂_lt_upperRadius : ENNReal.ofReal ((D : ℝ) ^ (s₂ - 1) / 4) < upperRadius Q θ x' :=
    have := defaultD_pow_pos a (s₂ - 1)
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff this).mpr (by linarith)) hs₂
  have dist_le : dist x x' ≤ 8 * (D : ℝ) ^ s I := by
    apply le_trans (dist_triangle x (c I) x')
    replace hx := mem_ball.mp (Grid_subset_ball hx)
    replace hx' := mem_ball'.mp (Grid_subset_ball hx')
    convert (add_lt_add hx hx').le using 1
    unfold s
    ring
  calc
    _ = ‖(∫ y in annulus_oo x' (ENNReal.ofReal (8 * D ^ s I)) (upperRadius Q θ x'), K x' y * f y) -
          ∫ y in annulus_oo x' (ENNReal.ofReal (D ^ (s₂ - 1) / 4)) (upperRadius Q θ x'),
            K x' y * f y‖ₑ := by
      congr
      apply eq_sub_of_add_eq
      rw [← setIntegral_union]
      · congr
        ext y
        simp_rw [annulus_oo, annulus_oc', annulus_oc, mem_union, mem_setOf_eq]
        rw [← mem_union, Set.Ioc_union_Ioo_eq_Ioo R₁_le_R₂ R₂_lt_upperRadius]
      · rw [Set.disjoint_iff]
        intro y ⟨⟨_, hy₁⟩, ⟨hy₂, _⟩⟩
        exact (lt_self_iff_false _).mp (lt_of_lt_of_le hy₂ hy₁)
      · apply measurableSet_annulus_oo
      · apply int_Kf.mono_set
        intro y hy
        simp only [annulus_ci, mem_Ioc, mem_setOf_eq, mem_Ici] at hy ⊢
        exact hy.1.le
      · apply int_Kf.mono_set
        intro y hy
        simp only [annulus_ci, mem_Ioo, mem_setOf_eq, mem_Ici] at hy ⊢
        exact R₁_le_R₂.trans hy.1.le
    _ ≤ ‖∫ y in annulus_oo x' (ENNReal.ofReal (8 * D ^ s I)) (upperRadius Q θ x'), K x' y * f y‖ₑ +
          ‖∫ y in annulus_oo x' (ENNReal.ofReal (D ^ (s₂ - 1) / 4)) (upperRadius Q θ x'),
            K x' y * f y‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add]
      apply ENNReal.coe_mono (nnnorm_sub_le _ _)
    _ ≤ 2 * linearizedNontangentialOperator Q θ K f x := by
      rw [two_mul, annulus_oo, annulus_oo]
      gcongr
      · refine le_trans ?_ <| le_iSup _ (8 * (D : ℝ) ^ s I)
        refine le_trans ?_ <| le_iSup _ x'
        simp [-defaultD, dist_le, enorm_eq_nnnorm]
      · refine le_trans ?_ <| le_iSup _ ((D : ℝ) ^ (s₂ - 1) / 4)
        refine le_trans ?_ <| le_iSup _ x'
        simp [-defaultD, enorm_eq_nnnorm,
          dist_le.trans <| (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp R₁_le_R₂] -/

-- Preliminary version of `nontangential_pointwise_bound₁` for `annulus_oo'`
omit [TileStructure Q D κ S o] in
private lemma nontangential_integral_bound₁ {x x' : X} {r : ℝ} (R : ℝ) (hr : dist x x' ≤ r) :
    ‖∫ y in annulus_oo' x' r R, K x' y * f y‖ₑ ≤
    nontangentialOperator K f x := by
  by_cases R₁_lt_R₂ : ENNReal.ofReal r < ENNReal.ofReal R; swap
  · simp [-defaultD, annulus_oo, Set.Ioo_eq_empty R₁_lt_R₂]
  have : r ≥ 0 := le_trans dist_nonneg hr
  refine le_trans ?_ <| le_iSup _ r
  refine le_trans ?_ <| le_iSup _ R
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at R₁_lt_R₂
  rw [iSup_pos R₁_lt_R₂]
  refine le_of_eq_of_le ?_ <| le_iSup _ x'
  rw [iSup_pos hr, annulus_oo'_eq _ _ _ (by positivity)]
  rfl

/- -- Bound for (7.2.3) in the proof of `nontangential_pointwise_bound`
private lemma nontangential_integral_bound₁ (hf : BoundedCompactSupport f) {x x' : X}
    {I : Grid X} (hx : x ∈ I) (hx' : x' ∈ I) (s₂ : ℤ) :
    ‖∫ y in annulus_co' x' (8 * (D : ℝ) ^ s I) (D ^ (s₂ - 1) / 4), K x' y * f y‖ₑ ≤
    nontangentialOperator K f x := by
  let t (n : ℕ) : Set X := annulus_oo' x' ((8 - 1 / (n + 1)) * (D : ℝ) ^ s I) (D ^ (s₂ - 1) / 4)
  have lb_pos (n : ℕ) : 0 < 8 - 1 / ((n : ℝ) + 1) := calc
    8 - 1 / ((n : ℝ) + 1) ≥ 8 - 1 / (0 + 1) := by gcongr; exact Nat.cast_nonneg' n
    _                     > 0               := by norm_num
  have t_inter : ⋂ (n : ℕ), t n = annulus_co' x' (8 * (D : ℝ) ^ s I) (D ^ (s₂ - 1) / 4) := by
    refine subset_antisymm (fun y hy ↦ ?_) (Set.subset_iInter fun n ↦ ?_)
    · refine ⟨ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_, mem_iInter.mp hy 0 |>.2⟩
      have lt : NNReal.toReal r < 8 * D ^ s I := by
        have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ENNReal.ofReal_ne_top).mpr hr
        rwa [ENNReal.toReal_ofReal (by positivity)] at this
      have ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos (sub_pos_of_lt lt) (defaultD_pow_pos a (s I)))
      rw [lt_div_iff₀ (defaultD_pow_pos a (s I))] at hn
      refine (lt_of_le_of_lt ?_ (mem_iInter.mp hy n).1).le
      have r_le : (r : ℝ) ≤ (8 - 1 / (n + 1)) * D ^ (s I) := by nlinarith
      rwa [ENNReal.ofReal_eq_coe_nnreal, ENNReal.coe_strictMono.le_iff_le]
      exact mul_nonneg (lb_pos n).le (defaultD_pow_pos a (s I)).le
    · apply annulus_co_subset_oo x' ?_ (le_refl _)
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg]
      · linarith [mul_pos (Nat.one_div_pos_of_nat (n := n)) (defaultD_pow_pos a (s I))]
      · exact mul_nonneg (lb_pos n).le (defaultD_pow_pos a (s I)).le
  have h_anti : Antitone t := fun _ _ _ ↦ annulus_oo_subset_oo x' (by gcongr) (le_refl _)
  have meas_t : ∀ (n : ℕ), MeasurableSet (t n) := by intro n; measurability
  have int : IntegrableOn (fun y ↦ K x' y * f y) (t 0) := by
    refine (integrableOn_K_mul_f x' hf
      (ENNReal.ofReal ((8 - 1 / ((0 : ℝ) + 1)) * (D : ℝ) ^ s I)) ?_).mono_set ?_
    · exact ENNReal.ofReal_pos.mpr <| mul_pos (by norm_num) (defaultD_pow_pos a (s I))
    · exact annulus_oo_subset_ci x' (by norm_num)
  have : Tendsto (fun i ↦ ‖∫ (a : X) in t i, K x' a * f a‖ₑ) atTop
      (nhds ‖∫ (a : X) in ⋂ n, t n, K x' a * f a‖ₑ) :=
    Filter.Tendsto.comp (continuous_enorm.tendsto _) (h_anti.tendsto_setIntegral meas_t int)
  rw [← t_inter]
  have dist_lt : dist x x' < 8 * (D : ℝ) ^ (s I) := by
    apply lt_of_le_of_lt (dist_triangle x (c I) x')
    replace hx := mem_ball.mp (Grid_subset_ball hx)
    replace hx' := mem_ball'.mp (Grid_subset_ball hx')
    apply lt_of_lt_of_eq (add_lt_add hx hx')
    unfold s
    ring
  have ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos (sub_pos_of_lt dist_lt) (defaultD_pow_pos a (s I)))
  refine le_of_tendsto this (Filter.eventually_atTop.mpr ⟨N, fun m hm ↦ ?_⟩)
  apply nontangential_integral_bound₁_oo
  rw [sub_mul]
  rw [lt_div_iff₀ (defaultD_pow_pos a (s I))] at hN
  have : dist x x' ≤ 8 * (D : ℝ) ^ s I - 1 / ((N : ℝ) + 1) * D ^ s I := by linarith
  apply this.trans
  gcongr -/

-- Bound for (7.2.4) and (7.2.5) in the proof of `nontangential_pointwise_bound`
private lemma nontangential_integral_bound₂ (hf : BoundedCompactSupport f) {x x' : X}
    {I : Grid X} (hx : x ∈ I) (hx' : x' ∈ I) {R : ℝ} (h : R ≤ 8 * D ^ (s I)) :
    ∫⁻ y in annulus_cc' x' ((D : ℝ) ^ (s I - 1) / 4) R, ‖K x' y * f y‖ₑ ≤
    2 ^ (7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x := by
  apply (lintegral_mono_set (annulus_cc_subset_cc _ (le_refl _) (ENNReal.ofReal_le_ofReal h))).trans
  have ineq : ∀ y ∈ annulus_cc' x' ((D : ℝ) ^ (s I - 1) / 4) (8 * D ^ (s I)), ‖K x' y * f y‖ₑ ≤
      2 ^ (7 * (a : ℝ) + 101 * a ^ 3) / volume (ball (c I) (16 * D ^ (s I))) * ‖f y‖ₑ := by
    intro y hy
    rw [enorm_mul]
    gcongr
    rw [annulus_cc'_eq _ _ _ (by positivity)] at hy
    apply le_trans <| ennnorm_K_le 5 hy.1
    gcongr
    · norm_num
    · norm_num
    · suffices dist (c I) x' < 16 * D ^ (s I) from ball_subset_ball' (by linarith)
      rw [← mem_ball', s]
      refine ball_subset_ball ?_ (Grid_subset_ball hx')
      linarith [defaultD_pow_pos a (GridStructure.s I)]
  apply le_trans <| setLIntegral_mono (hf.stronglyMeasurable.measurable.ennnorm.const_mul _) ineq
  simp_rw [ENNReal.mul_comm_div, div_eq_mul_inv]
  have := hf.stronglyMeasurable.measurable.ennnorm
  rw [lintegral_const_mul _ (this.mul_const _), lintegral_mul_const _ this, ← div_eq_mul_inv]
  apply mul_left_mono
  calc
    _ ≤ (∫⁻ y in ball (c I) (16 * D ^ s I), ‖f y‖ₑ) / volume (ball (c I) (16 * D ^ s I)) := by
      gcongr
      refine lintegral_mono' (Measure.le_iff.mpr (fun T hT ↦  ?_)) (le_refl _)
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
      refine measure_mono (inter_subset_inter_right T (fun y ↦ ?_))
      simp only [annulus_cc, mem_Icc, mem_setOf_eq, mem_ball, and_imp, dist_comm x']
      intro _ h
      calc dist y (c I)
        _ ≤ dist y x' + dist x' (c I) := dist_triangle y x' (c I)
        _ ≤ 8 * (D : ℝ) ^ s I + 4 * (D : ℝ) ^ s I :=
          add_le_add ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h)
            (mem_ball.mp (Grid_subset_ball hx')).le
        _ < 16 * (D : ℝ) ^ s I := by linarith [defaultD_pow_pos a (s I)]
    _ = ⨍⁻ y in ball (c I) (16 * D ^ s I), ‖f y‖ₑ ∂volume := by rw [setLaverage_eq]
    _ ≤ MB volume 𝓑 c𝓑 r𝓑 f x := by
      unfold MB maximalFunction
      rw [inv_one, ENNReal.rpow_one]
      have : ⟨4, I⟩ ∈ 𝓑 := by simp [𝓑]
      refine le_of_eq_of_le ?_ (le_biSup _ this)
      have : x ∈ ball (c I) (2 ^ 4 * (D : ℝ) ^ s I) := by
        refine (ball_subset_ball ?_) (Grid_subset_ball hx)
        unfold s
        linarith [defaultD_pow_pos a (GridStructure.s I)]
      simp only [c𝓑, r𝓑, ENNReal.rpow_one, indicator_of_mem this, ge_iff_le]
      norm_num
      rfl

omit [TileStructure Q D κ S o] in
private lemma support_K'_subset (b : ℤ) (c : ℤ) (x : X) :
    support (K' b c x) ⊆ annulus_cc' x (D ^ (b - 1) / 4) (D ^ c / 2) := by
  refine subset_trans ?_ (annulus_oo_subset_cc x (le_refl _) (le_refl _))
  intro y hy
  rw [mem_support] at hy
  simp only [annulus_oo, mem_Ioo, mem_setOf_eq]
  contrapose! hy
  apply Finset.sum_eq_zero (fun s hs ↦ ?_)
  rw [toFinset_Icc] at hs
  suffices ((D : ℝ) ^ s)⁻¹ * dist x y ∉ support ψ by simp [Ks, nmem_support.mp this, -defaultD]
  rw [support_ψ (one_lt_D (X := X)), mem_Ioo, not_and_or]
  by_cases h : D ^ (b - 1) / 4 < dist x y
  · exact Or.inr <| not_lt_of_ge <| calc
      _ ≥ ((D : ℝ) ^ c)⁻¹ * (D ^ c / 2) := by
        gcongr
        · exact defaultD_pow_pos a s
        · exact one_le_D
        · exact (Finset.mem_Icc.mp hs).2
        · exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp <| hy <|
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr h
      _ = 2⁻¹ := by field_simp
  · left
    push_neg at h
    apply not_lt_of_ge
    calc ((D : ℝ) ^ s)⁻¹ * dist x y
      _ ≤ ((D : ℝ) ^ b)⁻¹ * (D ^ (b - 1) / 4) := by
        gcongr
        · exact defaultD_pow_pos a b
        · exact one_le_D
        · exact (Finset.mem_Icc.mp hs).1
      _ ≤ _ := by
        apply le_of_eq
        rw [zpow_sub₀ (defaultD_pos a).ne.symm]
        field_simp
        exact mul_comm _ _

omit [TileStructure Q D κ S o] in
private lemma enorm_K'_le_enorm_K (a : ℤ) (b : ℤ) (x y : X) : ‖K' a b x y‖ₑ ≤ ‖K x y‖ₑ := by
  unfold K' Ks
  by_cases hxy : 0 = dist x y
  · simp [← hxy, psi_zero]
  rw [← mul_one ‖K x y‖ₑ, ← Finset.mul_sum, enorm_mul]
  apply mul_le_mul_left'
  rw [enorm_eq_nnnorm]
  norm_cast
  apply le_trans <| nnnorm_sum_le _ _
  simp_rw [← norm_toNNReal, Real.norm_eq_abs, ← Real.toNNReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _,
    Real.toNNReal_le_one, abs_eq_self.mpr <| zero_le_ψ _ _]
  exact sum_ψ_le (one_lt_D (X := X)) _ <| lt_of_le_of_ne dist_nonneg hxy

-- Pointwise bound needed for Lemma 7.2.2
private lemma nontangential_pointwise_bound (hf : BoundedCompactSupport f) (θ : Θ X) (x : X) :
    nontangentialMaximalFunction θ f x ≤ nontangentialOperator K f x +
      2 ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x := by
  refine iSup₂_le fun I hI ↦ iSup₂_le fun x' hx' ↦ iSup₂_le fun s₂ hs₂ ↦ iSup_le fun ineq ↦ ?_
  rw [← enorm_eq_nnnorm, ← integral_finset_sum]; swap
  · intro i hi
    simp_rw [mul_comm]
    exact hf.integrable_mul (integrable_Ks_x <| one_lt_D (X := X))
  simp_rw [← Finset.sum_mul]
  have ineq₃ {n : ℕ} (hn : n > 0) : (D : ℝ) ^ (s I - 1) / n < 8 * D ^ s I := by
    rw [zpow_sub₀ (defaultD_pos a).ne.symm, div_div, zpow_one]
    calc (D : ℝ) ^ s I / ((D : ℝ) * n)
      _ ≤ D ^ s I / 1 := by gcongr; exact_mod_cast (mul_pos (defaultD_pos' a) hn)
      _ < 8 * D ^ s I := by linarith [defaultD_pow_pos a (s I)]
  calc
    _ = ‖∫ y in annulus_cc' x' (D ^ (s I - 1) / 4) (D ^ s₂ / 2), K' (s I) s₂ x' y * f y‖ₑ := by
      rw [← integral_indicator measurableSet_annulus_cc]
      congr
      ext y
      by_cases hy : y ∈ annulus_cc x' (ENNReal.ofReal (D ^ (s I - 1) / 4))
          (ENNReal.ofReal (D ^ s₂ / 2))
      · simp [-defaultD, -toFinset_Icc, hy, K']
      · have := nmem_support.mp <| not_mem_subset (support_K'_subset (s I) s₂ x') hy
        unfold K' at this
        simp [-defaultD, -toFinset_Icc, hy, this]
    _ ≤ ‖∫ y in annulus_oo' x' (8 * D ^ (s I)) (D ^ (s₂ - 1) / 4), K' (s I) s₂ x' y * f y‖ₑ +
          ((∫⁻ y in annulus_cc' x' (D ^ (s I - 1) / 4) (8 * D ^ (s I)), ‖K' (s I) s₂ x' y * f y‖ₑ) +
          ∫⁻ y in annulus_cc' x' (D ^ (s₂ - 1) / 4) (D ^ s₂ / 2), ‖K' (s I) s₂ x' y * f y‖ₑ) := by
      apply annulus_integral_bound
      · exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (ineq₃ four_pos)
      · rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
        gcongr
        · exact one_lt_D (X := X)
        · exact sub_one_lt s₂
        · norm_num
      · refine integrableOn_K'_mul_f x' hf (ENNReal.ofReal (D ^ (s I - 1) / 4)) ?_ (s I) s₂
          |>.mono_set ?_
        · exact ENNReal.ofReal_pos.mpr <| div_pos (defaultD_pow_pos a (s I - 1)) four_pos
        · exact annulus_cc_subset_ci x' (le_refl _)
    _ ≤ ‖∫ y in annulus_oo' x' (8 * D ^ (s I)) (D ^ (s₂ - 1) / 4), K x' y * f y‖ₑ +
          ((∫⁻ y in annulus_cc' x' (D ^ (s I - 1) / 4) (8 * D ^ (s I)), ‖K x' y * f y‖ₑ) +
          ∫⁻ y in annulus_cc' x' (D ^ (s₂ - 1) / 4) (D ^ s₂ / 2), ‖K x' y * f y‖ₑ) := by
      have norm_K'_f_le : ∀ (y : X), ‖K' (s I) s₂ x' y * f y‖ₑ ≤ ‖K x' y * f y‖ₑ := by
        simp_rw [enorm_mul]
        exact fun y ↦ mul_le_mul_of_nonneg_right (enorm_K'_le_enorm_K _ _ _ _) (zero_le _)
      gcongr
      · refine le_of_eq (congrArg (‖·‖ₑ) ?_)
        apply setIntegral_congr_fun measurableSet_annulus_oo
        intro y hy
        simp only [mul_eq_mul_right_iff]
        apply Or.inl ∘ K'_eq_K (s I) s₂ x' y
        simp only [annulus_oo, mem_Ioo, mem_setOf_eq] at hy
        have i1 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hy.1
        have i2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hy.2.le
        refine mem_Icc.mpr ⟨(lt_trans (ineq₃ two_pos) i1).le, i2.trans ?_⟩
        rw [zpow_sub₀ (defaultD_pos a).ne.symm, div_div, zpow_one]
        have : (D : ℝ) * 4 > 0 := mul_pos (defaultD_pos a) four_pos
        apply (div_le_div_iff_of_pos_left (defaultD_pow_pos a s₂) this four_pos).mpr
        norm_cast
        linarith [defaultD_pos' a]
      · exact norm_K'_f_le _
      · exact norm_K'_f_le _
    _ ≤ nontangentialOperator K f x +
          (2 ^ (7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x +
          2 ^ (7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x) := by
      gcongr
      · apply nontangential_integral_bound₁ (D ^ (s₂ - 1) / 4)
        apply le_trans (dist_triangle x (c I) x')
        replace hI := mem_ball.mp (Grid_subset_ball hI)
        replace hx' := mem_ball'.mp (Grid_subset_ball hx')
        apply le_of_le_of_eq (add_lt_add hI hx').le
        unfold s
        ring
      · exact nontangential_integral_bound₂ hf hI hx' (le_refl _)
      · let I₂ := cubeOf s₂ x
        have hs₂' : s₂ ∈ Icc (-(S : ℤ)) (S : ℤ) :=
          Icc_subset_Icc (Set.range_subset_iff.mp range_s_subset I |>.1) (le_refl (S : ℤ)) hs₂
        have ⟨xI₂, hI₂⟩ := cubeOf_spec hs₂' I hI
        have : (I : Set X) ⊆ (I₂ : Set X) :=
          have : s I ≤ s I₂ := by rw [hI₂]; exact hs₂.1
          (fundamental_dyadic this).resolve_right (Set.not_disjoint_iff.mpr ⟨x, ⟨hI, xI₂⟩⟩)
        rw [← hI₂]
        apply nontangential_integral_bound₂ hf xI₂ (this hx')
        linarith [defaultD_pow_pos a (s (cubeOf s₂ x))]
    _ = _ := by
      rw [← two_mul, ← mul_assoc, add_assoc, ENNReal.rpow_add 1 _ two_ne_zero ENNReal.two_ne_top,
        ENNReal.rpow_one]

/-- Lemma 7.2.2. -/
lemma nontangential_operator_bound
    (hf : BoundedCompactSupport f)
    (θ : Θ X) :
    eLpNorm (nontangentialMaximalFunction θ f ·) 2 volume ≤ (C7_2_2 a) * eLpNorm f 2 volume := by
  have ha : 4 ≤ (a : ℝ) := by exact_mod_cast four_le_a X
  have aemeas_MB : AEMeasurable (MB volume 𝓑 c𝓑 r𝓑 f ·) :=
    (AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable
  have ⟨hT₁, hT₂⟩ := hasBoundedStrongType_Tstar f (hf.memℒp 2) hf.memℒp_top.eLpNorm_lt_top
    hf.isBoundedSupport.measure_lt_top
  calc eLpNorm (nontangentialMaximalFunction θ f) 2 volume
    _ ≤ eLpNorm (fun x ↦ nontangentialOperator K f x +
          2 ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x) 2 volume := by
      simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm']
      gcongr
      exact nontangential_pointwise_bound hf θ _
    _ ≤ eLpNorm (nontangentialOperator K f) 2 volume +
          eLpNorm ((2 : ℝ≥0∞) ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) *
          MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume := by
      simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
        enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
      simpa using ENNReal.lintegral_Lp_add_le hT₁.aemeasurable (aemeas_MB.const_mul _) one_le_two
    _ = eLpNorm (nontangentialOperator K f) 2 volume +
          2 ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) * eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume := by
      congr
      simp only [eLpNorm, eLpNorm', OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top]
      convert ENNReal.lintegral_Lp_smul aemeas_MB two_pos ((2 : ℝ≥0) ^ (1 + 7 * a + 101 * a ^ 3))
      · congr; norm_cast
      · ext; rw [ENNReal.smul_def, smul_eq_mul]; norm_cast
    _ ≤ (C_Ts a + 2 ^ (1 + 7 * a + 101 * a ^ 3 : ℝ) * CMB (defaultA a) 2) * eLpNorm f 2 volume := by
      rw [add_mul, mul_assoc]
      gcongr
      exact eLpNorm_MB_le hf
    _ ≤ ((2 ^ a ^ 3) + 2 ^ (1 + 7 * a + 101 * a ^ 3) * (2 ^ (2 * a))) * eLpNorm f 2 volume := by
      rw [C_Ts, CMB_defaultA_two_eq]
      gcongr
      · norm_cast
      · norm_cast
      · norm_cast
        simp only [Nat.cast_pow, Nat.cast_ofNat, ← NNReal.rpow_natCast]
        apply NNReal.rpow_le_rpow_of_exponent_le one_le_two
        rw [Nat.cast_mul]
        linarith
    _ ≤ (C7_2_2 a) * eLpNorm f 2 volume := by
      rw [← ENNReal.rpow_natCast, Nat.cast_pow]
      exact mul_right_mono <| calc 2 ^ (a : ℝ) ^ 3 + 2 ^ (1 + 7 * a + 101 * a ^ 3) * 2 ^ (2 * a)
        _ ≤ (2 : ℝ≥0∞) ^ ((101.6 : ℝ) * a ^ 3) + (2 : ℝ≥0∞) ^ ((101.6 : ℝ) * a ^ 3) := by
          gcongr
          · exact one_le_two
          · linarith [pow_pos (cast_a_pos X) 3]
          · simp_rw [← pow_add, ← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
            apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
            linarith [show 4 ^ 2 * (a : ℝ) ≤ a ^ 2 * a by gcongr]
        _ = (2 : ℝ≥0∞) ^ (101.6 * (a : ℝ) ^ 3 + 1) := by
          rw [← mul_two, ENNReal.rpow_add _ _ two_ne_zero ENNReal.two_ne_top, ENNReal.rpow_one]
        _ ≤ C7_2_2 a := by
          have := ENNReal.coe_rpow_def 2 (102 * a ^ 3)
          simp only [ENNReal.coe_ofNat, OfNat.ofNat_ne_zero, false_and, reduceIte] at this
          rw [C7_2_2, ← this]
          apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
          linarith [show 0.4 * 4 ^ 3 ≤ (0.4 : ℝ) * a ^ 3 by gcongr]

/-- The set of cubes in Lemma 7.2.4. -/
def kissing (I : Grid X) : Finset (Grid X) :=
  {J | s J = s I ∧ ¬Disjoint (ball (c I) (16 * D ^ s I)) (ball (c J) (16 * D ^ s J))}

lemma subset_of_kissing (h : J ∈ kissing I) :
    ball (c J) (D ^ s J / 4) ⊆ ball (c I) (33 * D ^ s I) := by
  simp_rw [kissing, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨x, xI, xJ⟩ := not_disjoint_iff.mp h.2
  apply ball_subset_ball'
  calc
    _ ≤ D ^ s J / 4 + dist (c J) x + dist x (c I) := by
      rw [add_assoc]; exact add_le_add_left (dist_triangle ..) _
    _ ≤ D ^ s J / 4 + 16 * D ^ s J + 16 * D ^ s I := by
      gcongr
      · exact (mem_ball'.mp xJ).le
      · exact (mem_ball.mp xI).le
    _ ≤ _ := by
      rw [h.1, div_eq_mul_inv, mul_comm _ 4⁻¹, ← distrib_three_right]
      gcongr
      norm_num

lemma volume_le_of_kissing (h : J ∈ kissing I) :
    volume (ball (c I) (33 * D ^ s I)) ≤ 2 ^ (9 * a) * volume (ball (c J) (D ^ s J / 4)) := by
  simp_rw [kissing, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨x, xI, xJ⟩ := not_disjoint_iff.mp h.2
  have : ball (c I) (33 * D ^ s I) ⊆ ball (c J) (128 * D ^ s J) := by
    apply ball_subset_ball'
    calc
      _ ≤ 33 * D ^ s I + dist (c I) x + dist x (c J) := by
        rw [add_assoc]; exact add_le_add_left (dist_triangle ..) _
      _ ≤ 33 * D ^ s I + 16 * D ^ s I + 16 * D ^ s J := by
        gcongr
        · exact (mem_ball'.mp xI).le
        · exact (mem_ball.mp xJ).le
      _ ≤ _ := by
        rw [h.1, ← distrib_three_right]
        gcongr; norm_num
  have double := measure_ball_le_pow_two' (μ := volume) (x := c J) (r := D ^ s J / 4) (n := 9)
  have A9 : (defaultA a : ℝ≥0) ^ 9 = (2 : ℝ≥0∞) ^ (9 * a) := by
    simp only [defaultA]; norm_cast; ring
  rw [show (2 : ℝ) ^ 9 * (D ^ s J / 4) = 128 * D ^ s J by ring, A9] at double
  exact (measure_mono this).trans double

lemma pairwiseDisjoint_of_kissing :
    (kissing I).toSet.PairwiseDisjoint fun i ↦ ball (c i) (D ^ s i / 4) := fun j mj k mk hn ↦ by
  apply disjoint_of_subset ball_subset_Grid ball_subset_Grid
  simp_rw [Finset.mem_coe, kissing, Finset.mem_filter] at mj mk
  exact (eq_or_disjoint (mj.2.1.trans mk.2.1.symm)).resolve_left hn

/-- Lemma 7.2.4. -/
lemma boundary_overlap (I : Grid X) : (kissing I).card ≤ 2 ^ (9 * a) := by
  have key : (kissing I).card * volume (ball (c I) (33 * D ^ s I)) ≤
      2 ^ (9 * a) * volume (ball (c I) (33 * D ^ s I)) := by
    calc
      _ = ∑ _ ∈ kissing I, volume (ball (c I) (33 * D ^ s I)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ J ∈ kissing I, 2 ^ (9 * a) * volume (ball (c J) (D ^ s J / 4)) :=
        Finset.sum_le_sum fun _ ↦ volume_le_of_kissing
      _ = 2 ^ (9 * a) * volume (⋃ J ∈ kissing I, ball (c J) (D ^ s J / 4)) := by
        rw [← Finset.mul_sum]; congr
        exact (measure_biUnion_finset pairwiseDisjoint_of_kissing fun _ _ ↦ measurableSet_ball).symm
      _ ≤ _ := by gcongr; exact iUnion₂_subset fun _ ↦ subset_of_kissing
  have vn0 : volume (ball (c I) (33 * D ^ s I)) ≠ 0 := by
    refine (measure_ball_pos volume _ ?_).ne'; simp only [defaultD]; positivity
  rw [ENNReal.mul_le_mul_right vn0 (measure_ball_ne_top _ _)] at key; norm_cast at key

irreducible_def C7_2_3 (a : ℕ) : ℝ≥0 := 2 ^ (12 * (a : ℝ))

/-- Lemma 7.2.3. -/
lemma boundary_operator_bound
    (hf : BoundedCompactSupport f) (hu : u ∈ t) :
    eLpNorm (boundaryOperator t u f) 2 volume ≤ (C7_2_3 a) * eLpNorm f 2 volume := by
  sorry

/-- The constant used in `tree_projection_estimate`.
Originally had value `2 ^ (104 * a ^ 3)` in the blueprint, but that seems to be a mistake. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (152 * (a : ℝ) ^ 3)

-- Auxiliary function used in the proof of Lemma 7.2.1
private def eI𝒬u_mul (u : 𝔓 X) (f : X → ℂ) : X → ℂ := fun y ↦ exp (.I * 𝒬 u y) * f y

private lemma boundedCompactSupport_eI𝒬u_mul (u : 𝔓 X) {f : X → ℂ} (hf : BoundedCompactSupport f) :
    BoundedCompactSupport (eI𝒬u_mul u f) := by
  apply hf.mul_bdd_left
  · refine isBounded_iff_forall_norm_le.mpr ⟨1, fun _ h ↦ ?_⟩
    obtain ⟨_, rfl⟩ := mem_range.mp h
    rw [mul_comm, norm_exp_ofReal_mul_I]
  · apply measurable_exp.stronglyMeasurable.comp_measurable
    exact (measurable_ofReal.comp' (map_continuous (𝒬 u)).measurable).const_mul I

private lemma norm_eI𝒬u_mul_eq (u : 𝔓 X) (f : X → ℂ) (x : X) : ‖eI𝒬u_mul u f x‖ = ‖f x‖ := by
  simp [eI𝒬u_mul, mul_comm I]

-- The bound for `carlesonSum` from `pointwise_tree_estimate` (Lemma 7.1.3)
variable (t) (u) (f) in
private def cS_bound (x' : X) :=
    C7_1_3 a * (MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x') +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) (eI𝒬u_mul u f)) x'

private lemma aeMeasurable_cS_bound : AEMeasurable (cS_bound t u f) := by
  refine AEMeasurable.add ?_ MeasureTheory.Measurable.nontangentialMaximalFunction.aemeasurable
  apply ((AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable.add ?_).const_mul
  exact MeasureTheory.Measurable.boundaryOperator.aemeasurable

-- The natural constant for Lemma 7.2.1 is ≤ the simpler constant `C7_2_1` we use instead.
private lemma le_C7_2_1 {a : ℕ} (ha : 4 ≤ a) :
    C7_1_3 a * CMB (defaultA a) 2 + C7_1_3 a * C7_2_3 a + C7_2_2 a ≤ (C7_2_1 a : ℝ≥0∞) := calc
  _ ≤ (3 : ℕ) • (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3 + 12 * a) := by
    rw [three'_nsmul]
    gcongr
    · rw [C7_1_3_eq_C7_1_6 ha, C7_1_6_def, CMB_defaultA_two_eq, ← ENNReal.coe_mul,
        ← NNReal.rpow_add two_ne_zero, ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_ofNat]
      apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      linarith [show 4 ≤ (a : ℝ) by exact_mod_cast ha]
    · rw [C7_1_3_eq_C7_1_6 ha, C7_2_3_def, C7_1_6_def]
      norm_cast
      exact le_of_eq (pow_add _ _ _).symm
    · rw [C7_2_2_def]
      norm_cast
      exact pow_right_mono₀ one_le_two <| (Nat.mul_le_mul_right _ (by norm_num)).trans le_self_add
  _ = 3 * 2 ^ (12 * (a : ℝ)) * (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3) := by
    rw [add_comm, ENNReal.rpow_add _ _ two_ne_zero ENNReal.two_ne_top]; ring
  _ ≤ (2 : ℝ≥0∞) ^ ((a : ℝ) ^ 3) * (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3) := by
    apply mul_right_mono
    norm_cast
    calc
      3 * 2 ^ (12 * a) ≤ 2 ^ 2 * 2 ^ (12 * a) := by gcongr; norm_num
      _                = 2 ^ (2 + 12 * a)     := by rw [pow_add]
      _                ≤ 2 ^ (a ^ 3)          := pow_le_pow_right₀ one_le_two <| calc
                          2 + 12 * a ≤ a + 12 * a  := by apply add_le_add_right; linarith
                          _          = 13 * a      := by ring
                          _          ≤ a ^ 2 * a   := by rw [mul_le_mul_right] <;> nlinarith
                          _          = a ^ 3       := rfl
  _ = _ := by
    rw [C7_2_1_def, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.two_ne_top]
    norm_cast
    ring

-- Main estimate used in the proof of `tree_projection_estimate`
private lemma eLpNorm_two_cS_bound_le (hu : u ∈ t) : eLpNorm (cS_bound t u f) 2 volume ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume := by
  let μ := volume (α := X)
  let aOC := (approxOnCube (𝓙 (t u)) (‖f ·‖))
  let g₁ := MB μ 𝓑 c𝓑 r𝓑 aOC
  let g₂ := t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖))
  let g₃ := nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) (eI𝒬u_mul u f))
  have m₁ : AEMeasurable g₁ :=
    (MeasureTheory.AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable
  have m₂ : AEMeasurable g₂ := MeasureTheory.Measurable.boundaryOperator.aemeasurable
  calc eLpNorm (cS_bound t u f) 2 μ
    _ = eLpNorm (C7_1_3 a • (g₁ + g₂) + g₃) 2 μ := rfl
    _ ≤ eLpNorm (C7_1_3 a • (g₁ + g₂)) 2 μ + eLpNorm g₃ 2 μ := by
      simpa [eLpNorm, eLpNorm'] using
        ENNReal.lintegral_Lp_add_le ((m₁.add m₂).const_smul (C7_1_3 a)) (hp1 := one_le_two)
          MeasureTheory.Measurable.nontangentialMaximalFunction.aemeasurable
    _ = C7_1_3 a • eLpNorm (g₁ + g₂) 2 μ + eLpNorm g₃ 2 μ := by
      congr
      simpa [eLpNorm, eLpNorm'] using ENNReal.lintegral_Lp_smul (m₁.add m₂) two_pos (C7_1_3 a)
    _ ≤ C7_1_3 a • (eLpNorm g₁ 2 μ + eLpNorm g₂ 2 μ) + eLpNorm g₃ 2 μ := by
      gcongr
      simpa [eLpNorm, eLpNorm'] using ENNReal.lintegral_Lp_add_le m₁ m₂ one_le_two
    _ ≤ C7_1_3 a • ((CMB (defaultA a) 2) * eLpNorm aOC 2 μ + (C7_2_3 a) * eLpNorm aOC 2 μ) +
          (C7_2_2 a) * eLpNorm aOC 2 μ := by
      gcongr
      · exact eLpNorm_MB_le boundedCompactSupport_approxOnCube
      · apply le_of_le_of_eq <| boundary_operator_bound boundedCompactSupport_approxOnCube hu
        simp [eLpNorm, eLpNorm', aOC, approxOnCube_ofReal, enorm_eq_nnnorm, μ]
      · apply le_trans <| nontangential_operator_bound boundedCompactSupport_approxOnCube (𝒬 u)
        refine mul_le_mul_left' (eLpNorm_mono (fun x ↦ ?_)) _
        apply le_of_le_of_eq norm_approxOnCube_le_approxOnCube_norm
        rw [Real.norm_of_nonneg <| approxOnCube_nonneg (fun _ ↦ norm_nonneg _)]
        simp_rw [norm_eI𝒬u_mul_eq]
    _ = (C7_1_3 a * CMB (defaultA a) 2 + C7_1_3 a * C7_2_3 a + C7_2_2 a) * eLpNorm aOC 2 μ := by
      rw [ENNReal.smul_def, smul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_right' (le_C7_2_1 (four_le_a X)) _

/-- Lemma 7.2.1. -/
lemma tree_projection_estimate
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume *
    eLpNorm (approxOnCube (𝓛 (t u)) (‖g ·‖)) 2 volume := by
  set aOC := approxOnCube (𝓛 (t u)) (‖g ·‖)
  let eaOC (x : X) := ENNReal.ofReal (aOC x)
  have aOC_nonneg {x : X} : 0 ≤ aOC x := approxOnCube_nonneg (fun _ ↦ norm_nonneg _)
  calc ENNReal.ofNNReal ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊
    _ ≤ ∫⁻ x, ‖conj (g x) * carlesonSum (t u) f x‖ₑ := ennnorm_integral_le_lintegral_ennnorm _
    _ = ∫⁻ x in (⋃ p ∈ t u, 𝓘 p), ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      rw [← lintegral_indicator]; swap
      · exact MeasurableSet.biUnion (t u).to_countable (fun _ _ ↦ coeGrid_measurable)
      simp_rw [enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul, RCLike.nnnorm_conj]
      refine lintegral_congr (fun x ↦ ?_)
      by_cases hx : x ∈ ⋃ p ∈ t u, 𝓘 p
      · rw [indicator_of_mem hx]
      · simp [indicator_of_not_mem hx, nmem_support.mp (hx <| support_carlesonSum_subset ·)]
    _ ≤ ∫⁻ x in (⋃ L ∈ 𝓛 (t u), (L : Set X)), ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      rw [biUnion_𝓛]
      refine lintegral_mono_set (fun x hx ↦ ?_)
      have ⟨p, hp⟩ : ∃ p ∈ t u, x ∈ 𝓘 p := by simpa using hx
      apply mem_iUnion.mpr ⟨𝓘 p, hp.2⟩
    _ = ∑ L in 𝓛 (t u), ∫⁻ x in L, ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      simp only [← mem_toFinset]
      refine lintegral_biUnion_finset ?_ (fun _ _ ↦ coeGrid_measurable) _
      rw [coe_toFinset]
      exact pairwiseDisjoint_𝓛
    _ ≤ ∑ L in 𝓛 (t u), ∫⁻ x in L, ‖g x‖ₑ * (⨅ x' ∈ L, ‖cS_bound t u f x'‖ₑ) := by
      gcongr ∑ L in 𝓛 (t u), ?_ with L hL
      refine setLIntegral_mono (Measurable.mul ?_ measurable_const) (fun x hx ↦ ?_)
      · exact measurable_coe_nnreal_ennreal_iff.mpr hg.stronglyMeasurable.measurable.nnnorm
      · gcongr
        refine le_iInf₂ (fun x' hx' ↦ ?_)
        simp only [mem_toFinset] at hL
        convert pointwise_tree_estimate hu hL hx hx' (boundedCompactSupport_eI𝒬u_mul u hf) using 1
        · congr
          simp_rw [mul_neg, eI𝒬u_mul, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
        · simp only [cS_bound, enorm_eq_self, norm_eI𝒬u_mul_eq u f]
    _ = ∑ L in 𝓛 (t u), ∫⁻ x in L, eaOC x * (⨅ x' ∈ L, ‖cS_bound t u f x'‖ₑ) := by
      refine Finset.sum_congr rfl (fun L hL ↦ ?_)
      rw [lintegral_mul_const, lintegral_mul_const]; rotate_left
      · exact ENNReal.measurable_ofReal.comp (stronglyMeasurable_approxOnCube _ _).measurable
      · exact hg.stronglyMeasurable.measurable.ennnorm
      simp_rw [eaOC, enorm_eq_nnnorm]
      simp_rw [lintegral_coe_eq_integral (‖g ·‖₊) hg.integrable.norm.restrict, coe_nnnorm]
      rw [integral_eq_lintegral_approxOnCube pairwiseDisjoint_𝓛 (mem_toFinset.mp hL) hg]
      simp_rw [← Real.ennnorm_eq_ofReal aOC_nonneg, approxOnCube_ofReal, nnnorm_real, aOC]
    _ ≤ ∑ L in 𝓛 (t u), ∫⁻ x in L, eaOC x * ‖cS_bound t u f x‖ₑ :=
      Finset.sum_le_sum fun L hL ↦
        setLIntegral_mono' coeGrid_measurable (fun x hx ↦ mul_left_mono (biInf_le _ hx))
    _ = ∫⁻ x in (⋃ L ∈ 𝓛 (t u), (L : Set X)), eaOC x * ‖cS_bound t u f x‖ₑ := by
      rw [← lintegral_biUnion_finset (hm := fun _ _ ↦ coeGrid_measurable)]
      · simp only [mem_toFinset]
      · simpa only [coe_toFinset] using pairwiseDisjoint_𝓛 (𝔖 := t u)
    _ ≤ ∫⁻ (x : X), eaOC x * ‖cS_bound t u f x‖ₑ := by
      nth_rewrite 2 [← setLIntegral_univ]
      exact lintegral_mono_set (fun _ _ ↦ trivial)
    _ ≤ eLpNorm eaOC 2 volume * eLpNorm (cS_bound t u f) 2 volume := by
      have isConj : Real.IsConjExponent 2 2 := by constructor <;> norm_num
      have : AEMeasurable eaOC := (stronglyMeasurable_approxOnCube _ _).aemeasurable.ennreal_ofReal
      convert ENNReal.lintegral_mul_le_Lp_mul_Lq volume isConj this aeMeasurable_cS_bound <;>
        simp [eLpNorm, eLpNorm']
    _ = eLpNorm (cS_bound t u f) 2 volume * eLpNorm aOC 2 volume := by
      rw [mul_comm]; congr; ext; exact (Real.ennnorm_eq_ofReal aOC_nonneg).symm
    _ ≤ _ := mul_right_mono (eLpNorm_two_cS_bound_le hu)

end TileStructure.Forest
