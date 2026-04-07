import Carleson.Forest
import Carleson.Operators
import Carleson.ToMathlib.HardyLittlewood

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

/-! ## Section 7.1 and Lemma 7.1.3 -/

open scoped Classical in
variable (t) in
/-- The definition `σ(u, x)` given in Section 7.1.
We may assume `u ∈ t` whenever proving things about this definition. -/
def σ (u : 𝔓 X) (x : X) : Finset ℤ := .image 𝔰 { p | p ∈ t u ∧ x ∈ E p }

variable (t) in
private lemma exists_p_of_mem_σ (u : 𝔓 X) (x : X) {s : ℤ} (hs : s ∈ t.σ u x) :
    ∃ p ∈ t.𝔗 u, x ∈ E p ∧ 𝔰 p = s := by
  have ⟨p, hp⟩ := Finset.mem_image.mp hs
  simp only [mem_𝔗, Finset.mem_filter] at hp
  use p, hp.1.2.1, hp.1.2.2, hp.2

/- \overline{σ} from the blueprint. -/
variable (t) in
def σMax (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : ℤ :=
  t.σ u x |>.max' hσ

/- \underline{σ} from the blueprint. -/
variable (t) in
def σMin (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : ℤ :=
  t.σ u x |>.min' hσ

variable (t) in
private lemma σMax_mem_σ (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : σMax t u x hσ ∈ t.σ u x :=
  (t.σ u x).max'_mem hσ

/-- The definition of `𝓙₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓙₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {J : Grid X | s J = -S ∨ ∀ p ∈ 𝔖, ¬(𝓘 p : Set X) ⊆ ball (c J) (100 * D ^ (s J + 1))}

/-- The definition of `𝓙(𝔖), defined above Lemma 7.1.2 -/
def 𝓙 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓙₀ 𝔖) x}

lemma 𝓙_subset_𝓙₀ {𝔖 : Set (𝔓 X)} : 𝓙 𝔖 ⊆ 𝓙₀ 𝔖 := sep_subset ..

lemma pairwiseDisjoint_𝓙 : (𝓙 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := fun I mI J mJ hn ↦ by
  have : IsAntichain (· ≤ ·) (𝓙 𝔖) := setOf_maximal_antichain _
  exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

lemma S_eq_zero_of_topCube_mem_𝓙₀ {𝔖 : Set (𝔓 X)} (h𝔖 : 𝔖.Nonempty) (h : topCube ∈ 𝓙₀ 𝔖) :
    S = 0 := by
  suffices (S : ℤ) = -(S : ℤ) by exact_mod_cast eq_zero_of_neg_eq this.symm
  rw [𝓙₀, mem_setOf_eq, s, s_topCube] at h
  apply h.resolve_right
  push_neg
  have ⟨p, hp⟩ := h𝔖
  refine ⟨p, hp, subset_topCube.trans <| Grid_subset_ball.trans <| ball_subset_ball ?_⟩
  apply mul_le_mul (by norm_num) (c0 := by positivity) (b0 := by norm_num)
  exact zpow_le_zpow_right₀ (one_le_realD _) (scale_mem_Icc.2.trans (Int.le.intro 1 rfl))

/-- The definition of `𝓛₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓛₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {L : Grid X | s L = -S ∨ (∃ p ∈ 𝔖, L ≤ 𝓘 p) ∧ ∀ p ∈ 𝔖, ¬𝓘 p ≤ L}

/-- The definition of `𝓛(𝔖), defined above Lemma 7.1.2 -/
def 𝓛 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓛₀ 𝔖) x}

lemma 𝓛_subset_𝓛₀ {𝔖 : Set (𝔓 X)} : 𝓛 𝔖 ⊆ 𝓛₀ 𝔖 := sep_subset ..

private lemma s_le_s_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖)
    {p : 𝔓 X} (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : s L ≤ s (𝓘 p) := by
  simp only [𝓛, 𝓛₀, Grid.le_def, not_and, not_le] at hL
  rcases hL.1 with h | h
  · exact h ▸ (range_s_subset ⟨𝓘 p, rfl⟩).1
  · by_contra!
    exact lt_asymm this <| h.2 p hp <| (GridStructure.fundamental_dyadic' this.le).resolve_right hpL

private lemma subset_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖) {p : 𝔓 X}
    (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : (L : Set X) ⊆ (𝓘 p : Set X) :=
  GridStructure.fundamental_dyadic' (s_le_s_of_mem_𝓛 hL hp hpL) |>.resolve_right fun h ↦ hpL h.symm

lemma le_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖) {p : 𝔓 X}
    (hp : p ∈ 𝔖) (hpL : ¬Disjoint (𝓘 p : Set X) (L : Set X)) : L ≤ 𝓘 p :=
  ⟨subset_of_mem_𝓛 hL hp hpL, s_le_s_of_mem_𝓛 hL hp hpL⟩

open scoped Classical in
/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J with J ∈ C, (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x

lemma stronglyMeasurable_approxOnCube (C : Set (Grid X)) (f : X → E') :
    StronglyMeasurable (approxOnCube (X := X) (K := K) C f) :=
  Finset.stronglyMeasurable_fun_sum _
    fun _ _ ↦ stronglyMeasurable_const.indicator coeGrid_measurable

lemma integrable_approxOnCube (C : Set (Grid X)) {f : X → E'} : Integrable (approxOnCube C f) := by
  refine integrable_finset_sum _ (fun i hi ↦ ?_)
  constructor
  · exact (aestronglyMeasurable_indicator_iff coeGrid_measurable).mpr aestronglyMeasurable_const
  · simp_rw [hasFiniteIntegral_iff_enorm, enorm_indicator_eq_indicator_enorm]
    apply lt_of_le_of_lt <| lintegral_indicator_const_le (i : Set X) _
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top volume_coeGrid_lt_top

lemma approxOnCube_nonneg {C : Set (Grid X)} {f : X → ℝ} (hf : ∀ (y : X), f y ≥ 0) {x : X} :
    approxOnCube C f x ≥ 0 :=
  Finset.sum_nonneg' (fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ integral_nonneg hf) _)

open scoped Classical in
lemma approxOnCube_apply {C : Set (Grid X)} (hC : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    (f : X → E') {x : X} {J : Grid X} (hJ : J ∈ C) (xJ : x ∈ J) :
    (approxOnCube C f) x = ⨍ y in J, f y := by
  rw [approxOnCube, ← Finset.sum_filter_not_add_sum_filter _ (J = ·)]
  have eq0 : ∑ i ∈ Finset.filter (¬ J = ·) (Finset.univ.filter (· ∈ C)),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 := by
    suffices ∀ i ∈ (Finset.univ.filter (· ∈ C)).filter (¬ J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 by simp [Finset.sum_congr rfl this]
    intro i hi
    rw [Finset.mem_filter, Finset.mem_filter_univ] at hi
    apply indicator_of_notMem <|
      Set.disjoint_left.mp ((hC.eq_or_disjoint hJ hi.1).resolve_left hi.2) xJ
  have eq_ave : ∑ i ∈ (Finset.univ.filter (· ∈ C)).filter (J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = ⨍ y in J, f y := by
    suffices (Finset.univ.filter (· ∈ C)).filter (J = ·) = {J} by simp [this, xJ, ← Grid.mem_def]
    exact subset_antisymm (fun _ h ↦ Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2.symm)
      (fun _ h ↦ by simp [Finset.mem_singleton.mp h, hJ])
  rw [eq0, eq_ave, zero_add]

lemma boundedCompactSupport_approxOnCube {𝕜 : Type*} [RCLike 𝕜] {C : Set (Grid X)} {f : X → 𝕜} :
    BoundedCompactSupport (approxOnCube C f) :=
  BoundedCompactSupport.finset_sum fun J _ ↦
    BoundedCompactSupport.indicator_of_isCompact_closure (memLp_top_const _)
    ((isBounded_iff_subset_ball (c J)).mpr ⟨4 * D ^ s J, Grid_subset_ball⟩).isCompact_closure
    coeGrid_measurable

-- Used in the proof of Lemma 7.1.6
lemma lintegral_eq_lintegral_approxOnCube {C : Set (Grid X)}
    (hC : C.PairwiseDisjoint fun I ↦ (I : Set X)) {J : Grid X} (hJ : J ∈ C) {f : X → ℂ}
    (hf : BoundedCompactSupport f) :
    ∫⁻ y in J, ‖f y‖ₑ = ∫⁻ y in J, ‖approxOnCube C (fun x ↦ (‖f x‖ : ℂ)) y‖ₑ := by
  have nonneg : 0 ≤ᶠ[ae (volume.restrict J)] fun y ↦ ‖f y‖ := Filter.Eventually.of_forall (by simp)
  have vol_J_ne_zero := (volume_coeGrid_pos (X := X) (i := J) (defaultD_pos a)).ne.symm
  have eq : ∫⁻ y in J, ‖approxOnCube C (fun x ↦ (‖f x‖ : ℂ)) y‖ₑ =
      ∫⁻ y in (J : Set X), ENNReal.ofReal (⨍ z in J, ‖f z‖) := by
    refine setLIntegral_congr_fun coeGrid_measurable fun y hy ↦ ?_
    rw [approxOnCube_apply hC _ hJ hy, ← ofReal_norm_eq_enorm]
    apply congrArg
    have : ‖⨍ y in J, (‖f y‖ : ℂ)‖ = ‖⨍ y in J, ‖f y‖‖ := by
      convert congrArg (‖·‖) <| integral_ofReal (f := (‖f ·‖)) using 1
      simp [average]
    rw [this, Real.norm_eq_abs, abs_eq_self]
    apply integral_nonneg (fun y ↦ by simp)
  rw [eq, lintegral_const, average_eq, smul_eq_mul, ENNReal.ofReal_mul, ENNReal.ofReal_inv_of_pos,
    ofReal_integral_eq_lintegral_ofReal hf.norm.integrable.restrict nonneg, mul_comm,
    ← mul_assoc, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  · simp [volume_coeGrid_lt_top.ne, ENNReal.mul_inv_cancel vol_J_ne_zero]
  · simpa using ENNReal.toReal_pos vol_J_ne_zero volume_coeGrid_lt_top.ne
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg

lemma approxOnCube_ofReal (C : Set (Grid X)) (f : X → ℝ) (x : X) :
    approxOnCube C (Complex.ofReal <| f ·) x = Complex.ofReal (approxOnCube C f x) := by
  simp_rw [approxOnCube, ofReal_sum]
  refine Finset.sum_congr rfl (fun J _ ↦ ?_)
  by_cases hx : x ∈ (J : Set X)
  · simpa only [indicator_of_mem hx] using integral_ofReal
  · simp only [indicator_of_notMem hx, ofReal_zero]

lemma norm_approxOnCube_le_approxOnCube_norm {C : Set (Grid X)} {f : X → E'} {x : X} :
    ‖approxOnCube C f x‖ ≤ approxOnCube C (‖f ·‖) x := by
  refine (norm_sum_le _ _).trans <| Finset.sum_le_sum (fun J hJ ↦ ?_)
  rw [norm_indicator_eq_indicator_norm]
  gcongr
  apply norm_integral_le_integral_norm

/-- The definition `I_i(x)`, given above Lemma 7.1.3.
The cube of scale `s` that contains `x`. There is at most 1 such cube, if it exists. -/
def cubeOf (i : ℤ) (x : X) : Grid X :=
  Classical.epsilon (fun I ↦ x ∈ I ∧ s I = i)

lemma cubeOf_spec {i : ℤ} (hi : i ∈ Icc (-S : ℤ) S) (I : Grid X) {x : X} (hx : x ∈ I) :
    x ∈ cubeOf i x ∧ s (cubeOf i x) = i := by
  apply Classical.epsilon_spec (p := fun I ↦ x ∈ I ∧ s I = i)
  by_cases hiS : i = S
  · use topCube, subset_topCube hx, hiS ▸ s_topCube
  simpa [and_comm] using Set.mem_iUnion₂.mp <| Grid_subset_biUnion i
    ⟨hi.1, s_topCube (X := X) ▸ lt_of_le_of_ne hi.2 hiS⟩ (subset_topCube hx)

/-- The definition `T_𝓝^θ f(x)`, given in (7.1.3).
For convenience, the suprema are written a bit differently than in the blueprint
(avoiding `cubeOf`), but this should be equivalent.
This is `0` if `x` doesn't lie in a cube. -/
def nontangentialMaximalFunction (θ : Θ X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (I : Grid X) (_ : x ∈ I) (x' ∈ I) (s₂ ∈ Icc (s I) S)
  (_ : ENNReal.ofReal (D ^ (s₂ - 1)) ≤ upperRadius Q θ x'),
  ‖∑ i ∈ Icc (s I) s₂, ∫ y, Ks i x' y * f y‖ₑ

protected theorem MeasureTheory.Measurable.nontangentialMaximalFunction {θ : Θ X} {f : X → ℂ} :
    Measurable (nontangentialMaximalFunction θ f) := by
  classical
  refine Measurable.iSup (fun I ↦ ?_)
  let c := ⨆ x' ∈ I, ⨆ s₂ ∈ Icc (s I) S, ⨆ (_ : ENNReal.ofReal (D ^ (s₂ - 1)) ≤ upperRadius Q θ x'),
    ‖∑ i ∈ (Icc (s I) s₂), ∫ (y : X), Ks i x' y * f y‖ₑ
  have : (fun x ↦ ⨆ (_ : x ∈ I), c) = fun x ↦ ite (x ∈ I) c 0 := by
    ext x; by_cases hx : x ∈ I <;> simp [hx]
  convert (measurable_const.ite coeGrid_measurable measurable_const) using 1

-- Set used in definition of `boundaryOperator`
open scoped Classical in
variable (t) (u) in def 𝓙' (x : X) (i : ℤ) : Finset (Grid X) :=
  { J | J ∈ 𝓙 (t u) ∧ (J : Set X) ⊆ ball x (16 * D ^ i) ∧ s J ≤ i }

private lemma mem_𝓙_of_mem_𝓙' {x : X} {i : ℤ} {J : Grid X} : J ∈ 𝓙' t u x i → J ∈ 𝓙 (t u) := by
  intro hJ
  simp only [𝓙', Finset.mem_filter] at hJ
  exact hJ.2.1

variable (f I J) in
/-- Scaled integral appearing in the definition of `boundaryOperator`. -/
def ijIntegral : ℝ≥0∞ :=
  D ^ ((s J - s I) / (a : ℝ)) / volume (ball (c I) (16 * D ^ (s I))) * ∫⁻ y in J, ‖f y‖ₑ

lemma ijIntegral_lt_top (hf : BoundedCompactSupport f) : ijIntegral f I J < ⊤ := by
  refine ENNReal.mul_lt_top ?_ hf.integrable.integrableOn.2
  apply ENNReal.div_lt_top (by simp)
  exact (measure_ball_pos volume _ <| mul_pos (by norm_num) (defaultD_pow_pos a (s I))).ne'

variable (t) in
/-- The operator `S_{1,𝔲} f(x)`, given in (7.1.4). -/
def boundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ∑ I : Grid X, (I : Set X).indicator (fun _ ↦ ∑ J ∈ 𝓙' t u (c I) (s I), ijIntegral f I J) x

lemma measurable_boundaryOperator {u : 𝔓 X} {f : X → ℂ} : Measurable (t.boundaryOperator u f) := by
  refine Finset.measurable_sum _ (fun I _ ↦ ?_)
  exact (Finset.measurable_sum _ (fun J _ ↦ measurable_const)).indicator coeGrid_measurable

lemma boundaryOperator_lt_top (hf : BoundedCompactSupport f) : t.boundaryOperator u f x < ⊤ := by
  refine ENNReal.sum_lt_top.mpr (fun I _ ↦ ?_)
  by_cases hx : x ∈ (I : Set X)
  · rw [indicator_of_mem hx]
    exact ENNReal.sum_lt_top.mpr (fun _ _ ↦ ijIntegral_lt_top hf)
  · simp [hx]


/-- The indexing set for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def 𝓑 : Set (ℕ × ℕ × Grid X) := Iic (S + 5) ×ˢ Iic (2 * S + 3) ×ˢ univ

/-- The center function for the collection of balls 𝓑. -/
def c𝓑 (z : ℕ × ℕ × Grid X) : X := c z.2.2

/-- The radius function for the collection of balls 𝓑. -/
def r𝓑 (z : ℕ × ℕ × Grid X) : ℝ := 2 ^ z.1 * D ^ (s z.2.2 + z.2.1)

lemma 𝓑_finite : (𝓑 (X := X)).Finite :=
  finite_Iic _ |>.prod <| finite_Iic _ |>.prod finite_univ

lemma laverage_le_biInf_MB' {c₀ : X} {r₀ : ℝ} (hr : 4 * D ^ s J + dist (c J) c₀ ≤ r₀)
    (h : ∃ i ∈ 𝓑, c𝓑 i = c₀ ∧ r𝓑 i = r₀) :
    ⨍⁻ x in ball c₀ r₀, ‖f x‖ₑ ∂volume ≤ ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one, le_iInf_iff]
  intro y my; obtain ⟨b, mb, cb, rb⟩ := h
  replace my : y ∈ ball (c𝓑 b) (r𝓑 b) := by
    rw [cb, rb]; refine Grid_subset_ball.trans (ball_subset_ball' hr) my
  exact le_iSup₂_of_le b mb (by rw [indicator_of_mem my, cb, rb])

lemma laverage_le_biInf_MB {r₀ : ℝ} (hr : 4 * D ^ s J ≤ r₀)
    (h : ∃ i ∈ 𝓑, c𝓑 i = c J ∧ r𝓑 i = r₀) :
    ⨍⁻ x in ball (c J) r₀, ‖f x‖ₑ ∂volume ≤ ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  refine laverage_le_biInf_MB' ?_ h; rwa [dist_self, add_zero]


/-- Lemma 7.1.1, freely translated. -/
lemma convex_scales (hu : u ∈ t) : OrdConnected (t.σ u x : Set ℤ) := by
  rw [ordConnected_def]; intro i mi j mj k mk
  simp_rw [Finset.mem_coe, σ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at mi mj ⊢
  obtain ⟨p, ⟨mp, xp, Qxp, sxp⟩, sp⟩ := mi
  obtain ⟨p'', ⟨mp'', xp'', Qxp'', sxp''⟩, sp''⟩ := mj
  have ilj : i ≤ j := nonempty_Icc.mp ⟨k, mk⟩
  rw [← sp, ← sp''] at ilj mk
  obtain ⟨K, sK, lK, Kl⟩ := Grid.exists_sandwiched (le_of_mem_of_mem ilj xp xp'') k mk
  have := range_subset_iff.mp (biUnion_Ω (i := K)) x
  simp_rw [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at this
  obtain ⟨(p' : 𝔓 X), (𝓘p' : 𝓘 p' = K), Qxp'⟩ := this
  rw [← 𝓘p'] at lK Kl sK; refine ⟨p', ?_, sK⟩
  have l₁ : p ≤ p' := tile_le_of_cube_le_and_not_disjoint lK Qxp Qxp'
  have l₂ : p' ≤ p'' := tile_le_of_cube_le_and_not_disjoint Kl Qxp' Qxp''
  refine ⟨(t.ordConnected hu).out mp mp'' ⟨l₁, l₂⟩, ⟨(Grid.le_def.mp lK).1 xp, Qxp', ?_⟩⟩
  exact Icc_subset_Icc sxp.1 sxp''.2 ⟨(Grid.le_def.mp lK).2, (Grid.le_def.mp Kl).2⟩

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓙 : ⋃ J ∈ 𝓙 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  classical
  refine subset_antisymm (iUnion₂_subset_iUnion ..) fun x mx ↦ ?_
  simp_rw [mem_iUnion] at mx ⊢; obtain ⟨I, mI⟩ := mx
  obtain ⟨J, sJ, mJ⟩ :=
    Grid.exists_containing_subcube _ ⟨le_rfl, scale_mem_Icc.1⟩ mI
  have : J ∈ (𝓙₀ 𝔖).toFinset := by rw [mem_toFinset]; left; exact sJ
  obtain ⟨M, lM, maxM⟩ := (𝓙₀ 𝔖).toFinset.exists_le_maximal this
  simp_rw [mem_toFinset] at maxM
  use M, maxM, (Grid.le_def.mp lM).1 mJ

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓛 : ⋃ J ∈ 𝓛 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  classical
  refine subset_antisymm (iUnion₂_subset_iUnion ..) fun x mx ↦ ?_
  simp_rw [mem_iUnion] at mx ⊢; obtain ⟨I, mI⟩ := mx
  obtain ⟨J, sJ, mJ⟩ :=
    Grid.exists_containing_subcube _ ⟨le_rfl, scale_mem_Icc.1⟩ mI
  have : J ∈ (𝓛₀ 𝔖).toFinset := by rw [mem_toFinset]; left; exact sJ
  obtain ⟨M, lM, maxM⟩ := (𝓛₀ 𝔖).toFinset.exists_le_maximal this
  simp_rw [mem_toFinset] at maxM
  use M, maxM, (Grid.le_def.mp lM).1 mJ

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓛 : (𝓛 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := fun I mI J mJ hn ↦ by
  have : IsAntichain (· ≤ ·) (𝓛 𝔖) := setOf_maximal_antichain _
  exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

/-- The constant used in `first_tree_pointwise`.
Has value `10 * 2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_1_4 (a : ℕ) : ℝ≥0 := 10 * 2 ^ ((𝕔 + 4) * a ^ 3)

-- Used in the proof of `exp_sub_one_le`, which is used to prove Lemma 7.1.4
private lemma exp_Lipschitz : LipschitzWith 1 (fun (t : ℝ) ↦ exp (.I * t)) := by
  have mul_I : Differentiable ℝ fun (t : ℝ) ↦ I * t := Complex.ofRealCLM.differentiable.const_mul I
  refine lipschitzWith_of_nnnorm_deriv_le mul_I.cexp (fun x ↦ ?_)
  have : (fun (t : ℝ) ↦ cexp (I * t)) = cexp ∘ (fun (t : ℝ) ↦ I * t) := rfl
  rw [this, deriv_comp x differentiableAt_exp (mul_I x), Complex.deriv_exp, deriv_const_mul_field']
  simp_rw [show deriv ofReal x = 1 from ofRealCLM.hasDerivAt.deriv, mul_one]
  rw [nnnorm_mul, nnnorm_I, mul_one, ← norm_toNNReal, mul_comm, Complex.norm_exp_ofReal_mul_I]
  exact Real.toNNReal_one.le

-- Used in the proof of Lemma 7.1.4
private lemma exp_sub_one_le (t : ℝ) : ‖exp (.I * t) - 1‖ ≤ ‖t‖ := by
  simpa [enorm_eq_nnnorm] using exp_Lipschitz t 0

-- Used in the proofs of Lemmas 7.1.4 and 7.1.5
private lemma dist_lt_5 (hu : u ∈ t) (mp : p ∈ t.𝔗 u) (Qxp : Q x ∈ Ω p) :
    dist_(p) (𝒬 u) (Q x) < 5 := calc
  _ ≤ dist_(p) (𝒬 u) (𝒬 p) + dist_(p) (Q x) (𝒬 p) := dist_triangle_right ..
  _ < 4 + 1 :=
    add_lt_add ((t.smul_four_le hu mp).2 (by convert mem_ball_self zero_lt_one)) (subset_cball Qxp)
  _ = 5 := by norm_num

-- The bound in the third display in the proof of Lemma 7.1.4
private lemma L7_1_4_bound (hu : u ∈ t) {s : ℤ} (hs : s ∈ t.σ u x) {y : X} (hKxy : Ks s x y ≠ 0) :
    ‖exp (.I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖ₑ ≤
    5 * 2 ^ (4 * a) * 2 ^ (s - σMax t u x ⟨s, hs⟩) := by
  rw [← enorm_norm]
  have tr : 5 * 2 ^ (4 * a) * 2 ^ (s - t.σMax u x ⟨s, hs⟩) =
      ‖(5 : ℝ) * 2 ^ (4 * a) * 2 ^ (s - t.σMax u x ⟨s, hs⟩)‖ₑ := by
    simp_rw [enorm_mul, enorm_pow]; congr <;> rw [enorm_eq_nnnorm]
    · norm_num
    · norm_num
    · rw [nnnorm_zpow, ENNReal.coe_zpow (by simp), Real.nnnorm_ofNat, ENNReal.coe_ofNat]
  rw [tr]; apply Real.enorm_le_enorm (norm_nonneg _)
  have ⟨pₛ, pu, xpₛ, hpₛ⟩ := t.exists_p_of_mem_σ u x hs
  have ⟨p', p'u, xp', hp'⟩ := t.exists_p_of_mem_σ u x (t.σMax_mem_σ u x ⟨s, hs⟩)
  have hr : (D : ℝ) ^ s / 2 > 0 := by rw [defaultD]; positivity
  have s_le : GridStructure.s (𝓘 pₛ) ≤ GridStructure.s (𝓘 p') := by convert (σ t u x).le_max' s hs
  have exp_bound :
      ‖exp (.I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖ ≤ ‖𝒬 u y - Q x y - 𝒬 u x + Q x x‖ := by
    convert exp_sub_one_le (- 𝒬 u y + Q x y + 𝒬 u x - Q x x) using 1
    · simp
    · rw [← norm_neg]; ring_nf
  have : dist_(pₛ) (𝒬 u) (Q x) ≤ 2 ^ (s - σMax t u x ⟨s, hs⟩) * dist_(p') (𝒬 u) (Q x) := by
    have pₛ_le_p' : 𝓘 pₛ ≤ 𝓘 p' := le_of_mem_of_mem s_le xpₛ.1 xp'.1
    have sub_ge_0 : t.σMax u x ⟨s, hs⟩ - s ≥ 0 := by unfold σMax; linarith [(σ t u x).le_max' s hs]
    have : GridStructure.s (𝓘 pₛ) + (σMax t u x ⟨s, hs⟩ - s) = GridStructure.s (𝓘 p') := by
      simp_rw [← hp', ← hpₛ, 𝔰, _root_.s]; ring
    apply le_trans <| Grid.dist_strictMono_iterate' sub_ge_0 pₛ_le_p' this
    gcongr
    calc  C2_1_2 a ^ (t.σMax u x ⟨s, hs⟩ - s)
      _ ≤ C2_1_2 a ^ (t.σMax u x ⟨s, hs⟩ - s : ℝ)                     := by norm_cast
      _ ≤ (1 / 2 : ℝ) ^ (t.σMax u x ⟨s, hs⟩ - s : ℝ)                  :=
        Real.rpow_le_rpow (by rw [C2_1_2]; positivity)
          ((C2_1_2_le_inv_256 X).trans (by norm_num)) (by norm_cast)
      _ = 2 ^ (s - σMax t u x ⟨s, hs⟩)                                := by simp [← Int.cast_sub]
  calc ‖exp (.I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖
    _ ≤ dist_{x, D ^ s / 2} (𝒬 u) (Q x) :=
      exp_bound.trans <| oscillation_le_cdist x _ (𝒬 u) (Q x)
        (mem_ball_comm.mp (mem_Ioo.mp (dist_mem_Ioo_of_Ks_ne_zero hKxy)).2) (mem_ball_self hr)
    _ ≤ _ := cdist_mono <| ball_subset_ball (show (D : ℝ) ^ s / 2 ≤ 4 * D ^ s by linarith)
    _ ≤ defaultA a * dist_{𝔠 pₛ, 2 * D ^ s} (𝒬 u) (Q x) := by
      have two_mul_two : 2 * (2 * (D : ℝ) ^ s) = 4 * D ^ s := by ring
      have x_in_ball : dist (𝔠 pₛ) x < 2 * (2 * D ^ s) := by
        rw [two_mul_two, ← hpₛ]
        exact mem_ball'.mp <| Grid_subset_ball xpₛ.1
      refine le_of_eq_of_le ?_ (cdist_le x_in_ball)
      rw [two_mul_two]
    _ ≤ defaultA a * (defaultA a ^ 3 * dist_(pₛ) (𝒬 u) (Q x)) := by
      gcongr
      convert cdist_le_iterate (div_pos (defaultD_pow_pos a s) four_pos) _ _ _ using 2
      · rw [show 2 ^ 3 * ((D : ℝ) ^ s / 4) = 2 * D ^ s by ring]
      · rw [hpₛ]
    _ = (defaultA a) ^ 4 * dist_(pₛ) (𝒬 u) (Q x) := by ring
    _ ≤ (2 ^ a) ^ 4 * (2 ^ (s - t.σMax u x _) * dist_(p') (𝒬 u) (Q x)) := by norm_cast; gcongr
    _ ≤ (2 ^ a) ^ 4 * (2 ^ (s - t.σMax u x _) * 5) := by gcongr; exact (dist_lt_5 hu p'u xp'.2.1).le
    _ = 5 * 2 ^ (4 * a) * 2 ^ (s - σMax t u x ⟨s, hs⟩) := by ring

-- The bound used implicitly in the fourth displayed inequality in the proof of Lemma 7.1.4
variable (f) in
private lemma L7_1_4_integrand_bound (hu : u ∈ t) {s : ℤ} (hs : s ∈ t.σ u x) (y : X) :
    ‖(exp (.I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks s x y * f y‖ₑ ≤
    5 * 2 ^ (s - σMax t u x ⟨s, hs⟩) *
      (2 ^ ((𝕔 + 3) * a ^ 3) / volume (ball x (D ^ s))) * ‖f y‖ₑ := by
  by_cases hKxy : Ks s x y = 0
  · rw [hKxy, mul_zero, zero_mul, enorm_zero]; positivity
  · rw [enorm_mul, enorm_mul]; refine mul_le_mul_left ?_ _
    apply mul_le_mul' (L7_1_4_bound hu hs hKxy) enorm_Ks_le |>.trans
    rw [mul_assoc 5, mul_comm (2 ^ (4 * a)), ← mul_assoc, mul_assoc, mul_div, C2_1_3]
    gcongr; norm_cast; rw [← pow_add]
    refine Nat.pow_le_pow_right two_pos <| Nat.add_le_of_le_sub ?_ ?_
    · exact Nat.mul_le_mul_right _ (by norm_num)
    · rw [← Nat.sub_mul, (show a ^ 3 = a ^ 2 * a from rfl)]
      simp only [Nat.reduceSubDiff, add_tsub_cancel_left, one_mul]
      nlinarith [four_le_a X]

-- The geometric sum used to prove `L7_1_4_sum`
private lemma sum_pow_two_le (a b : ℤ) : ∑ s ∈ Finset.Icc a b, (2 : ℝ≥0∞) ^ s ≤ 2 ^ (b + 1) := by
  by_cases h : b < a
  · simp [Finset.Icc_eq_empty_of_lt h]
  obtain ⟨k, rfl⟩ : ∃ (k : ℕ), b = a + k := ⟨(b - a).toNat, by simp [not_lt.mp h]⟩
  suffices ∑ s ∈ Finset.Icc a (a + k), (2 : ℝ≥0∞) ^ s = 2 ^ a * ∑ n ∈ Finset.range (k + 1), 2 ^ n by
    rw [this, add_assoc, ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top]; gcongr; norm_cast
    rw [Nat.geomSum_eq le_rfl]; norm_num
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun n hn ↦ (n - a).toNat)
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range, Int.toNat_lt (Int.sub_nonneg.mpr hn.1), Nat.cast_add, Nat.cast_one]
    linarith
  · intro n hn m hm hnm
    rw [Finset.mem_Icc] at hn hm
    have := congrArg Int.ofNat hnm
    simpa [max_eq_left (Int.sub_nonneg.mpr hn.1), max_eq_left (Int.sub_nonneg.mpr hm.1)] using this
  · exact fun n hn ↦ by use a + n, by simp [Nat.le_of_lt_succ (Finset.mem_range.mp hn)], by simp
  · intro n hn
    rw [← zpow_natCast, Int.ofNat_toNat, ← ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top,
      sup_eq_left.mpr <| Int.sub_nonneg_of_le (Finset.mem_Icc.mp hn).1, add_sub_cancel]

-- The sum used in the proof of Lemma 7.1.4
private lemma L7_1_4_sum (hσ : (t.σ u x).Nonempty) :
    ∑ s ∈ t.σ u x, (2 : ℝ≥0∞) ^ (s - t.σMax u x hσ) ≤ 2 := by
  have {s : ℤ} : (2 : ℝ≥0∞) ^ (s - t.σMax u x hσ) = 2 ^ s * 2 ^ (-t.σMax u x hσ) := by
    rw [← ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top, Int.sub_eq_add_neg]
  simp_rw [this, ← Finset.sum_mul]
  suffices ∑ s ∈ t.σ u x, (2 : ℝ≥0∞) ^ s ≤ 2 ^ (t.σMax u x hσ + 1) by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (t.σMax u x hσ + 1) * 2 ^ (-t.σMax u x hσ) := by gcongr
      _ = _ := by rw [← ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top]; simp
  refine (Finset.sum_le_sum_of_subset ?_).trans (sum_pow_two_le (t.σMin u x hσ) (t.σMax u x hσ))
  exact fun s hs ↦ Finset.mem_Icc.mpr <| ⟨(t.σ u x).min'_le s hs, (t.σ u x).le_max' s hs⟩

-- Inequality used twice in the proof of Lemma 7.1.4
private lemma L7_1_4_dist_le {p : 𝔓 X} (xp : x ∈ E p) {J : Grid X}
    (hJ : ((J : Set X) ∩ ball x (D ^ 𝔰 p / 2)).Nonempty) :
    dist (c J) (𝔠 p) ≤ 4 * D ^ (s J) + 4.5 * D ^ (𝔰 p) := by
  have ⟨z, hz⟩ := hJ
  calc dist (c J) (𝔠 p)
    _ ≤ dist (c J) z + dist z x + dist x (𝔠 p)           := dist_triangle4 (c J) z x (𝔠 p)
    _ ≤ 4 * D ^ (s J) + 0.5 * D ^ (𝔰 p) + 4 * D ^ (𝔰 p)  := by
      apply add_le_add_three
      · exact (mem_ball'.mp <| Grid_subset_ball hz.1).le
      · convert (mem_ball.mp hz.2).le using 1
        exact (eq_div_iff two_ne_zero).mpr (by linarith)
      · exact (mem_ball.mp <| Grid_subset_ball xp.1).le
    _ ≤ 4 * D ^ (s J) + 4.5 * D ^ (𝔰 p)                  := by linarith [defaultD_pow_pos a (𝔰 p)]

-- Inequality needed for the proof of `L7_1_4_integral_le_integral`
private lemma s_le_s {p : 𝔓 X} (pu : p ∈ t.𝔗 u) (xp : x ∈ E p)
    {J : Grid X} (hJ : J ∈ 𝓙 (t.𝔗 u) ∧ ((J : Set X) ∩ ball x (D ^ 𝔰 p / 2)).Nonempty) :
    s J ≤ 𝔰 p := by
  have ⟨z, hz⟩ := hJ.2
  by_cases! h : s J ≤ 𝔰 p ∨ s J = -S
  · exact h.elim id (· ▸ (range_s_subset ⟨𝓘 p, rfl⟩).1)
  apply False.elim ∘ hJ.1.1.resolve_left h.2 p pu ∘ le_trans Grid_subset_ball ∘ ball_subset_ball'
  have : (D : ℝ) ^ 𝔰 p ≤ D ^ s J := (zpow_le_zpow_iff_right₀ (one_lt_realD (X := X))).mpr h.1.le
  calc 4 * (D : ℝ) ^ GridStructure.s (𝓘 p) + dist (GridStructure.c (𝓘 p)) (c J)
    _ ≤ 4 * (D : ℝ) ^ (s J) + (4 * D ^ (s J) + 4.5 * D ^ (s J)) := by
      gcongr 4 * ?_ + ?_
      · exact this
      · exact dist_comm (c (𝓘 p)) (c J) ▸ L7_1_4_dist_le xp hJ.2 |>.trans (by gcongr)
    _ ≤ 100 * D ^ (s J + 1) := by
      rw [zpow_add' (Or.inl (realD_pos a).ne.symm), zpow_one]
      nlinarith [one_le_realD a, defaultD_pow_pos a (s J)]

private lemma ball_covered_by_𝓙 (hu : u ∈ t) {p : 𝔓 X} (pu : p ∈ t u) (xp : x ∈ E p) :
    ball x (D ^ 𝔰 p / 2) ⊆ ⋃ J ∈ 𝓙 (t.𝔗 u), (J : Set X) :=
  calc ball x (D ^ 𝔰 p / 2)
    _ ⊆ ball x (4 * D ^ 𝔰 p)          := ball_subset_ball <| by linarith [defaultD_pow_pos a (𝔰 p)]
    _ ⊆ (𝓘 u : Set X)                 := ball_subset_of_mem_𝓘 hu pu xp.1
    _ ⊆ ⋃ (I : Grid X), (I : Set X)   := le_iSup _ _
    _ = ⋃ J ∈ 𝓙 (t.𝔗 u), (J : Set X) := biUnion_𝓙.symm

private lemma Grid_subset_ball' {J : Grid X} {p : 𝔓 X} (pu : p ∈ t.𝔗 u) {x : X} (xp : x ∈ E p)
  (hJ : J ∈ 𝓙 (t.𝔗 u) ∧ (↑J ∩ ball x (↑D ^ 𝔰 p / 2)).Nonempty) :
  (J : Set X) ⊆ ball (𝔠 p) (16 * ↑D ^ 𝔰 p) := by
  have ⟨z, hz⟩ := hJ.2
  refine Grid_subset_ball.trans (ball_subset_ball' ?_)
  change _ * _ ^ (s J) + dist (c J) _ ≤ _
  have := (zpow_le_zpow_iff_right₀ (one_lt_realD (X := X))).mpr <| s_le_s pu xp hJ
  linarith [L7_1_4_dist_le xp hJ.2, defaultD_pow_pos a (𝔰 p)]

-- The integral bound needed for the proof of Lemma 7.1.4
private lemma L7_1_4_integral_le_integral (hu : u ∈ t) (hf : BoundedCompactSupport f) {p : 𝔓 X}
    (pu : p ∈ t u) (xp : x ∈ E p) : ∫⁻ y in ball x (D ^ 𝔰 p / 2), ‖f y‖ₑ ≤
    ∫⁻ y in ball (𝔠 p) (16 * D ^ 𝔰 p), ‖approxOnCube (𝓙 (t u)) (‖f ·‖) y‖ₑ := by
  classical
  let Js := Set.toFinset { J ∈ 𝓙 (t u) | ((J : Set X) ∩ ball x (D ^ (𝔰 p) / 2)).Nonempty }
  have mem_Js {J : Grid X} : J ∈ Js ↔ J ∈ 𝓙 (t.𝔗 u) ∧ (↑J ∩ ball x (D ^ 𝔰 p / 2)).Nonempty := by
    simp [Js]
  have Js_disj : (Js : Set (Grid X)).Pairwise (Disjoint on fun J ↦ (J : Set X)) :=
    fun i₁ hi₁ i₂ hi₂ h ↦ pairwiseDisjoint_𝓙 (mem_Js.mp hi₁).1 (mem_Js.mp hi₂).1 h
  calc
    _ ≤ ∫⁻ y in (⋃ J ∈ Js, (J : Set X)), ‖f y‖ₑ := by
      apply lintegral_mono_set
      have h := ball_covered_by_𝓙 hu pu xp
      refine (subset_inter_iff.mpr ⟨h, subset_refl _⟩).trans fun y hy ↦ ?_
      have ⟨J, hJ, yJ⟩ := Set.mem_iUnion₂.mp hy.1
      exact ⟨J, ⟨⟨J, by simp [mem_Js.mpr ⟨hJ, ⟨y, mem_inter yJ hy.2⟩⟩]⟩, yJ⟩⟩
    _ = ∑ J ∈ Js, ∫⁻ y in J, ‖f y‖ₑ := by
      rw [lintegral_biUnion_finset Js_disj fun _ _ ↦ coeGrid_measurable]
    _ = ∑ J ∈ Js, ∫⁻ y in J, ‖approxOnCube (𝓙 (t u)) (‖f ·‖) y‖ₑ := by
      refine Finset.sum_congr rfl fun J hJ ↦ ?_
      have eo : EqOn (fun y ↦ ‖approxOnCube (𝓙 (t u)) (‖f ·‖) y‖ₑ)
          (fun _ ↦ ‖⨍ y in J, ‖f y‖‖ₑ) J := fun y hy ↦ by
        dsimp only; congr; exact approxOnCube_apply pairwiseDisjoint_𝓙 (‖f ·‖) (mem_Js.mp hJ).1 hy
      have vJn0 : volume (J : Set X) ≠ 0 := (volume_coeGrid_pos (defaultD_pos a)).ne'
      have vJnt : volume (J : Set X) ≠ ⊤ := volume_coeGrid_lt_top.ne
      rw [setLIntegral_congr_fun coeGrid_measurable eo, setLIntegral_const, setAverage_eq,
        enorm_smul, Measure.real, enorm_inv]; swap
      · exact ENNReal.toReal_ne_zero.mpr ⟨vJn0, vJnt⟩
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal vJnt, ← mul_rotate,
        ENNReal.mul_inv_cancel vJn0 vJnt, one_mul,
        integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable.restrict,
        Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
      have := (hf.integrable.integrableOn (s := J)).2
      unfold HasFiniteIntegral at this; exact this.ne
    _ = ∫⁻ y in (⋃ J ∈ Js, (J : Set X)), ‖approxOnCube (𝓙 (t u)) (‖f ·‖) y‖ₑ := by
      rw [lintegral_biUnion_finset Js_disj fun _ _ ↦ coeGrid_measurable]
    _ ≤ _ := by
      refine lintegral_mono_set (iUnion₂_subset_iff.mpr fun J hJ ↦ ?_)
      exact Grid_subset_ball' pu xp (mem_Js.mp hJ)

-- An average over `ball (𝔠 p) (16 * D ^ 𝔰 p)` is bounded by `MB`; needed for Lemma 7.1.4
private lemma L7_1_4_laverage_le_MB (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L) (g : X → ℝ)
    {p : 𝔓 X} (pu : p ∈ t.𝔗 u) (xp : x ∈ E p) :
    (∫⁻ y in ball (𝔠 p) (16 * D ^ 𝔰 p), ‖g y‖ₑ) / volume (ball (𝔠 p) (16 * D ^ 𝔰 p)) ≤
    MB volume 𝓑 c𝓑 r𝓑 g x' := by
  have mem_𝓑 : (4, 0, 𝓘 p) ∈ 𝓑 := by simp [𝓑]
  convert le_biSup (hi := mem_𝓑) <| fun i ↦ ((ball (c𝓑 i) (r𝓑 i)).indicator (x := x') <|
    fun _ ↦ ⨍⁻ y in ball (c𝓑 i) (r𝓑 i), ‖g y‖ₑ ∂volume)
  · have x'_in_ball : x' ∈ ball (c𝓑 (4, 0, 𝓘 p)) (r𝓑 (4, 0, 𝓘 p)) := by
      simp_rw [c𝓑, r𝓑, _root_.s, Nat.cast_zero, add_zero]
      have : x' ∈ 𝓘 p := subset_of_mem_𝓛 hL pu (not_disjoint_iff.mpr ⟨x, xp.1, hx⟩) hx'
      refine Metric.ball_subset_ball ?_ <| Grid_subset_ball this
      linarith [defaultD_pow_pos a (GridStructure.s (𝓘 p))]
    have hc𝓑 : 𝔠 p = c𝓑 (4, 0, 𝓘 p) := by simp [c𝓑, 𝔠]
    have hr𝓑 : 16 * D ^ 𝔰 p = r𝓑 (4, 0, 𝓘 p) := by rw [r𝓑, 𝔰]; norm_num
    simp [-defaultD, laverage, x'_in_ball, ENNReal.div_eq_inv_mul, hc𝓑, hr𝓑]
  · simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one]

/-- Lemma 7.1.4 -/
lemma first_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖∑ i ∈ t.σ u x, ∫ y, (exp (.I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y * f y‖ₑ ≤
    C7_1_4 a * MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  let _ : MulPosReflectLE ℝ := inferInstance -- perf: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/performance.20example.20with.20type-class.20inference
  let _ : PosMulReflectLE ℝ := inferInstance -- perf: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/performance.20example.20with.20type-class.20inference
  set g := approxOnCube (𝓙 (t u)) (‖f ·‖)
  let q (y) := -𝒬 u y + Q x y + 𝒬 u x - Q x x
  rcases (t.σ u x).eq_empty_or_nonempty with hσ | hσ; · simp [hσ]
  have : ∀ s ∈ t.σ u x, ‖∫ y, (cexp (I * (q y)) - 1) * Ks s x y * f y‖ₑ ≤
      ∫⁻ y, ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ := fun s hs ↦
    (enorm_integral_le_lintegral_enorm _).trans (by simp)
  conv_lhs =>
    enter [1, 2, s, 2, y]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  refine (enorm_sum_le _ _).trans <| ((t.σ u x).sum_le_sum this).trans ?_
  suffices ∀ s ∈ t.σ u x, ∫⁻ y, ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ ≤
      (5 * 2 ^ ((𝕔 + 4) * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 g x') * 2 ^ (s - t.σMax u x hσ) by
    apply ((t.σ u x).sum_le_sum this).trans
    rw [← Finset.mul_sum]
    apply le_trans <| mul_le_mul_right (L7_1_4_sum hσ) _
    rw [mul_comm _ 2, ← mul_assoc, ← mul_assoc, C7_1_4]
    gcongr; norm_num
  intro s hs
  have eq1 : ∫⁻ y, ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ =
      ∫⁻ y in ball x (D ^ s / 2), ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ := by
    rw [← lintegral_indicator measurableSet_ball]; congr! 2 with y
    symm; rw [indicator_apply_eq_self]; intro my
    suffices Ks s x y = 0 by simp [this]
    contrapose! my; apply dist_mem_Ioo_of_Ks_ne_zero at my
    rw [mem_Ioo] at my; rw [mem_ball']; exact my.2
  have eq2 : ∫⁻ y in ball x (D ^ s / 2), ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ ≤
      5 * 2 ^ (s - σMax t u x ⟨s, hs⟩) * (2 ^ ((𝕔 + 3) * a ^ 3) / volume (ball x (D ^ s))) *
      ∫⁻ y in ball x (D ^ s / 2), ‖f y‖ₑ := by
    convert (lintegral_mono (L7_1_4_integrand_bound f hu hs)).trans ?_
    · norm_cast
    · rw [lintegral_const_mul'' _ hf.aestronglyMeasurable.enorm.restrict]
  apply le_of_eq_of_le eq1 ∘ eq2.trans
  rw [← mul_rotate _ (5 * 2 ^ ((𝕔 + 4) * a ^ 3)), ← mul_assoc, mul_comm _ 5]
  simp_rw [mul_assoc]; gcongr _ * (_ * ?_)
  rw [show (𝕔 + 4) * a ^ 3 = (𝕔 + 3) * a ^ 3 + a ^ 3 by ring, pow_add, mul_assoc,
    ENNReal.mul_comm_div]
  gcongr
  have ⟨pₛ, pₛu, xpₛ, hpₛ⟩ := t.exists_p_of_mem_σ u x hs
  have ball_subset : ball (𝔠 pₛ) (16 * D ^ s) ⊆ ball x ((2 ^ 5) * D ^ s) := by
    apply ball_subset_ball'
    calc
      _ ≤ (16 : ℝ) * D ^ s + 4 * D ^ 𝔰 pₛ :=
        add_le_add_right (mem_ball'.mp (Grid_subset_ball xpₛ.1)).le _
      _ = 16 * D ^ s + 4 * D ^ s := by nth_rw 3 [← hpₛ]
      _ ≤ _ := by linarith only [defaultD_pow_pos a s]
  calc
  _ ≤ 2 ^ (5 * a) * ((∫⁻ y in ball x (D ^ s / 2), ‖f y‖ₑ) / volume (ball (𝔠 pₛ) (16 * D ^ s))) := by
    rw [mul_comm, ENNReal.div_mul _ (.inr (by positivity)) (.inr (by finiteness))]; gcongr
    refine ENNReal.div_le_of_le_mul' ((measure_mono ball_subset).trans ?_)
    convert measure_ball_two_le_same_iterate (μ := volume) x (D ^ s) 5 using 2
    simp [mul_comm 5 a, pow_mul]
  _ ≤ _ := by
    gcongr ?_ * ?_
    · apply pow_right_mono₀ one_le_two
      rw [pow_succ a 2, mul_le_mul_iff_left₀ (a_pos X)]
      nlinarith [four_le_a X]
    · refine le_trans ?_ (L7_1_4_laverage_le_MB hL hx hx' g pₛu xpₛ)
      rw [hpₛ]; gcongr ?_ / _
      rw [← hpₛ]; exact L7_1_4_integral_le_integral hu hf pₛu xpₛ

/-- Lemma 7.1.5 -/
lemma second_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L) :
    ‖∑ i ∈ t.σ u x, ∫ y, Ks i x y * approxOnCube (𝓙 (t u)) f y‖ₑ ≤
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x' := by
  rcases (t.σ u x).eq_empty_or_nonempty with hne | hne; · simp [hne]
  let s₁ := Finset.min' (t.σ u x) hne
  have ms₁ : s₁ ∈ t.σ u x := Finset.min'_mem ..
  simp_rw [σ, Finset.mem_image, Finset.mem_filter_univ] at ms₁
  obtain ⟨p, ⟨mp, xp, _, _⟩, sp⟩ := ms₁
  have Lle : L ≤ 𝓘 p := by
    rcases 𝓛_subset_𝓛₀ hL with hL | hL
    · exact le_of_mem_of_mem (hL.symm ▸ scale_mem_Icc.1) hx xp
    · exact (le_or_ge_of_mem_of_mem xp hx).resolve_left (hL.2 p mp)
  let s₂ := Finset.max' (t.σ u x) hne
  have ms₂ : s₂ ∈ t.σ u x := Finset.max'_mem ..
  simp_rw [σ, Finset.mem_image, Finset.mem_filter_univ] at ms₂
  obtain ⟨p', ⟨mp', xp', Qxp', _⟩, sp'⟩ := ms₂
  have s_ineq : 𝔰 p ≤ 𝔰 p' := by
    rw [sp, sp']; exact (t.σ u x).min'_le s₂ (Finset.max'_mem ..)
  have pinc : 𝓘 p ≤ 𝓘 p' := le_of_mem_of_mem s_ineq xp xp'
  have d5 : dist_(p') (𝒬 u) (Q x) < 5 := dist_lt_5 hu mp' Qxp'
  have d5' : dist_{x, D ^ s₂} (𝒬 u) (Q x) < 5 * defaultA a ^ 5 := by
    have i1 : dist x (𝔠 p) < 4 * D ^ 𝔰 p' :=
      (mem_ball.mp (Grid_subset_ball xp)).trans_le <|
        mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (one_le_realD _) s_ineq) zero_le_four
    have i2 : dist (𝔠 p') (𝔠 p) < 4 * D ^ 𝔰 p' :=
      mem_ball'.mp (ball_subset_Grid.trans (Grid.le_def.mp pinc).1 |>.trans Grid_subset_ball <|
        mem_ball_self (by unfold defaultD; positivity))
    calc
      _ ≤ dist_{𝔠 p, 8 * D ^ 𝔰 p'} (𝒬 u) (Q x) := by
        refine cdist_mono (ball_subset_ball' ?_); rw [← sp']
        calc
          _ ≤ (D : ℝ) ^ 𝔰 p' + 4 * D ^ 𝔰 p' := add_le_add_right i1.le _
          _ = 5 * D ^ 𝔰 p' := by ring
          _ ≤ _ := by gcongr; norm_num
      _ ≤ defaultA a * dist_{𝔠 p', 4 * D ^ 𝔰 p'} (𝒬 u) (Q x) := by
        convert cdist_le (x₂ := 𝔠 p) _ using 1
        · exact dist_congr rfl (by ring)
        · apply i2.trans_le; nth_rw 1 [← one_mul (4 * _)]; gcongr; exact one_le_two
      _ ≤ defaultA a ^ 5 * dist_(p') (𝒬 u) (Q x) := by
        rw [pow_succ', mul_assoc]; gcongr
        convert cdist_le_iterate _ (𝒬 u) (Q x) 4 using 1
        · exact dist_congr rfl (by ring)
        · unfold defaultD; positivity
      _ < _ := by rw [mul_comm]; gcongr
  have d1 : dist_{x, D ^ (s₂ - 1)} (𝒬 u) (Q x) < 1 := by
    calc
      _ ≤ dist_{x, D ^ s₂} (𝒬 u) (Q x) * 2 ^ (-𝕔 * a : ℤ) := by
        rw [neg_mul, zpow_neg, le_mul_inv_iff₀ (by positivity), mul_comm]
        convert le_cdist_iterate _ (𝒬 u) (Q x) (𝕔 * a) using 1
        · apply dist_congr rfl
          rw [Nat.cast_pow, ← pow_mul, show a * (𝕔 * a) = 𝕔 * a ^ 2 by ring, ← Nat.cast_pow]
          change _ = (D : ℝ) * _
          rw [← zpow_one_add₀ (realD_pos _).ne', add_sub_cancel]
        · unfold defaultD; positivity
      _ < 5 * defaultA a ^ 5 * 2 ^ (-𝕔 * a : ℤ) := by gcongr
      _ = 5 * (2 : ℝ) ^ (-(𝕔 - 5) * a : ℤ) := by
        rw [Nat.cast_pow, ← pow_mul, ← zpow_natCast, show (2 : ℕ) = (2 : ℝ) by rfl, mul_assoc,
          ← zpow_add₀ two_ne_zero]
        congr
        simp
        ring
      _ ≤ 5 * 2 ^ (-3 : ℤ) := by
        gcongr
        · exact one_le_two
        · simp only [neg_sub, sub_mul, Int.reduceNeg, tsub_le_iff_right, le_neg_add_iff_add_le]
          norm_cast
          calc
          3 + 5 * a
          _ ≤ a + 5 * a := by gcongr; linarith [four_le_a X]
          _ = 6 * a := by ring
          _ ≤ 𝕔 * a := by gcongr; linarith [seven_le_c]
      _ < _ := by norm_num
  have x'p : x' ∈ 𝓘 p := (Grid.le_def.mp Lle).1 hx'
  refine le_iSup₂_of_le (𝓘 p) x'p <| le_iSup₂_of_le x xp <|
    le_iSup₂_of_le (𝔰 p') ⟨s_ineq, scale_mem_Icc.2⟩ <| le_iSup_of_le ?_ ?_
  · apply le_upperRadius; convert d1
  · convert le_rfl; change (Icc (𝔰 p) _).toFinset = _; rw [sp, sp']
    apply subset_antisymm
    · rw [← Finset.toFinset_coe (t.σ u x), toFinset_subset_toFinset]
      exact (convex_scales hu).out (Finset.min'_mem ..) (Finset.max'_mem ..)
    · intro z mz; rw [toFinset_Icc, Finset.mem_Icc]
      exact ⟨Finset.min'_le _ _ mz, Finset.le_max' _ _ mz⟩

/-- The constant used in `third_tree_pointwise`.
Has value `2 ^ (128 * a ^ 3)` in the blueprint. -/
irreducible_def C7_1_6 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 3 + 𝕔 / 4) * a ^ 3)

-- Used in the proof of Lemmas 7.1.3 and 7.1.6 to translate between `∑ p` into `∑ s`
open scoped Classical in
private lemma p_sum_eq_s_sum {α : Type*} [AddCommMonoid α] (I : ℤ → X → α) :
    ∑ p ∈ Finset.univ.filter (· ∈ t.𝔗 u), (E p).indicator (I (𝔰 p)) x =
    ∑ s ∈ t.σ u x, I s x := by
  -- Restrict to a sum over those `p` such that `x ∈ E p`.
  let 𝔗' := Finset.univ.filter (fun p ↦ p ∈ t.𝔗 u ∧ x ∈ E p)
  have : ∑ p ∈ 𝔗', (E p).indicator (I (𝔰 p)) x =
      ∑ p ∈ Finset.univ.filter (· ∈ t.𝔗 u), (E p).indicator (I (𝔰 p)) x := by
    apply Finset.sum_subset (fun p hp ↦ by simp [(Finset.mem_filter.mp hp).2.1])
    intro p p𝔗 p𝔗'
    simp_rw [𝔗', Finset.mem_filter_univ, not_and] at p𝔗 p𝔗'
    exact indicator_of_notMem (p𝔗' p𝔗) (I (𝔰 p))
  rw [← this]
  -- Now the relevant values of `p` and `s` are in bijection.
  apply Finset.sum_bij (fun p _ ↦ 𝔰 p)
  · intro p hp
    simp only [σ, Finset.mem_image]
    exact ⟨p, by simpa [𝔗'] using hp⟩
  · intro p hp p' hp' hpp'
    simp only [E, Grid.mem_def, sep_and, Finset.mem_filter, 𝔗'] at hp hp'
    by_contra h
    exact Nonempty.not_disjoint ⟨Q x, ⟨hp.2.2.1.2, hp'.2.2.1.2⟩⟩ <| disjoint_Ω h <|
      (eq_or_disjoint hpp').resolve_right <| Nonempty.not_disjoint ⟨x, ⟨hp.2.2.1.1, hp'.2.2.1.1⟩⟩
  · intro s hs
    simpa [𝔗', σ] using hs
  · intro p hp
    simp only [Finset.mem_filter, 𝔗'] at hp
    exact indicator_of_mem hp.2.2 (I (𝔰 p))

-- Equation 7.1.10 from the blueprint
private lemma L7_1_6_integral_eq {J : Grid X} (hJ : J ∈ 𝓙 (t.𝔗 u)) {i : ℤ}
    (hf : BoundedCompactSupport f) : ∫ y in J, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y) =
    ∫ y in J, (⨍ z in J, (Ks i x y - Ks i x z)) * f y := by
  -- Preliminary trivialities
  have i1 : IntegrableOn (fun y ↦ Ks i x y * f y) (J : Set X) := by
    simp_rw [mul_comm]
    exact (hf.integrable_mul (integrable_Ks_x (one_lt_realD (X := X)))).restrict
  have i2 : IntegrableOn (fun y ↦ Ks i x y * ⨍ z in J, f z) (J : Set X) :=
    ((integrable_Ks_x (one_lt_realD (X := X))).mul_const _).integrableOn
  have eq1 : ∀ y ∈ (J : Set X), Ks i x y * (f y - approxOnCube (𝓙 (t.𝔗 u)) f y) =
      Ks i x y * (f y - ⨍ z in J, f z) :=
    fun y hy ↦ by rw [approxOnCube_apply pairwiseDisjoint_𝓙 _ hJ hy]
  have eq2 : ∀ y ∈ (J : Set X), ⨍ z in (J : Set X), Ks i x y • f y - Ks i x z • f y =
      (⨍ z in (J : Set X), Ks i x y • f y) - ⨍ z in (J : Set X), Ks i x z • f y :=
    fun y hy ↦ integral_sub ((integrableOn_const_iff).mpr (Or.inr volume_coeGrid_lt_top)).to_average
      ((integrable_Ks_x (one_lt_realD (X := X))).smul_const _).restrict.to_average
  have μJ_neq_0 : NeZero (volume.restrict (J : Set X)) :=
    NeZero.mk fun h ↦ (volume_coeGrid_pos (defaultD_pos a) (i := J)).ne <|
      by simpa [h] using Measure.restrict_apply_self volume (J : Set X)
  have μJ_finite := Restrict.isFiniteMeasure volume (hs := ⟨volume_coeGrid_lt_top (i := J)⟩)
  -- Split both sides into two separate integrals
  rw [setIntegral_congr_fun coeGrid_measurable eq1]
  simp_rw [mul_sub, integral_sub i1 i2, ← smul_eq_mul, ← average_smul_const, sub_smul]
  rw [setIntegral_congr_fun coeGrid_measurable eq2, integral_sub]
  · congr 1 -- Check that corresponding integrals are equal
    · exact setIntegral_congr_fun coeGrid_measurable (fun y hy ↦ (average_const _ _).symm)
    · simp_rw [average_smul_const, integral_smul_const, integral_smul, average_eq]
      rw [smul_comm, smul_assoc]
  -- Check integrability to justify the last use of `integral_sub`
  · simpa [average_const]
  · simp_rw [average_smul_const]
    change Integrable ((⨍ z in (J : Set X), Ks i x z) • f) (volume.restrict J)
    exact hf.integrable.restrict.smul _

-- Integral norm bound used implicitly in the third display of the proof of Lemma 7.1.6.
private lemma L7_1_6_integral_le {J : Grid X} (hJ : J ∈ 𝓙 (t u)) {i : ℤ}
    (hf : BoundedCompactSupport f) : ‖∫ y in J, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ ≤
    D2_1_3 a / volume (ball x (D ^ i)) * 2 ^ (3 / a : ℝ) *
    (D ^ ((s J - i) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
  let g (y : X) := ‖(⨍ z in J, Ks i x y - Ks i x z) * f y‖ₑ
  let h : X → ℝ≥0∞ := (D2_1_3 a / volume (ball x (D ^ i)) * 2 ^ (3 / a : ℝ) *
    D ^ ((s J - i : ℝ) / a)) • (‖f ·‖ₑ)
  simp_rw [L7_1_6_integral_eq hJ hf]
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  refine le_of_le_of_eq (setLIntegral_mono' (f := g) (g := h) coeGrid_measurable fun y hy ↦ ?_) (by
    simp_rw [h, Pi.smul_apply, smul_eq_mul]
    rw [lintegral_const_mul'' _ hf.aestronglyMeasurable.enorm.restrict, mul_assoc])
  simp_rw [g, h, enorm_mul, Pi.smul_apply, smul_eq_mul]
  refine mul_le_mul_left ?_ _
  have ⟨z₀, z₀J, hz₀⟩ : ∃ z₀ ∈ (J : Set X),
      ⨍⁻ z in J, ‖Ks i x y - Ks i x z‖ₑ ∂volume ≤ ‖Ks i x y - Ks i x z₀‖ₑ := by
    apply exists_setLAverage_le (volume_coeGrid_pos (defaultD_pos a)).ne.symm
    · exact coeGrid_measurable.nullMeasurableSet
    · simp_rw [← edist_eq_enorm_sub]; refine (lintegral_edist_lt_top ?_ ?_).ne
      · exact integrable_const_iff.mpr (by simp [volume_coeGrid_lt_top, isFiniteMeasure_iff])
      · exact (integrable_Ks_x (one_lt_realD (X := X))).restrict
  calc
    _ ≤ _ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := hz₀
    _ ≤ _ := enorm_Ks_sub_Ks_le
    _ ≤ _ := by
      rw [mul_assoc]; gcongr
      calc
      _ ≤ (8 * (D : ℝ≥0∞) ^ s J / D ^ i) ^ (a : ℝ)⁻¹ := by
        gcongr
        have : 8 * D ^ s J = ENNReal.ofReal (8 * D ^ s J) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← Real.rpow_intCast,
            ← ENNReal.ofReal_rpow_of_pos (realD_pos _), ENNReal.ofReal_natCast,
            ENNReal.rpow_intCast]
        rw [this, edist_le_ofReal (by positivity)]
        calc
          _ ≤ dist y (c J) + dist z₀ (c J) := dist_triangle_right _ _ _
          _ ≤ 4 * D ^ (s J) + 4 * D ^ (s J) :=
            add_le_add (mem_ball.mp (Grid_subset_ball hy)).le (mem_ball.mp (Grid_subset_ball z₀J)).le
          _ = 8 * D ^ (s J) := by ring
      _ = _ := by
        rw [← mul_div, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), sub_div,
          ENNReal.rpow_sub _ _ (by norm_cast; unfold defaultD; positivity) (by finiteness)]
        conv_rhs =>
          rw [div_eq_mul_inv, ENNReal.rpow_mul, div_eq_mul_inv _ (a : ℝ), ENNReal.rpow_mul,
            div_eq_mul_inv _ (a : ℝ), ENNReal.rpow_mul, ENNReal.rpow_intCast, ENNReal.rpow_intCast,
            ← ENNReal.div_rpow_of_nonneg _ _ (by positivity)]
        norm_num

-- Prove an upper bound for the function `I` used in the proof of Lemma 7.1.6
private lemma L7_1_6_I_le (hu : u ∈ t) (hf : BoundedCompactSupport f) {p : 𝔓 X} (hp : p ∈ t u)
    {x : X} (hxp : x ∈ E p) : ‖∫ y, Ks (𝔰 p) x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ ≤
    D2_1_3 a / volume (ball x (D ^ 𝔰 p)) * 2 ^ (3 / a : ℝ) *
    ∑ J ∈ 𝓙' t u (𝔠 p) (𝔰 p), (D : ℝ≥0∞) ^ ((s J - 𝔰 p) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ := by
  let U := ⋃ J ∈ 𝓙' t u (𝔠 p) (𝔰 p), (J : Set X)
  calc
  _ = ‖∫ y in U, Ks (𝔰 p) x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ := by
    refine congrArg (‖·‖ₑ) <| (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
    refine Eventually.of_forall (fun y hy ↦ ?_)
    suffices Ks (𝔰 p) x y = 0 by rw [this, zero_mul]
    contrapose! hy
    replace hy := dist_mem_Ioo_of_Ks_ne_zero hy |>.2
    have ⟨J, hJ, yJ⟩ : ∃ J ∈ 𝓙 (t u), y ∈ J := by
      have ⟨J, hJ⟩ := Set.mem_iUnion.mp <| ball_covered_by_𝓙 hu hp hxp (mem_ball'.mpr hy)
      use J
      simpa using hJ
    refine ⟨J, ⟨⟨J, ?_⟩, yJ⟩⟩
    suffices J ∈ 𝓙' t u (𝔠 p) (𝔰 p) by simp [this]
    simpa [𝓙', hJ] using And.intro (Grid_subset_ball' hp hxp ⟨hJ, y, yJ, mem_ball'.mpr hy⟩)
      (s_le_s hp hxp ⟨hJ, ⟨y, ⟨yJ, mem_ball'.mpr hy⟩⟩⟩)
  _ = ‖∑ J ∈ 𝓙' t u (𝔠 p) (𝔰 p), ∫ y in J, Ks (𝔰 p) x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ := by
    refine congrArg _ (integral_biUnion_finset _ (fun _ _ ↦ coeGrid_measurable) ?_ ?_)
    · exact fun i hi j hj hij ↦ pairwiseDisjoint_𝓙 (mem_𝓙_of_mem_𝓙' hi) (mem_𝓙_of_mem_𝓙' hj) hij
    · intro i hi
      simp_rw [mul_comm (Ks (𝔰 p) x _)]
      refine (BoundedCompactSupport.integrable_mul ?_ ?_).integrableOn
      · exact hf.sub boundedCompactSupport_approxOnCube
      · exact integrable_Ks_x (one_lt_realD (X := X))
  _ ≤ ∑ J ∈ 𝓙' t u (𝔠 p) (𝔰 p), ‖∫ y in J, Ks (𝔰 p) x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ :=
    enorm_sum_le (𝓙' t u (𝔠 p) (𝔰 p)) _
  _ ≤ _ := Finset.sum_le_sum (fun J hJ ↦ L7_1_6_integral_le (mem_𝓙_of_mem_𝓙' hJ) hf)
  _ = _ := by rw [Finset.mul_sum]

-- Translate `∑ p` into `∑ I, ∑ p` in the proof of Lemma 7.1.6
variable (t) (u) (x) in
open scoped Classical in
lemma sum_p_eq_sum_I_sum_p (f : X → ℤ → ℝ≥0∞) :
    ∑ p ∈ Finset.univ.filter (· ∈ t u), (E p).indicator 1 x * f (𝔠 p) (𝔰 p) =
    ∑ I : Grid X, ∑ p ∈ Finset.univ.filter (fun p ↦ p ∈ t u ∧ 𝓘 p = I),
    (E p).indicator 1 x * f (c I) (s I) := by
  set ps := fun (I : Grid X) ↦ Finset.univ.filter (fun p ↦ p ∈ t u ∧ 𝓘 p = I)
  calc
  _ = ∑ p ∈ Finset.univ.biUnion ps, (E p).indicator 1 x * f (𝔠 p) (𝔰 p) :=
    Finset.sum_congr (by ext p; simp [ps]) (fun _ _ ↦ rfl)
  _ = ∑ I : Grid X, ∑ p ∈ Finset.univ.filter (fun p ↦ p ∈ t u ∧ 𝓘 p = I),
        (E p).indicator 1 x * f (𝔠 p) (𝔰 p) := by
    refine (Finset.sum_biUnion ?_)
    intro I _ J _ I_ne_J a haI haJ p hp
    apply False.elim ∘ I_ne_J
    specialize haI hp
    specialize haJ hp
    simp only [mem_𝔗, ps, Finset.mem_filter] at haI haJ
    rw [← haI.2.2, ← haJ.2.2]
  _ = _ := by
    refine Finset.sum_congr rfl (fun I _ ↦ Finset.sum_congr rfl (fun p hp ↦ ?_))
    rw [← (Finset.mem_filter.mp hp).2.2, 𝔰, 𝔠]

lemma le_C7_1_6 (a4 : 4 ≤ a) :
    D2_1_3 a * defaultA a ^ 5 * (2 : ℝ≥0∞) ^ (3 / a : ℝ) ≤ C7_1_6 a := by
  simp_rw [D2_1_3, defaultA, C7_1_6, ENNReal.coe_pow, ENNReal.coe_ofNat, Nat.cast_pow,
    Nat.cast_ofNat, ← pow_mul, ← pow_add]
  calc
    _ ≤ (2 : ℝ≥0∞) ^ ((𝕔 + 2 + 𝕔 / 4) * a ^ 3 + a * 5) * 2 := by
      refine mul_le_mul_right ?_ _
      conv_rhs => rw [← ENNReal.rpow_one 2]
      refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      rw [div_le_one (by norm_cast; lia)]; norm_cast; lia
    _ ≤ _ := by
      rw [← pow_succ, add_assoc,
        show (𝕔 + 3 + 𝕔 / 4) * a ^ 3 = (𝕔 + 2 + 𝕔 / 4) * a ^ 3 + a ^ 3 by ring]
      gcongr; · exact one_le_two
      calc
        _ ≤ 4 * 4 * a := by lia
        _ ≤ a * a * a := by gcongr
        _ = _ := by ring

/-- Lemma 7.1.6 -/
lemma third_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖∑ i ∈ t.σ u x, ∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ ≤
    C7_1_6 a * t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  classical
  let I (i : ℤ) (x : X) := ‖∫ (y : X), Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ
  let Js (p : 𝔓 X) := Set.toFinset <| { J ∈ 𝓙 (t u) | ↑J ⊆ ball x (16 * D ^ 𝔰 p) ∧ s J ≤ 𝔰 p }
  let ps (I : Grid X) := Finset.univ.filter (fun p ↦ p ∈ t u ∧ 𝓘 p = I)
  let 𝔗_fin := Finset.univ.filter (· ∈ t u)
  have A5_pos : (defaultA a : ℝ) ^ 5 > 0 := pow_pos (by norm_num) 5
  calc
    _ ≤ ∑ i ∈ t.σ u x, ‖∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ :=
      enorm_sum_le (t.σ u x) _
    _ = ∑ p ∈ 𝔗_fin, (E p).indicator 1 x * I (𝔰 p) x := by
      rw [← p_sum_eq_s_sum I]
      simp_rw [indicator_eq_indicator_one_mul _ (I _), 𝔗_fin]
    _ ≤ ∑ p ∈ 𝔗_fin, (E p).indicator 1 x *
          (D2_1_3 a / (volume (ball x (D ^ 𝔰 p))) * 2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (𝔠 p) (𝔰 p), D ^ ((s J - 𝔰 p) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      refine Finset.sum_le_sum fun J hJ ↦ ?_
      by_cases xJ : x ∈ E J
      · rw [indicator_of_mem xJ, Pi.one_apply, one_mul, one_mul]
        exact L7_1_6_I_le hu hf (Finset.mem_filter.mp hJ).2 xJ
      · simp only [indicator_of_notMem xJ, zero_mul, le_refl]
    _ = ∑ I : Grid X, ∑ p ∈ ps I, (E p).indicator 1 x *
          (D2_1_3 a / (volume (ball x (D ^ s I))) * 2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      let summand := fun (y : X) (i : ℤ) ↦
          D2_1_3 a / volume (ball x (D ^ i)) * 2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u y i, D ^ ((s J - (i : ℝ)) / a) * ∫⁻ y in J, ‖f y‖ₑ
      exact sum_p_eq_sum_I_sum_p t u x summand
    _ ≤ ∑ I : Grid X, ∑ p ∈ ps I, (E p).indicator 1 x *
          (D2_1_3 a / (volume (ball (c I) (16 * D ^ s I)) / defaultA a ^ 5) *
          2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      refine Finset.sum_le_sum fun I _ ↦ Finset.sum_le_sum fun p hp ↦ ?_
      by_cases xEp : x ∈ E p; swap
      · simp only [indicator_of_notMem xEp, zero_mul, le_refl]
      apply mul_le_mul_right
      gcongr; apply ENNReal.div_le_of_le_mul'
      calc
        _ ≤ volume (ball x (32 * D ^ s I)) := by
          refine measure_mono (ball_subset_ball' ?_)
          suffices dist (c I) x < 4 * D ^ (s I) by linarith [defaultD_pow_pos a (s I)]
          exact mem_ball'.mp <| (Finset.mem_filter.mp hp).2.2 ▸ Grid_subset_ball (E_subset_𝓘 xEp)
        _ ≤ _ := by
          rw [show (32 : ℝ) = 2 ^ 5 by norm_num]
          exact measure_ball_two_le_same_iterate x (D ^ s I) 5
    _ ≤ ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          (D2_1_3 a / (volume (ball (c I) (16 * D ^ s I)) / defaultA a ^ 5) *
          2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      simp_rw [← Finset.sum_mul]
      gcongr with I hI
      by_cases! ex : ∃ p ∈ ps I, x ∈ E p
      · obtain ⟨p, hp, xEp⟩ := ex
        have L_subset_I : (L : Set X) ⊆ (I : Set X) := by
          simp only [ps, Finset.mem_filter] at hp
          exact hp.2.2 ▸ subset_of_mem_𝓛 hL hp.2.1 (not_disjoint_iff.mpr ⟨x, ⟨E_subset_𝓘 xEp, hx⟩⟩)
        simp only [L_subset_I hx', indicator_of_mem, Pi.one_apply]
        rw [Finset.sum_eq_single_of_mem p hp]
        · exact le_of_eq <| (indicator_eq_one_iff_mem _).mpr xEp
        · intro p' hp' p'_ne_p
          simp only [ps, Finset.mem_filter] at hp hp'
          exact (indicator_eq_zero_iff_notMem _).mpr fun xEp' ↦
            disjoint_left.mp (disjoint_Ω p'_ne_p (hp'.2.2.trans hp.2.2.symm)) xEp'.2.1 xEp.2.1
      · suffices ∑ p ∈ ps I, (E p).indicator (1 : X → ℝ≥0∞) x = 0 by rw [this]; exact zero_le _
        exact Finset.sum_eq_zero (fun p hp ↦ indicator_of_notMem (ex p hp) _)
    _ = ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          ((D2_1_3 a * defaultA a ^ 5 * 2 ^ (3 / a : ℝ)) /
          volume (ball (c I) (16 * D ^ s I)) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      congr! 2 with I
      rw [← ENNReal.div_mul _ (.inr (by positivity)) (.inr (by finiteness)), mul_rotate (_ / _),
        ← mul_div_assoc]
      congr 2; ring
    _ ≤ ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          (C7_1_6 a / volume (ball (c I) (16 * D ^ s I)) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      gcongr; exact le_C7_1_6 (four_le_a X)
    _ = C7_1_6 a *
        ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          (1 / volume (ball (c I) (16 * D ^ s I)) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      rw [Finset.mul_sum]; congr! 1 with I
      simp_rw [← mul_assoc, ← mul_div_assoc, mul_one, mul_comm (C7_1_6 a : ℝ≥0∞)]
    _ = _ := by
      unfold boundaryOperator; congr! 2 with I
      simp_rw [← indicator_mul_const, Pi.one_apply, one_mul]; congr! 2
      rw [Finset.mul_sum]; congr! 2 with J hJ
      rw [← mul_assoc, mul_comm (_ / _), ← mul_div_assoc, mul_one, ijIntegral]; congr! 1
      exact lintegral_eq_lintegral_approxOnCube pairwiseDisjoint_𝓙 (mem_𝓙_of_mem_𝓙' hJ) hf

/-- The constant used in `pointwise_tree_estimate`.
Has value `2 ^ (129 * a ^ 3)` in the blueprint. -/
irreducible_def C7_1_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 4 + 𝕔 / 4) * a ^ 3)

lemma C7_1_6_le_C7_1_3 {a : ℕ} : C7_1_6 a ≤ C7_1_3 a := by
  rw [C7_1_6_def, C7_1_3_def]
  gcongr
  · norm_num
  · lia

lemma C7_1_4_le_C7_1_3 {a : ℕ} (ha : 4 ≤ a) : C7_1_4 a ≤ C7_1_3 a := by
  have : (10 : ℝ≥0) ≤ 2 ^ 4 := by norm_num
  grw [C7_1_4_def, C7_1_3_def, this, ← pow_add]
  gcongr
  · norm_num
  suffices 4 ≤ (𝕔 / 4) * a ^ 3 by linarith
  have : 4 ≤ (4 / 4) * a ^ 3 := calc
    4 = 4 * 1 * 1 := by norm_num
    _ ≤ a * a * a := by gcongr <;> linarith
    _ = (4 / 4) * a ^ 3 := by ring
  apply this.trans
  gcongr
  linarith [seven_le_c]

/-- Lemma 7.1.3. -/
lemma pointwise_tree_estimate (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖carlesonSum (t u) (fun y ↦ exp (.I * - 𝒬 u y) * f y) x‖ₑ ≤
    C7_1_3 a * (MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x') +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x' := by
  set g := approxOnCube (𝓙 (t u)) f
  -- Convert the sum over `p` into a sum over `s`.
  unfold carlesonSum carlesonOn
  rw [p_sum_eq_s_sum fun s x ↦ ∫ (y : X), cexp (I * (Q x y - Q x x)) * Ks s x y *
        (fun y ↦ cexp (I * -𝒬 u y) * f y) y]
  -- Next introduce an extra factor of `‖cexp (I * 𝒬 u x)‖ₑ`, i.e., 1. Then simplify.
  have : 1 = ‖cexp (I * 𝒬 u x)‖ₑ := by simp
  rw [← one_mul ‖_‖ₑ, this, ← enorm_mul, Finset.mul_sum]
  have : ∑ i ∈ t.σ u x, cexp (I * 𝒬 u x) * ∫ (y : X), (cexp (I * (Q x y - Q x x)) * Ks i x y *
            (cexp (I * -𝒬 u y) * f y)) =
          ∑ i ∈ t.σ u x, ∫ (y : X),
            (f y * ((exp (I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y) +
            (f y - g y) * Ks i x y + g y * Ks i x y) := by
    simp_rw [← integral_const_mul, Ks, mul_sub, mul_add, sub_eq_add_neg, exp_add]
    exact Finset.fold_congr (fun s hs ↦ integral_congr_ae (funext fun y ↦ by ring).eventuallyEq)
  rw [this]
  -- It suffices to show that the integral splits into the three terms bounded by Lemmas 7.1.4-6
  suffices ∑ i ∈ t.σ u x, ∫ (y : X),
             (f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) +
             (f y - g y) * Ks i x y + g y * Ks i x y =
           ∑ i ∈ t.σ u x,
             ((∫ (y : X), f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) +
             (∫ (y : X), (f y - g y) * Ks i x y) + (∫ (y : X), g y * Ks i x y)) by
    -- Separate the LHS into three pieces
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib]
    apply le_trans <| ENNReal.coe_strictMono.monotone <| (nnnorm_add_le _ _).trans
      (add_le_add_left (nnnorm_add_le _ _) _)
    rw [ENNReal.coe_add, ENNReal.coe_add, mul_add]
    -- Apply Lemmas 7.1.4, 7.1.5, and 7.1.6
    simp_rw [← mul_comm (Ks _ x _)]
    refine add_le_add_three ?_ ?_ (second_tree_pointwise hu hL hx hx')
    · simp_rw [mul_comm (Ks _ x _), mul_comm (f _)]
      have h : C7_1_3 a ≥ C7_1_4 a := C7_1_4_le_C7_1_3 (four_le_a X)
      exact (first_tree_pointwise hu hL hx hx' hf).trans <| mul_left_mono (by exact_mod_cast h)
    · have h : C7_1_3 a ≥ C7_1_6 a := C7_1_6_le_C7_1_3
      exact (third_tree_pointwise hu hL hx hx' hf).trans <| mul_left_mono (by exact_mod_cast h)
  -- In order to split the integral, we will first need some trivial integrability results
  have h1 {i : ℤ} : Integrable (fun y ↦ approxOnCube (𝓙 (t.𝔗 u)) f y * Ks i x y) := by
    classical
    apply (integrable_Ks_x <| one_lt_realD (K := K)).bdd_mul
      (c := ∑ J with J ∈ 𝓙 (t u), ‖⨍ y in J, f y‖)
    · exact (stronglyMeasurable_approxOnCube _ _).aestronglyMeasurable
    · refine ae_of_all _ fun x ↦ (norm_sum_le _ _).trans <| Finset.sum_le_sum (fun J hJ ↦ ?_)
      by_cases h : x ∈ (J : Set X) <;> simp [h]
  have : ∀ (y : X), ‖cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖ ≤ 2 := by
    refine fun y ↦ le_of_le_of_eq (norm_sub_le _ _) ?_
    norm_cast
    rw [mul_comm, norm_exp_ofReal_mul_I, one_add_one_eq_two]
  have h2 {i : ℤ} : Integrable
      (fun y ↦ f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) :=
    hf.integrable_mul <| (integrable_Ks_x <| one_lt_realD (K := K)).bdd_mul (c := 2)
      (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ this)
  have h3 {i : ℤ} : Integrable (fun y ↦ (f y - approxOnCube (𝓙 (t.𝔗 u)) f y) * Ks i x y) := by
    simp_rw [sub_mul]
    exact hf.integrable_mul (integrable_Ks_x <| one_lt_realD (K := K)) |>.sub h1
  exact Finset.fold_congr fun i _ ↦ (by rw [integral_add _ h1, integral_add h2 h3]; exact h2.add h3)

end TileStructure.Forest
