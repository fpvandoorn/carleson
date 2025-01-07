import Carleson.Forest
import Carleson.HardyLittlewood
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.ToMathlib.Misc
import Carleson.Psi

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

/-! ## Section 7.1 and Lemma 7.1.3 -/

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

/-- The definition of `𝓛₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓛₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {L : Grid X | s L = -S ∨ (∃ p ∈ 𝔖, L ≤ 𝓘 p) ∧ ∀ p ∈ 𝔖, ¬𝓘 p ≤ L}

/-- The definition of `𝓛(𝔖), defined above Lemma 7.1.2 -/
def 𝓛 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓛₀ 𝔖) x}

lemma 𝓛_subset_𝓛₀ {𝔖 : Set (𝔓 X)} : 𝓛 𝔖 ⊆ 𝓛₀ 𝔖 := sep_subset ..

private lemma s_le_s_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖)
    {p : 𝔓 X} (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : s L ≤ s (𝓘 p) := by
  simp only [𝓛, Maximal, 𝓛₀, Grid.le_def, not_and, not_le, mem_setOf_eq, and_imp] at hL
  rcases hL.1 with h | h
  · exact h ▸ (range_s_subset ⟨𝓘 p, rfl⟩).1
  · by_contra!
    exact lt_asymm this <| h.2 p hp <| (GridStructure.fundamental_dyadic' this.le).resolve_right hpL

private lemma subset_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖) {p : 𝔓 X}
    (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : (L : Set X) ⊆ (𝓘 p : Set X) :=
  GridStructure.fundamental_dyadic' (s_le_s_of_mem_𝓛 hL hp hpL) |>.resolve_right fun h ↦ hpL h.symm

/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x

lemma stronglyMeasurable_approxOnCube (C : Set (Grid X)) (f : X → E') :
    StronglyMeasurable (approxOnCube (X := X) (K := K) C f) :=
  Finset.stronglyMeasurable_sum _ (fun _ _ ↦ stronglyMeasurable_const.indicator coeGrid_measurable)

lemma integrable_approxOnCube (C : Set (Grid X)) {f : X → E'} : Integrable (approxOnCube C f) := by
  refine integrable_finset_sum _ (fun i hi ↦ ?_)
  constructor
  · exact (aestronglyMeasurable_indicator_iff coeGrid_measurable).mpr aestronglyMeasurable_const
  · simp_rw [hasFiniteIntegral_iff_nnnorm, nnnorm_indicator_eq_indicator_nnnorm,
      ENNReal.coe_indicator]
    apply lt_of_le_of_lt <| lintegral_indicator_const_le (i : Set X) _
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top volume_coeGrid_lt_top

lemma approxOnCube_nonneg (C : Set (Grid X)) {f : X → ℝ} (hf : ∀ (y : X), f y ≥ 0) (x : X) :
    approxOnCube C f x ≥ 0 :=
  Finset.sum_nonneg' (fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ integral_nonneg hf) _)

lemma approxOnCube_apply {C : Set (Grid X)} (hC : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    (f : X → E') {x : X} {J : Grid X} (hJ : J ∈ C) (xJ : x ∈ J) :
    (approxOnCube C f) x = ⨍ y in J, f y := by
  rw [approxOnCube, ← Finset.sum_filter_not_add_sum_filter _ (J = ·)]
  have eq0 : ∑ i ∈ Finset.filter (¬ J = ·) (Finset.univ.filter (· ∈ C)),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 := by
    suffices ∀ i ∈ (Finset.univ.filter (· ∈ C)).filter (¬ J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 by simp [Finset.sum_congr rfl this]
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [Set.disjoint_left.mp ((hC.eq_or_disjoint hJ hi.1).resolve_left hi.2) xJ]
  have eq_ave : ∑ i ∈ (Finset.univ.filter (· ∈ C)).filter (J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = ⨍ y in J, f y := by
    suffices (Finset.univ.filter (· ∈ C)).filter (J = ·) = {J} by simp [this, xJ, ← Grid.mem_def]
    exact subset_antisymm (fun _ h ↦ Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2.symm)
      (fun _ h ↦ by simp [Finset.mem_singleton.mp h, hJ])
  rw [eq0, eq_ave, zero_add]

/-- The definition `I_i(x)`, given above Lemma 7.1.3.
The cube of scale `s` that contains `x`. There is at most 1 such cube, if it exists. -/
def cubeOf (i : ℤ) (x : X) : Grid X :=
  Classical.epsilon (fun I ↦ x ∈ I ∧ s I = i)

/-- The definition `T_𝓝^θ f(x)`, given in (7.1.3).
For convenience, the suprema are written a bit differently than in the blueprint
(avoiding `cubeOf`), but this should be equivalent.
This is `0` if `x` doesn't lie in a cube. -/
def nontangentialMaximalFunction (θ : Θ X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (I : Grid X) (_ : x ∈ I) (x' ∈ I) (s₂ ∈ Icc (s I) S) (_ : D ^ (s₂ - 1) ≤ upperRadius Q θ x'),
  ‖∑ i ∈ Icc (s I) s₂, ∫ y, Ks i x' y * f y‖₊

variable (t) in
/-- The operator `S_{1,𝔲} f(x)`, given in (7.1.4). -/
def boundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ∑ I : Grid X, (I : Set X).indicator (x := x) fun _ ↦
  ∑ J ∈ { J | J ∈ 𝓙 (t u) ∧ (J : Set X) ⊆ ball (c I) (16 * D ^ (s I)) ∧ s J ≤ s I },
  D ^ ((s J - s I) / a) / volume (ball (c I) (16 * D ^ (s I))) * ∫⁻ y in J, ‖f y‖₊

/-- The indexing set for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def 𝓑 : Set (ℕ × Grid X) := Icc 0 (S + 5) ×ˢ univ

/-- The center function for the collection of balls 𝓑. -/
def c𝓑 (z : ℕ × Grid X) : X := c z.2

/-- The radius function for the collection of balls 𝓑. -/
def r𝓑 (z : ℕ × Grid X) : ℝ := 2 ^ z.1 * D ^ s z.2

lemma 𝓑_finite : (𝓑 (X := X)).Finite :=
  finite_Icc .. |>.prod finite_univ

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
  have l₁ : p ≤ p' := ⟨lK,
    (relative_fundamental_dyadic lK).resolve_left (not_disjoint_iff.mpr ⟨_, Qxp, Qxp'⟩)⟩
  have l₂ : p' ≤ p'' := ⟨Kl,
    (relative_fundamental_dyadic Kl).resolve_left (not_disjoint_iff.mpr ⟨_, Qxp', Qxp''⟩)⟩
  refine ⟨(t.ordConnected hu).out mp mp'' ⟨l₁, l₂⟩, ⟨(Grid.le_def.mp lK).1 xp, Qxp', ?_⟩⟩
  exact Icc_subset_Icc sxp.1 sxp''.2 ⟨(Grid.le_def.mp lK).2, (Grid.le_def.mp Kl).2⟩

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓙 : ⋃ J ∈ 𝓙 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  refine subset_antisymm (iUnion₂_subset_iUnion ..) fun x mx ↦ ?_
  simp_rw [mem_iUnion] at mx ⊢; obtain ⟨I, mI⟩ := mx
  obtain ⟨J, sJ, mJ⟩ :=
    Grid.exists_containing_subcube _ ⟨le_rfl, scale_mem_Icc.1⟩ mI
  have : J ∈ (𝓙₀ 𝔖).toFinset := by rw [mem_toFinset]; left; exact sJ
  obtain ⟨M, lM, maxM⟩ := (𝓙₀ 𝔖).toFinset.exists_le_maximal this
  simp_rw [mem_toFinset] at maxM
  use M, maxM, (Grid.le_def.mp lM).1 mJ

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓙 : (𝓙 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := fun I mI J mJ hn ↦ by
  have : IsAntichain (· ≤ ·) (𝓙 𝔖) := setOf_maximal_antichain _
  exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓛 : ⋃ J ∈ 𝓛 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
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
irreducible_def C7_1_4 (a : ℕ) : ℝ≥0 := 10 * 2 ^ (104 * (a : ℝ) ^ 3)

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
private lemma exp_sub_one_le (t : ℝ) : ‖exp (.I * t) - 1‖ ≤ ‖t‖ := by simpa using exp_Lipschitz t 0

-- Used in the proofs of Lemmas 7.1.4 and 7.1.5
private lemma dist_lt_5 (hu : u ∈ t) (mp : p ∈ t.𝔗 u) (Qxp : Q x ∈ Ω p) :
    dist_(p) (𝒬 u) (Q x) < 5 := calc
  _ ≤ dist_(p) (𝒬 u) (𝒬 p) + dist_(p) (Q x) (𝒬 p) := dist_triangle_right ..
  _ < 4 + 1 :=
    add_lt_add ((t.smul_four_le hu mp).2 (by convert mem_ball_self zero_lt_one)) (subset_cball Qxp)
  _ = 5 := by norm_num

-- The bound in the third display in the proof of Lemma 7.1.4
private lemma L7_1_4_bound (hu : u ∈ t) {s : ℤ} (hs : s ∈ t.σ u x) {y : X} (hKxy : Ks s x y ≠ 0) :
    ‖exp (.I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖ ≤
    5 * 2 ^ (4 * a) * 2 ^ (s - σMax t u x ⟨s, hs⟩) :=
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
          ((C2_1_2_le_inv_512 X).trans (by norm_num)) (by norm_cast)
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
    ‖(exp (.I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks s x y * f y‖ ≤
    5 * 2^(s - σMax t u x ⟨s, hs⟩) * (2^(103 * a ^ 3) / volume.real (ball x (D ^ s))) * ‖f y‖ := by
  by_cases hKxy : Ks s x y = 0
  · rw [hKxy, mul_zero, zero_mul, norm_zero]; positivity
  · rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (f y))
    apply mul_le_mul (L7_1_4_bound hu hs hKxy) norm_Ks_le (norm_nonneg _) (by positivity) |>.trans
    rw [mul_assoc 5, mul_comm (2 ^ (4 * a)), ← mul_assoc, mul_assoc, mul_div, C2_1_3]
    gcongr
    norm_cast
    rw_mod_cast [← pow_add]
    refine Nat.pow_le_pow_of_le_right two_pos <| Nat.add_le_of_le_sub ?_ ?_
    · exact Nat.mul_le_mul_right _ (by norm_num)
    · rw [← Nat.sub_mul, (show a ^ 3 = a ^ 2 * a from rfl)]; nlinarith [four_le_a X]

-- The geometric sum used to prove `L7_1_4_sum`
private lemma sum_pow_two_le (a b : ℤ) : ∑ s ∈ Finset.Icc a b, (2 : ℝ≥0) ^ s ≤ 2 ^ (b + 1) := by
  by_cases h : b < a
  · simp [Finset.Icc_eq_empty_of_lt h]
  obtain ⟨k, rfl⟩ : ∃ (k : ℕ), b = a + k := ⟨(b - a).toNat, by simp [not_lt.mp h]⟩
  suffices ∑ s ∈ Finset.Icc a (a + k), (2 : ℝ≥0) ^ s = 2 ^ a * ∑ n ∈ Finset.range (k + 1), 2 ^ n by
    rw [this, add_assoc, zpow_add' (Or.inl two_pos.ne.symm), mul_le_mul_left (zpow_pos two_pos a),
      geom_sum_of_one_lt one_lt_two (k + 1), NNReal.sub_def (r := 2)]
    norm_num
    exact le_self_add
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun n hn ↦ (n - a).toNat)
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range, Int.toNat_lt (Int.sub_nonneg.mpr hn.1), Nat.cast_add, Nat.cast_one]
    linarith
  · intro n hn m hm hnm
    rw [Finset.mem_Icc] at hn hm
    simpa [Int.sub_nonneg.mpr hn.1, Int.sub_nonneg.mpr hm.1] using congrArg Int.ofNat hnm
  · exact fun n hn ↦ by use a + n, by simp [Nat.le_of_lt_succ (Finset.mem_range.mp hn)], by simp
  · intro n hn
    rw [← zpow_natCast, Int.ofNat_toNat, ← zpow_add' (Or.inl two_pos.ne.symm),
      sup_eq_left.mpr <| Int.sub_nonneg_of_le (Finset.mem_Icc.mp hn).1, add_sub_cancel]

-- The sum used in the proof of Lemma 7.1.4
private lemma L7_1_4_sum (hσ : (t.σ u x).Nonempty) :
    ∑ s ∈ t.σ u x, (2 : ℝ≥0) ^ (s - t.σMax u x hσ) ≤ 2 := by
  have {s : ℤ} : (2 : ℝ≥0) ^ (s - t.σMax u x hσ) = 2 ^ s * 2 ^ (- t.σMax u x hσ) := by
    rw [← zpow_add' (Or.inl two_pos.ne.symm), Int.sub_eq_add_neg]
  simp_rw [this, ← Finset.sum_mul]
  suffices ∑ s ∈ t.σ u x, (2 : ℝ≥0) ^ s ≤ 2 ^ (t.σMax u x hσ + 1) from calc
    _ ≤ (2 : ℝ≥0) ^ (t.σMax u x hσ + 1) * 2 ^ (-t.σMax u x hσ) := by gcongr
    _ = 2 := by rw [zpow_add' (Or.inl two_pos.ne.symm)]; field_simp
  refine le_trans (Finset.sum_le_sum_of_subset ?_) (sum_pow_two_le (t.σMin u x hσ) (t.σMax u x hσ))
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
        exact (eq_div_iff two_pos.ne.symm).mpr (by linarith)
      · exact (mem_ball.mp <| Grid_subset_ball xp.1).le
    _ ≤ 4 * D ^ (s J) + 4.5 * D ^ (𝔰 p)                  := by linarith [defaultD_pow_pos a (𝔰 p)]

-- Inequality needed for the proof of `L7_1_4_integral_le_integral`
private lemma L7_1_4_s_le_s {p : 𝔓 X} (pu : p ∈ t.𝔗 u) (xp : x ∈ E p)
    {J : Grid X} (hJ : J ∈ 𝓙 (t.𝔗 u) ∧ ((J : Set X) ∩ ball x (D ^ 𝔰 p / 2)).Nonempty) :
    s J ≤ 𝔰 p := by
  have ⟨z, hz⟩ := hJ.2
  by_cases h : s J ≤ 𝔰 p ∨ s J = -S
  · exact h.elim id (· ▸ (range_s_subset ⟨𝓘 p, rfl⟩).1)
  push_neg at h
  apply False.elim ∘ hJ.1.1.resolve_left h.2 p pu ∘ le_trans Grid_subset_ball ∘ ball_subset_ball'
  have : (D : ℝ) ^ 𝔰 p ≤ D ^ s J := (zpow_le_zpow_iff_right₀ (one_lt_D (X := X))).mpr h.1.le
  calc 4 * (D : ℝ) ^ GridStructure.s (𝓘 p) + dist (GridStructure.c (𝓘 p)) (c J)
    _ ≤ 4 * (D : ℝ) ^ (s J) + (4 * D ^ (s J) + 4.5 * D ^ (s J)) := by
      gcongr 4 * ?_ + ?_
      · exact this
      · exact dist_comm (c (𝓘 p)) (c J) ▸ L7_1_4_dist_le xp hJ.2 |>.trans (by gcongr)
    _ ≤ 100 * D ^ (s J + 1) := by
      rw [zpow_add' (Or.inl (defaultD_pos a).ne.symm), zpow_one]
      nlinarith [one_le_D (a := a), defaultD_pow_pos a (s J)]

-- The integral bound needed for the proof of Lemma 7.1.4
private lemma L7_1_4_integral_le_integral (hu : u ∈ t) (hf : BoundedCompactSupport f) {p : 𝔓 X}
    (pu : p ∈ t.𝔗 u) (xp : x ∈ E p) : ∫ y in ball x ((D : ℝ) ^ (𝔰 p) / 2), ‖f y‖ ≤
    ∫ y in ball (𝔠 p) (16 * (D : ℝ) ^ (𝔰 p)), ‖approxOnCube (𝓙 (t u)) (‖f ·‖) y‖ := by
  let Js := Set.toFinset { J ∈ 𝓙 (t u) | ((J : Set X) ∩ ball x (D ^ (𝔰 p) / 2)).Nonempty }
  have mem_Js {J : Grid X} : J ∈ Js ↔ J ∈ 𝓙 (t.𝔗 u) ∧ (↑J ∩ ball x (D ^ 𝔰 p / 2)).Nonempty := by
    simp [Js]
  have Js_disj : (Js : Set (Grid X)).Pairwise (Disjoint on fun J ↦ (J : Set X)) :=
    fun i₁ hi₁ i₂ hi₂ h ↦ pairwiseDisjoint_𝓙 (mem_Js.mp hi₁).1 (mem_Js.mp hi₂).1 h
  calc ∫ y in ball x (D ^ (𝔰 p) / 2), ‖f y‖
    _ ≤ ∫ y in (⋃ J ∈ Js, (J : Set X)), ‖f y‖ := by
      apply setIntegral_mono_set hf.integrable.norm.integrableOn (Eventually.of_forall (by simp))
      suffices h : ball x (D ^ (𝔰 p) / 2) ⊆ ⋃ J ∈ 𝓙 (t.𝔗 u), (J : Set X) by
        refine ((subset_inter_iff.mpr ⟨h, subset_refl _⟩).trans (fun y hy ↦ ?_)).eventuallyLE
        have ⟨J, hJ, yJ⟩ := Set.mem_iUnion₂.mp hy.1
        exact ⟨J, ⟨⟨J, by simp [mem_Js.mpr ⟨hJ, ⟨y, mem_inter yJ hy.2⟩⟩]⟩, yJ⟩⟩
      calc ball x (D ^ 𝔰 p / 2)
        _ ⊆ ball x (4 * D ^ 𝔰 p)     := ball_subset_ball <| by linarith [defaultD_pow_pos a (𝔰 p)]
        _ ⊆ (𝓘 u : Set X)                 := ball_subset_of_mem_𝓘 hu pu xp.1
        _ ⊆ ⋃ (I : Grid X), (I : Set X)   := le_iSup _ _
        _ = ⋃ J ∈ 𝓙 (t.𝔗 u), (J : Set X) := biUnion_𝓙.symm
    _ = ∑ J in Js, ∫ y in J, ‖f y‖ := by
      have Js_disj : (Js : Set (Grid X)).Pairwise (Disjoint on fun J ↦ (J : Set X)) :=
        fun i₁ hi₁ i₂ hi₂ h ↦ pairwiseDisjoint_𝓙 (mem_Js.mp hi₁).1 (mem_Js.mp hi₂).1 h
      apply integral_finset_biUnion Js (fun _ _ ↦ coeGrid_measurable) Js_disj
      exact fun i hi ↦ hf.norm.integrable.integrableOn
    _ = ∑ J in Js, ∫ y in J, (approxOnCube (𝓙 (t u)) (‖f ·‖)) y := by
      refine Finset.sum_congr rfl (fun J hJ ↦ ?_)
      have eq : EqOn (approxOnCube (𝓙 (t u)) (‖f ·‖)) (fun _ ↦ ⨍ y in J, ‖f y‖) J :=
        fun y hy ↦ approxOnCube_apply pairwiseDisjoint_𝓙 (‖f ·‖) (mem_Js.mp hJ).1 hy
      rw [setIntegral_congr_fun coeGrid_measurable eq, setIntegral_const, average]
      simp [← mul_assoc, CommGroupWithZero.mul_inv_cancel (volume (J : Set X)).toReal <|
        ENNReal.toReal_ne_zero.mpr ⟨(volume_coeGrid_pos _).ne.symm, volume_coeGrid_lt_top.ne⟩]
    _ = ∫ y in (⋃ J ∈ Js, (J : Set X)), (approxOnCube (𝓙 (t u)) (‖f ·‖)) y := by
      refine integral_finset_biUnion Js (fun _ _ ↦ coeGrid_measurable) ?_ ?_ |>.symm
      · exact fun i₁ hi₁ i₂ hi₂ h ↦ pairwiseDisjoint_𝓙 (mem_Js.mp hi₁).1 (mem_Js.mp hi₂).1 h
      · exact fun i hi ↦ And.intro (stronglyMeasurable_approxOnCube _ _).aestronglyMeasurable
          (integrable_approxOnCube (𝓙 (t u))).restrict.hasFiniteIntegral
    _ = ∫ y in (⋃ J ∈ Js, (J : Set X)), ‖(approxOnCube (𝓙 (t u)) (‖f ·‖)) y‖ :=
      setIntegral_congr_fun (Js.measurableSet_biUnion fun _ _ ↦ coeGrid_measurable) <| fun y _ ↦
        (Real.norm_of_nonneg <| approxOnCube_nonneg (𝓙 (t u)) (fun _ ↦ norm_nonneg _) y).symm
    _ ≤ ∫ y in ball (𝔠 p) (16 * (D : ℝ) ^ (𝔰 p)), ‖approxOnCube (𝓙 (t u)) (‖f ·‖) y‖ := by
      apply setIntegral_mono_set (integrable_approxOnCube _).norm.integrableOn <|
        Eventually.of_forall (fun _ ↦ norm_nonneg _)
      refine (iUnion₂_subset_iff.mpr (fun J hJ ↦ ?_)).eventuallyLE
      replace hJ := mem_Js.mp hJ
      have ⟨z, hz⟩ := hJ.2
      refine Grid_subset_ball.trans (ball_subset_ball' ?_)
      change _ * _ ^ (s J) + dist (c J) _ ≤ _
      have := (zpow_le_zpow_iff_right₀ (one_lt_D (X := X))).mpr <| L7_1_4_s_le_s pu xp hJ
      linarith [L7_1_4_dist_le xp hJ.2, defaultD_pow_pos a (𝔰 p)]

-- An average over `ball (𝔠 p) (16 * D ^ 𝔰 p)` is bounded by `MB`; needed for Lemma 7.1.4
private lemma L7_1_4_laverage_le_MB (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L) (g : X → ℝ)
    {p : 𝔓 X} (pu : p ∈ t.𝔗 u) (xp : x ∈ E p) :
    (∫⁻ y in ball (𝔠 p) (16 * D ^ 𝔰 p), ‖g y‖₊) / volume (ball (𝔠 p) (16 * D ^ 𝔰 p)) ≤
    MB volume 𝓑 c𝓑 r𝓑 g x' := by
  have mem_𝓑 : ⟨4, 𝓘 p⟩ ∈ 𝓑 := by simp [𝓑]
  convert le_biSup (hi := mem_𝓑) <| fun i ↦ ((ball (c𝓑 i) (r𝓑 i)).indicator (x := x') <|
    fun _ ↦ ⨍⁻ y in ball (c𝓑 i) (r𝓑 i), ‖g y‖₊ ∂volume)
  · have x'_in_ball : x' ∈ ball (c𝓑 (4, 𝓘 p)) (r𝓑 (4, 𝓘 p)) := by
      simp only [c𝓑, r𝓑, _root_.s]
      have : x' ∈ 𝓘 p := subset_of_mem_𝓛 hL pu (not_disjoint_iff.mpr ⟨x, xp.1, hx⟩) hx'
      refine Metric.ball_subset_ball ?_ <| Grid_subset_ball this
      linarith [defaultD_pow_pos a (GridStructure.s (𝓘 p))]
    have hc𝓑 : 𝔠 p = c𝓑 (4, 𝓘 p) := by simp [c𝓑, 𝔠]
    have hr𝓑 : 16 * D ^ 𝔰 p = r𝓑 (4, 𝓘 p) := by rw [r𝓑, 𝔰]; norm_num
    simp [-defaultD, laverage, x'_in_ball, ENNReal.div_eq_inv_mul, hc𝓑, hr𝓑]
  · simp [MB, maximalFunction]

/-- Lemma 7.1.4 -/
lemma first_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖∑ i in t.σ u x, ∫ y, (exp (.I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y * f y ‖₊ ≤
    C7_1_4 a * MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  set g := approxOnCube (𝓙 (t u)) (‖f ·‖)
  let q (y : X) := -𝒬 u y + Q x y + 𝒬 u x - Q x x
  by_cases hσ : (t.σ u x).Nonempty; swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hσ]
  by_cases hMB : MB volume 𝓑 c𝓑 r𝓑 g x' = ∞ -- `MB` is finite, but we don't need to prove that.
  · exact hMB ▸ le_of_le_of_eq (OrderTop.le_top _) (by simp [C7_1_4])
  rw [← ENNReal.coe_toNNReal hMB]
  norm_cast
  have : ∀ s ∈ t.σ u x, ‖∫ (y : X), (cexp (I * (q y)) - 1) * Ks s x y * f y‖₊ ≤
      (∫ (y : X), ‖(cexp (I * (q y)) - 1) * Ks s x y * f y‖).toNNReal :=
    fun s hs ↦ by apply le_trans (norm_integral_le_integral_norm _) (by simp)
  refine (nnnorm_sum_le _ _).trans <| ((t.σ u x).sum_le_sum this).trans ?_
  suffices ∀ s ∈ t.σ u x, (∫ (y : X), ‖(cexp (I * (q y)) - 1) * Ks s x y * f y‖).toNNReal ≤
      (5 * 2 ^ (104 * a ^ 3) * (MB volume 𝓑 c𝓑 r𝓑 g x').toNNReal) * 2 ^ (s - t.σMax u x hσ) by
    apply le_trans ((t.σ u x).sum_le_sum this)
    rw [← Finset.mul_sum]
    apply le_trans <| mul_le_mul_left' (L7_1_4_sum hσ) _
    rw [mul_comm _ 2, ← mul_assoc, ← mul_assoc, C7_1_4]
    gcongr
    · norm_num
    · exact_mod_cast pow_le_pow_right₀ one_lt_two.le (le_refl _)
  intro s hs
  have eq1 : ∫ (y : X), ‖(cexp (I * (q y)) - 1) * Ks s x y * f y‖ =
      ∫ y in ball x (D ^ s / 2), ‖(cexp (I * (q y)) - 1) * Ks s x y * f y‖ := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (EventuallyEq.of_eq (Set.indicator_eq_self.mpr fun y hy ↦ ?_)).symm
    exact mem_ball_comm.mp (mem_Ioo.mp (dist_mem_Ioo_of_Ks_ne_zero fun h ↦ by simp [h] at hy)).2
  have eq2 : (∫ y in ball x (D ^ s / 2), ‖(cexp (I * (q y)) - 1) * Ks s x y * f y‖).toNNReal ≤
      5 * 2 ^ (s - σMax t u x ⟨s, hs⟩) * (2 ^ (103 * a ^ 3) / volume.real (ball x (D ^ s))) *
      (∫ y in ball x (D ^ s / 2), ‖f y‖).toNNReal := by
    rw [Real.coe_toNNReal _ <| setIntegral_nonneg measurableSet_ball (fun _ _ ↦ norm_nonneg _)]
    convert le_trans (integral_mono_of_nonneg (Eventually.of_forall ?_)
      (hf.integrable.norm.const_mul _).restrict
      (Eventually.of_forall <| L7_1_4_integrand_bound f hu hs)) ?_
    · norm_cast
    · simp only [Pi.zero_apply, norm_nonneg, implies_true]
    · exact isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    · rw [integral_mul_left]; gcongr; simp
  apply le_of_eq_of_le (congrArg Real.toNNReal eq1) ∘ eq2.trans
  simp only [Real.coe_toNNReal', NNReal.val_eq_coe, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_pow, NNReal.coe_zpow]
  simp_rw [sup_of_le_left <| setIntegral_nonneg measurableSet_ball (fun _ _ ↦ norm_nonneg _)]
  have : 5 * 2 ^ (s - t.σMax u x hσ) * (2 ^ (103 * a ^ 3) / volume.real (ball x (D ^ s))) *
      (∫ y in ball x (D ^ s / 2), ‖f y‖) = 5 * (2 ^ (103 * a ^ 3) *
      ((∫ y in ball x (D ^ s / 2), ‖f y‖) / volume.real (ball x (D ^ s)))) *
      2 ^ (s - t.σMax u x hσ) := by ring
  rw [this, mul_le_mul_right (zpow_pos two_pos _), mul_assoc, mul_le_mul_left (by norm_num)]
  rw [Nat.succ_mul 103, pow_add, mul_assoc, mul_le_mul_left (pow_pos two_pos _)]
  have ⟨pₛ, pₛu, xpₛ, hpₛ⟩ := t.exists_p_of_mem_σ u x hs
  have ball_subset : ball (𝔠 pₛ) (16 * D ^ s) ⊆ ball x ((2 ^ 5) * D ^ s) :=
    ball_subset_ball' <| calc 16 * (D : ℝ) ^ s + dist (𝔠 pₛ) x
      _ ≤ 16 * D ^ s + 4 * D ^ _ := add_le_add_left (mem_ball'.mp (Grid_subset_ball xpₛ.1)).le _
      _ = 16 * D ^ s + 4 * D ^ s := by nth_rewrite 3 [← hpₛ]; rfl
      _ ≤ (2 ^ 5) * D ^ s        := by linarith [defaultD_pow_pos a s]
  calc (∫ y in ball x (D ^ s / 2), ‖f y‖) / volume.real (ball x (D ^ s))
  _ ≤ 2 ^ (5 * a) * ((∫ y in ball x (D^s / 2), ‖f y‖) / volume.real (ball (𝔠 pₛ) (16 * D^s))) := by
    rw [mul_comm (2 ^ (5 * a)), div_mul]
    apply div_le_div₀ (setIntegral_nonneg measurableSet_ball (fun _ _ ↦ norm_nonneg _)) (le_refl _)
    · exact div_pos (hb := pow_pos two_pos (5 * a)) <|
        measure_ball_pos_real (𝔠 pₛ) (16 * D ^ s) (mul_pos (by norm_num) <| defaultD_pow_pos a s)
    · apply (div_le_iff₀' (pow_pos two_pos (5 * a))).mpr
      apply le_trans <| ENNReal.toReal_mono (measure_ball_ne_top x _) <|
        OuterMeasureClass.measure_mono volume ball_subset
      apply le_of_le_of_eq <| measure_real_ball_two_le_same_iterate x (D ^ s) 5
      simp [mul_comm 5 a, pow_mul]
  _ ≤ 2 ^ (a ^ 3) * (MB volume 𝓑 c𝓑 r𝓑 g x').toNNReal := by
    gcongr ?_ * ?_
    · apply pow_right_mono₀ one_lt_two.le
      rw [pow_succ a 2, mul_le_mul_right (a_pos X)]
      nlinarith [four_le_a X]
    · refine le_trans ?_ <| ENNReal.toReal_mono hMB <| L7_1_4_laverage_le_MB hL hx hx' g pₛu xpₛ
      rw [hpₛ, ENNReal.toReal_div]
      refine div_le_div_of_nonneg_right ?_ measureReal_nonneg
      rw [← integral_norm_eq_lintegral_nnnorm]
      · exact hpₛ ▸ L7_1_4_integral_le_integral hu hf pₛu xpₛ
      · exact (stronglyMeasurable_approxOnCube (𝓙 (t u)) (‖f ·‖)).aestronglyMeasurable.restrict

/-- Lemma 7.1.5 -/
lemma second_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L) :
    ‖∑ i in t.σ u x, ∫ y, Ks i x y * approxOnCube (𝓙 (t u)) f y‖₊ ≤
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x' := by
  rcases (t.σ u x).eq_empty_or_nonempty with hne | hne; · simp [hne]
  let s₁ := Finset.min' (t.σ u x) hne
  have ms₁ : s₁ ∈ t.σ u x := Finset.min'_mem ..
  simp_rw [σ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ms₁
  obtain ⟨p, ⟨mp, xp, _, _⟩, sp⟩ := ms₁
  have Lle : L ≤ 𝓘 p := by
    rcases 𝓛_subset_𝓛₀ hL with hL | hL
    · exact le_of_mem_of_mem (hL.symm ▸ scale_mem_Icc.1) hx xp
    · exact (le_or_ge_of_mem_of_mem xp hx).resolve_left (hL.2 p mp)
  let s₂ := Finset.max' (t.σ u x) hne
  have ms₂ : s₂ ∈ t.σ u x := Finset.max'_mem ..
  simp_rw [σ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ms₂
  obtain ⟨p', ⟨mp', xp', Qxp', _⟩, sp'⟩ := ms₂
  have s_ineq : 𝔰 p ≤ 𝔰 p' := by
    rw [sp, sp']; exact (t.σ u x).min'_le s₂ (Finset.max'_mem ..)
  have pinc : 𝓘 p ≤ 𝓘 p' := le_of_mem_of_mem s_ineq xp xp'
  have d5 : dist_(p') (𝒬 u) (Q x) < 5 := dist_lt_5 hu mp' Qxp'
  have d5' : dist_{x, D ^ s₂} (𝒬 u) (Q x) < 5 * defaultA a ^ 5 := by
    have i1 : dist x (𝔠 p) < 4 * D ^ 𝔰 p' :=
      (mem_ball.mp (Grid_subset_ball xp)).trans_le <|
        mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ one_le_D s_ineq) zero_le_four
    have i2 : dist (𝔠 p') (𝔠 p) < 4 * D ^ 𝔰 p' :=
      mem_ball'.mp (ball_subset_Grid.trans (Grid.le_def.mp pinc).1 |>.trans Grid_subset_ball <|
        mem_ball_self (by unfold defaultD; positivity))
    calc
      _ ≤ dist_{𝔠 p, 8 * D ^ 𝔰 p'} (𝒬 u) (Q x) := by
        refine cdist_mono (ball_subset_ball' ?_); rw [← sp']
        calc
          _ ≤ (D : ℝ) ^ 𝔰 p' + 4 * D ^ 𝔰 p' := add_le_add_left i1.le _
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
      _ ≤ dist_{x, D ^ s₂} (𝒬 u) (Q x) * 2 ^ (-100 * a : ℤ) := by
        rw [neg_mul, zpow_neg, le_mul_inv_iff₀ (by positivity), mul_comm]
        convert le_cdist_iterate _ (𝒬 u) (Q x) (100 * a) using 1
        · apply dist_congr rfl
          rw [Nat.cast_npow, ← pow_mul, show a * (100 * a) = 100 * a ^ 2 by ring, ← Nat.cast_npow]
          change _ = (D : ℝ) * _
          rw [← zpow_one_add₀ (defaultD_pos _).ne', add_sub_cancel]
        · unfold defaultD; positivity
      _ < 5 * defaultA a ^ 5 * 2 ^ (-100 * a : ℤ) := by gcongr
      _ = 5 * (2 : ℝ) ^ (-95 * a : ℤ) := by
        rw [Nat.cast_npow, ← pow_mul, ← zpow_natCast, show (2 : ℕ) = (2 : ℝ) by rfl, mul_assoc,
          ← zpow_add₀ two_ne_zero]; congr; omega
      _ ≤ 5 * 2 ^ (-3 : ℤ) := by
        gcongr
        · exact one_le_two
        · linarith [four_le_a X]
      _ < _ := by norm_num
  have x'p : x' ∈ 𝓘 p := (Grid.le_def.mp Lle).1 hx'
  refine le_iSup₂_of_le (𝓘 p) x'p <| le_iSup₂_of_le x xp <|
    le_iSup₂_of_le (𝔰 p') ⟨s_ineq, scale_mem_Icc.2⟩ <| le_iSup_of_le ?_ ?_
  · have : ((D : ℝ≥0∞) ^ (𝔰 p' - 1)).toReal = D ^ (s₂ - 1) := by
      rw [sp', ← ENNReal.toReal_zpow]; simp
    apply le_sSup; rwa [mem_setOf, dist_congr rfl this]
  · convert le_rfl; change (Icc (𝔰 p) _).toFinset = _; rw [sp, sp']
    apply subset_antisymm
    · rw [← Finset.toFinset_coe (t.σ u x), toFinset_subset_toFinset]
      exact (convex_scales hu).out (Finset.min'_mem ..) (Finset.max'_mem ..)
    · intro z mz; rw [toFinset_Icc, Finset.mem_Icc]
      exact ⟨Finset.min'_le _ _ mz, Finset.le_max' _ _ mz⟩

/-- The constant used in `third_tree_pointwise`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.1.6 -/
lemma third_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖∑ i in t.σ u x, ∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖₊ ≤
    C7_1_6 a * t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  sorry

/-- The constant used in `pointwise_tree_estimate`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
irreducible_def C7_1_3 (a : ℕ) : ℝ≥0 := max (C7_1_4 a) (C7_1_6 a) --2 ^ (151 * (a : ℝ) ^ 3)

-- Used in the proof of Lemma 7.1.3 to translate `∑ p` into `∑ s`
private lemma p_sum_eq_s_sum (I : ℤ → X → ℂ) :
    ∑ p ∈ Finset.filter (fun p ↦ p ∈ (fun x ↦ t.𝔗 x) u) Finset.univ, (E p).indicator (I (𝔰 p)) x =
    ∑ s ∈ t.σ u x, I s x := by
  -- Restrict to a sum over those `p` such that `x ∈ E p`.
  let 𝔗' := Finset.filter (fun p ↦ p ∈ (fun x ↦ t.𝔗 x) u ∧ x ∈ E p) Finset.univ
  have : ∑ p ∈ 𝔗', (E p).indicator (I (𝔰 p)) x = ∑ p ∈ Finset.filter
      (fun p ↦ p ∈ (fun x ↦ t.𝔗 x) u) Finset.univ, (E p).indicator (I (𝔰 p)) x := by
    apply Finset.sum_subset (fun p hp ↦ by simp [(Finset.mem_filter.mp hp).2.1])
    intro p p𝔗 p𝔗'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, 𝔗'] at p𝔗 p𝔗'
    exact indicator_of_not_mem (p𝔗' p𝔗) (I (𝔰 p))
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

/-- Lemma 7.1.3. -/
lemma pointwise_tree_estimate (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖carlesonSum (t u) (fun y ↦ exp (.I * - 𝒬 u y) * f y) x‖₊ ≤
    C7_1_3 a * (MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x') +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x' := by
  set g := approxOnCube (𝓙 (t u)) f
  -- Convert the sum over `p` into a sum over `s`.
  unfold carlesonSum carlesonOn
  rw [p_sum_eq_s_sum fun s x ↦ ∫ (y : X), cexp (I * (Q x y - Q x x)) * K x y *
    («ψ» D (D ^ (-s) * dist x y)) * (fun y ↦ cexp (I * -𝒬 u y) * f y) y]
  -- Next introduce an extra factor of `‖cexp (I * 𝒬 u x)‖₊`, i.e., 1. Then simplify.
  have : 1 = ‖cexp (I * 𝒬 u x)‖₊ := by simp [mul_comm I, nnnorm]
  rw [← one_mul ‖_‖₊, this, ← nnnorm_mul, Finset.mul_sum]
  have : ∑ i ∈ t.σ u x, cexp (I * 𝒬 u x) * ∫ (y : X), (cexp (I * (Q x y - Q x x)) * K x y *
            («ψ» D (D ^ (-i) * dist x y)) * (cexp (I * -𝒬 u y) * f y)) =
          ∑ i ∈ t.σ u x, ∫ (y : X),
            (f y * ((exp (I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y) +
            (f y - g y) * Ks i x y + g y * Ks i x y) := by
    simp_rw [← integral_mul_left, Ks, mul_sub, mul_add, sub_eq_add_neg, exp_add]
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
      (add_le_add_right (nnnorm_add_le _ _) _)
    rw [ENNReal.coe_add, ENNReal.coe_add, mul_add]
    -- Apply Lemmas 7.1.4, 7.1.5, and 7.1.6
    simp_rw [← mul_comm (Ks _ x _)]
    refine add_le_add_three ?_ ?_ (second_tree_pointwise hu hL hx hx')
    · simp_rw [mul_comm (Ks _ x _), mul_comm (f _)]
      have h : C7_1_3 a ≥ C7_1_4 a := by rw [C7_1_3_def]; exact le_max_left (C7_1_4 a) (C7_1_6 a)
      exact (first_tree_pointwise hu hL hx hx' hf).trans <| mul_right_mono (by exact_mod_cast h)
    · have h : C7_1_3 a ≥ C7_1_6 a := by rw [C7_1_3_def]; exact le_max_right (C7_1_4 a) (C7_1_6 a)
      exact (third_tree_pointwise hu hL hx hx' hf).trans <| mul_right_mono (by exact_mod_cast h)
  -- In order to split the integral, we will first need some trivial integrability results
  have h1 {i : ℤ} : Integrable (fun y ↦ approxOnCube (𝓙 (t.𝔗 u)) f y * Ks i x y) := by
    apply (integrable_Ks_x <| one_lt_D (K := K)).bdd_mul
    · exact (stronglyMeasurable_approxOnCube _ _).aestronglyMeasurable
    · use ∑ J ∈ { p | p ∈ 𝓙 (t.𝔗 u) }, ‖⨍ y in J, f y‖
      refine fun x ↦ (norm_sum_le _ _).trans <| Finset.sum_le_sum (fun J hJ ↦ ?_)
      by_cases h : x ∈ (J : Set X) <;> simp [h]
  have : ∃ C, ∀ (y : X), ‖cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖ ≤ C := by
    refine ⟨2, fun y ↦ le_of_le_of_eq (norm_sub_le _ _) ?_⟩
    norm_cast
    rw [mul_comm, norm_exp_ofReal_mul_I, one_add_one_eq_two]
  have h2 {i : ℤ} : Integrable
      (fun y ↦ f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) :=
    hf.integrable_mul <| (integrable_Ks_x <| one_lt_D (K := K)).bdd_mul
      (Measurable.aestronglyMeasurable (by fun_prop)) this
  have h3 {i : ℤ} : Integrable (fun y ↦ (f y - approxOnCube (𝓙 (t.𝔗 u)) f y) * Ks i x y) := by
    simp_rw [sub_mul]
    exact hf.integrable_mul (integrable_Ks_x <| one_lt_D (K := K)) |>.sub h1
  exact Finset.fold_congr fun i _ ↦ by rw [integral_add _ h1, integral_add h2 h3]; exact h2.add h3

end TileStructure.Forest
