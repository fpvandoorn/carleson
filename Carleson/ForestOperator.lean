import Carleson.Forest
import Carleson.HardyLittlewood

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

/- Maybe we should try to avoid using \overline{σ} and \underline{σ} in Lean:
I don't think the set is always non-empty(?) -/
-- def σMax (u : 𝔓 X) (x : X) : ℤ :=
--  Finset.image 𝔰 { p | p ∈ t u ∧ x ∈ E p } |>.max' sorry

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

/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y, f y) x

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
Has value `10 * 2 ^ (105 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_1_4 (a : ℕ) : ℝ≥0 := 10 * 2 ^ (105 * (a : ℝ) ^ 3)

/-- Lemma 7.1.4 -/
lemma first_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ‖∑ i in t.σ u x, ∫ y, (exp (.I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y * f y ‖₊ ≤
    C7_1_4 a * MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  sorry

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
  have d5 : dist_(p') (𝒬 u) (Q x) < 5 :=
    calc
      _ ≤ dist_(p') (𝒬 u) (𝒬 p') + dist_(p') (Q x) (𝒬 p') := dist_triangle_right ..
      _ < 4 + 1 :=
        add_lt_add_of_lt_of_lt ((t.smul_four_le hu mp').2 (by convert mem_ball_self zero_lt_one))
          (subset_cball Qxp')
      _ = _ := by norm_num
  have d5' : dist_{x, D ^ s₂} (𝒬 u) (Q x) < 5 * defaultA a ^ 5 := by
    have i1 : dist x (𝔠 p) < 4 * D ^ 𝔰 p' :=
      (mem_ball.mp (Grid_subset_ball xp)).trans_le <|
        mul_le_mul_of_nonneg_left (zpow_le_of_le one_le_D s_ineq) zero_le_four
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
    have := le_cdist_iterate (x := x) (r := D ^ (s₂ - 1)) (by positivity) (𝒬 u) (Q x) (100 * a)
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
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ‖∑ i in t.σ u x, ∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖₊ ≤
    C7_1_6 a * t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  sorry

/-- The constant used in `pointwise_tree_estimate`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_1_3 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.1.3. -/
lemma pointwise_tree_estimate (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ‖carlesonSum (t u) (fun y ↦ exp (.I * - 𝒬 u y) * f y) x‖₊ ≤
    C7_1_3 a * (MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x'):= by
  set g := approxOnCube (𝓙 (t u)) (‖f ·‖)
  sorry


/-! ## Section 7.2 and Lemma 7.2.1 -/

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (103 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_2 (a : ℕ) : ℝ≥0 := 2 ^ (103 * (a : ℝ) ^ 3)

/-- Lemma 7.2.2. -/
lemma nontangential_operator_bound
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f)
    (θ : Θ X) :
    eLpNorm (nontangentialMaximalFunction θ f · |>.toReal) 2 volume ≤ eLpNorm f 2 volume := by
  sorry

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
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

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
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
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

/-- Lemma 7.2.3. -/
lemma boundary_operator_bound
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f)
    (hu : u ∈ t) :
    eLpNorm (boundaryOperator t u f · |>.toReal) 2 volume ≤ eLpNorm f 2 volume := by
  sorry

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.2.1. -/
lemma tree_projection_estimate
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f)
    (hg : IsBounded (range g)) (h2g : HasCompactSupport g) (h3g : AEStronglyMeasurable g)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume *
    eLpNorm (approxOnCube (𝓛 (t u)) (‖g ·‖)) 2 volume := by
  sorry

/-! ## Section 7.3 and Lemma 7.3.1 -/

/-- The constant used in `local_dens1_tree_bound`.
Has value `2 ^ (101 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_2 (a : ℕ) : ℝ≥0 := 2 ^ (101 * (a : ℝ) ^ 3)

/-- Lemma 7.3.2. -/
lemma local_dens1_tree_bound (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) :
    volume (L ∩ ⋃ (p ∈ t u), E p) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) := by
  sorry

/-- The constant used in `local_dens2_tree_bound`.
Has value `2 ^ (200 * a ^ 3 + 19)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
-- feel free to modify the constant to something simpler.
irreducible_def C7_3_3 (a : ℕ) : ℝ≥0 := 2 ^ (201 * (a : ℝ) ^ 3)

/-- Lemma 7.3.3. -/
lemma local_dens2_tree_bound (hJ : J ∈ 𝓙 (t u)) {q : 𝔓 X} (hq : q ∈ t u)
    (hJq : ¬ Disjoint (J : Set X) (𝓘 q)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  sorry

/-- The constant used in `density_tree_bound1`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_1 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- First part of Lemma 7.3.1. -/
lemma density_tree_bound1
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f)
    (hg : IsBounded (range g)) (h2g : HasCompactSupport g) (h3g : AEStronglyMeasurable g)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_1 a *  dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-- The constant used in `density_tree_bound2`.
Has value `2 ^ (256 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (256 * (a : ℝ) ^ 3)

/-- Second part of Lemma 7.3.1. -/
lemma density_tree_bound2 -- some assumptions on f are superfluous
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f)
    (h4f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : IsBounded (range g)) (h2g : HasCompactSupport g) (h3g : AEStronglyMeasurable g)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-! ## Section 7.4 except Lemmas 4-6 -/

/-- The definition of `Tₚ*g(x)`, defined above Lemma 7.4.1 -/
def adjointCarleson (p : 𝔓 X) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in E p, conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y

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

lemma _root_.MeasureTheory.AEStronglyMeasurable.adjointCarleson (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (adjointCarleson p f) := by
  refine .integral_prod_right'
    (f := fun z ↦ conj (Ks (𝔰 p) z.2 z.1) * exp (Complex.I * (Q z.2 z.2 - Q z.2 z.1)) * f z.2) ?_
  refine .mono_ac (.prod .rfl restrict_absolutelyContinuous) ?_
  refine .mul (.mul ?_ ?_) ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable (aestronglyMeasurable_Ks.prod_swap)
  · refine Complex.continuous_exp.comp_aestronglyMeasurable (.const_mul (.sub ?_ ?_) _)
    · refine Measurable.aestronglyMeasurable ?_
      fun_prop
    · refine continuous_ofReal.comp_aestronglyMeasurable ?_
      exact aestronglyMeasurable_Q₂ (X := X) |>.prod_swap
  · exact hf.snd

lemma _root_.MeasureTheory.AEStronglyMeasurable.adjointCarlesonSum {ℭ : Set (𝔓 X)}
    (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (adjointCarlesonSum ℭ f) :=
  Finset.aestronglyMeasurable_sum _ fun _ _ ↦ hf.adjointCarleson

/-- Part 1 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support1 (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    adjointCarleson p f =
    (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (adjointCarleson p ((𝓘 p : Set X).indicator f)) := by
  sorry

/-- Part 2 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support2 (hu : u ∈ t) (hp : p ∈ t u)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    adjointCarleson p f =
    (𝓘 p : Set X).indicator (adjointCarleson p ((𝓘 p : Set X).indicator f)) := by
  sorry

/-- The constant used in `adjoint_tree_estimate`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_2 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- Lemma 7.4.2. -/
lemma adjoint_tree_estimate (hu : u ∈ t) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    eLpNorm (adjointCarlesonSum (t u) f) 2 volume ≤
    C7_4_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  sorry

/-- The constant used in `adjoint_tree_control`.
Has value `2 ^ (156 * a ^ 3)` in the blueprint. -/
irreducible_def C7_4_3 (a : ℕ) : ℝ≥0 :=
  C7_4_2 a + CMB (defaultA a) 2 + 1

/-- Lemma 7.4.3. -/
lemma adjoint_tree_control (hu : u ∈ t) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
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
      · exact h3f.adjointCarlesonSum.norm.add <| .maximalFunction_toReal 𝓑_finite.countable
      · exact h3f.norm
      gcongr
      refine eLpNorm_add_le ?_ ?_ one_le_two |>.trans ?_
      · exact h3f.adjointCarlesonSum.norm
      · exact .maximalFunction_toReal 𝓑_finite.countable
      rfl
  _ ≤ eLpNorm (adjointCarlesonSum (t u) f) 2 volume +
    eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f · |>.toReal) 2 volume +
    eLpNorm f 2 volume := by simp_rw [eLpNorm_norm]; rfl
  _ ≤ C7_4_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume +
    CMB (defaultA a) 2 * eLpNorm f 2 volume +
    eLpNorm f 2 volume := by
      gcongr
      · exact adjoint_tree_estimate hu hf h2f h3f
      · exact hasStrongType_MB 𝓑_finite one_lt_two _ (h2f.memℒp_of_isBounded hf h3f) |>.2
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
      _ ≥ 2 ^ (Z * n) := by apply pow_le_pow_right one_le_two; rw [mul_add_one]; omega
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

/-! ## Section 7.5 -/

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := 𝓙 (𝔖₀ t u₁ u₂) ∩ Iic (𝓘 u₁)

/-- The definition of χ-tilde, defined in the proof of Lemma 7.5.2 -/
def χtilde (J : Grid X) (x : X) : ℝ≥0 :=
  8 - D ^ (- s J) * dist x (c J) |>.toNNReal

variable (t u₁ u₂) in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J x / ∑ J' ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χtilde J' x

-- /-- The definition of `B`, defined in (7.5.1) -/
-- protected def _root_.Grid.ball (I : Grid X) : Set X := ball (c I) (8 * D ^ s I)

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ)  (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

/-- Part of Lemma 7.5.1. -/
lemma union_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    ⋃ J ∈ 𝓙₅ t u₁ u₂, (J : Set X) = 𝓘 u₁ := by
  sorry

/-- Part of Lemma 7.5.1. -/
lemma pairwiseDisjoint_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
  (h : ¬ Disjoint (J : Set X) J') : s J + 1 ≤ s J' := by
  sorry

/-- The constant used in `dist_χ_χ_le`.
Has value `2 ^ (226 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_2 (a : ℕ) : ℝ≥0 := 2 ^ (226 * (a : ℝ) ^ 3)

/-- Part of Lemma 7.5.2. -/
lemma sum_χ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (x : X) :
    ∑ J ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χ t u₁ u₂ J x = (𝓘 u₁ : Set X).indicator 1 x := by
  sorry

/-- Part of Lemma 7.5.2. -/
lemma χ_mem_Icc (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hx : x ∈ 𝓘 u₁) :
    χ t u₁ u₂ J x ∈ Icc 0 ((ball (c I) (8 * D ^ s I)).indicator 1 x) := by
  sorry

/-- Part of Lemma 7.5.2. -/
lemma dist_χ_χ_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hx : x ∈ 𝓘 u₁) (hx' : x' ∈ 𝓘 u₁) :
    dist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x) ≤ C7_5_2 a * dist x x' / D ^ s J := by
  sorry


/-! ### Subsection 7.5.2 and Lemma 7.5.4 -/

/-- The constant used in `holder_correlation_tile`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_5 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.5.5. -/
lemma holder_correlation_tile (hu : u ∈ t) (hp : p ∈ t u)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    nndist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
      (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
    (nndist x x' / D ^ (𝔰 p : ℝ)) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖₊ := by
  sorry

/-- Lemma 7.5.6. -/
lemma limited_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ∈ Icc (s J) (s J + 3) := by
  sorry

/-- The constant used in `local_tree_control`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_7 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.5.7. -/
lemma local_tree_control (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    C7_5_7 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- Lemma 7.5.8. -/
lemma scales_impacting_interval (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hp : p ∈ t u₁ ∪ (t u₂ ∩ 𝔖₀ t u₁ u₂))
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) : s J ≤ 𝔰 p := by
  sorry

/-- The constant used in `global_tree_control1_1`.
Has value `2 ^ (154 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_9_1 (a : ℕ) : ℝ≥0 := 2 ^ (154 * (a : ℝ) ^ 3)

/-- The constant used in `global_tree_control1_2`.
Has value `2 ^ (153 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_9_2 (a : ℕ) : ℝ≥0 := 2 ^ (153 * (a : ℝ) ^ 3)

/-- Part 1 of Lemma 7.5.9 -/
lemma global_tree_control1_1 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊) +
    C7_5_9_1 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- Part 2 of Lemma 7.5.9 -/
lemma global_tree_control1_2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f)
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
    nndist (exp (.I * 𝒬 u x) * adjointCarlesonSum ℭ f x)
      (exp (.I * 𝒬 u x') * adjointCarlesonSum ℭ f x') ≤
    C7_5_9_1 a * (nndist x x' / D ^ (𝔰 p : ℝ)) ^ (a : ℝ)⁻¹ *
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- The constant used in `global_tree_control2`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_10 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- Lemma 7.5.10 -/
lemma global_tree_control2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    ⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖₊ +
    C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- The constant used in `holder_correlation_tree`.
Has value `2 ^ (535 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_4 (a : ℕ) : ℝ≥0 := 2 ^ (535 * (a : ℝ) ^ 3)

/-- Lemma 7.5.4. -/
lemma holder_correlation_tree (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    HolderOnWith (C7_5_4 a *
    ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖₊) +
    (⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f₁ ·‖) x).toNNReal) *
    ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖₊) +
    (⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f₂ ·‖) x).toNNReal))
    nnτ (holderFunction t u₁ u₂ f₁ f₂ J) (ball (c J) (8 * D ^ s J)) := by
  sorry


/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/

/-- The constant used in `lower_oscillation_bound`.
Has value `2 ^ (Z * n / 2 - 201 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_11 (a n : ℕ) : ℝ≥0 := 2 ^ (Z * n / 2 - 201 * (a : ℝ) ^ 3)

/-- Lemma 7.5.11 -/
lemma lower_oscillation_bound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    C7_5_11 a n ≤ dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
  sorry

/-- The constant used in `correlation_distant_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_5 (a n : ℕ) : ℝ≥0 := 2 ^ (541 * (a : ℝ) ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))

/-- Lemma 7.4.5 -/
lemma correlation_distant_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-! ## Section 7.6 and Lemma 7.4.6 -/

variable (t u₁) in
/-- The definition `𝓙'` at the start of Section 7.6.
We use a different notation to distinguish it from the 𝓙' used in Section 7.5 -/
def 𝓙₆ : Set (Grid X) := 𝓙 (t u₁) ∩ Iic (𝓘 u₁)

/-- Part of Lemma 7.6.1. -/
lemma union_𝓙₆ (hu₁ : u₁ ∈ t) :
    ⋃ J ∈ 𝓙₆ t u₁, (J : Set X) = 𝓘 u₁ := by
  sorry

/-- Part of Lemma 7.6.1. -/
lemma pairwiseDisjoint_𝓙₆ (hu₁ : u₁ ∈ t) :
    (𝓙₆ t u₁).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

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

/-- The constant used in `square_function_count`.
Has value `Z * n / (202 * a ^ 3) - 2` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_4 (a : ℕ) (s : ℤ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 2) * (8 * D ^ (- s)) ^ κ

/-- Lemma 7.6.4. -/
lemma square_function_count (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁) (s' : ℤ /- ? -/) :
    ⨍⁻ x : X, (∑ I ∈ {I : Grid X | s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
    ¬ Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)) },
    (ball (c I) (8 * D ^ s I)).indicator 1 x) ^ 2 ≤ C7_6_4 a s' := by
  sorry

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


/-! ## Section 7.7 and Proposition 2.0.4 -/


/-- The row-decomposition of a tree, defined in the proof of Lemma 7.7.1.
The indexing is off-by-one compared to the blueprint. -/
def rowDecomp (t : Forest X n) (j : ℕ) : Row X n := sorry

/-- Part of Lemma 7.7.1 -/
@[simp]
lemma biUnion_rowDecomp : ⋃ j < 2 ^ n, t.rowDecomp j = (t : Set (𝔓 X)) := by
  sorry

/-- Part of Lemma 7.7.1 -/
lemma pairwiseDisjoint_rowDecomp :
    (Iio (2 ^ n)).PairwiseDisjoint (rowDecomp t · : ℕ → Set (𝔓 X)) := by
  sorry

@[simp] lemma rowDecomp_apply : t.rowDecomp j u = t u := by
  sorry

/-- The constant used in `row_bound`.
Has value `2 ^ (156 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_1 (a n : ℕ) : ℝ≥0 := 2 ^ (156 * (a : ℝ) ^ 3 - n / 2)

/-- The constant used in `indicator_row_bound`.
Has value `2 ^ (257 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_2 (a n : ℕ) : ℝ≥0 := 2 ^ (257 * (a : ℝ) ^ 3 - n / 2)

/-- Part of Lemma 7.7.2. -/
lemma row_bound (hj : j < 2 ^ n) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) f) 2 volume ≤
    C7_7_2_1 a n * eLpNorm f 2 volume := by
  sorry

/-- Part of Lemma 7.7.2. -/
lemma indicator_row_bound (hj : j < 2 ^ n) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
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

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := 2 ^ (432 * a ^ 3 - (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (X := X) (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry
