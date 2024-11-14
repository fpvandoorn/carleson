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

end TileStructure.Forest
