import Carleson.ForestOperator.AlmostOrthogonality
import Mathlib.Tactic.Rify
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.ToMathlib.Data.ENNReal
import Carleson.Calculations

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

/-! ## Section 7.5 -/

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := 𝓙 (𝔖₀ t u₁ u₂) ∩ Iic (𝓘 u₁)

/-- The definition of χ-tilde, defined in the proof of Lemma 7.5.2 -/
def χtilde (J : Grid X) (u₁ : 𝔓 X) : X → ℝ≥0 :=
  (𝓘 u₁ : Set X).indicator fun x ↦ (8 - D ^ (- s J) * dist x (c J)).toNNReal

variable (t u₁ u₂) in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J u₁ x / ∑ J' ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χtilde J' u₁ x

-- /-- The definition of `B`, defined in (7.5.1) -/
-- protected def _root_.Grid.ball (I : Grid X) : Set X := ball (c I) (8 * D ^ s I)

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ)  (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/- AUXILIARY LEMMAS:START -/
lemma IF_subset_THEN_distance_between_centers (subset : (J : Set X) ⊆ J') :
    dist (c J) (c J') < 4 * D ^ s J' := by
  apply Grid_subset_ball
  exact (subset (Grid.c_mem_Grid))

lemma IF_disjoint_with_ball_THEN_distance_bigger_than_radius {J : X} {r : ℝ} {pSet : Set X} {p : X}
    (belongs : p ∈ pSet) (h : Disjoint (Metric.ball J r) pSet) :
    dist J p ≥ r := by
  rw [disjoint_iff_inter_eq_empty, inter_comm] at h
  by_contra! contr
  apply (Set.mem_empty_iff_false p).mp
  rw [← h]
  apply (Set.mem_inter_iff ..).mpr
  apply mem_ball_comm.mp at contr
  exact ⟨belongs, contr⟩

lemma dist_triangle5 (a b c d e : X) :
    dist a e ≤ dist a b + dist b c + dist c d + dist d e :=
  calc
    dist a e ≤ dist a d + dist d e := dist_triangle a d e
    _ ≤ (dist a c + dist c d) + dist d e := add_le_add_right (dist_triangle a c d) _
    _ ≤ (dist a b + dist b c + dist c d) + dist d e :=
      add_le_add_right (add_le_add_right (dist_triangle a b c) _) _

lemma 𝓘_subset_iUnion_𝓙_𝔖₀ : (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := by
  rw [biUnion_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)]
  apply subset_iUnion_of_subset (𝓘 u₁)
  rfl
/- AUXILIARY LEMMAS:END -/

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

/-- Part of Lemma 7.5.1. -/
lemma union_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    ⋃ J ∈ 𝓙₅ t u₁ u₂, (J : Set X) = 𝓘 u₁ := by
  apply Set.Subset.antisymm
  · intros x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨cube, ⟨_, interval⟩, h⟩
    exact Set.mem_of_mem_of_subset h interval.left
  · intros x hx
    have existsCube : x ∈ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := 𝓘_subset_iUnion_𝓙_𝔖₀ hx
    simp only [mem_iUnion, exists_prop] at existsCube
    rcases existsCube with ⟨cube, cube_in_𝓙, xInCube⟩
    simp only [mem_iUnion, exists_prop]
    have notDisjoint := Set.not_disjoint_iff.mpr ⟨x, xInCube, hx⟩
    have cubeIn𝓙₀ : cube ∈ 𝓙₀ (t.𝔖₀ u₁ u₂) := mem_of_mem_inter_left cube_in_𝓙
    simp only [mem_setOf_eq] at cubeIn𝓙₀
    cases cubeIn𝓙₀ with
    | inl west =>
      refine ⟨cube, ?_, xInCube⟩
      unfold 𝓙₅
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
          apply subset_of_nmem_Iic_of_not_disjoint cube
          · have notIn : cube ∉ t.𝓙₅ u₁ u₂ := λ a => contr cube a xInCube
            rw [𝓙₅, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
            exact Or.resolve_left notIn (Set.not_not_mem.mpr cube_in_𝓙)
          · exact notDisjoint
        _ ⊆ ball (c cube) (4 * D ^ s cube) := by
          exact Grid_subset_ball (i := cube)
        _ ⊆ ball (c cube) (100 * D ^ (s cube + 1)) := by
          unfold ball
          intro y xy
          rw [mem_setOf_eq] at xy ⊢
          have numbers : 4 * (D : ℝ) ^ s cube < 100 * D ^ (s cube + 1) := by
            gcongr
            linarith
            exact one_lt_D (X := X)
            linarith
          exact gt_trans numbers xy
      have black : ¬↑(𝓘 p) ⊆ ball (c cube) (100 * D ^ (s cube + 1)) := by
        have in_𝔖₀ := 𝔗_subset_𝔖₀ (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u)
        rw [subset_def] at in_𝔖₀
        exact east p (in_𝔖₀ p belongs)
      contradiction

/-- Part of Lemma 7.5.1. -/
lemma pairwiseDisjoint_𝓙₅ :
    (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  have ss : (𝓙 (t.𝔖₀ u₁ u₂) ∩ Iic (𝓘 u₁)) ⊆ 𝓙 (t.𝔖₀ u₁ u₂) := inter_subset_left
  exact PairwiseDisjoint.subset (pairwiseDisjoint_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)) ss

lemma bigger_than_𝓙_is_not_in_𝓙₀ {𝔖 : Set (𝔓 X)} {A B : Grid X}
    (le : A ≤ B) (sle : s A < s B) (A_in : A ∈ 𝓙 𝔖) :
    B ∉ 𝓙₀ 𝔖 := by
  apply And.right at A_in
  simp only [Grid.le_def, and_imp] at A_in
  intro contr
  apply Lean.Omega.Int.le_lt_asymm (x := s A) (y := s B)
  · exact (A_in contr le.1 (le_of_lt sle)).2
  · exact sle

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (J : Set X) J') :
    s J - 1 ≤ s J' := by
  by_contra! contr
  have pNotSubset : ∀ p ∈ t.𝔖₀ u₁ u₂, ¬↑(𝓘 p) ⊆ ball (c J) (100 * D^(s J + 1)) := by
    obtain ⟨⟨Jin𝓙₀, _⟩, _⟩ := hJ
    have notMin : s J ≠ -S := by linarith [(scale_mem_Icc (i := J')).left]
    exact Jin𝓙₀.resolve_left notMin
  have ⟨p, pIn, pSubset⟩ : ∃ p ∈ t.𝔖₀ u₁ u₂, (𝓘 p : Set X) ⊆ ball (c J) (100 * D^(s J + 1)) := by
    have ⟨J'', belongs, plusOne⟩ : ∃ J'', J' ≤ J'' ∧ s J'' = s J' + 1 :=
      Grid.exists_scale_succ (by linarith)
    have ⟨r, rIn, rSubset⟩ : ∃ p ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p) ⊆ ball (c J'') (100 * D^(s J' + 1 + 1)) := by
      have : J'' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ belongs (by linarith) hJ'.1
      simp only [𝓙₀, mem_setOf_eq, plusOne] at this
      push_neg at this
      exact this.2
    use r
    use rIn
    calc (𝓘 r : Set X)
    _ ⊆ ball (c J'') (100 * D^(s J' + 1 + 1)) := rSubset
    _ ⊆ ball (c J) (100 * D^(s J + 1)) := by
      intro x
      simp only [ball, mem_setOf_eq]
      intro triangle_1
      have smaller : s J'' < s J := by linarith
      have DisBig := twentyfive_le_realD X
      calc dist x (c J)
      _ ≤ dist x (c J'') + dist (c J'') (c J) := dist_triangle x (c J'') (c J)
      _ ≤ 100 * D^(s J'' + 1) + dist (c J'') (c J) := by
        rw [← plusOne] at triangle_1
        gcongr
      _ ≤ 100 * D^(s J'' + 1) + 4 * D^(s J) := by
        have subset : (J'' : Set X) ⊆ J := by
          cases fundamental_dyadic smaller.le with
          | inl subset => exact subset
          | inr disj =>
            have disjoint := disj.mono_left belongs.1
            rw [disjoint_comm] at disjoint
            contradiction
        linarith [IF_subset_THEN_distance_between_centers subset]
      _ ≤ 100 * D^(s J) + 4 * D^(s J) := by
        gcongr
        · linarith
        · exact smaller
      _ < 100 * D^(s J + 1) := by
        ring_nf
        rw [zpow_one_add₀ (by linarith), mul_comm (D : ℝ), mul_assoc]
        gcongr
        linarith
  exact (pNotSubset p pIn) pSubset

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

section OneInOneOut

omit [ProofData a q K σ₁ σ₂ F G] in
lemma ψ_le_max [ProofData a q K σ₁ σ₂ F G] {x : ℝ} : ψ x ≤ max 0 ((2 - 4 * x) ^ (a : ℝ)⁻¹) := by
  by_cases h₁ : x ≤ 1 / 4
  · exact (ψ_le_one ..).trans ((Real.one_le_rpow (by linarith) (by simp)).trans (le_max_right ..))
  by_cases h₂ : 1 / 2 ≤ x
  · rw [ψ_formula₄ h₂]; exact le_max_left ..
  push_neg at h₁ h₂; rw [ψ_formula₃ (one_lt_D (X := X)) ⟨h₁.le, h₂.le⟩]
  refine le_trans ?_ (le_max_right ..)
  set y := 2 - 4 * x; apply Real.self_le_rpow_of_le_one
  · unfold y; linarith
  · unfold y; linarith
  · exact Nat.cast_inv_le_one a

lemma le_of_mem_E {y : X} (hy : y ∈ E p) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    2 - 4 * ((D : ℝ) ^ (-𝔰 p) * dist y x) ≤ dist x x' / D ^ (𝔰 p) * 4 := by
  have := one_le_D (a := a)
  calc
    _ ≤ 2 - 4 * (D : ℝ) ^ (-𝔰 p) * (dist x (𝔠 p) - dist y (𝔠 p)) := by
      rw [mul_assoc]; gcongr; rw [sub_le_iff_le_add]; exact dist_triangle_left ..
    _ ≤ 2 - 4 * (D : ℝ) ^ (-𝔰 p) * dist x (𝔠 p) + 16 := by
      rw [mul_sub, sub_add]; gcongr; rw [mul_rotate, show (16 : ℝ) = 4 * 4 by norm_num]; gcongr
      rw [zpow_neg, inv_mul_le_iff₀' (by positivity)]
      exact (mem_ball.mp ((E_subset_𝓘.trans Grid_subset_ball) hy)).le
    _ = 4 * (D : ℝ) ^ (-𝔰 p) * (5 * D ^ 𝔰 p - dist x (𝔠 p)) - 2 := by
      rw [mul_sub, show 4 * (D : ℝ) ^ (-𝔰 p) * (5 * D ^ 𝔰 p) = 20 * (D ^ 𝔰 p * D ^ (-𝔰 p)) by ring,
        ← zpow_add₀ (by positivity), add_neg_cancel, zpow_zero, mul_one]; ring
    _ ≤ 4 * (D : ℝ) ^ (-𝔰 p) * (dist x' (𝔠 p) - dist x (𝔠 p)) - 2 := by
      gcongr; rwa [mem_ball, not_lt] at hx'
    _ ≤ 4 * (D : ℝ) ^ (-𝔰 p) * dist x x' - 2 := by
      gcongr; rw [sub_le_iff_le_add]; exact dist_triangle_left ..
    _ ≤ _ := by rw [zpow_neg, mul_rotate, inv_mul_eq_div]; norm_num

lemma enorm_ψ_le_edist {y : X} (my : y ∈ E p) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖ψ (D ^ (-𝔰 p) * dist y x)‖ₑ ≤ 4 * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  by_cases h : 1 / 2 ≤ D ^ (-𝔰 p) * dist y x
  · rw [ψ_formula₄ h, enorm_zero]; exact zero_le _
  replace h : 0 ≤ 2 - 4 * (D ^ (-𝔰 p) * dist y x) := by linarith
  calc
    _ ≤ ‖max 0 ((2 - 4 * (D ^ (-𝔰 p) * dist y x)) ^ (a : ℝ)⁻¹)‖ₑ :=
      Real.enorm_le_enorm (zero_le_ψ ..) (ψ_le_max (X := X))
    _ = ‖2 - 4 * (D ^ (-𝔰 p) * dist y x)‖ₑ ^ (a : ℝ)⁻¹ := by
      rw [max_eq_right (Real.rpow_nonneg h _), Real.enorm_rpow_of_nonneg h (by positivity)]
    _ ≤ ‖dist x x' / D ^ (𝔰 p) * 4‖ₑ ^ (a : ℝ)⁻¹ := by
      gcongr; exact Real.enorm_le_enorm h (le_of_mem_E my hx')
    _ = (edist x x' / D ^ (𝔰 p) * 4) ^ (a : ℝ)⁻¹ := by
      rw [enorm_mul]; nth_rw 2 [enorm_eq_nnnorm]; rw [Real.nnnorm_ofNat, ENNReal.coe_ofNat]; congr
      rw [enorm_eq_nnnorm, nnnorm_div, nnnorm_zpow]; norm_cast
      rw [ENNReal.coe_div (by simp; positivity), ENNReal.coe_zpow (by simp)]; norm_cast; congr
      rw [edist_dist, ← Real.enorm_of_nonneg dist_nonneg, enorm_eq_nnnorm]
    _ ≤ _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), mul_comm]; gcongr
      nth_rw 2 [← ENNReal.rpow_one 4]
      exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.cast_inv_le_one a)

/-- This bound is used in both nontrivial cases of Lemma 7.5.5. -/
lemma volume_xDsp_bound (hx : x ∈ 𝓘 p) :
    volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a) ≤ volume (ball x (D ^ 𝔰 p)) := by
  apply ENNReal.div_le_of_le_mul'
  have h : dist x (𝔠 p) + 4 * D ^ 𝔰 p ≤ 8 * D ^ 𝔰 p := by
    calc
      _ ≤ 4 * (D : ℝ) ^ 𝔰 p + 4 * ↑D ^ 𝔰 p := by
        gcongr; exact (mem_ball.mp (Grid_subset_ball hx)).le
      _ = _ := by rw [← add_mul]; norm_num
  convert measure_ball_le_of_dist_le' (μ := volume) (by norm_num) h
  unfold As defaultA; norm_cast; rw [← pow_mul']; congr 2
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow]; norm_num

lemma holder_correlation_tile_one
    (hf : BoundedCompactSupport f) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖adjointCarleson p f x‖ₑ ≤ C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
      (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖₊ :=
  calc
    _ ≤ ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x)‖ₑ * ‖exp (I * (Q y y - Q y x))‖ₑ * ‖f y‖ₑ := by
      simp_rw [← enorm_mul]; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr 1 with y; norm_cast; nth_rw 1 [mul_comm I]; nth_rw 2 [← enorm_norm]
      rw [norm_exp_ofReal_mul_I, enorm_one, mul_one, ← enorm_norm, RCLike.norm_conj, enorm_norm]
    _ ≤ ∫⁻ y in E p, C2_1_3 a / volume (ball y (D ^ 𝔰 p)) *
        ‖ψ (D ^ (-𝔰 p) * dist y x)‖ₑ * ‖f y‖ₑ := by gcongr; exact enorm_Ks_le
    _ ≤ ∫⁻ y in E p, C2_1_3 a / (volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a)) *
        (4 * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹) * ‖f y‖ₑ := by
      refine setLIntegral_mono ((Measurable.enorm hf.stronglyMeasurable.measurable).const_mul _)
        fun y my ↦ ?_
      gcongr with y
      · exact volume_xDsp_bound (E_subset_𝓘 my)
      · exact enorm_ψ_le_edist my hx'
    _ = C2_1_3 a * 2 ^ (3 * a) * 4 / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
        (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
      rw [lintegral_const_mul _ hf.stronglyMeasurable.measurable.enorm, ← mul_assoc]; congr 2
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (by simp) (by simp), mul_assoc,
        ENNReal.mul_comm_div, ← mul_div_assoc, ← mul_assoc, mul_comm (2 ^ (3 * a))]
    _ ≤ _ := by
      gcongr; rw [C2_1_3, C7_5_5]; norm_cast
      simp_rw [Nat.cast_pow, NNReal.rpow_natCast, Nat.cast_ofNat,
        show (4 : ℝ≥0) = 2 ^ 2 by norm_num, ← pow_add]
      apply pow_le_pow_right' one_le_two
      calc
        _ = 102 * a ^ 3 + 3 * a * 1 * 1 + 2 * 1 * 1 * 1 := by norm_num
        _ ≤ 102 * a ^ 3 + 3 * a * a * a + 2 * a * a * a := by gcongr <;> linarith [four_le_a X]
        _ = 107 * a ^ 3 := by ring
        _ ≤ _ := by gcongr; norm_num

end OneInOneOut

section BothIn

lemma integrable_adjointCarleson_interior (hf : BoundedCompactSupport f) :
    Integrable (fun y ↦ exp (.I * 𝒬 u x) * (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y))
      (volume.restrict (E p)) := by
  have fb := hf.isBounded
  simp_rw [isBounded_iff_forall_norm_le, mem_range, forall_exists_index,
    forall_apply_eq_imp_iff] at fb
  obtain ⟨B, hB⟩ := fb
  refine Integrable.const_mul ?_ _; simp_rw [mul_rotate]
  refine Integrable.bdd_mul ?_ ?_ ⟨B, fun y ↦ ?_⟩
  · have bep : IsBounded (E p) := by
      rw [isBounded_iff_subset_ball (𝔠 p)]; use 4 * D ^ 𝔰 p
      exact E_subset_𝓘.trans Grid_subset_ball
    obtain ⟨C, nnC, hC⟩ := IsBounded.exists_bound_of_norm_Ks bep (𝔰 p)
    apply Measure.integrableOn_of_bounded (M := C) volume_E_lt_top.ne ?_ ?_
    · exact continuous_conj.comp_aestronglyMeasurable
        (measurable_Ks.comp measurable_prod_mk_right).aestronglyMeasurable
    · simp only [RCLike.norm_conj]
      exact ae_restrict_of_forall_mem measurableSet_E fun y my ↦ hC y x my
  · refine ((Measurable.const_mul ?_ I).cexp.mul
      hf.stronglyMeasurable.measurable).aestronglyMeasurable
    refine (measurable_ofReal.comp ?_).sub (measurable_ofReal.comp ?_)
    · have pair : Measurable fun y : X ↦ (y, y) := by fun_prop
      exact measurable_Q₂.comp pair
    · exact measurable_Q₂.comp measurable_prod_mk_right
  · rw [norm_mul, ← one_mul B]
    refine mul_le_mul ?_ (hB y) (norm_nonneg _) zero_le_one
    rw_mod_cast [mul_comm, norm_exp_ofReal_mul_I]

/-- Sub-equations (7.5.10) and (7.5.11) in Lemma 7.5.5. -/
lemma holder_correlation_rearrange (hf : BoundedCompactSupport f) :
    edist (exp (.I * 𝒬 u x) * adjointCarleson p f x) (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    (∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x‖ₑ * ‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ) +
      ∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x - Ks (𝔰 p) y x'‖ₑ :=
  calc
    _ = ‖∫ y in E p,
        exp (.I * 𝒬 u x) * (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y) -
        exp (.I * 𝒬 u x') * (conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x')) * f y)‖ₑ := by
      rw [edist_eq_enorm_sub, adjointCarleson, adjointCarleson, ← integral_mul_left,
        ← integral_mul_left, ← integral_sub] <;> exact integrable_adjointCarleson_interior hf
    _ = ‖∫ y in E p, f y *
          (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x + 𝒬 u x)) -
          conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x' + 𝒬 u x')))‖ₑ := by
      congr! 3 with y
      rw [← mul_assoc _ _ (f y), ← mul_assoc _ _ (f y), ← sub_mul, mul_comm (f y)]
      congr 1
      rw [mul_comm _ (_ * _), mul_comm _ (_ * _), mul_assoc, mul_assoc, ← exp_add, ← exp_add,
        mul_add, mul_add]
    _ = ‖∫ y in E p, f y *
          exp (.I * (Q y y - Q y x' + 𝒬 u x')) * exp (-(.I * (Q y y - Q y x' + 𝒬 u x'))) *
          (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x + 𝒬 u x)) -
          conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x' + 𝒬 u x')))‖ₑ := by
      congr! 3 with y
      rw [mul_assoc _ (exp _) (exp _), ← exp_add, add_neg_cancel, exp_zero, mul_one]
    _ ≤ ∫⁻ y in E p, ‖f y‖ₑ *
          ‖exp (.I * (Q y y - Q y x' + 𝒬 u x'))‖ₑ * ‖exp (-(.I * (Q y y - Q y x' + 𝒬 u x'))) *
          (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x + 𝒬 u x)) -
          conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x' + 𝒬 u x')))‖ₑ := by
      simp_rw [← enorm_mul, ← mul_assoc]; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in E p, ‖f y‖ₑ *
          ‖conj (Ks (𝔰 p) y x) * exp (.I * (- Q y x + Q y x' + 𝒬 u x - 𝒬 u x' : ℝ)) -
          conj (Ks (𝔰 p) y x')‖ₑ := by
      congr 1 with y; norm_cast; nth_rw 1 [mul_comm I]; nth_rw 2 [← enorm_norm]
      rw [norm_exp_ofReal_mul_I, enorm_one, mul_one]; congr 2
      rw [mul_sub, ← mul_assoc, mul_rotate, mul_assoc, ← exp_add, ← sub_eq_add_neg, ← mul_sub,
        ← mul_assoc, mul_rotate, mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      congr; norm_cast; ring
    _ ≤ ∫⁻ y in E p, ‖f y‖ₑ *
          (‖conj (Ks (𝔰 p) y x) * (exp (.I * (- Q y x + Q y x' + 𝒬 u x - 𝒬 u x' : ℝ)) - 1)‖ₑ +
          ‖conj (Ks (𝔰 p) y x) - conj (Ks (𝔰 p) y x')‖ₑ) := by
      gcongr with y
      rw [← sub_add_cancel (conj (Ks (𝔰 p) y x) * _) (conj (Ks (𝔰 p) y x)), ← mul_sub_one,
        add_sub_assoc]
      exact _root_.enorm_add_le _ _
    _ = (∫⁻ y in E p, ‖f y‖ₑ *
          ‖conj (Ks (𝔰 p) y x) * (exp (.I * (- Q y x + Q y x' + 𝒬 u x - 𝒬 u x' : ℝ)) - 1)‖ₑ) +
        ∫⁻ y in E p, ‖f y‖ₑ * ‖conj (Ks (𝔰 p) y x) - conj (Ks (𝔰 p) y x')‖ₑ := by
      simp_rw [mul_add]; apply lintegral_add_right
      apply hf.stronglyMeasurable.measurable.enorm.mul (Measurable.enorm (Measurable.sub ?_ ?_)) <;>
        exact (continuous_conj.comp_stronglyMeasurable
          (measurable_Ks.comp measurable_prod_mk_right).stronglyMeasurable).measurable
    _ ≤ (∫⁻ y in E p, ‖f y‖ₑ * ‖conj (Ks (𝔰 p) y x)‖ₑ * ‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ) +
        ∫⁻ y in E p, ‖f y‖ₑ * ‖conj (Ks (𝔰 p) y x) - conj (Ks (𝔰 p) y x')‖ₑ := by
      simp_rw [mul_assoc]; gcongr with y; rw [enorm_mul]; gcongr
      exact enorm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      congr! 4
      · congr 1; rw [← enorm_norm, RCLike.norm_conj, enorm_norm]
      · rw [← map_sub, ← enorm_norm, RCLike.norm_conj, enorm_norm]

/-- Multiplicative factor for the bound on `‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ`. -/
irreducible_def Q7_5_5 (a : ℕ) : ℝ≥0 := 10 * 2 ^ (6 * a)

lemma QQQQ_bound_real {y : X} (my : y ∈ E p) (hu : u ∈ t) (hp : p ∈ t u)
    (hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) (hx' : x' ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖-Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ ≤ Q7_5_5 a * (dist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  rcases eq_or_ne x x' with rfl | hd
  · have : (a : ℝ)⁻¹ ≠ 0 := by rw [ne_eq, inv_eq_zero, Nat.cast_eq_zero]; linarith [four_le_a X]
    simp [this]
  replace hd : 0 < dist x x' := dist_pos.mpr hd
  have Dsppos : (0 : ℝ) < D ^ 𝔰 p := by simp only [defaultD]; positivity
  have dxx' : dist x x' < 10 * D ^ 𝔰 p :=
    calc
      _ ≤ dist x (𝔠 p) + dist x' (𝔠 p) := dist_triangle_right ..
      _ < 5 * D ^ 𝔰 p + 5 * D ^ 𝔰 p := by rw [mem_ball] at hx hx'; gcongr
      _ = _ := by rw [← add_mul]; norm_num
  let k : ℤ := ⌊Real.logb 2 (10 * D ^ 𝔰 p / dist x x') / a⌋
  have knn : 0 ≤ k := by
    calc
      _ ≥ ⌊Real.logb 2 1 / a⌋ := by
        simp_rw [k]; gcongr
        · exact one_lt_two
        · rw [one_le_div hd]; exact dxx'.le
      _ = _ := by simp
  calc
    _ ≤ dist_{x, 16 / 10 * dist x x'} (Q y) (𝒬 u) := by
      rw [show -Q y x + Q y x' + 𝒬 u x - 𝒬 u x' = Q y x' - 𝒬 u x' - Q y x + 𝒬 u x by ring]
      apply oscillation_le_cdist <;> rw [mem_ball]
      · rw [← one_mul (dist x' x), dist_comm]; exact mul_lt_mul_of_pos_right (by norm_num) hd
      · simp [hd]
    _ ≤ 2 ^ (-k) * dist_{x, (defaultA a) ^ k * (16 / 10 * dist x x')} (Q y) (𝒬 u) := by
      rw [← div_le_iff₀' (by positivity), zpow_neg, div_inv_eq_mul, mul_comm]
      have : ∀ r : ℝ, r ^ k = r ^ k.toNat := fun r ↦ by
        rw [← zpow_natCast]; congr; exact (Int.toNat_of_nonneg knn).symm
      rw [this, this]; exact le_cdist_iterate (by positivity) ..
    _ ≤ 2 ^ (-k) * dist_{x, 16 * D ^ 𝔰 p} (Q y) (𝒬 u) := by
      refine mul_le_mul_of_nonneg_left (cdist_mono (ball_subset_ball ?_)) (by positivity)
      calc
        _ ≤ ((2 : ℝ) ^ a) ^ (Real.logb 2 (10 * D ^ 𝔰 p / dist x x') / a) *
            (16 / 10 * dist x x') := by
          simp_rw [defaultA]; rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_intCast]; gcongr
          · norm_cast; exact Nat.one_le_two_pow
          · exact Int.floor_le _
        _ = _ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
            mul_div_cancel₀ _ (by norm_cast; linarith [four_le_a X]),
            Real.rpow_logb zero_lt_two one_lt_two.ne' (by positivity), div_mul_comm,
            mul_div_cancel_right₀ _ hd.ne', ← mul_assoc]
          norm_num
    _ ≤ 2 ^ (-k) * defaultA a * dist_{𝔠 p, 8 * D ^ 𝔰 p} (Q y) (𝒬 u) := by
      rw [show (16 : ℝ) = 2 * 8 by norm_num, mul_assoc, mul_assoc]; gcongr; apply cdist_le
      exact (mem_ball'.mp hx).trans_le (by rw [← mul_assoc]; gcongr; norm_num)
    _ ≤ 2 ^ (-k) * defaultA a * (defaultA a ^ 5 * dist_(p) (Q y) (𝒬 u)) := by
      gcongr; rw [show 8 * (D : ℝ) ^ 𝔰 p = 2 ^ 5 * (D ^ 𝔰 p / 4) by ring]
      exact cdist_le_iterate (by positivity) ..
    _ = 2 ^ (6 * a) * 2 ^ (-k) * dist_(p) (Q y) (𝒬 u) := by
      simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, mul_assoc _ _ (_ ^ 5)]
      rw [← pow_succ', ← pow_mul', mul_comm (2 ^ _)]
    _ ≤ 5 * 2 ^ (6 * a) * 2 ^ (-k) := by
      rw [mul_rotate 5]; gcongr
      calc
        _ ≤ dist_(p) (Q y) (𝒬 p) + dist_(p) (𝒬 p) (𝒬 u) := dist_triangle ..
        _ ≤ 1 + 4 := by
          gcongr <;> apply le_of_lt
          · rw [← mem_ball]; exact subset_cball my.2.1
          · rw [← mem_ball']; convert (t.smul_four_le hu hp).2 (mem_ball_self zero_lt_one)
        _ = _ := by norm_num
    _ ≤ 2 * 5 * 2 ^ (6 * a) * (dist x x' / (10 * D ^ 𝔰 p)) ^ (a : ℝ)⁻¹ := by
      rw [mul_rotate 2, mul_assoc _ 2]; gcongr
      calc
        _ ≤ (2 : ℝ) ^ (1 - Real.logb 2 (10 * D ^ 𝔰 p / dist x x') / a) := by
          rw [← Real.rpow_intCast]; apply Real.rpow_le_rpow_of_exponent_le one_le_two
          simp_rw [Int.cast_neg, k, neg_le_sub_iff_le_add']
          exact (Int.lt_floor_add_one _).le
        _ = _ := by
          rw [sub_eq_add_neg, Real.rpow_add zero_lt_two, Real.rpow_one, div_eq_mul_inv, ← neg_mul,
            Real.rpow_mul zero_le_two, ← Real.logb_inv, inv_div,
            Real.rpow_logb zero_lt_two one_lt_two.ne' (by positivity)]
    _ ≤ _ := by
      rw [show (2 : ℝ) * 5 = 10 by norm_num, Q7_5_5, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_ofNat, NNReal.coe_ofNat]; gcongr
      nth_rw 1 [← one_mul (_ ^ _)]; gcongr; norm_num

lemma QQQQ_bound {y : X} (my : y ∈ E p) (hu : u ∈ t) (hp : p ∈ t u)
    (hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) (hx' : x' ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖-Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ ≤ Q7_5_5 a * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  calc
    _ ≤ ‖Q7_5_5 a * (dist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹‖ₑ := by
      rw [← enorm_norm]
      apply Real.enorm_le_enorm (norm_nonneg _) (QQQQ_bound_real my hu hp hx hx')
    _ = _ := by
      rw [enorm_mul, Real.enorm_rpow_of_nonneg (by positivity) (by norm_cast; positivity),
        NNReal.enorm_eq, div_eq_mul_inv, enorm_mul, enorm_inv (by unfold defaultD; positivity),
        ← div_eq_mul_inv]; congr
      · rw [Real.enorm_eq_ofReal dist_nonneg, dist_nndist]; exact ENNReal.ofReal_coe_nnreal
      · rw [Real.enorm_eq_ofReal (by positivity), ← Real.rpow_intCast,
          ← ENNReal.ofReal_rpow_of_pos (by simp), ENNReal.rpow_intCast]; norm_cast

lemma holder_correlation_tile_two (hu : u ∈ t) (hp : p ∈ t u) (hf : BoundedCompactSupport f)
    (hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) (hx' : x' ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    edist (exp (.I * 𝒬 u x) * adjointCarleson p f x) (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
      (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖₊ := by
  calc
    _ ≤ (∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x‖ₑ * ‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ) +
        ∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x - Ks (𝔰 p) y x'‖ₑ := holder_correlation_rearrange hf
    _ ≤ (∫⁻ y in E p, ‖f y‖ₑ *
          (C2_1_3 a / volume (ball y (D ^ 𝔰 p))) *
            (Q7_5_5 a * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹)) +
        ∫⁻ y in E p, ‖f y‖ₑ *
          (D2_1_3 a / volume (ball y (D ^ 𝔰 p)) * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹) := by
      refine add_le_add (setLIntegral_mono' measurableSet_E fun y my ↦ ?_)
        (lintegral_mono fun _ ↦ ?_)
      · exact mul_le_mul' (mul_le_mul_left' nnnorm_Ks_le _) (QQQQ_bound my hu hp hx hx')
      · gcongr; exact nnnorm_Ks_sub_Ks_le
    _ = (C2_1_3 a * Q7_5_5 a + D2_1_3 a) * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ *
        ∫⁻ y in E p, ‖f y‖ₑ / volume (ball y (D ^ 𝔰 p)) := by
      conv_lhs =>
        enter [1, 2, y]
        rw [← mul_div_assoc, mul_comm ‖f y‖ₑ, mul_div_assoc, ← mul_rotate]
      have nt₀ : (nndist x x' / (D : ℝ≥0∞) ^ 𝔰 p) ^ (a : ℝ)⁻¹ < ⊤ := by
        apply ENNReal.rpow_lt_top_of_nonneg (by positivity); rw [← lt_top_iff_ne_top]
        exact ENNReal.div_lt_top ENNReal.coe_ne_top (ENNReal.zpow_pos (by simp) (by simp) _).ne'
      have nt₁ : Q7_5_5 a * (nndist x x' / (D : ℝ≥0∞) ^ 𝔰 p) ^ (a : ℝ)⁻¹ * C2_1_3 a ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) nt₀.ne) (by simp)
      rw [lintegral_const_mul' _ _ nt₁]
      conv_lhs =>
        enter [2, 2, y]
        rw [← mul_assoc, ← mul_div_assoc, mul_comm ‖f y‖ₑ, mul_div_assoc, ← mul_rotate]
      have nt₂ : (nndist x x' / (D : ℝ≥0∞) ^ 𝔰 p) ^ (a : ℝ)⁻¹ * D2_1_3 a ≠ ⊤ :=
        ENNReal.mul_ne_top nt₀.ne (by simp)
      rw [lintegral_const_mul' _ _ nt₂, ← add_mul]; congr 1
      rw [← mul_rotate, mul_comm _ (D2_1_3 a : ℝ≥0∞), ← add_mul]
    _ ≤ (C2_1_3 a * Q7_5_5 a + D2_1_3 a) * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ *
        ∫⁻ y in E p, ‖f y‖ₑ / (volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a)) := by
      refine mul_le_mul_left' (setLIntegral_mono' measurableSet_E fun y my ↦ ?_) _
      exact ENNReal.div_le_div_left (volume_xDsp_bound (E_subset_𝓘 my)) _
    _ = 2 ^ (3 * a) * (C2_1_3 a * Q7_5_5 a + D2_1_3 a) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
        (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
      conv_lhs =>
        enter [2, 2, y]
        rw [ENNReal.div_eq_inv_mul]
      rw [lintegral_const_mul _ hf.stronglyMeasurable.measurable.enorm, ← mul_assoc]; congr 1
      rw [ENNReal.inv_div (by simp) (by simp), ← mul_rotate, ENNReal.mul_div_right_comm]; congr
      exact coe_nnreal_ennreal_nndist ..
    _ ≤ _ := by
      gcongr; rw [C2_1_3, D2_1_3, C7_5_5, Q7_5_5]; norm_cast
      simp_rw [NNReal.rpow_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ ≤ (2 : ℝ≥0) ^ (3 * a) *
            (2 ^ (102 * a ^ 3) * (2 ^ 4 * 2 ^ (6 * a)) + 2 ^ (150 * a ^ 3)) := by gcongr; norm_num
        _ ≤ (2 : ℝ≥0) ^ (3 * a) * (2 ^ (150 * a ^ 3) + 2 ^ (150 * a ^ 3)) := by
          gcongr; rw [← pow_add, ← pow_add]; apply pow_le_pow_right' one_le_two
          calc
            _ = 102 * a ^ 3 + 4 * 1 * 1 * 1 + 6 * a * 1 * 1 := by ring
            _ ≤ 102 * a ^ 3 + 4 * a * a * a + 6 * a * a * a := by gcongr <;> linarith [four_le_a X]
            _ = 112 * a ^ 3 := by ring
            _ ≤ _ := by gcongr; norm_num
        _ = (2 : ℝ≥0) ^ (150 * a ^ 3 + (3 * a + 1)) := by
          rw [← two_mul, ← pow_succ', ← pow_add]; ring
        _ ≤ _ := by
          apply pow_le_pow_right' one_le_two
          rw [show 151 * a ^ 3 = 150 * a ^ 3 + a ^ 3 by ring]; gcongr
          calc
            _ = 3 * a * 1 + 1 * 1 * 1 := by ring
            _ ≤ 3 * a * a + 1 * a * a := by gcongr <;> linarith [four_le_a X]
            _ = 4 * a * a := by ring
            _ ≤ _ := by rw [pow_succ, sq]; gcongr; exact four_le_a X

end BothIn

/-- Lemma 7.5.5. -/
lemma holder_correlation_tile (hu : u ∈ t) (hp : p ∈ t u) (hf : BoundedCompactSupport f) :
    edist (exp (.I * 𝒬 u x) * adjointCarleson p f x) (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
      (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖₊ := by
  by_cases hxx : x ∉ ball (𝔠 p) (5 * D ^ 𝔰 p) ∧ x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)
  · rw [adjoint_tile_support1, indicator_of_not_mem hxx.1, indicator_of_not_mem hxx.2]; simp
  rw [not_and_or, not_not_mem, not_not_mem] at hxx
  wlog hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p) generalizing x x'
  · rw [or_comm] at hxx; specialize this hxx (hxx.resolve_right hx)
    rwa [edist_comm, edist_comm x' x] at this
  clear hxx
  by_cases hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)
  · nth_rw 2 [adjoint_tile_support1]
    rw [indicator_of_not_mem hx', mul_zero, edist_zero_right, enorm_mul, mul_comm I, ← enorm_norm,
      norm_exp_ofReal_mul_I, enorm_one, one_mul]
    exact holder_correlation_tile_one hf hx'
  push_neg at hx'
  exact holder_correlation_tile_two hu hp hf hx hx'

/-- Part of Lemma 7.5.6. -/
lemma limited_scale_impact__first_estimate (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) : s J ≤ 𝔰 p := by
  by_contra! contr
  apply Int.not_le.mpr contr
  apply Int.sub_one_lt_iff.mp
  apply Int.sub_lt_of_sub_lt
  rify
  apply lt_of_le_of_lt (hbc := calculation_logD_64 (X := X))
  apply tsub_le_iff_left.mpr
  have DIsOne := one_lt_D (X := X)
  rw [
    ← Real.logb_rpow (b := D) (x := 𝔰 p) (by positivity) (by linarith),
    ← Real.logb_mul (by positivity) (by positivity),
    ← Real.logb_rpow (b := D) (x := s J) (by positivity) (by linarith)
  ]
  apply (Real.logb_le_logb DIsOne (by positivity) (by positivity)).mpr
  have bigger : D ^ (s J) / 8 + 8 * D ^ (𝔰 p) ≥ D ^ s J / (4 : ℝ) := by
    rw [not_disjoint_iff] at h
    rcases h with ⟨middleX, h1, h2⟩
    calc (D ^ s J / (4 : ℝ))
    _ ≤ dist (c J) (𝔠 p) := by
      apply IF_disjoint_with_ball_THEN_distance_bigger_than_radius (p := 𝔠 p) (belongs := Grid.c_mem_Grid)
      have inter_1 : (J : Set X) ∩ ball (c J) (D ^ s J / 4) = ball (c J) (D ^ s J / 4) := inter_eq_self_of_subset_right ball_subset_Grid
      have inter_2 : (𝓘 u₁ : Set X) ∩ J = J := inter_eq_self_of_subset_right hJ.2.1
      rw [← inter_1, ← inter_2]
      apply Disjoint.inter_left
      apply Disjoint.inter_left
      rw [disjoint_comm]
      by_contra notDisjoint
      apply hp.2
      apply overlap_implies_distance hu₁ hu₂ hu h2u (hpu₁ := notDisjoint)
      right
      exact hp.1
    _ ≤ dist (𝔠 p) middleX + dist middleX (c J) := by
      rw [dist_comm]
      exact dist_triangle ..
    _ ≤ 8 * D ^ (𝔰 p) + dist middleX (c J) := by
      gcongr
      rw [mem_ball, dist_comm] at h1
      exact le_of_lt h1
    _ ≤ D ^ (s J) / 8 + 8 * D ^ (𝔰 p) := by
      rw [add_comm]
      gcongr
      rw [mem_ball, ← div_eq_inv_mul] at h2
      exact le_of_lt h2
  apply le_neg_add_iff_le.mp
  have := mul_le_mul_of_nonneg_left (a := 8) (sub_nonneg_of_le bigger) (by positivity)
  ring_nf at this
  norm_cast

/-- Part of Lemma 7.5.6. -/
lemma limited_scale_impact__second_estimate (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ≤ s J + 3 := by
  by_contra! three
  have ⟨J', belongs, plusOne⟩ : ∃ J', J ≤ J' ∧ s J' = s J + 1 :=
    Grid.exists_scale_succ (by change s J < 𝔰 p; linarith)
  have ⟨p', ⟨_, distance⟩, hundred⟩ : ∃ p' ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p') ⊆ ball (c J') (100 * D ^ (s J + 2)) := by
    rw [← one_add_one_eq_two, ← add_assoc, ← plusOne]
    have J'Touches𝔖₀ : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ (le := belongs) (sle := by linarith [plusOne]) (A_in := hJ.1)
    rw [𝓙₀, Set.nmem_setOf_iff] at J'Touches𝔖₀
    push_neg at J'Touches𝔖₀
    exact J'Touches𝔖₀.right
  apply calculation_9 (X := X)
  apply one_le_of_le_mul_right₀ (b := 2 ^ ((Z : ℝ) * n / 2)) (by positivity)
  have DIsPos := defaultD_pos a
  calc 2 ^ ((Z : ℝ) * (n : ℝ) / 2)
    _ ≤ dist_{𝓘 p'} (𝒬 u₁) (𝒬 u₂) := by
      exact distance
    _ ≤ dist_{c J', 100 * D ^ (s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      apply cdist_mono
      intros x hx
      exact hundred (ball_subset_Grid hx)
    _ ≤ 2 ^ ((-100 : ℝ) * a) * dist_{c J', 100 * D^(s J + 3)} (𝒬 u₁) (𝒬 u₂) := by
      apply calculation_8 (X := X)
      rw [mul_comm, calculation_6 (s J) (X := X), calculation_7 (s J) (X := X)]
      exact_mod_cast le_cdist_iterate (k := 100 * a) (f := 𝒬 u₁) (g := 𝒬 u₂) (hr := by positivity)
    _ ≤ 2 ^ ((-100 : ℝ) * a) * dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂) := by
      gcongr
      apply cdist_mono
      simp only [not_disjoint_iff] at h
      rcases h with ⟨middleX, lt_2, lt_3⟩
      have lt_4 := IF_subset_THEN_distance_between_centers belongs.left
      intros x lt_1
      calc dist x (𝔠 p)
      _ ≤ dist x (c J') + dist (c J') (c J) + dist (c J) middleX + dist middleX (𝔠 p) := by
        exact dist_triangle5 x (c J') (c J) middleX (𝔠 p)
      _ < 10 * D ^ 𝔰 p := by
        simp only [mem_ball] at lt_3
        rw [dist_comm] at lt_3 lt_4
        exact calculation_4 (lt_1 := lt_1) (lt_2 := lt_2) (lt_3 := lt_3) (lt_4 := lt_4) (three := three) (plusOne := plusOne) (X := X)
    _ ≤ 2 ^ ((-94 : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂) := by
      apply calculation_5
      have bigger : 0 < (D : ℝ) ^ 𝔰 p / 4 := by positivity
      calc dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂)
      _ ≤ dist_{𝔠 p, 2 ^ 6 * (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
        apply cdist_mono
        apply ball_subset_ball
        ring_nf
        linarith
      _ ≤ (2 ^ (a : ℝ)) ^ (6 : ℝ) * dist_{𝔠 p, (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
        exact_mod_cast cdist_le_iterate (f := (𝒬 u₁)) (g := (𝒬 u₂)) (r := (D ^ (𝔰 p)) / 4) (k := 6) (x := 𝔠 p) bigger
    _ ≤ 2^((-94 : ℝ) * a) * 2^((Z : ℝ) * n / 2) := by
      rcases hp with ⟨tile, notIn𝔖₀⟩
      unfold 𝔖₀ at notIn𝔖₀
      simp only [mem_setOf_eq, not_or, not_and, sep_union, mem_union] at notIn𝔖₀
      gcongr
      apply le_of_not_ge
      exact notIn𝔖₀.2 tile

/-- Lemma 7.5.6. -/
lemma limited_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ∈ Icc (s J) (s J + 3) :=
  ⟨limited_scale_impact__first_estimate hu₁ hu₂ hu h2u hp hJ h,
    limited_scale_impact__second_estimate hp hJ h⟩

lemma local_tree_control_sumsumsup (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    ∑ k ∈ Finset.Icc (s J) (s J + 3),
    ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
      ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
  calc
    _ = ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖ₑ := by
      rw [ENNReal.coe_biSup]; · rfl
      simp_rw [bddAbove_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      have bcs := hf.adjointCarlesonSum (ℭ := t u₂ \ 𝔖₀ t u₁ u₂)
      obtain ⟨C, hC⟩ := isBounded_range_iff_forall_norm_le.mp bcs.isBounded
      use ⟨C, (norm_nonneg _).trans (hC (c J))⟩; exact hC
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset, ‖adjointCarleson p f x‖ₑ := by
      apply iSup₂_mono fun x mx ↦ ?_
      simp_rw [enorm_eq_nnnorm, ← ENNReal.coe_finset_sum, ENNReal.coe_le_coe, adjointCarlesonSum,
        filter_mem_univ_eq_toFinset]
      exact nnnorm_sum_le ..
    _ = ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset,
          (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (fun y ↦ ‖adjointCarleson p f y‖ₑ) x := by
      congr! 5 with x mx p mp
      nth_rw 1 [adjoint_tile_support1, ← adjoint_eq_adjoint_indicator E_subset_𝓘,
        enorm_indicator_eq_indicator_enorm]
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (fun p ↦ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))),
            ‖adjointCarleson p f x‖ₑ := by
      apply iSup₂_mono fun x mx ↦ ?_
      rw [Finset.sum_indicator_eq_sum_filter]
      apply Finset.sum_le_sum_of_subset fun p mp ↦ ?_
      rw [Finset.mem_filter] at mp ⊢
      exact ⟨mp.1, not_disjoint_iff.mpr ⟨_, (ball_subset_ball (by gcongr; norm_num)) mp.2, mx⟩⟩
    _ ≤ ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (fun p ↦ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))),
        ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
      ENNReal.biSup_finsetSum_le_finsetSum_biSup
    _ = ∑ k ∈ Finset.Icc (s J) (s J + 3), ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (fun p ↦ 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))),
            ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ := by
      conv_rhs => enter [2, p, 1]; rw [← Finset.filter_filter, Finset.filter_comm]
      refine (Finset.sum_fiberwise_of_maps_to (fun p mp ↦ ?_) _).symm
      rw [Finset.mem_filter, mem_toFinset] at mp
      simpa only [Finset.mem_Icc] using limited_scale_impact hu₁ hu₂ hu h2u mp.1 hJ mp.2
    _ ≤ _ := by gcongr; exact Finset.subset_univ _

lemma local_tree_control_sup_bound {k : ℤ} (mk : k ∈ Finset.Icc (s J) (s J + 3))
    (mp : 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * ↑D ^ 𝔰 p)) (ball (c J) (8⁻¹ * ↑D ^ s J)))
    (nfm : Measurable fun x ↦ ‖f x‖ₑ) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ ≤
    2 ^ (103 * a ^ 3) * (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in E p, ‖f x‖₊ :=
  calc
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * ↑D ^ s J),
        ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y‖ₑ :=
      iSup₂_mono fun x mx ↦ enorm_integral_le_lintegral_enorm _
    _ = ⨆ x ∈ ball (c J) (8⁻¹ * ↑D ^ s J), ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr! with x mx y
      rw [enorm_mul, enorm_mul, enorm_eq_nnnorm, RCLike.nnnorm_conj]
      nth_rw 1 [← enorm_norm, norm_exp_I_mul_sub_ofReal, enorm_one, mul_one, ← enorm_eq_nnnorm]
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * ↑D ^ s J), ∫⁻ y in E p,
        C2_1_3 a / volume (ball y (D ^ 𝔰 p)) * ‖f y‖ₑ := by gcongr; exact nnnorm_Ks_le
    _ = ∫⁻ x in E p, C2_1_3 a / volume (ball x (D ^ 𝔰 p)) * ‖f x‖ₑ := by
      have := one_le_D (a := a)
      exact biSup_const (nonempty_ball.mpr (by positivity))
    _ ≤ ∫⁻ x in E p,
        C2_1_3 a / (volume (ball (c J) (16 * D ^ 𝔰 p)) / 2 ^ (5 * a)) * ‖f x‖ₑ := by
      apply setLIntegral_mono (nfm.const_mul _) fun x mx ↦ ?_
      gcongr
      have dpJ : dist (c J) (𝔠 p) < (8⁻¹ + 8) * D ^ 𝔰 p := by
        obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp mp.2
        rw [mem_ball] at my₁ my₂
        calc
          _ ≤ dist y (c J) + dist y (𝔠 p) := dist_triangle_left ..
          _ < 8⁻¹ * D ^ s J + 8 * D ^ 𝔰 p := by gcongr
          _ ≤ _ := by
            rw [Finset.mem_Icc, ← mp.1] at mk; rw [add_mul]; gcongr; exacts [one_le_D, mk.1]
      have inc : ball (c J) (16 * D ^ 𝔰 p) ⊆ ball x (32 * D ^ 𝔰 p) := fun y my ↦ by
        rw [mem_ball] at my ⊢
        calc
          _ ≤ dist y (c J) + dist (c J) (𝔠 p) + dist (𝔠 p) x := dist_triangle4 ..
          _ < 16 * D ^ (𝔰 p) + (8⁻¹ + 8) * D ^ (𝔰 p) + 4 * D ^ (𝔰 p) := by
            gcongr; rw [dist_comm, ← mem_ball]; exact Grid_subset_ball mx.1
          _ ≤ _ := by rw [← add_mul, ← add_mul]; gcongr; norm_num
      have dbl := measure_ball_le_pow_two' (μ := volume) (x := x) (r := D ^ 𝔰 p) (n := 5)
      simp_rw [show (2 : ℝ) ^ 5 = 32 by norm_num, defaultA, ← ENNReal.coe_pow,
        Nat.cast_pow, Nat.cast_ofNat, ← pow_mul', ENNReal.coe_pow, ENNReal.coe_ofNat] at dbl
      exact ENNReal.div_le_of_le_mul' ((measure_mono inc).trans dbl)
    _ ≤ _ := by
      rw [lintegral_const_mul _ nfm]; gcongr
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (by left; norm_num) (by left; positivity),
        ← ENNReal.mul_div_right_comm, mp.1, ENNReal.div_eq_inv_mul, mul_comm]
      gcongr; unfold C2_1_3; norm_cast
      simp_rw [NNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
      refine pow_le_pow_right' one_le_two ?_
      rw [show 103 * a ^ 3 = a * a * a + 102 * a ^ 3 by ring]; gcongr; nlinarith [four_le_a X]

/-- The constant used in `local_tree_control`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_7 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.5.7. -/
lemma local_tree_control (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    C7_5_7 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc (s J) (s J + 3),
        ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
          ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
      local_tree_control_sumsumsup hu₁ hu₂ hu h2u hJ hf
    _ ≤ ∑ k ∈ Finset.Icc (s J) (s J + 3),
        ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
          2 ^ (103 * a ^ 3) * (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in E p, ‖f x‖₊ := by
      gcongr with k mk p mp
      simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mp
      exact local_tree_control_sup_bound mk mp hf.stronglyMeasurable.measurable.enorm
    _ = 2 ^ (103 * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ *
          ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
            ∫⁻ x in E p, ‖f x‖₊ := by
      simp_rw [Finset.mul_sum, mul_assoc]
    _ = 2 ^ (103 * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in ⋃ p ∈ Finset.univ.filter (fun p ↦ 𝔰 p = k ∧
          ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))), E p, ‖f x‖₊ := by
      congr! with k mk
      refine (lintegral_biUnion_finset ?_ (fun _ _ ↦ measurableSet_E) _).symm
      intro p mp q mq hn
      by_cases hi : 𝓘 p = 𝓘 q
      · by_contra h; rw [not_disjoint_iff] at h; obtain ⟨x, mx₁ : x ∈ E p, mx₂ : x ∈ E q⟩ := h
        apply absurd (disjoint_Ω hn hi); rw [not_disjoint_iff]; use Q x, mx₁.2.1, mx₂.2.1
      · apply disjoint_of_subset E_subset_𝓘 E_subset_𝓘
        simp_rw [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at mp mq
        have := eq_or_disjoint (mq.1 ▸ mp.1)
        exact this.resolve_left hi
    _ ≤ 2 ^ (103 * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in ball (c J) (16 * D ^ k), ‖f x‖₊ := by
      gcongr with k mk; refine lintegral_mono_set (iUnion₂_subset fun p mp ↦ ?_)
      simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mp
      refine (E_subset_𝓘.trans Grid_subset_ball).trans (ball_subset_ball' ?_)
      obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp mp.2
      rw [mem_ball] at my₁ my₂; change 4 * D ^ 𝔰 p + dist (𝔠 p) (c J) ≤ _
      calc
        _ ≤ 4 * D ^ 𝔰 p + (dist y (𝔠 p) + dist y (c J)) := by gcongr; exact dist_triangle_left ..
        _ ≤ 4 * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 8⁻¹ * D ^ s J := by rw [add_assoc]; gcongr
        _ ≤ (4 + 8 + 8⁻¹) * D ^ k := by
          rw [Finset.mem_Icc] at mk; simp_rw [add_mul, mp.1]; gcongr; exacts [one_le_D, mk.1]
        _ ≤ _ := by gcongr; norm_num
    _ = 2 ^ (103 * a ^ 3) *
        ∑ k ∈ Finset.Icc (s J) (s J + 3), ⨍⁻ x in ball (c J) (16 * D ^ k), ‖f x‖₊ ∂volume := by
      simp_rw [setLaverage_eq, ENNReal.div_eq_inv_mul]
    _ ≤ 2 ^ (103 * a ^ 3) *
        ∑ k ∈ Finset.Icc (s J) (s J + 3), ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      gcongr with k mk; rw [Finset.mem_Icc] at mk
      simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one, le_iInf_iff]
      intro y my
      obtain ⟨b, mb, eb⟩ : ∃ i ∈ 𝓑, ball (c𝓑 i) (r𝓑 i) = ball (c J) (16 * D ^ k) := by
        use ⟨4, (k - s J).toNat, J⟩
        simp only [𝓑, c𝓑, r𝓑, mem_prod, mem_Iic, mem_univ, le_add_iff_nonneg_left, zero_le,
          and_true, true_and]
        rw [show s J + (k - s J).toNat = k by omega, Int.toNat_le, 𝓑max, Nat.cast_ofNat]
        exact ⟨by omega, by norm_num⟩
      replace my : y ∈ ball (c𝓑 b) (r𝓑 b) := by
        rw [eb]; refine Grid_subset_ball.trans (ball_subset_ball ?_) my
        calc
          (4 : ℝ) * D ^ s J ≤ 16 * D ^ s J := by gcongr; norm_num
          _ ≤ _ := by gcongr; exacts [one_le_D, mk.1]
      exact le_iSup₂_of_le b mb (by rw [indicator_of_mem my, eb])
    _ = 2 ^ (103 * a ^ 3) * 2 ^ 2 * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      rw [Finset.sum_const, Int.card_Icc, show s J + 3 + 1 - s J = 4 by omega, nsmul_eq_mul,
        show (Int.toNat 4 : ℝ≥0∞) = 2 ^ 2 by simp; norm_num, mul_assoc]
    _ ≤ _ := by
      gcongr; rw [C7_5_7, ← pow_add]; norm_cast
      refine pow_le_pow_right' one_le_two ?_
      rw [show 104 * a ^ 3 = 103 * a ^ 3 + a * a * a by ring]; gcongr; nlinarith [four_le_a X]

/-- Lemma 7.5.8. -/
lemma scales_impacting_interval (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hp : p ∈ t u₁ ∪ (t u₂ ∩ 𝔖₀ t u₁ u₂))
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) : s J ≤ 𝔰 p := by
  rcases hJ with ⟨hJLeft, _⟩
  apply 𝓙_subset_𝓙₀ at hJLeft
  apply Set.mem_or_mem_of_mem_union at hp
  have belongs : p ∈ t.𝔖₀ u₁ u₂ := by
    cases hp with
    | inl h1 => exact 𝔗_subset_𝔖₀ hu₁ hu₂ hu h2u h1
    | inr h2 => exact Set.mem_of_mem_inter_right h2
  cases hJLeft with
  | inl scaleVerySmall =>
    exact trans scaleVerySmall (scale_mem_Icc.left)
  | inr noGridInBall =>
    have pGridIsNotInBall := noGridInBall p belongs
    rw [not_subset] at pGridIsNotInBall
    rcases pGridIsNotInBall with ⟨x, ⟨xInTile, xIsNotInBall⟩⟩
    rw [Metric.mem_ball'] at xIsNotInBall
    by_contra! contr
    apply xIsNotInBall
    simp only [not_disjoint_iff] at h
    rcases h with ⟨middleX, xxx, yyy⟩
    calc dist (c J) x
    _ = dist (x) (c J) := by
      apply dist_comm
    _ ≤ dist (x) (𝔠 p) + dist (𝔠 p) (c J) := dist_triangle ..
    _ < dist (x) (𝔠 p) + 16 * D ^ s J := by
      gcongr
      calc dist (𝔠 p) (c J)
        _ ≤ dist middleX (𝔠 p) + dist middleX (c J) := by
          nth_rw 2 [dist_comm]
          apply dist_triangle
        _ < 8 * D ^ 𝔰 p + 8 * D ^ s J := by
          exact add_lt_add xxx yyy
        _ = 8 * D ^ s J + 8 * D ^ 𝔰 p := by
          rw [add_comm]
        _ < 8 * D ^ (s J) + 8 * D ^ (s J) := by
          gcongr
          exact one_lt_D (X := X)
        _ = 16 * D ^ s J := by
          linarith
    _ < 4 * D ^ 𝔰 p + 16 * D ^ s J := by
      gcongr
      rw [dist_comm]
      apply Metric.mem_ball'.mp
      apply Grid_subset_ball (X := X) (i := 𝓘 p)
      exact xInTile
    _ < 100 * D ^ (s J + 1) := by
      apply (div_lt_div_iff_of_pos_right zero_lt_four).mp
      ring_nf
      rewrite (config := {occs := .pos [1]}) [add_comm]
      apply lt_tsub_iff_left.mp
      have DIsPos := one_lt_D (X := X)
      calc (D : ℝ) ^ 𝔰 p
        _ < D ^ (s J) := by gcongr; exact DIsPos
        _ < D ^ (s J) * (25 * D - 4) := by
          rewrite (config := {occs := .pos [1]}) [mul_comm]
          apply lt_mul_left
          · positivity
          · linarith
        _ = (D ^ (s J) * D) * 25 - D ^ (s J) * 4 := by ring
        _ = D ^ ((s J) + 1) * 25 - D ^ (s J) * 4 := by
          rw [zpow_add_one₀ (by positivity)]
        _ = D ^ (1 + (s J)) * 25 - D ^ (s J) * 4 := by ring_nf

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
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊) +
    C7_5_9_1 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- Part 2 of Lemma 7.5.9 -/
lemma global_tree_control1_2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f)
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
    (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖₊) +
    C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  calc
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖₊ ≤ (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖₊) + (C7_5_9_1 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x) := by
      exact global_tree_control1_1 (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u) (ℭ := t u₂ ∩ 𝔖₀ t u₁ u₂) (hℭ := by right; rfl) (hJ := hJ) (hf := hf)
    _ ≤ (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖₊) + (⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖₊) + C7_5_9_1 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
      sorry
    _ ≤ (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖₊) + C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
      rw [add_assoc]
      gcongr
      have ltc := local_tree_control (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u) (hJ := hJ) (hf := hf)
      apply add_le_of_add_le_right (hle := ltc)
      -- NOTE
      -- 
      -- rw [`right_distrib`] stopped working because the statement of `lemma local_tree_control` was changed.
      -- 
      -- The solution is to:
      -- 1. change the statement of `lemma global_tree_control1_1` (from `(fun x ↦ ‖f x‖) x` to `f x`)
      -- 2. change all expressions in this proof accordingly (from `(fun x ↦ ‖f x‖) x` to `f x`)
      -- 
      -- DETAILS
      -- The goal before the statement of `lemma local_tree_control` was changed:
      -- ⊢ (↑(C7_5_7 a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (fun x ↦ ‖f x‖) x) +
      -- ↑(C7_5_9_1 a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (fun x ↦ ‖f x‖) x ≤
      -- ↑(C7_5_10 a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (fun x ↦ ‖f x‖) x
      -- 
      -- The goal now:
      -- ⊢ (↑(C7_5_7 a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x) +
      -- ↑(C7_5_9_1 a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (fun x ↦ ‖f x‖) x ≤
      -- ↑(C7_5_10 a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (fun x ↦ ‖f x‖) x
      rw [← right_distrib, C7_5_7, C7_5_9_1, C7_5_10]
      gcongr
      norm_cast
      rw [
        show 2 ^ (104 * a ^ 3) = 2 ^ (104 * a ^ 3) * 1 by ring,
        show 2 ^ (155 * a ^ 3) = 2 ^ (104 * a ^ 3) * 2 ^ (51 * a ^ 3) by ring,
        show 2 ^ (154 * a ^ 3) = 2 ^ (104 * a ^ 3) * 2 ^ (50 * a ^ 3) by ring,
        show 2 ^ (104 * a ^ 3) * 1 + 2 ^ (104 * a ^ 3) * 2 ^ (50 * a ^ 3) = 2 ^ (104 * a ^ 3) * (1 + 2 ^ (50 * a ^ 3)) by ring
      ]
      gcongr
      have four : 4 ≤ a := four_le_a X
      refine Nat.one_add_le_iff.mpr ?_
      rw [Nat.pow_lt_pow_iff_right Nat.le.refl]
      gcongr
      linarith

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

end TileStructure.Forest
