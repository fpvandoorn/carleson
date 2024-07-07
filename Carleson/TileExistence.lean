import Carleson.TileStructure
import Carleson.DoublingMeasure

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate

namespace ShortVariables
set_option hygiene false
scoped notation "D'" => (Real.toNNReal D)

end ShortVariables

noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

-- this still holds for more general parameters
lemma ball_bound {Y : Set X} (k : ℝ) (hk_lower : -S ≤ k)
  (hY : Y ⊆ ball o (4*D^S-D^k)) (y : X) (hy : y ∈ Y) :
    ball o (4 * D ^ S) ⊆ ball y (8 * D^(2 * S) * D^k) := by
  calc
    ball o (4 * D ^ S)
      ⊆ ball y (2 * (4 * D ^ S)) := by
        rw [two_mul]
        refine ball_subset ?h
        simp only [add_sub_cancel_right]
        obtain hy' := hY hy
        rw [mem_ball,dist_comm] at hy'
        apply hy'.le.trans
        rw [tsub_le_iff_right, le_add_iff_nonneg_right]
        positivity
    _ = ball y (8 * D ^ S) := by congr! 1; ring
    _ ⊆ ball y (8 * D ^ (2 * S) * D ^ k) := by
        apply ball_subset_ball
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add (defaultD_pos a)]
        apply Real.rpow_le_rpow_of_exponent_le one_le_D
        rw [Nat.cast_mul, Nat.cast_two]
        linarith

-- lemma tsum_top_eq

variable (X) in def J' : ℕ := 3 + 2 * S * 100 * a ^ 2

lemma twopow_J : 2 ^ J' X = 8 * D ^ (2 * S) := by
  dsimp [J']
  rw [pow_add, mul_assoc (2 * S), mul_comm (2 * S), pow_mul]
  norm_num

lemma twopow_J' : 2 ^ J' X = 8 * nnD ^ (2 * S) := by
  dsimp only [_root_.nnD]
  ext
  push_cast
  rw_mod_cast [twopow_J]

variable (X) in
def C4_1_1 := As (2 ^ a) (2 ^ J' X)

lemma counting_balls (k : ℝ) (hk_lower : -S ≤ k) (Y : Set X) (hY : Y ⊆ ball o (4*D^S-D^k))
    (hYdisjoint: Y.PairwiseDisjoint (fun y ↦ ball y (D^k))) :
    (Set.encard Y).toENNReal ≤ C4_1_1 X := by
  suffices (Set.encard Y).toENNReal * volume (ball o (4 * D^S)) ≤ (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D^S)) by
    have volume_pos : 0 < volume (ball o (4 * D^S)) := by
      apply measure_ball_pos volume o
      simp only [defaultD, gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      refine zpow_pos_of_pos ?ha S
      positivity
    have volume_finite : volume (ball o (4 * D^S)) < ⊤ := measure_ball_lt_top
    rw [← ENNReal.mul_le_mul_left volume_pos.ne.symm volume_finite.ne, mul_comm,mul_comm (volume _)]
    exact this
  have val_ne_zero : (As (2 ^ a) (2 ^ J' X):ℝ≥0∞) ≠ 0 := by exact_mod_cast (As_pos' X (2 ^J' X)).ne.symm
  calc
    (Y.encard).toENNReal * volume (ball o (4 * D ^ S))
      = ∑' (y : Y), volume (ball o (4 * D^S)) := by rw [ENNReal.tsum_const_eq']
    _ ≤ ∑' (y : Y), volume (ball (y : X) (8 * D ^ (2 * S) * D^k)) := by
      apply tsum_le_tsum _ ENNReal.summable ENNReal.summable
      intro ⟨y,hy⟩
      apply volume.mono
      simp only
      exact ball_bound k hk_lower hY y hy
    _ ≤ ∑' (y : Y), (As (2 ^ a) (2 ^ J' X)) * volume (ball (y : X) (D^k)) := by
      apply tsum_le_tsum _ ENNReal.summable ENNReal.summable
      intro y hy
      rw_mod_cast [← twopow_J]
      apply volume_ball_le_same'
      · positivity
      · exact le_refl _
    _ ≤ (As (2 ^ a) (2 ^ J' X)) * ∑' (y : Y), volume (ball (y : X) (D^k)):= by
      rw [ENNReal.tsum_mul_left]
    _ = (As (2 ^ a) (2 ^ J' X)) * volume (⋃ y ∈ Y, ball y (D^k)) := by
      rw [ENNReal.mul_eq_mul_left val_ne_zero ENNReal.coe_ne_top]
      · rw [measure_biUnion _ hYdisjoint (fun y _ => measurableSet_ball)]
        apply hYdisjoint.countable_of_isOpen (fun y _ => isOpen_ball)
        intro y _
        use y
        rw [mem_ball, dist_self]
        exact Real.rpow_pos_of_pos (defaultD_pos a) _
    _ ≤ (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D ^ S)) := by
        rw [ENNReal.mul_le_mul_left val_ne_zero ENNReal.coe_ne_top]
        apply volume.mono _
        rw [iUnion₂_subset_iff]
        intro y hy z hz
        specialize hY hy
        simp only [mem_ball] at hY hz ⊢
        calc
          dist z o
            ≤ dist z y + dist y o := by exact dist_triangle z y o
          _ < D^k + (4 * D^S - D^k) := by exact add_lt_add hz hY
          _ = 4 * D ^ S := by rw [add_sub_cancel]

variable (X) in
def property_set (k : ℝ) : Set (Set X) :=
  {s| s ⊆ ball o (4 * D^S - D^k) ∧ s.PairwiseDisjoint (fun y => ball y (D^k))}

variable (X) in
lemma property_set_nonempty (k:ℝ ): ∅ ∈ property_set X k := by
  dsimp [property_set]
  simp only [empty_subset, pairwiseDisjoint_empty, and_self]

variable (X) in
lemma chain_property_set_has_bound (k : ℝ):
    ∀ c ⊆ property_set X k, IsChain (. ⊆ .) c → ∃ ub ∈ property_set X k,
    ∀ s ∈ c, s ⊆ ub := by
  intro c hc hchain
  use ⋃ s ∈ c,s
  dsimp only [property_set] at hc ⊢
  simp only [mem_setOf_eq, iUnion_subset_iff]
  constructor
  · constructor
    · intro i hi
      specialize hc hi
      rw [mem_setOf_eq] at hc
      exact hc.left
    · intro x hx y hy
      simp only [mem_iUnion, exists_prop] at hx hy
      obtain ⟨sx,hsx, hsx'⟩ := hx
      obtain ⟨sy,hsy, hsy'⟩ := hy
      obtain hxy|hyx := hchain.total hsx hsy
      · specialize hxy hsx'
        specialize hc hsy
        rw [mem_setOf_eq] at hc
        exact hc.right hxy hsy'
      · specialize hyx hsy'
        specialize hc hsx
        rw [mem_setOf_eq] at hc
        exact hc.right hsx' hyx
  · exact fun s a ↦ subset_iUnion₂_of_subset s a fun ⦃a⦄ a ↦ a

variable (X) in
def zorn_apply_maximal_set (k : ℝ):
    ∃ s ∈ property_set X k, ∀ s' ∈ property_set X k, s ⊆ s' → s' = s :=
  zorn_subset (property_set X k) (chain_property_set_has_bound X k)

variable (X) in
def Yk (k : ℝ): Set X := (zorn_apply_maximal_set X k).choose

lemma Yk_pairwise (k:ℝ) : (Yk X k).PairwiseDisjoint (fun (y:X) ↦ ball y (D^k)) :=
  (zorn_apply_maximal_set X k).choose_spec.left.right

lemma Yk_subset (k:ℝ) : Yk X k ⊆ ball o (4 * D^S - D^k) :=
  (zorn_apply_maximal_set X k).choose_spec.left.left

lemma Yk_maximal (k : ℝ) {s :Set X} (hs_sub : s ⊆ ball o (4 * D^S - D^k))
    (hs_pairwise : s.PairwiseDisjoint (fun y ↦ ball y (D^k))) (hmax_sub : Yk X k ⊆ s):
    s = Yk X k :=
  (zorn_apply_maximal_set X k).choose_spec.right _ (And.intro hs_sub hs_pairwise) hmax_sub

lemma cover_big_ball (k : ℝ) : ball o (4 * D^S - D^k) ⊆ ⋃ y ∈ Yk X k, ball y (2 * D^k) := by
  intro y hy
  have : ∃ z ∈ Yk X k, ¬Disjoint (ball y (D^k)) (ball z (D^k)) := by
    by_contra hcon
    apply hcon
    push_neg at hcon
    suffices hmem : y ∈ Yk X k by
      use y, hmem
      rw [disjoint_self, bot_eq_empty, ball_eq_empty, not_le]
      apply Real.rpow_pos_of_pos (defaultD_pos a) k
    suffices (Yk X k) ∪ {y} = Yk X k by
      rw [union_singleton, insert_eq_self] at this
      exact this
    apply Yk_maximal
    · rw [union_subset_iff]
      use Yk_subset k
      rw [singleton_subset_iff]
      exact hy
    · rw [pairwiseDisjoint_union]
      use Yk_pairwise k
      simp only [pairwiseDisjoint_singleton, true_and, mem_singleton_iff,forall_eq]
      exact fun z hz _ ↦ (hcon z hz).symm
    · exact subset_union_left
  obtain ⟨z,hz,hz'⟩ := this
  simp only [mem_iUnion, mem_ball, exists_prop]
  use z,hz
  rw [Set.not_disjoint_iff] at hz'
  obtain ⟨x,hx,hx'⟩ := hz'
  rw [mem_ball, dist_comm] at hx
  rw [two_mul]
  exact (dist_triangle y x z).trans_lt (add_lt_add hx hx')

/-! Proof that there exists a grid structure. -/
-- Note: we might want to slightly adapt the construction so that there is only 1 tile at level S
-- with center `o` (then we might not cover all of `ball o (D ^ S)`, but most of it)
def grid_existence : GridStructure X D κ S o :=
  sorry

/-! Proof that there exists a tile structure on a grid structure. -/

variable [GridStructure X D κ S o] {I : Grid X}

/-- Use Zorn's lemma to define this. -/
-- Note: 𝓩 I is a subset of finite set range Q.
def 𝓩 (I : Grid X) : Set (Θ X) := sorry

/-- The constant appearing in 4.2.2 (3 / 10). -/
@[simp] def C𝓩 : ℝ := 3 / 10

lemma 𝓩_subset : 𝓩 I ⊆ range Q := sorry
lemma 𝓩_disj {f g : Θ X} (hf : f ∈ 𝓩 I) (hg : g ∈ 𝓩 I) (hfg : f ≠ g) :
    Disjoint (ball_{I} f C𝓩) (ball_{I} g C𝓩) :=
  sorry

lemma 𝓩_disj' : (𝓩 I).PairwiseDisjoint (ball_{I} · C𝓩) := fun _ hf _ hg => 𝓩_disj hf hg

lemma 𝓩_finite : (𝓩 I).Finite := sorry
lemma card_𝓩_le :
    Nat.card (𝓩 I) ≤ (2 : ℝ) ^ (2 * a) * Nat.card (range (Q : X → Θ X)) := sorry

/-- Note: we might only need that `𝓩` is maximal, not that it has maximal cardinality.
So maybe we don't need this. -/
lemma maximal_𝓩_card {𝓩' : Set (Θ X)}
    (h𝓩' : 𝓩' ⊆ range Q)
    (h2𝓩' : ∀ {f g : Θ X} (hf : f ∈ 𝓩') (hg : g ∈ 𝓩') (hfg : f ≠ g),
      Disjoint (ball_{I} f C𝓩) (ball_{I} g C𝓩)) : Nat.card 𝓩' ≤ Nat.card (𝓩 I) := by
  sorry

lemma maximal_𝓩 {𝓩' : Set (Θ X)} (h𝓩' : 𝓩' ⊆ range Q)
    (h2𝓩' : ∀ {f g : Θ X} (hf : f ∈ 𝓩') (hg : g ∈ 𝓩') (hfg : f ≠ g),
      Disjoint (ball_{I} f C𝓩) (ball_{I} g C𝓩)) (h𝓩 : 𝓩 I ⊆ 𝓩') : 𝓩 I = 𝓩' := by
  sorry

instance : Fintype (𝓩 I) := sorry
instance : Inhabited (𝓩 I) := sorry

/-- 7 / 10 -/
@[simp] def C4_2_1 : ℝ := 7 / 10 /- 0.6 also works? -/

/-- Equation (4.2.3), Lemma 4.2.1 -/
lemma frequency_ball_cover : range Q ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 := by
  intro θ hθ
  have : ∃ z, z ∈ 𝓩 I ∧ ¬ Disjoint (ball_{I} z C𝓩) (ball_{I} θ C𝓩) := by
    by_contra! h
    have hθ' : θ ∉ 𝓩 I := by
      intro hθ'
      have := h _ hθ'
      simp only [C𝓩, disjoint_self, bot_eq_empty, ball_eq_empty] at this
      norm_num at this
    let 𝓩' := insert θ (𝓩 I)
    have h𝓩' : 𝓩' ⊆ range Q := by
      rw [insert_subset_iff]
      exact ⟨by simpa using hθ, 𝓩_subset⟩
    have h2𝓩' : 𝓩'.PairwiseDisjoint (ball_{I} · C𝓩) := by
      rw [pairwiseDisjoint_insert_of_not_mem hθ']
      exact ⟨𝓩_disj', fun j hj ↦ (h j hj).symm⟩
    have := maximal_𝓩 h𝓩' (fun hf hg => h2𝓩' hf hg)
    simp only [subset_insert, true_implies, 𝓩'] at this
    rw [eq_comm, insert_eq_self] at this
    exact hθ' this
  obtain ⟨z, hz, hz'⟩ := this
  rw [Set.not_disjoint_iff] at hz'
  obtain ⟨z', h₁z', h₂z'⟩ := hz'
  simp only [mem_iUnion, mem_ball, exists_prop, C𝓩, C4_2_1] at h₁z' h₂z' ⊢
  exact ⟨z, hz, by linarith
    [dist_triangle_left (α := (WithFunctionDistance (c I) (D ^ s I / 4))) θ z z']⟩

local instance tileData_existence [GridStructure X D κ S o] :
    PreTileStructure Q D κ S o where
  𝔓 := Σ I : Grid X, 𝓩 I
  fintype_𝔓 := Sigma.instFintype
  𝓘 p := p.1
  surjective_𝓘 I := ⟨⟨I, default⟩, rfl⟩
  𝒬 p := p.2
  range_𝒬 := by
    rintro _ ⟨p, rfl⟩
    exact 𝓩_subset p.2.2

namespace Construction

def Ω₁_aux (I : Grid X) (k : ℕ) : Set (Θ X) :=
  if hk : k < Nat.card (𝓩 I) then
    let z : Θ X := (Finite.equivFin (𝓩 I) |>.symm ⟨k, hk⟩).1
    ball_{I} z C4_2_1 \ (⋃ i ∈ 𝓩 I \ {z}, ball_{I} i C𝓩) \ ⋃ i < k, Ω₁_aux I i
  else ∅

lemma Ω₁_aux_disjoint (I : Grid X) {k l : ℕ} (hn : k ≠ l) : Disjoint (Ω₁_aux I k) (Ω₁_aux I l) := by
  wlog h : k < l generalizing k l
  · exact (this hn.symm (hn.symm.lt_of_le (Nat.le_of_not_lt h))).symm
  have : Ω₁_aux I k ⊆ ⋃ i < l, Ω₁_aux I i := subset_biUnion_of_mem h
  apply disjoint_of_subset_left this
  rw [Ω₁_aux]
  split_ifs
  · exact disjoint_sdiff_right
  · exact disjoint_empty _

lemma disjoint_ball_Ω₁_aux (I : Grid X) {z z' : Θ X} (hz : z ∈ 𝓩 I) (hz' : z' ∈ 𝓩 I) (hn : z ≠ z') :
    Disjoint (ball_{I} z' C𝓩) (Ω₁_aux I (Finite.equivFin (𝓩 I) ⟨z, hz⟩)) := by
  rw [Ω₁_aux]
  simp only [(Finite.equivFin (𝓩 I) ⟨z, hz⟩).2, dite_true, Fin.eta, Equiv.symm_apply_apply]
  rw [sdiff_sdiff_comm, ← disjoint_sdiff_comm, diff_eq_empty.mpr]
  · exact empty_disjoint _
  · apply subset_biUnion_of_mem (show z' ∈ 𝓩 I \ {z} by tauto)

def Ω₁ (p : 𝔓 X) : Set (Θ X) := Ω₁_aux p.1 (Finite.equivFin (𝓩 p.1) p.2)

/-- Lemma 4.2.2 -/
lemma disjoint_frequency_cubes {f g : 𝓩 I} (h : (Ω₁ ⟨I, f⟩ ∩ Ω₁ ⟨I, g⟩).Nonempty) : f = g := by
  simp_rw [← not_disjoint_iff_nonempty_inter, Ω₁] at h
  contrapose! h
  apply Ω₁_aux_disjoint
  contrapose! h
  rwa [Fin.val_eq_val, Equiv.apply_eq_iff_eq] at h

/-- Equation (4.2.6), first inclusion -/
lemma ball_subset_Ω₁ (p : 𝔓 X) : ball_(p) (𝒬 p) C𝓩 ⊆ Ω₁ p := by
  rw [Ω₁, Ω₁_aux]; set I := p.1; set z := p.2
  let k := (Finite.equivFin ↑(𝓩 I)) z
  simp_rw [Fin.eta, Equiv.symm_apply_apply, k.2, dite_true]
  change ball_{I} z.1 C𝓩 ⊆ _ \ ⋃ i < k.1, Ω₁_aux I i
  refine subset_diff.mpr ⟨subset_diff.mpr ⟨ball_subset_ball (by norm_num), ?_⟩, ?_⟩
  · rw [disjoint_iUnion₂_right]; intro i hi; rw [mem_diff_singleton] at hi
    exact 𝓩_disj z.coe_prop hi.1 hi.2.symm
  · rw [disjoint_iUnion₂_right]; intro i hi
    let z' := (Finite.equivFin ↑(𝓩 I)).symm ⟨i, by omega⟩
    have zn : z ≠ z' := by simp only [ne_eq, Equiv.eq_symm_apply, z']; exact Fin.ne_of_gt hi
    simpa [z'] using disjoint_ball_Ω₁_aux I z'.2 z.2 (Subtype.coe_ne_coe.mpr zn.symm)

/-- Equation (4.2.6), second inclusion -/
lemma Ω₁_subset_ball (p : 𝔓 X) : Ω₁ p ⊆ ball_(p) (𝒬 p) C4_2_1 := by
  rw [Ω₁, Ω₁_aux]
  split_ifs
  · let z : Θ X := p.2
    have qz : 𝒬 p = z := rfl
    have zeq : z = p.2 := rfl
    simp only [qz, zeq, Fin.eta, Equiv.symm_apply_apply, sdiff_sdiff, diff_subset]
  · exact empty_subset _

/-- Equation (4.2.5) -/
lemma iUnion_ball_subset_iUnion_Ω₁ : ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 ⊆ ⋃ f : 𝓩 I, Ω₁ ⟨I, f⟩ := by
  rw [iUnion₂_subset_iff]; intro z mz (ϑ : Θ X) mϑ
  let f := Finite.equivFin (𝓩 I)
  by_cases h : ∃ y ∈ 𝓩 I, ϑ ∈ ball_{I} y C𝓩
  · obtain ⟨z', mz', hz'⟩ := h
    exact mem_of_mem_of_subset (mem_of_mem_of_subset hz' (ball_subset_Ω₁ ⟨I, ⟨z', mz'⟩⟩))
      (subset_iUnion_of_subset _ subset_rfl)
  · let L := {k : Fin (Nat.card (𝓩 I)) | ϑ ∈ ball_{I} (f.symm k).1 C4_2_1}
    have Ln : L.Nonempty := by use f ⟨z, mz⟩; rwa [mem_setOf, Equiv.symm_apply_apply]
    obtain ⟨k, mem_k, hk⟩ := L.exists_min_image id L.toFinite Ln
    simp_rw [L, mem_setOf_eq] at mem_k
    simp only [id_eq] at hk
    have q : ∀ i < k, ϑ ∉ Ω₁_aux I i := by
      by_contra! h; obtain ⟨i, li, hi⟩ := h
      have := Ω₁_subset_ball ⟨I, f.symm i⟩
      simp_rw [Ω₁, Equiv.apply_symm_apply] at this
      replace this : ϑ ∈ ball_{I} (f.symm i).1 C4_2_1 := mem_of_mem_of_subset hi this
      replace this : i ∈ L := by simp only [L, mem_setOf_eq, this]
      exact absurd (hk i this) (not_le.mpr li)
    rw [mem_iUnion]; use f.symm k; rw [Ω₁, Ω₁_aux]; dsimp only
    rw [Equiv.apply_symm_apply]; simp_rw [k.2]; rw [dite_true, mem_diff, mem_diff]
    refine ⟨⟨mem_k, ?_⟩, ?_⟩
    · rw [mem_iUnion₂]; push_neg at h ⊢; exact fun i mi ↦ h i (mem_of_mem_diff mi)
    · rw [mem_iUnion₂]; push_neg; exact fun i mi ↦ q ⟨i, mi.trans k.2⟩ mi

/-- 1 / 5 -/
@[simp] def CΩ : ℝ := 1 / 5

open Classical in
def Ω (p : 𝔓 X) : Set (Θ X) :=
  if h : IsMax p.1 then Ω₁ p else
  have := Grid.opSize_succ_lt h
  ball_(p) (𝒬 p) CΩ ∪ ⋃ (z : Θ X) (hz : z ∈ 𝓩 p.1.succ ∩ Ω₁ p), Ω ⟨p.1.succ, ⟨z, hz.1⟩⟩
termination_by p.1.opSize

lemma 𝔓_induction (P : 𝔓 X → Prop) (base : ∀ p, IsMax p.1 → P p)
    (ind : ∀ p, ¬IsMax p.1 → (∀ z : 𝓩 p.1.succ, P ⟨p.1.succ, z⟩) → P p) :
    ∀ p, P p := fun p ↦ by
  by_cases h : IsMax p.1
  · exact base p h
  · have := Grid.opSize_succ_lt h
    exact ind p h fun z ↦ (𝔓_induction P base ind ⟨p.1.succ, z⟩)
termination_by p => p.1.opSize

lemma Ω_subset_cball {p : 𝔓 X} : Ω p ⊆ ball_(p) (𝒬 p) 1 := by
  induction p using 𝔓_induction with
  | base p maxI =>
    rw [Ω]; simp only [maxI, dite_true]
    exact (Ω₁_subset_ball p).trans (ball_subset_ball (by norm_num))
  | ind p nmaxI ih =>
    rw [Ω]; simp only [nmaxI, dite_false, mem_union]
    intro ϑ mϑ
    rcases mϑ with c | c; · exact mem_of_mem_of_subset c (ball_subset_ball (by norm_num))
    obtain ⟨I, ⟨y, my⟩⟩ := p
    dsimp only at nmaxI ih c
    set J := I.succ
    rw [mem_iUnion₂] at c
    obtain ⟨z, ⟨mz₁, mz₂⟩, hz⟩ := c
    simp only [mem_ball]
    calc
      _ ≤ dist_{I} ϑ z + dist_{I} z y := dist_triangle ..
      _ < dist_{I} ϑ z + C4_2_1 := by
        gcongr; simpa using mem_of_mem_of_subset mz₂ (Ω₁_subset_ball ⟨I, ⟨y, my⟩⟩)
      _ ≤ C2_1_2 a * dist_{J} ϑ z + C4_2_1 := by
        gcongr; refine Grid.dist_strictMono (lt_of_le_of_ne Grid.le_succ ?_)
        contrapose! nmaxI; exact Grid.max_of_le_succ nmaxI.symm.le
      _ < C2_1_2 a * 1 + C4_2_1 := by
        gcongr
        · rw [C2_1_2]; positivity
        · simpa only [mem_ball] using mem_of_mem_of_subset hz (ih ⟨z, mz₁⟩)
      _ < 2 ^ (-2 : ℝ) + C4_2_1 := by
        gcongr; rw [mul_one, C2_1_2, Real.rpow_lt_rpow_left_iff one_lt_two, neg_mul, neg_lt_neg_iff]
        norm_cast; linarith [four_le_a X]
      _ < _ := by norm_num

lemma Ω_disjoint_aux {I : Grid X} (nmaxI : ¬IsMax I) {y z : 𝓩 I} (hn : y ≠ z) :
    Disjoint (ball_{I} y.1 CΩ) (⋃ z', ⋃ (x : z' ∈ 𝓩 I.succ ∩ Ω₁ ⟨I, z⟩),
      Ω ⟨I.succ, ⟨z', x.1⟩⟩) := by
  have dj := (disjoint_frequency_cubes (f := y) (g := z)).mt hn
  rw [← not_disjoint_iff_nonempty_inter, not_not] at dj
  contrapose! hn; rw [not_disjoint_iff] at hn
  obtain ⟨(ϑ : Θ X), mϑ, mϑ'⟩ := hn
  rw [mem_iUnion₂] at mϑ'; obtain ⟨x, ⟨mx₁, mx₂⟩, mϑ₂⟩ := mϑ'
  have u : x ∈ ball_{I} y.1 C𝓩 := by
    rw [@mem_ball, @dist_comm]
    calc
    _ ≤ dist_{I} ϑ y.1 + dist_{I} ϑ x := dist_triangle_left ..
    _ < CΩ + dist_{I} ϑ x := by gcongr; simpa [mem_ball] using mϑ
    _ ≤ CΩ + C2_1_2 a * dist_{I.succ} ϑ x := by
      gcongr; refine Grid.dist_strictMono (lt_of_le_of_ne Grid.le_succ ?_)
      contrapose! nmaxI; exact Grid.max_of_le_succ nmaxI.symm.le
    _ < CΩ + C2_1_2 a * 1 := by
      gcongr
      · rw [C2_1_2]; positivity
      · simpa only using mem_of_mem_of_subset mϑ₂ (Ω_subset_cball (p := ⟨I.succ, ⟨x, mx₁⟩⟩))
    _ < CΩ + 2 ^ (-4 : ℝ) := by
      gcongr; rw [mul_one, C2_1_2, Real.rpow_lt_rpow_left_iff one_lt_two, neg_mul, neg_lt_neg_iff]
      norm_cast; linarith [four_le_a X]
    _ ≤ _ := by norm_num
  replace u := mem_of_mem_of_subset u (ball_subset_Ω₁ ⟨I, y⟩)
  have := dj.ne_of_mem u mx₂; contradiction

lemma Ω_disjoint {p q : 𝔓 X} (hn : p ≠ q) (h𝓘 : 𝓘 p = 𝓘 q) : Disjoint (Ω p) (Ω q) := by
  change p.1 = q.1 at h𝓘; obtain ⟨I, y⟩ := p; obtain ⟨_, z⟩ := q
  subst h𝓘; dsimp only at hn z ⊢
  replace hn : y ≠ z := fun e ↦ hn (congrArg (Sigma.mk I) e)
  induction I using Grid.induction with
  | base I maxI =>
    unfold Ω; simp only [maxI, dite_true]
    contrapose! hn; rw [not_disjoint_iff_nonempty_inter] at hn
    exact disjoint_frequency_cubes hn
  | ind I nmaxI ih =>
    unfold Ω; simp only [nmaxI, dite_false]
    have dj := (disjoint_frequency_cubes (f := y) (g := z)).mt hn
    rw [← not_disjoint_iff_nonempty_inter, not_not] at dj
    rw [disjoint_union_left]; constructor <;> (rw [disjoint_union_right]; constructor)
    · have binc : ∀ x, ball_{I} x.1 CΩ ⊆ Ω₁ ⟨I, x⟩ := fun x ↦
        (ball_subset_ball (by norm_num)).trans (ball_subset_Ω₁ ⟨I, x⟩)
      exact (dj.mono_left (binc y)).mono_right (binc z)
    · exact Ω_disjoint_aux nmaxI hn
    · exact (Ω_disjoint_aux nmaxI hn.symm).symm
    · rw [disjoint_iUnion₂_left]; intro a ⟨ma₁, ma₂⟩
      rw [disjoint_iUnion₂_right]; intro b ⟨mb₁, mb₂⟩
      exact ih ⟨a, ma₁⟩ ⟨b, mb₁⟩ (by simp [dj.ne_of_mem ma₂ mb₂])

lemma Ω_biUnion {I : Grid X} : range Q ⊆ ⋃ p ∈ 𝓘 ⁻¹' ({I} : Set (Grid X)), Ω p := by
  induction I using Grid.induction with
  | base I maxI =>
    intro ϑ mϑ; simp only [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop]
    have l := mem_of_mem_of_subset mϑ <|
      (frequency_ball_cover (I := I)).trans iUnion_ball_subset_iUnion_Ω₁
    rw [mem_iUnion] at l; obtain ⟨z, mz⟩ := l; use ⟨I, z⟩
    exact ⟨rfl, by rw [Ω]; simp only [maxI, dite_true, mz]⟩
  | ind I nmaxI ih =>
    intro ϑ mϑ
    replace ih := mem_of_mem_of_subset mϑ ih
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at ih ⊢
    obtain ⟨⟨J, z⟩, (e : J = I.succ), h⟩ := ih
    have := mem_of_mem_of_subset z.2 (𝓩_subset.trans (frequency_ball_cover (I := I)))
    rw [mem_iUnion₂] at this; obtain ⟨z', mz', dz⟩ := this
    have zi : ball_{I} z' C4_2_1 ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 :=
      subset_iUnion₂_of_subset z' mz' (subset_refl _)
    replace zi : ↑z ∈ ⋃ f, Ω₁ ⟨I, f⟩ :=
      mem_of_mem_of_subset dz <| zi.trans iUnion_ball_subset_iUnion_Ω₁
    rw [mem_iUnion] at zi; obtain ⟨z'', mz''⟩ := zi
    use ⟨I, z''⟩, rfl
    rw [Ω]; simp only [nmaxI, dite_false, mem_union]; right
    rw [mem_iUnion₂]; use z.1, ⟨z.2, mz''⟩, e ▸ h

lemma Ω_RFD {p q : 𝔓 X} (h𝓘 : 𝓘 p ≤ 𝓘 q) : Disjoint (Ω p) (Ω q) ∨ Ω q ⊆ Ω p := by
  by_cases h : 𝔰 q ≤ 𝔰 p
  · rw [or_iff_not_imp_left]; intro hi
    obtain ⟨I, y⟩ := p
    obtain ⟨J, z⟩ := q
    have hij : I = J := le_antisymm h𝓘 (Grid.le_dyadic h h𝓘 le_rfl)
    have k := @Ω_disjoint (p := ⟨I, y⟩) ⟨J, z⟩
    replace k : (⟨I, y⟩ : 𝔓 X) = ⟨J, z⟩ := by tauto
    rw [k]
  · obtain ⟨J, sJ, lbJ, ubJ⟩ :=
      Grid.exists_sandwiched h𝓘 (𝔰 q - 1) (by change 𝔰 p ≤ _ ∧ _ ≤ 𝔰 q; omega)
    have := mem_of_mem_of_subset q.2.2 (𝓩_subset.trans (frequency_ball_cover (I := J)))
    rw [mem_iUnion₂] at this; obtain ⟨z', mz', dz⟩ := this
    have zi : ball_{J} z' C4_2_1 ⊆ ⋃ z ∈ 𝓩 I, ball_{J} z C4_2_1 :=
      subset_iUnion₂_of_subset z' mz' (subset_refl _)
    replace zi : ↑q.2 ∈ ⋃ f, Ω₁ ⟨J, f⟩ :=
      mem_of_mem_of_subset dz <| zi.trans iUnion_ball_subset_iUnion_Ω₁
    clear! z'
    rw [mem_iUnion] at zi; obtain ⟨a, ma⟩ := zi -- Paper's `q'` is `⟨J, a⟩`
    have nmaxJ : ¬IsMax J := by
      by_contra maxJ; rw [Grid.isMax_iff] at maxJ
      rw [maxJ, show s topCube = S by exact s_topCube (X := X)] at sJ
      have : 𝔰 q ≤ S := (range_s_subset ⟨q.1, rfl⟩).2
      omega
    have succJ : J.succ = q.1 := (Grid.succ_def nmaxJ).mpr ⟨ubJ, by change 𝔰 q = _; omega⟩
    have key : Ω q ⊆ Ω ⟨J, a⟩ := by
      nth_rw 2 [Ω]; simp only [nmaxJ, dite_false]; intro ϑ mϑ; right; rw [mem_iUnion₂]
      use q.2, ?_, ?_
      · rw [succJ]; exact ⟨q.2.2, ma⟩
      · change ϑ ∈ Ω ⟨q.1, q.2⟩ at mϑ; convert mϑ
    let q' : 𝔓 X := ⟨J, a⟩
    change 𝓘 p ≤ 𝓘 q' at lbJ
    rcases Ω_RFD lbJ with c | c
    · exact Or.inl (disjoint_of_subset_right key c)
    · exact Or.inr (key.trans c)
termination_by (𝔰 q - 𝔰 p).toNat
decreasing_by
  simp_wf
  change (s J - 𝔰 p).toNat < 𝔰 q - 𝔰 p
  rw [sJ, Int.toNat_of_nonneg (by omega), sub_right_comm]
  exact sub_one_lt _

end Construction

def tile_existence : TileStructure Q D κ S o where
  Ω := Construction.Ω
  biUnion_Ω {I} := Construction.Ω_biUnion
  disjoint_Ω := Construction.Ω_disjoint
  relative_fundamental_dyadic {p q} := Construction.Ω_RFD (I := I)
  cball_subset {p} := by
    rw [Construction.Ω]; split_ifs with h
    · have : ball_(p) (𝒬 p) 5⁻¹ ⊆ ball_(p) (𝒬 p) C𝓩 := ball_subset_ball (by norm_num)
      exact this.trans (Construction.ball_subset_Ω₁ p)
    · simp
  subset_cball {p} := Construction.Ω_subset_cball
