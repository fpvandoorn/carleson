import Carleson.GridStructure
import Carleson.DoublingMeasure
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Subset

open Set MeasureTheory Metric Function Complex Bornology Notation
open scoped NNReal ENNReal ComplexConjugate


noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma realD_pos : 0 < (D:ℝ) := by
  simp only [Nat.cast_pos]
  exact defaultD_pos a

lemma realD_nonneg : 0 ≤ (D:ℝ) := realD_pos.le


lemma ball_bound {Y : Set X} (k : ℤ) (hk_lower : -S ≤ k)
  (hY : Y ⊆ ball o (4*D^(S:ℤ)-D^k:ℝ)) (y : X) (hy : y ∈ Y) :
    ball o (4 * D ^ (S:ℤ):ℝ) ⊆ ball y (8 * D^(2 * S:ℤ) * D^k:ℝ) := by
  calc
    ball o (4 * D ^ (S:ℤ))
      ⊆ ball y (2 * (4 * D ^ (S:ℤ)):ℝ) := by
        rw [two_mul]
        refine ball_subset ?h
        simp only [add_sub_cancel_right]
        obtain hy' := hY hy
        rw [mem_ball,dist_comm] at hy'
        apply hy'.le.trans
        rw [tsub_le_iff_right, le_add_iff_nonneg_right]
        positivity
    _ = ball y (8 * D ^ (S:ℤ):ℝ) := by congr! 1; ring
    _ ⊆ ball y (8 * D ^ (2 * S:ℤ) * D ^ k:ℝ) := by
        apply ball_subset_ball
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [← zpow_add₀ realD_pos.ne.symm]
        apply zpow_le_of_le (one_le_realD X)
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

lemma counting_balls {k : ℤ} (hk_lower : -S ≤ k) {Y : Set X}
    (hY : Y ⊆ ball o (4*D^S-D^k))
    (hYdisjoint: Y.PairwiseDisjoint (fun y ↦ ball y (D^k:ℝ))) :
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
      . rw [measure_biUnion _ hYdisjoint (fun y _ => measurableSet_ball)]
        apply hYdisjoint.countable_of_isOpen (fun y _ => isOpen_ball)
        intro y _
        use y
        rw [mem_ball, dist_self]
        exact zpow_pos_of_pos (realD_pos) _
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
def property_set (k : ℤ) : Set (Set X) :=
  {s| s ⊆ ball o (4 * D^S - D^k:ℝ) ∧ s.PairwiseDisjoint (fun y => ball y (D^k:ℝ))}

variable (X) in
lemma property_set_nonempty (k:ℤ): ∅ ∈ property_set X k := by
  dsimp [property_set]
  simp only [empty_subset, pairwiseDisjoint_empty, and_self]

variable (X) in
lemma chain_property_set_has_bound (k : ℤ):
    ∀ c ⊆ property_set X k, IsChain (. ⊆ .) c → ∃ ub ∈ property_set X k,
    ∀ s ∈ c, s ⊆ ub := by
  intro c hc hchain
  use ⋃ s ∈ c,s
  dsimp only [property_set] at hc ⊢
  simp only [mem_setOf_eq, iUnion_subset_iff]
  constructor
  . constructor
    . intro i hi
      specialize hc hi
      rw [mem_setOf_eq] at hc
      exact hc.left
    . intro x hx y hy
      simp only [mem_iUnion, exists_prop] at hx hy
      obtain ⟨sx,hsx, hsx'⟩ := hx
      obtain ⟨sy,hsy, hsy'⟩ := hy
      obtain hxy|hyx := hchain.total hsx hsy
      . specialize hxy hsx'
        specialize hc hsy
        rw [mem_setOf_eq] at hc
        exact hc.right hxy hsy'
      . specialize hyx hsy'
        specialize hc hsx
        rw [mem_setOf_eq] at hc
        exact hc.right hsx' hyx
  . exact fun s a ↦ subset_iUnion₂_of_subset s a fun ⦃a⦄ a ↦ a

variable (X) in
def zorn_apply_maximal_set (k : ℤ):
    ∃ s ∈ property_set X k, ∀ s' ∈ property_set X k, s ⊆ s' → s' = s :=
  zorn_subset (property_set X k) (chain_property_set_has_bound X k)

variable (X) in
def Yk (k : ℤ): Set X := (zorn_apply_maximal_set X k).choose

lemma Yk_pairwise (k:ℤ) : (Yk X k).PairwiseDisjoint (fun (y:X) ↦ ball y (D^k:ℝ)) :=
  (zorn_apply_maximal_set X k).choose_spec.left.right

lemma Yk_subset (k:ℤ) : Yk X k ⊆ ball o (4 * D^S - D^k:ℝ) :=
  (zorn_apply_maximal_set X k).choose_spec.left.left

lemma Yk_maximal (k : ℤ) {s :Set X} (hs_sub : s ⊆ ball o (4 * D^S - D^k : ℝ))
    (hs_pairwise : s.PairwiseDisjoint (fun y ↦ ball y (D^k:ℝ))) (hmax_sub : Yk X k ⊆ s):
    s = Yk X k :=
  (zorn_apply_maximal_set X k).choose_spec.right _ (And.intro hs_sub hs_pairwise) hmax_sub

lemma cover_big_ball (k : ℤ) : ball o (4 * D^S - D^k:ℝ) ⊆ ⋃ y ∈ Yk X k, ball y (2 * D^k:ℝ) := by
  intro y hy
  have : ∃ z ∈ Yk X k, ¬Disjoint (ball y (D^k:ℝ)) (ball z (D^k:ℝ)) := by
    by_contra hcon
    apply hcon
    push_neg at hcon
    suffices hmem : y ∈ Yk X k by
      use y, hmem
      rw [disjoint_self, bot_eq_empty, ball_eq_empty, not_le]
      apply zpow_pos_of_pos (by exact_mod_cast defaultD_pos a) k
    suffices (Yk X k) ∪ {y} = Yk X k by
      rw [union_singleton, insert_eq_self] at this
      exact this
    apply Yk_maximal
    . rw [union_subset_iff]
      use Yk_subset k
      rw [singleton_subset_iff]
      exact hy
    . rw [pairwiseDisjoint_union]
      use Yk_pairwise k
      simp only [pairwiseDisjoint_singleton, true_and]
      simp only [mem_singleton_iff,forall_eq]
      intro z hz _
      specialize hcon z hz
      exact hcon.symm
    . exact subset_union_left
  obtain ⟨z,hz,hz'⟩ := this
  simp only [mem_iUnion, mem_ball, exists_prop]
  use z,hz
  rw [Set.not_disjoint_iff] at hz'
  obtain ⟨x,hx,hx'⟩ := hz'
  rw [mem_ball, dist_comm] at hx
  rw [two_mul]
  exact (dist_triangle y x z).trans_lt (add_lt_add hx hx')

variable (X) in
lemma Yk_nonempty {k : ℤ} (hmin : (0:ℝ) < 4 * D^S - D^k) : (Yk X k).Nonempty := by
  have : o ∈ ball o (4 * D^S - D^k) := mem_ball_self hmin
  have h1 : {o} ⊆ ball o (4 * D^S - D^k) := singleton_subset_iff.mpr this
  have h2 : ({o} : Set X).PairwiseDisjoint (fun y ↦ ball y (D^k)) :=
    pairwiseDisjoint_singleton o fun y ↦ ball y (D ^ k)
  by_contra hcon
  apply hcon
  push_neg at hcon
  use o
  have hsuper : (Yk X k) ⊆ {o} := by rw [hcon]; exact empty_subset {o}
  have : {o} = Yk X k := by
    apply Yk_maximal _ h1 h2 hsuper
  rw [← this]
  trivial

-- not sure if we actually need this; just countability seems quite good enough
lemma Yk_finite {k:ℤ} (hk_lower : -S ≤ k): (Yk X k).Finite := by
  rw [← Set.encard_ne_top_iff]
  apply LT.lt.ne
  rw [← ENat.toENNReal_lt,ENat.toENNReal_top]
  calc
    ((Yk X k).encard : ℝ≥0∞)
      ≤ C4_1_1 X := counting_balls hk_lower (Yk_subset k) (Yk_pairwise k)
    _ < ⊤ := ENNReal.coe_lt_top


variable (X) in
lemma Yk_countable (k:ℤ) : (Yk X k).Countable := by
  apply (Yk_pairwise k).countable_of_isOpen (fun y _ => isOpen_ball)
  simp only [nonempty_ball]
  exact fun y _ => zpow_pos_of_pos realD_pos k

variable (X) in
def Yk_encodable (k:ℤ) : Encodable (Yk X k) := (Yk_countable X k).toEncodable

def Encodable.linearOrder {α : Type*} (i:Encodable α) : LinearOrder α :=
  LinearOrder.lift' (i.encode) (i.encode_injective)

instance {k : ℤ}: LinearOrder (Yk X k) := (Yk_encodable X k).linearOrder
instance {k : ℤ}: WellFoundedLT (Yk X k) where
  wf := by
    apply (@OrderEmbedding.wellFounded (Yk X k) ℕ)
    use ⟨(Yk_encodable X k).encode,(Yk_encodable X k).encode_injective⟩
    . simp only [Embedding.coeFn_mk, Subtype.forall]
      intro i hi j hj
      rfl
    exact wellFounded_lt

local instance {k : ℤ} : SizeOf (Yk X k) where
  sizeOf := (Yk_encodable X k).encode

lemma I_induction_proof {k:ℤ} (hk:-S ≤ k) (hneq : ¬ k = -S) : -S ≤ k - 1 := by
  have : -S < k := by exact lt_of_le_of_ne hk fun a_1 ↦ hneq (id (Eq.symm a_1))
  linarith

mutual
  def I1 {k:ℤ} (hk : -S ≤ k) (y : Yk X k) : Set X :=
    if hk': k = -S then
      ball y (D^(-S:ℤ))
    else
      let hk'' : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk' (id (Eq.symm a_1))
      have h1: 0 ≤ S + (k - 1) := by linarith
      have : (S + (k-1)).toNat < (S + k).toNat := by
        rw [Int.lt_toNat,Int.toNat_of_nonneg h1]
        linarith
      ⋃ (y': Yk X (k-1)),
        ⋃ (_ : y' ∈ Yk X (k-1) ↓∩ ball (y:X) (D^k)), I3 (I_induction_proof hk hk') y'
  termination_by (3 * (S+k).toNat, sizeOf y)

  def I2 {k:ℤ} (hk : -S ≤ k) (y : Yk X k) : Set X :=
    if hk': k = -S then
      ball y (2 * D^(-S:ℤ))
    else
      let hk'' : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk' (id (Eq.symm a_1))
      have : (S + (k-1)).toNat < (S + k).toNat := by
        rw [Int.lt_toNat,Int.toNat_of_nonneg (by linarith)]
        linarith
      ⋃ (y':Yk X (k-1)),
        ⋃ (_ : y' ∈ Yk X (k-1) ↓∩ ball y (2 * D^k)), I3 (I_induction_proof hk hk') y'
  termination_by (3 * (S+k).toNat, sizeOf y)


  def Xk {k:ℤ} (hk : -S ≤ k) : Set X := ⋃ (y' : Yk X k), I1 hk y'
  termination_by (3 * (S+k).toNat + 1, 0)

  def I3 {k:ℤ} (hk : -S ≤ k) (y:Yk X k) : Set X :=
    I1 hk y ∪ (I2 hk y \ (Xk hk ∪ ⋃ (y' < y), I3 hk y'))

  termination_by (3 * (S+k).toNat + 2, sizeOf y)

end

lemma I3_apply {k:ℤ} (hk : -S ≤ k) (y : Yk X k) :
  I3 hk y = I1 hk y ∪ (I2 hk y \ (Xk hk ∪ ⋃ (y' < y), I3 hk y')) := by
  rw [I3]

lemma I1_subset_I3 {k : ℤ} (hk : -S ≤ k) (y:Yk X k) :
    I1 hk y ⊆ I3 hk y := by
  intro i hi
  rw [I3]
  left
  exact hi

lemma I1_subset_I2 {k:ℤ} (hk : -S ≤ k) (y:Yk X k) :
    I1 hk y ⊆ I2 hk y := by
  rw [I1,I2]
  if hk_s : k = -S then
    intro y'
    rw [dif_pos hk_s,dif_pos hk_s]
    apply ball_subset_ball
    nth_rw 1 [← one_mul (D^(-S:ℤ):ℝ)]
    exact mul_le_mul_of_nonneg_right (by linarith) (zpow_nonneg realD_nonneg _)
  else
    rw [dif_neg hk_s, dif_neg hk_s]
    simp only [iUnion_subset_iff]
    intro y' hy' z hz
    simp only [mem_iUnion, exists_prop, exists_and_left]
    use y'
    rw [and_iff_left hz]
    revert hy'
    apply ball_subset_ball
    nth_rw 1 [← one_mul (D^k : ℝ)]
    apply mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg realD_nonneg _)

lemma I3_subset_I2 {k:ℤ} (hk : -S ≤ k) (y:Yk X k):
    I3 hk y ⊆ I2 hk y := by
  intro x hx
  rw [I3] at hx
  simp only [ mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
    not_and] at hx
  obtain l|r := hx
  . exact I1_subset_I2 hk y l
  . exact r.left

mutual
  lemma I1_measurableSet {k:ℤ} (hk:-S ≤ k) (y: Yk X k) : MeasurableSet (I1 hk y) := by
    if hk_s : k = -S then
      rw [I1,dif_pos hk_s]
      exact measurableSet_ball
    else
      let hk'' : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk_s (id (Eq.symm a_1))
      have h1: 0 ≤ S + (k - 1) := by linarith
      have : (S + (k-1)).toNat < (S + k).toNat := by
        rw [Int.lt_toNat,Int.toNat_of_nonneg h1]
        linarith
      rw [I1,dif_neg hk_s]
      letI := (Yk_countable X (k-1)).to_subtype
      refine MeasurableSet.biUnion ?_ ?_
      . exact to_countable (Yk X (k - 1) ↓∩ ball (↑y) (D ^ k))
      . simp only [mem_preimage]
        intro b _
        exact I3_measurableSet (I_induction_proof hk hk_s) b
  termination_by (3 * (S+k).toNat, sizeOf y)


  lemma I2_measurableSet {k:ℤ} (hk:-S ≤ k) (y: Yk X k) : MeasurableSet (I2 hk y) := by
    if hk_s : k = -S then
      rw [I2,dif_pos hk_s]
      exact measurableSet_ball
    else
      let hk'' : -S < k := by exact lt_of_le_of_ne hk fun a_1 ↦ hk_s (id (Eq.symm a_1))
      have : (S + (k-1)).toNat < (S + k).toNat := by
        rw [Int.lt_toNat,Int.toNat_of_nonneg (by linarith)]
        linarith
      rw [I2,dif_neg hk_s]
      letI := (Yk_countable X (k-1)).to_subtype
      apply MeasurableSet.biUnion
      . exact to_countable (Yk X (k - 1) ↓∩ ball (↑y) (2 * D ^ k))
      . simp only [mem_preimage]
        intro b _
        exact I3_measurableSet (I_induction_proof hk hk_s) b
  termination_by (3 * (S+k).toNat, sizeOf y)


  lemma Xk_measurableSet {k:ℤ} (hk : -S ≤ k) : MeasurableSet (Xk hk) := by
    rw [Xk]
    letI := (Yk_countable X k).to_subtype
    apply MeasurableSet.iUnion
    intro b
    exact I1_measurableSet hk b
  termination_by (3 * (S+k).toNat + 1, 0)

  lemma I3_measurableSet {k:ℤ} (hk:-S ≤ k) (y:Yk X k) : MeasurableSet (I3 hk y) := by
    rw [I3]
    apply MeasurableSet.union
    . exact I1_measurableSet hk y
    apply MeasurableSet.diff
    . exact I2_measurableSet hk y
    apply MeasurableSet.union
    . exact Xk_measurableSet hk
    letI := (Yk_countable X k).to_subtype
    apply MeasurableSet.iUnion
    intro b
    apply MeasurableSet.iUnion
    intro _
    exact I3_measurableSet hk b
  termination_by (3 * (S+k).toNat+2, sizeOf y)

end

section basic_grid_structure

mutual
  lemma I1_prop_1 {k:ℤ} (hk : -S ≤ k) {x : X} {y1 y2 : Yk X k} :
      x ∈ I1 hk y1 ∩ I1 hk y2 → y1 = y2 := by
    rw [I1,I1]
    if hk_s : k = -S then
      rw [dif_pos hk_s,dif_pos hk_s]
      subst hk_s
      intro hx
      ext
      rw [(Yk_pairwise (-S)).elim (y1.property) (y2.property)]
      rw [not_disjoint_iff]
      use x
      exact hx
    else
      have : -S ≤ k - 1 := I_induction_proof hk hk_s
      have : ((2 * (S + (k - 1))).toNat : ℤ) + 1 < 2 * (S + k) := by
        rw [Int.toNat_of_nonneg (by linarith)]
        linarith

      rw [dif_neg hk_s,dif_neg hk_s]
      intro hx
      simp only [mem_preimage, mem_inter_iff, mem_iUnion,
        exists_prop, exists_and_left] at hx
      obtain ⟨⟨z1,hz1,hz1'⟩,⟨z2,hz2,hz2'⟩⟩ := hx
      have hz_eq : z1 = z2 := I3_prop_1 (I_induction_proof hk hk_s) (And.intro hz1' hz2')
      subst hz_eq
      ext
      apply (Yk_pairwise k).elim (y1.property) (y2.property)
      rw [not_disjoint_iff]
      use z1
  termination_by (2 * (S + k)).toNat

  lemma I3_prop_1 {k:ℤ} (hk : -S ≤ k) {x : X} {y1 y2 : Yk X k} :
      x ∈ I3 hk y1 ∩ I3 hk y2 → y1 = y2 := by
    intro hx
    have hx' := hx
    rw [I3,I3] at hx
    obtain ⟨hl,hr⟩ := hx'
    simp only [mem_inter_iff, mem_union, mem_diff, mem_iUnion, exists_prop, not_or,
      not_exists, not_and] at hx
    if hx_mem_Xk : x ∈ Xk hk then
      rw [not_iff_false_intro hx_mem_Xk] at hx
      simp_rw [false_and,and_false,or_false] at hx
      exact I1_prop_1 hk hx
    else
    have hx_not_mem_i1 (y' : Yk X k): x ∉ I1 hk y' := by
      simp only [Xk, mem_iUnion, not_exists] at hx_mem_Xk
      apply hx_mem_Xk
    rw [iff_false_intro (hx_not_mem_i1 y1), iff_false_intro (hx_not_mem_i1 y2)] at hx
    rw [false_or,false_or,iff_true_intro hx_mem_Xk,true_and,true_and] at hx
    apply Linarith.eq_of_not_lt_of_not_gt
    . exact fun h ↦ hx.right.right y1 h hl
    exact fun h ↦ hx.left.right y2 h hr
  termination_by (2 * (S + k)).toNat + 1
end


lemma I3_prop_3_2 {k:ℤ} (hk : -S ≤ k) (y : Yk X k):
    I3 hk y ⊆ ball (y : X) (4*D^k) := by
  intro x hx
  have : x ∈ I2 hk y := I3_subset_I2 hk y hx
  simp only [I2] at this
  if hk_s : k = -S then
    rw [dif_pos hk_s] at this
    subst hk_s
    revert this
    apply ball_subset_ball
    exact mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg realD_nonneg _)
  else
    rw [dif_neg hk_s] at this
    simp only [mem_preimage, mem_iUnion, exists_prop,
      exists_and_left] at this
    obtain ⟨y',hy',hyi3⟩ := this
    have : -S ≤ k - 1 := I_induction_proof hk hk_s
    have : (S + (k - 1)).toNat < (S + k) := by
      rw [Int.toNat_of_nonneg (by linarith)]
      linarith
    have : x ∈ ball (y' : X) (4 * D^(k-1)) := I3_prop_3_2 _ y' hyi3
    rw [mem_ball] at this hy' ⊢
    calc
      dist x (y:X)
        ≤ dist x (y' : X) + dist (y' : X) (y:X) := dist_triangle _ _ _
      _ <  4 * D ^ (k - 1) + 2 * D ^ k := add_lt_add this hy'
      _ ≤ 1 * D ^ (k - 1 + 1) + 2 * D^ k := by
        simp only [one_mul, add_le_add_iff_right]
        rw [zpow_add₀ realD_pos.ne.symm _ 1,zpow_one,mul_comm _ (D:ℝ)]
        apply mul_le_mul_of_nonneg_right (four_le_realD X) (zpow_nonneg realD_nonneg _)
      _ ≤ 4 * D ^ k := by
        rw [sub_add_cancel,← right_distrib]
        apply mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg realD_nonneg _)
termination_by (S + k).toNat

mutual
  lemma I2_prop_2 {k:ℤ} (hk : -S ≤ k) :
      ball o (4 * D^S - 2 * D^k) ⊆ ⋃ (y:Yk X k), I2 hk y := by
    simp only [I2, mem_preimage, iUnion_coe_set]
    if hk_s : k = -S then
      simp_rw [dif_pos hk_s]
      subst hk_s
      calc
        ball o (4 * D^S - 2 * (D^(-S:ℤ)))
          ⊆ ball o (4 * D^S - D^(-S:ℤ)) := by
            apply ball_subset_ball
            rw [two_mul,tsub_le_iff_right,sub_add_add_cancel,le_add_iff_nonneg_right]
            exact zpow_nonneg realD_nonneg _
        _ ⊆ ⋃ (i ∈ Yk X (-S)), ball i (2 * D^(-S:ℤ)) := cover_big_ball (-S:ℤ)
    else
      simp_rw [dif_neg hk_s]
      intro x hx
      have : -S < k := by exact lt_of_le_of_ne hk fun a_1 ↦ hk_s (id (Eq.symm a_1))
      have : ((2 * (S + (k - 1))).toNat : ℤ) + 1 < 2 * (S + k) := by
        rw [Int.toNat_of_nonneg (by linarith)]
        linarith
      have hsub1 : ball o (4 * D^S - 2 * D^k) ⊆ ⋃ y, I3 (I_induction_proof hk hk_s) y := by
        calc
          ball o (4 * D ^ S - 2 * D ^ k)
            ⊆ ball o (4 * D^S - 2 * D^(k-1)) := by
              apply ball_subset_ball
              simp only [tsub_le_iff_right]
              rw [sub_eq_add_neg,add_assoc]
              simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero,
                gt_iff_lt, Nat.ofNat_pos, mul_le_mul_left]
              exact zpow_le_of_le (one_le_realD X) (by linarith)
          _ ⊆ ⋃ y, I3 _ y := I3_prop_2 _
      have hmem_i3 : x ∈ ⋃ y, I3 _ y := hsub1 hx
      simp only [mem_iUnion] at hmem_i3
      obtain ⟨y',hy''⟩ := hmem_i3
      have hy''' : x ∈ ball (y':X) (D^k) := by
        apply (?_ : I3 _ y' ⊆ ball (y' : X) (D^k)) hy''
        calc
          I3 _ y'
            ⊆ ball y' (4 * D ^(k-1)) := I3_prop_3_2 _ y'
          _ ⊆ ball y' (D * D^(k-1)) := by
            apply ball_subset_ball
            exact mul_le_mul_of_nonneg_right (four_le_realD X) (zpow_nonneg realD_nonneg _)
          _ = ball (y': X) (D^k) := by
            nth_rw 1 [← zpow_one (D:ℝ),← zpow_add₀ realD_pos.ne.symm,add_sub_cancel]
      rw [mem_ball_comm] at hy'''
      have hyfin : (y' :X) ∈ ball o (4 * D^S - D^k) := by
        simp only [mem_ball] at hx hy''' ⊢
        calc
          dist ↑y' o
            ≤ dist (y' : X) x + dist x o := dist_triangle _ _ _
          _ < D^k + (4 * D^S - 2 * D^k) := add_lt_add hy''' hx
          _ ≤ 4 * D ^ S - D ^ k := by linarith
      have hyfin' : (y' : X) ∈ ⋃ (y'' ∈ Yk X k), ball (y'') (2 * D^k) := cover_big_ball k hyfin
      rw [← iUnion_coe_set (Yk X k) (fun z ↦ ball (z : X) (2 * D^k))] at hyfin'
      simp only [mem_iUnion, exists_prop] at hyfin'
      obtain ⟨y2,hy2'⟩ := hyfin'
      simp only [mem_iUnion, exists_prop, exists_and_left]
      use y2,y2.property,y',hy2',y'.property
  termination_by (2 * (S + k)).toNat

  lemma I3_prop_2 {k:ℤ} (hk : -S ≤ k) :
      ball o (4 * D^S - 2 * D^k) ⊆ ⋃ (y:Yk X k), I3 hk y := by
    intro x hx

    if hx_mem_Xk : x ∈ Xk hk then
      rw [Xk] at hx_mem_Xk
      simp only [mem_iUnion] at hx_mem_Xk ⊢
      apply hx_mem_Xk.elim
      intro y hy
      use y
      rw [I3]
      left
      exact hy
    else
      simp only [mem_iUnion]
      have : x ∈ ⋃ (y : Yk X k), I2 hk y := I2_prop_2 hk hx
      simp only [mem_iUnion] at this
      have : {i|x ∈ I2 hk i}.Nonempty := this
      have H := (@wellFounded_lt (Yk X k) _ _)
      let y := H.min {i|x ∈ I2 hk i} this
      have hy_i2 : x ∈ I2 hk y := H.min_mem {i|x ∈ I2 hk i} this
      have hy_is_min : ∀ y', x ∈ I2 hk y' → ¬ y' < y := by
        intro y' hy'
        exact H.not_lt_min {i|x ∈ I2 hk i} this hy'
      use y
      revert hy_i2 hy_is_min
      generalize y = y
      intro hy_i2 hy_min
      rw [I3]
      have hx_not_mem_i1 : ∀ y',x ∉ I1 hk y' := by
        simp only [Xk,mem_iUnion,not_exists] at hx_mem_Xk
        exact hx_mem_Xk
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and]
      right
      use hy_i2,hx_mem_Xk
      intro y' hy'
      rw [I3]
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and]
      use hx_not_mem_i1 y'
      intro hy_i2'
      specialize hy_min y' hy_i2' hy'
      contradiction

  termination_by (2 * (S + k)).toNat + 1

end


lemma I3_prop_3_1 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    ball (y:X) (2⁻¹ * D^k) ⊆ I3 hk y := by
  rw [I3]
  refine fun x hx => subset_union_left ((?_ : ball (y:X) (2⁻¹ * D^k) ⊆ I1 hk y) hx)
  rw [I1]
  clear hx x
  if hk_s : k = -S then
    rw [dif_pos hk_s]
    subst hk_s
    apply ball_subset_ball
    nth_rw 2 [← one_mul (D^(-S:ℤ):ℝ)]
    exact mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg realD_nonneg _)
  else
    rw [dif_neg hk_s]
    simp only [mem_preimage]
    have : (y:X) ∈ ball o (4 * D^S-D^k:ℝ) := by
      exact Yk_subset k y.property
    have : ball (y:X) (2⁻¹ * D^k) ⊆ ⋃ (y':Yk X (k-1)), I3 (I_induction_proof hk hk_s) y' := by
      calc
        ball (y:X) (2⁻¹ * D^k)
          ⊆ ball o (4 * D^S - D^k + 2⁻¹ * D^k) := by
            apply ball_subset
            ring_nf
            rw [mul_comm]
            rw [mem_ball] at this
            exact this.le
        _ ⊆ ball o (4 * D^S-2 * D^(k-1)) := by
          apply ball_subset_ball
          rw [sub_eq_add_neg,sub_eq_add_neg]
          rw [add_assoc]
          rw [add_le_add_iff_left]
          simp only [neg_add_le_iff_le_add, le_add_neg_iff_add_le]
          calc
            (2⁻¹ * D ^ k + 2 * D ^ (k - 1) : ℝ)
              = 2⁻¹ * D^(k) + 2⁻¹ * 4 * D^(k-1) := by
                rw [add_right_inj]
                norm_num
            _ ≤ 2⁻¹ * (2 * D ^ k) := by
              rw [mul_assoc,← left_distrib]
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              rw [two_mul]
              apply add_le_add_left
              nth_rw 2 [← add_sub_cancel 1 k]
              rw [zpow_add₀ realD_pos.ne.symm,zpow_one]
              exact mul_le_mul_of_nonneg_right (four_le_realD X) (zpow_nonneg realD_pos.le _)
            _ = D ^ k := by
              rw [← mul_assoc]
              norm_num
        _ ⊆ ⋃ (y':Yk X (k - 1)), I3 (I_induction_proof hk hk_s) y' := I3_prop_2 (I_induction_proof hk hk_s)
    intro x hx
    have : x ∈ ⋃ (y':Yk X (k - 1)), I3 _ y' := this hx
    rw [mem_iUnion] at this
    obtain ⟨y',hy'⟩ := this
    have : x ∈ ball (y':X) (4 * D^(k-1)) := I3_prop_3_2 _ y' hy'
    have : (y':X) ∈ ball (y:X) (D^k) := by
      rw [mem_ball] at this hx ⊢
      rw [dist_comm] at this
      calc
        dist (y':X) (y:X)
          ≤ dist (y':X) x + dist x (y:X) := dist_triangle _ _ _
        _ < 4 * D^(k-1) + 2⁻¹ * D^(k) := add_lt_add this hx
        _ = 2⁻¹ * 8 * D^(k-1) + 2⁻¹ * D^k := by norm_num
        _ ≤ 2⁻¹ * (D^k + D^k) := by
          rw [mul_assoc,← left_distrib]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simp only [Nat.cast_add, Nat.cast_one, add_le_add_iff_right]
          nth_rw 2 [← add_sub_cancel 1 k,]
          rw [zpow_add₀ realD_pos.ne.symm,zpow_one]
          exact mul_le_mul_of_nonneg_right (eight_le_realD X) (zpow_nonneg realD_pos.le _)
        _ = D ^ k := by
          rw [← two_mul,← mul_assoc,inv_mul_cancel (by norm_num),one_mul]
    rw [mem_iUnion]
    use y'
    rw [mem_iUnion]
    use this

end basic_grid_structure

lemma I3_nonempty {k:ℤ} (hk : -S ≤ k) (y:Yk X k) :
  (I3 hk y).Nonempty := by
  use y
  . apply I3_prop_3_1 hk y
    rw [mem_ball,dist_self]
    simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    exact zpow_pos_of_pos realD_pos k

-- the additional argument `hk` to get decent equality theorems
lemma cover_by_cubes {l : ℤ} (hl :-S ≤ l):
    ∀ {k:ℤ}, l ≤ k → (hk : -S ≤ k) → ∀ y, I3 hk y ⊆ ⋃ (yl : Yk X l), I3 hl yl := by
  apply Int.le_induction
  . intro _ y x hx
    rw [mem_iUnion]
    use y
  intro k hlk hind
  rw [← add_sub_cancel_right k 1] at hind
  intro hk1 y x hx
  have h : -S < k + 1 := by linarith
  have : x ∈ I2 hk1 y := I3_subset_I2 hk1 y hx
  rw [I2,dif_neg h.ne.symm] at this
  simp only [mem_preimage, mem_iUnion,
    exists_prop, exists_and_left] at this
  obtain ⟨z,_,hz'⟩ := this
  specialize hind (I_induction_proof hk1 h.ne.symm) z hz'
  exact hind

lemma dyadic_property {l:ℤ} (hl : -S ≤ l) {k:ℤ} (hl_k : l ≤ k) :
    (hk : -S ≤ k) → ∀ (y:Yk X k), ∀ (y':Yk X l),
    ¬ Disjoint (I3 hl y') (I3 hk y) → I3 hl y' ⊆ I3 hk y := by
  simp_rw [not_disjoint_iff]
  simp only [forall_exists_index, and_imp]
  intro hk y y' x hxl hxk
  if hk_l : k = l then
    subst hk_l
    apply Eq.le
    apply congr_heq
    . congr
    simp only [heq_eq_eq]
    exact I3_prop_1 hk (And.intro hxl hxk)
  else
    have : l < k := by exact lt_of_le_of_ne hl_k fun a ↦ hk_l (id (Eq.symm a))
    have hl_k_m1 : l ≤ k-1 := by linarith
    have hk_not_neg_s : ¬ k = -S := by linarith
    -- intro x' hx'
    have : x ∈ ⋃ (y'': Yk X (k-1)), I3 (I_induction_proof hk hk_not_neg_s) y'' := by
      apply cover_by_cubes (I_induction_proof hk hk_not_neg_s) (by linarith) hk y hxk

    simp only [mem_iUnion] at this
    obtain ⟨y'',hy''⟩ := this
    have : l + (-l + (k-1)).toNat < k := by
      rw [Int.toNat_of_nonneg (by linarith)]
      linarith
    have : I3 hl y' ⊆ I3 (I_induction_proof hk hk_not_neg_s) y'' := by
      apply dyadic_property hl hl_k_m1 (I_induction_proof hk hk_not_neg_s)
      rw [not_disjoint_iff]
      use x
    apply this.trans

    if hx_mem_Xk : x ∈ Xk hk then
      have hx_i1: x ∈ I1 hk y := by
        rw [I3] at hxk
        simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
          not_and] at hxk
        rw [not_iff_false_intro hx_mem_Xk,false_and,and_false,or_false] at hxk
        exact hxk

      rw [I1] at hx_i1
      rw [dif_neg hk_not_neg_s] at hx_i1
      simp only [mem_preimage, mem_iUnion, exists_prop, exists_and_left] at hx_i1
      obtain ⟨u,hu,hu'⟩ := hx_i1
      have hxy'' : x ∈ I3 _ y'' := this hxl
      have : y'' = u := by
        apply I3_prop_1
        use hxy''
      subst this
      apply Subset.trans _ (I1_subset_I3 _ _)
      rw [I1,dif_neg hk_not_neg_s]
      intro x' hx'
      simp only [mem_preimage, mem_iUnion, exists_prop, exists_and_left]
      use y''
    else
      have hx_not_mem_i1 (y_1 : Yk X k) : x ∉ I1 hk y_1 := by
        rw [Xk] at hx_mem_Xk
        simp only [mem_iUnion, not_exists] at hx_mem_Xk
        exact hx_mem_Xk y_1
      have hx_mem_i2_and : x ∈ I2 hk y ∧ ∀ u < y, x ∉ I3 hk u:= by
        rw [I3] at hxk
        simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
          not_and] at hxk
        rw [iff_false_intro (hx_not_mem_i1 y),iff_true_intro hx_mem_Xk] at hxk
        rw [false_or,true_and] at hxk
        exact hxk
      have hx_mem_i2 := hx_mem_i2_and.left
      have hx_not_mem_i3_u := hx_mem_i2_and.right
      have hx_not_mem_i2_u: ∀ u < y, x ∉ I2 hk u := by
        intro u hu
        specialize hx_not_mem_i3_u u hu
        rw [I3] at hx_not_mem_i3_u
        simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
          not_and, not_forall, Classical.not_imp, Decidable.not_not] at hx_not_mem_i3_u
        rw [iff_true_intro (hx_not_mem_i1 u),iff_true_intro hx_mem_Xk] at hx_not_mem_i3_u
        rw [true_and,true_implies] at hx_not_mem_i3_u
        intro h
        obtain ⟨v,hv,hv'⟩ := hx_not_mem_i3_u h
        exact hx_mem_i2_and.right v (hv.trans hu) hv'

      rw [I2, dif_neg hk_not_neg_s] at hx_mem_i2
      simp only [mem_preimage, mem_iUnion, exists_prop,
        exists_and_left] at hx_mem_i2
      obtain ⟨u,hu,hxu⟩ := hx_mem_i2
      obtain rfl : y'' = u := by
        apply I3_prop_1 (I_induction_proof hk hk_not_neg_s)
        use hy''
      have : I3 (I_induction_proof hk hk_not_neg_s) y'' ∩ Xk hk = ∅ := by
        ext x'
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro hx_i3' hx_xk'
        apply hx_mem_Xk
        rw [Xk] at hx_xk' ⊢
        simp only [mem_iUnion] at hx_xk' ⊢
        obtain ⟨u,hu⟩ := hx_xk'
        use u
        rw [I1,dif_neg hk_not_neg_s] at hu ⊢
        simp only [mem_preimage, mem_iUnion, exists_prop,
          exists_and_left] at hu ⊢
        obtain ⟨u',hu',hu''⟩ := hu
        use u',hu'
        obtain rfl : u' = y'' := I3_prop_1 (I_induction_proof hk hk_not_neg_s) (And.intro hu'' hx_i3')
        exact hxu
      intro x' hx'
      rw [I3]
      have hx_not_xk : x' ∉ Xk hk := by
        intro hcontra
        have : x' ∈ (∅ : Set X) := by
          rw [← this]
          exact mem_inter hx' hcontra
        exact this
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and,iff_true_intro hx_not_xk,true_and]
      right
      constructor
      . rw [I2, dif_neg hk_not_neg_s]
        simp only [mem_preimage, mem_iUnion, exists_prop,
          exists_and_left]
        use y''
      intro u hu
      have hx_not_i1' : x' ∉ I1 hk u := by
        intro hx_i1'
        apply hx_not_xk
        rw [Xk]
        simp only [mem_iUnion]
        use u
      rw [I3]
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and, not_forall, Classical.not_imp, Decidable.not_not]
      rw [iff_true_intro hx_not_xk,iff_true_intro hx_not_i1',true_and,true_implies]
      intro hx_i2'
      by_contra
      apply hx_not_mem_i2_u u hu
      rw [I2, dif_neg hk_not_neg_s] at hx_i2' ⊢
      simp only [mem_preimage, mem_iUnion] at hx_i2' ⊢
      obtain ⟨z,hz,hz'⟩ := hx_i2'
      use z,hz
      suffices z = y'' by
        subst this
        exact hy''
      apply I3_prop_1 (I_induction_proof hk hk_not_neg_s)
      exact mem_inter hz' hx'
  termination_by ((-l + k).toNat)

structure ClosenessProperty {k1 k2 : ℤ} (hk1 : -S ≤ k1) (hk2 : -S ≤ k2)
    (y1 : Yk X k1) (y2 : Yk X k2) : Prop where
  I3_subset : I3 hk1 y1 ⊆ I3 hk2 y2
  I3_compl_inter_ball : ((I3 hk2 y2)ᶜ ∩ ball (y1:X) (6 * D^k1)).Nonempty

local macro "clProp(" hkl:term ", " y1:term " | " hkr:term ", " y2:term ")" : term =>
 `(ClosenessProperty $hkl $hkr $y1 $y2)

lemma transitive_boundary {k1 k2 k3 : ℤ} (hk1 : -S ≤ k1) (hk2 : -S ≤ k2) (hk3 : -S ≤ k3)
  (hk1_2 : k1 < k2) (hk2_3 : k2 ≤ k3) (y1 : Yk X k1) (y2 : Yk X k2) (y3 : Yk X k3)
    (x:X) (hx : x ∈ I3 hk1 y1 ∩ I3 hk2 y2 ∩ I3 hk3 y3) :
    clProp(hk1,y1|hk3,y3) → (clProp(hk1,y1|hk2,y2) ∧ clProp(hk2,y2|hk3,y3)) := by
  rintro ⟨_,⟨x',hx'⟩⟩
  simp only [mem_inter_iff, mem_compl_iff] at hx
  have hi3_1_2 : I3 hk1 y1 ⊆ I3 hk2 y2 := by
    apply dyadic_property hk1 hk1_2.le hk2 y2 y1
    rw [not_disjoint_iff]
    use x
    use hx.left.left
    exact hx.left.right
  have hi3_2_3 : I3 hk2 y2 ⊆ I3 hk3 y3 := by
    apply dyadic_property hk2 hk2_3 hk3 y3 y2
    rw [not_disjoint_iff]
    use x
    use hx.left.right
    exact hx.right
  simp only [mem_inter_iff, mem_compl_iff] at hx' ⊢
  have hx_4k2 : x ∈ ball (y2:X) (4 * D^k2) := I3_prop_3_2 hk2 y2 hx.left.right
  have hx_4k2' : x ∈ ball (y1:X) (4 * D^k1) := I3_prop_3_2 hk1 y1 hx.left.left
  rw [mem_ball,dist_comm] at hx_4k2'
  constructor
  . exact ⟨hi3_1_2,by
    use x', fun h => hx'.left (hi3_2_3 h)
    exact hx'.right⟩
  . exact ⟨hi3_2_3,by
    use x', hx'.left
    obtain hx_dist := hx'.right
    rw [mem_ball] at hx_dist ⊢
    calc
      dist x' ↑y2
        ≤ dist x' y1 + dist (y1:X) x + dist x y2 := dist_triangle4 x' y1 x y2
      _ < dist x' y1 + dist (y1:X) x + 4 * D^k2 := by
        rw [Real.add_lt_add_iff_left]
        exact hx_4k2
      _ < 6 * D^k1 + 4 * D^k1 + 4 * D^k2 := by
        rw [add_lt_add_iff_right]
        exact add_lt_add hx_dist hx_4k2'
      _ ≤ 2 * D^k2 + 4 * D^k2 := by
        rw [← right_distrib 6 4 (D^k1:ℝ)]
        have hz : (6 + 4 : ℝ) = 2 * 5 := by norm_num
        rw [hz]
        simp only [add_le_add_iff_right]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc
          (5 * D ^ k1:ℝ)
            ≤ D * D^k1 := by
              exact mul_le_mul_of_nonneg_right (five_le_realD X) (zpow_nonneg realD_pos.le _)
          _ ≤ D ^ k2 := by
            nth_rw 1 [← zpow_one (D:ℝ)]
            rw [← zpow_add₀ realD_pos.ne.symm]
            refine zpow_le_of_le (one_le_realD X) (by linarith)
      _ = 6 * D ^ k2 := by
        rw [← right_distrib]
        norm_num
    ⟩

def const_K  : ℕ := 2 ^ (4 * a + 1)

namespace ShortVariables
set_option hygiene false in
scoped notation "K'" => @const_K a
end ShortVariables

variable (X) in
def C4_1_7 [ProofData a q K σ₁ σ₂ F G]: ℝ≥0 := As (defaultA a) (2^4)

variable (X) in
lemma C4_1_7_eq : C4_1_7 X = 2 ^ (4 * a) := by
  dsimp [C4_1_7,As]
  rw [← Real.rpow_natCast 2 4]
  rw [Real.logb_rpow (by linarith : 0 < (2:ℝ)) (by norm_num)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.ceil_ofNat]
  group

-- #check C4_1_7

lemma volume_tile_le_volume_ball (k:ℤ) (hk:-S ≤ k) (y:Yk X k):
    volume (I3 hk y) ≤ C4_1_7 X * volume (ball (y:X) (4⁻¹ * D^k)) := by
  calc
    volume (I3 hk y)
      ≤ volume (ball (y:X) (2^4 * (4⁻¹ * D^k))) := by
        rw [← mul_assoc]
        norm_num only
        apply volume.mono
        exact I3_prop_3_2 hk y
    _ ≤ C4_1_7 X * volume (ball (y:X) (4⁻¹ * D^k:ℝ)):= by
      rw [C4_1_7]
      apply volume_ball_le_same' (y:X) (by linarith)
      apply mul_le_mul_of_nonneg_right (le_refl _)
      simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      exact zpow_nonneg realD_nonneg _

lemma le_s {k:ℤ} (hk_mK : -S ≤ k-K') (k' : Ioc (k-K') k): (-S:ℤ) ≤ k' := by
  have := k'.property.left
  linarith

lemma small_boundary (k:ℤ) (hk:-S ≤ k) (hk_mK : -S ≤ k - K') (y:Yk X k):
    ∑' (z:Yk X (k-K')), volume (⋃ (_ : clProp(hk_mK,z|hk,y)), (I3 hk_mK z))
      ≤ 2⁻¹ * volume (I3 hk y) := by
  -- have hioc_fin' : (Set.Ioc (k-K') k).Finite := by exact finite_Ioc (k - ↑K') k
  suffices
    (K') * ∑' (z:Yk X (k-K')), volume (⋃ (_:clProp(hk_mK,z|hk,y)),I3 hk_mK z)
      ≤ C4_1_7 X * volume (I3 hk y) by
    rw [C4_1_7_eq X] at this
    dsimp only [const_K] at this
    nth_rw 1 [pow_add 2 (4 * a) 1] at this
    rw [pow_one 2,Nat.cast_mul,Nat.cast_two] at this
    rw [mul_comm _ 2,mul_assoc] at this
    rw [ENNReal.mul_le_iff_le_inv (by norm_num) (by norm_num)] at this
    rw [← mul_assoc,mul_comm 2⁻¹ _,mul_assoc] at this
    simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.coe_pow, ENNReal.coe_ofNat] at this
    rw [← ENNReal.mul_le_mul_left]
    . exact this
    . exact Ne.symm (NeZero.ne' (2 ^ (4 * a)))
    . simp only [ne_eq, ENNReal.pow_eq_top_iff, ENNReal.two_ne_top, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, false_and, not_false_eq_true]
  letI : Countable (Yk X (k-K')) := (Yk_countable X (k-K')).to_subtype
  calc
    K' * ∑' (z : ↑(Yk X (k - K'))), volume (⋃ (_ : clProp(hk_mK,z|hk,y)), I3 hk_mK z)
      = ∑ (_:Ioc (k-K') k),
        ∑'(z:Yk X (k-K')),volume (⋃ (_ : clProp(hk_mK,z|hk,y)), I3 hk_mK z) := by
        -- have : K' = (Ioc (k-K') k).card := by sorry
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_ofFinset, Int.card_Ioc, sub_sub_cancel,
          Int.toNat_ofNat, nsmul_eq_mul]
    _ = ∑ (_:Ioc (k-K') k), volume (
        ⋃ (z:Yk X (k-K')),⋃ (_:clProp(hk_mK,z|hk,y)),I3 hk_mK z) := by
      apply Finset.sum_congr (rfl)
      intro x
      simp only [Finset.mem_univ, true_implies]
      symm
      refine measure_iUnion ?_ ?_
      . intro i i' hneq
        simp only [disjoint_iUnion_right, disjoint_iUnion_left]
        intro _ _
        rw [Set.disjoint_iff]
        intro x hx
        apply hneq
        exact I3_prop_1 hk_mK hx
      . intro i
        letI : Decidable (clProp(hk_mK,i|hk,y)):=
          Classical.propDecidable _
        rw [Set.iUnion_eq_if]
        if h:(clProp(hk_mK,i|hk,y)) then
          rw [if_pos h]
          exact I3_measurableSet hk_mK i
        else
          rw [if_neg h]
          exact MeasurableSet.empty
    _ ≤ ∑ (k':Ioc (k-K') k), volume (
        ⋃ (z ∈ {z':Yk X k'|clProp((le_s hk_mK k'),z'|hk,y)}), I3 (le_s hk_mK k') z) := by
      apply Finset.sum_le_sum
      simp only [Finset.mem_univ, mem_setOf_eq, true_implies, mem_Ioc]
      intro k'
      apply volume.mono
      simp only [iUnion_subset_iff]
      intro z hz x hx
      have : x ∈ I3 hk y := hz.I3_subset hx
      have : x ∈ ⋃ z, I3 (le_s hk_mK k') z:=
        cover_by_cubes (le_s hk_mK k') (k'.property.right) hk y this
      simp only [mem_iUnion] at this
      obtain ⟨y',hy'⟩ := this
      simp only [mem_iUnion, exists_prop]
      use y'
      constructor
      . apply And.right
        apply transitive_boundary hk_mK (le_s hk_mK k') hk k'.property.left k'.property.right z y' y
        simp only [mem_inter_iff]
        exact And.intro (And.intro hx hy') this
        exact hz
      exact hy'
    _ = ∑ (k':Ioc (k-K') k), ∑'(z:Yk X k'),
        volume (⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)), I3 (le_s hk_mK k') z) := by
      apply Finset.sum_congr (rfl)
      intro k'
      simp only [Finset.mem_univ, true_implies, ge_iff_le]
      letI := (Yk_countable X k').to_subtype
      refine measure_iUnion ?_ ?_
      . intro i i' hneq
        simp only [mem_setOf_eq, disjoint_iUnion_right, disjoint_iUnion_left]
        intro _ _
        rw [Set.disjoint_iff]
        intro x hx
        apply hneq
        apply I3_prop_1
        exact hx
      intro i
      apply MeasurableSet.iUnion
      intro _
      exact I3_measurableSet (le_s hk_mK k') i
    _ ≤ ∑ (k':Ioc (k-K') k),
        ∑'(z:Yk X k'), C4_1_7 X * volume (⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)),
        ball (z:X) (4⁻¹ * D^(k':ℤ))) := by
      apply Finset.sum_le_sum
      intro k'
      simp only [Finset.mem_univ, true_implies]
      apply tsum_le_tsum _ (ENNReal.summable) (ENNReal.summable)
      intro z
      letI : Decidable (clProp(le_s hk_mK k',z|hk,y)) := Classical.propDecidable _
      simp_rw [iUnion_eq_if,apply_ite volume,measure_empty]
      simp only [mul_ite, mul_zero]
      if h : clProp(le_s hk_mK k',z|hk,y) then
        rw [if_pos h,if_pos h]
        exact volume_tile_le_volume_ball (↑k') (le_s hk_mK k') z
      else
        rw [if_neg h,if_neg h]
    _ = C4_1_7 X * ∑ (k' : Ioc (k-K') k),
        ∑'(z:Yk X k'), volume (⋃ (_:clProp((le_s hk_mK k'),z|hk,y)),ball (z:X) (4⁻¹*D^(k':ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr (rfl)
      simp only [Finset.mem_univ, true_implies,]
      intro k'
      rw [ENNReal.tsum_mul_left]
    _ = C4_1_7 X * ∑ (k' : Ioc (k-K') k),
        volume (⋃ (z:Yk X k'),⋃ (_:clProp((le_s hk_mK k'),z|hk,y)),ball (z:X) (4⁻¹*D^(k':ℤ))) := by
      congr
      ext k'
      symm
      letI := (Yk_countable X k').to_subtype
      apply measure_iUnion
      . intro i i' hneq
        simp only [disjoint_iUnion_right, disjoint_iUnion_left]
        intro _ _
        apply Disjoint.mono
        . trans ball (i:X) (2⁻¹ * D^(k':ℤ))
          . apply ball_subset_ball
            apply mul_le_mul_of_nonneg_right _ (zpow_nonneg realD_nonneg _)
            apply le_of_mul_le_mul_right _ (by norm_num : (0:ℝ) < 4)
            norm_num
          apply I3_prop_3_1
          have := k'.property.left
          linarith
        . trans ball (i':X) (2⁻¹ * D^(k':ℤ))
          . apply ball_subset_ball
            apply mul_le_mul_of_nonneg_right _ (zpow_nonneg realD_nonneg _)
            apply le_of_mul_le_mul_right _ (by norm_num : (0:ℝ) < 4)
            norm_num
          apply I3_prop_3_1
          have := k'.property.left
          linarith
        rw [Set.disjoint_iff]
        intro x hx
        apply hneq
        apply I3_prop_1
        exact hx
      intro i
      apply MeasurableSet.iUnion
      intro _
      exact measurableSet_ball
    _ ≤ C4_1_7 X * ∑' (k' : Ioc (k-K') k),
        volume (⋃ (z:Yk X k'),⋃ (_:clProp((le_s hk_mK k'),z|hk,y)),ball (z:X) (4⁻¹*D^(k':ℤ))) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le (C4_1_7 X : ℝ≥0∞))
      exact ENNReal.sum_le_tsum Finset.univ
    _ = C4_1_7 X * volume (⋃ (k' : Ioc (k-K') k),
        ⋃ (z:Yk X k'),⋃ (_:clProp((le_s hk_mK k'),z|hk,y)),ball (z:X) (4⁻¹*D^(k':ℤ))) := by
      congr
      symm
      apply measure_iUnion
      . rw [Symmetric.pairwise_on]
        . intro l' l hl
          simp only [disjoint_iUnion_right, disjoint_iUnion_left]
          intro u hu u' hu'
          rw [Set.disjoint_iff]
          obtain ⟨x,hx⟩ := hu'.I3_compl_inter_ball
          intro x' hx'
          have : x ∈ ball (u:X) (2⁻¹ * D^(l:ℤ)) := by
            simp only [mem_inter_iff, mem_compl_iff, mem_ball] at hx hx' ⊢
            calc
              dist x (u:X)
                ≤ dist x (u':X) + dist (u':X) x' + dist x' (u:X) := dist_triangle4 x (↑u') x' ↑u
              _ < 6 * D^(l':ℤ ) + 4⁻¹ * D^(l':ℤ) + 4⁻¹ * D^(l:ℤ) := by
                rw [← dist_comm x' u']
                exact add_lt_add (add_lt_add hx.right hx'.left) hx'.right
              _ = 4⁻¹ * 25 * D^(l':ℤ) + 4⁻¹ * D^(l:ℤ) := by
                rw [← right_distrib]
                norm_num
              _ ≤ 4⁻¹ * D^(l:ℤ) + 4⁻¹ * D^(l:ℤ) := by
                rw [add_le_add_iff_right,mul_assoc]
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                trans D * D^(l':ℤ)
                . exact mul_le_mul_of_nonneg_right (twentyfive_le_realD X)
                    (zpow_nonneg realD_nonneg _)
                nth_rw 1 [← zpow_one (D:ℝ)]
                rw [← zpow_add₀ realD_pos.ne.symm]
                have : (l':ℤ) < l := hl
                exact zpow_le_of_le (one_le_realD X) (by linarith)
              _ = 2⁻¹ * D^(l:ℤ) := by
                rw [← two_mul _,← mul_assoc]
                norm_num
          have : x ∈ I3 hk y := by
            apply dyadic_property (le_s hk_mK l) (l.property.right) hk
            . rw [Set.not_disjoint_iff]
              use x, I3_prop_3_1 (le_s hk_mK l) u this
              apply hu.I3_subset
              exact I3_prop_3_1 (le_s hk_mK l) u this
            exact I3_prop_3_1 (le_s hk_mK l) u this
          exact hx.left this
        exact fun ⦃x y⦄ a ↦ id (Disjoint.symm a)
      intro k'
      letI := (Yk_countable X k').to_subtype
      apply MeasurableSet.iUnion
      intro b
      apply MeasurableSet.iUnion
      intro _
      exact measurableSet_ball
    _ ≤ C4_1_7 X * volume (I3 hk y) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le _)
      apply volume.mono
      simp only [mem_Ioc, iUnion_subset_iff]
      intro k' y' hy'
      intro x
      apply Subset.trans _ hy'.I3_subset
      apply Subset.trans _ (I3_prop_3_1 _ _)
      apply ball_subset_ball
      exact mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg realD_nonneg _)

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

lemma frequency_ball_cover :
    range Q ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 := by
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

lemma disjoint_frequency_cubes {f g : 𝓩 I} (h : (Ω₁ ⟨I, f⟩ ∩ Ω₁ ⟨I, g⟩).Nonempty) : f = g := by
  simp_rw [← not_disjoint_iff_nonempty_inter, Ω₁] at h
  contrapose! h
  apply Ω₁_aux_disjoint
  contrapose! h
  rwa [Fin.val_eq_val, Equiv.apply_eq_iff_eq] at h

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

lemma Ω₁_subset_ball (p : 𝔓 X) : Ω₁ p ⊆ ball_(p) (𝒬 p) C4_2_1 := by
  rw [Ω₁, Ω₁_aux]
  split_ifs
  · let z : Θ X := p.2
    have qz : 𝒬 p = z := rfl
    have zeq : z = p.2 := rfl
    simp only [qz, zeq, Fin.eta, Equiv.symm_apply_apply, sdiff_sdiff, diff_subset]
  · exact empty_subset _

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

end Construction

lemma 𝔓_induction (P : 𝔓 X → Prop) (base : ∀ p, IsMax p.1 → P p)
    (ind : ∀ p, ¬IsMax p.1 → (∀ z : 𝓩 p.1.succ, P ⟨p.1.succ, z⟩) → P p) :
    ∀ p, P p := fun p ↦ by
  by_cases h : IsMax p.1
  · exact base p h
  · have := Grid.opSize_succ_lt h
    exact ind p h fun z ↦ (𝔓_induction P base ind ⟨p.1.succ, z⟩)
termination_by p => p.1.opSize

lemma Ω_subset_cdist {p : 𝔓 X} : Construction.Ω p ⊆ ball_(p) (𝒬 p) 1 := by
  apply 𝔓_induction fun p ↦ Construction.Ω p ⊆ ball_(p) (𝒬 p) 1
  · intro p maxI ϑ mϑ
    rw [Construction.Ω] at mϑ; simp only [maxI, dite_true] at mϑ
    have : ball_(p) (𝒬 p) C4_2_1 ⊆ ball_(p) (𝒬 p) 1 := ball_subset_ball (by norm_num)
    exact mem_of_mem_of_subset mϑ ((Construction.Ω₁_subset_ball p).trans this)
  · intro p nmaxI ih ϑ mϑ
    rw [Construction.Ω] at mϑ; simp only [nmaxI, dite_false, mem_union] at mϑ
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
        gcongr; simpa using mem_of_mem_of_subset mz₂ (Construction.Ω₁_subset_ball ⟨I, ⟨y, my⟩⟩)
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

def tile_existence : TileStructure Q D κ S o where
  Ω := Construction.Ω
  biUnion_Ω := sorry
  disjoint_Ω := sorry
  relative_fundamental_dyadic {p q} hs := by
    rw [or_iff_not_imp_left]; intro hi
    sorry
  cdist_subset {p} := by
    rw [Construction.Ω]; split_ifs with hh
    · have : ball_(p) (𝒬 p) 5⁻¹ ⊆ ball_(p) (𝒬 p) C𝓩 := ball_subset_ball (by norm_num)
      exact this.trans (Construction.ball_subset_Ω₁ p)
    · simp
  subset_cdist {p} := Ω_subset_cdist
