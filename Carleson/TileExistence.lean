import Carleson.GridStructure
import Carleson.DoublingMeasure
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Subset

open Set MeasureTheory Metric Function Complex Bornology Notation
open scoped NNReal ENNReal ComplexConjugate

namespace ShortVariables
set_option hygiene false
scoped notation "D'" => (Real.toNNReal D)

end ShortVariables

noncomputable section

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

-- this still holds for more general parameters
lemma ball_bound (k : ℝ) (hk_lower : -S ≤ k) {Y : Set X} (hY : Y ⊆ ball o (4*D^S-D^k))
    (y : X) (hy : y ∈ Y):
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
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        exact Real.rpow_nonneg (defaultD_pos a).le _
    _ = ball y (8 * D^S) := by
      ring_nf -- this tactic is out of place C:
    _ ⊆ ball y (8 * D ^ (2 * S) * D ^ k) := by
      apply ball_subset_ball
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simp_rw [← Real.rpow_intCast]
      rw [← Real.rpow_add (defaultD_pos a)]
      apply Real.rpow_le_rpow_of_exponent_le (one_le_D X)
      simp only [Int.cast_mul, Int.cast_ofNat]
      rw [two_mul,add_assoc]
      simp only [le_add_iff_nonneg_right]
      rw [← sub_self (↑S),sub_eq_add_neg]
      exact add_le_add_left hk_lower _

section


lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
  if hfin : s.Finite then
    have hfin' : Finite s := by exact hfin
    rw [tsum_def]
    simp only [ENNReal.summable, ↓reduceDite]
    have hsup: support (fun (_ : s) ↦ (1 : ℝ≥0∞)) = Set.univ := by
      ext i
      simp only [mem_support, ne_eq, one_ne_zero, not_false_eq_true, mem_univ]
    have hsupfin: (Set.univ : Set s).Finite := by exact finite_univ
    rw [← hsup] at hsupfin
    rw [if_pos hsupfin]
    rw [hfin.encard_eq_coe_toFinset_card]
    simp only [ENat.toENNReal_coe]
    rw [Finset.card_eq_sum_ones]
    rw [finsum_eq_sum (fun (_ : s) ↦ (1 :ℝ≥0∞)) hsupfin]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_inj]
    apply Finset.card_bij (fun a _ => a.val)
    . intro a
      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
        Subtype.coe_prop, imp_self]
    . intro a _ a' _ heq
      ext
      exact heq
    . intro a ha
      use ⟨a,by
        simp only [Finite.mem_toFinset] at ha
        exact ha⟩
      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
        exists_const]
  else
  have : Infinite s := by exact infinite_coe_iff.mpr hfin
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)]
  rw [Set.encard_eq_top_iff.mpr hfin]
  simp only [ENat.toENNReal_top]

lemma tsum_const_eq' {α : Type*} (s : Set α) (c : ℝ≥0∞) :
    ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
  nth_rw 1 [← one_mul c]
  rw [ENNReal.tsum_mul_right,tsum_one_eq']

end

-- lemma tsum_top_eq


variable (X) in def J' : ℝ := 3 + 2 * S * 100 * a ^2

lemma twopow_J : 2 ^ J' X = 8 * D ^ (2 * S) := by
  dsimp [J']
  rw [Real.rpow_add, mul_assoc (2 * (S:ℝ)), mul_comm (2 * (S:ℝ)),Real.rpow_mul]
  . rw [← Real.rpow_intCast]
    simp only [Int.cast_mul, Int.cast_ofNat, mul_eq_mul_right_iff]
    left
    norm_num
  . norm_num
  norm_num


lemma twopow_J' : ((2 : ℝ≥0) ^ J' X : ℝ≥0) = 8 * D' ^ (2 * S) := by
  dsimp only [J', defaultD]
  rw [Real.toNNReal_rpow_of_nonneg]
  simp only [Real.toNNReal_ofNat]
  norm_num
  rw [NNReal.rpow_add,mul_assoc (2 * (S : ℝ )), mul_comm (2 * (S : ℝ))]
  congr 1
  . norm_num
  . rw [NNReal.rpow_mul]
    refine NNReal.eq ?_
    simp only [NNReal.coe_rpow, NNReal.coe_ofNat, NNReal.coe_zpow]
    rw [← Real.rpow_intCast]
    simp only [Int.cast_mul, Int.cast_ofNat]
  . norm_num
  norm_num

variable (X) in
def C4_1_1 := As (2 ^ a) (2 ^ J' X)

lemma counting_balls {k : ℝ} (hk_lower : -S ≤ k) {Y : Set X}
    (hY : Y ⊆ ball o (4*D^S-D^k))
    (hYdisjoint: Y.PairwiseDisjoint (fun y ↦ ball y (D^k))) :
    (Set.encard Y).toENNReal ≤ C4_1_1 X := by
  suffices (Set.encard Y).toENNReal * volume (ball o (4 * D^S)) ≤ (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D^S)) by
    have volume_pos : 0 < volume (ball o (4 * D^S)) := by
      apply measure_ball_pos volume o
      simp only [defaultD, gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      refine zpow_pos_of_pos ?ha S
      apply Real.rpow_pos_of_pos
      linarith
    have volume_finite : volume (ball o (4 * D^S)) < ⊤ := measure_ball_lt_top
    rw [← ENNReal.mul_le_mul_left volume_pos.ne.symm volume_finite.ne]
    rw [mul_comm,mul_comm (volume _)]
    exact this
  have val_ne_zero : (As (2 ^ a) (2 ^ J' X):ℝ≥0∞) ≠ 0 := (As_pos' X (2 ^J' X)).ne.symm
  calc
    (Y.encard).toENNReal * volume (ball o (4 * D ^ S))
      = ∑' (y : Y), volume (ball o (4 * D^S)) := by
      rw [tsum_const_eq']
    _ ≤ ∑' (y : Y), volume (ball (y : X) (8 * D ^ (2 * S) * D^k)) := by
      apply tsum_le_tsum _ ENNReal.summable ENNReal.summable
      intro ⟨y,hy⟩
      apply volume.mono
      simp only
      exact ball_bound k hk_lower hY y hy
    _ ≤ ∑' (y : Y), (As (2 ^ a) (2 ^ J' X)) * volume (ball (y : X) (D^k)) := by
      apply tsum_le_tsum _ ENNReal.summable ENNReal.summable
      intro ⟨y,hy⟩
      rw [← twopow_J]
      simp only
      apply volume_ball_le_same'
      . exact Real.rpow_pos_of_pos (by linarith) _
      . exact le_refl _
    _ ≤ (As (2 ^ a) (2 ^ J' X)) * ∑' (y : Y), volume (ball (y : X) (D^k)):= by
      rw [ENNReal.tsum_mul_left]
    _ = (As (2 ^ a) (2 ^ J' X)) * volume (⋃ y ∈ Y, ball y (D^k)) := by
      rw [ENNReal.mul_eq_mul_left val_ne_zero ENNReal.coe_ne_top]
      . rw [measure_biUnion _ hYdisjoint (fun y _ => measurableSet_ball)]
        apply hYdisjoint.countable_of_isOpen (fun y _ => isOpen_ball)
        intro y _
        use y
        simp only [mem_ball, dist_self]
        exact Real.rpow_pos_of_pos (defaultD_pos a) _
    _ ≤ (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D ^ S)) := by
      rw [ENNReal.mul_le_mul_left val_ne_zero ENNReal.coe_ne_top]
      apply volume.mono
      rw [iUnion₂_subset_iff]
      intro y hy z hz
      specialize hY hy
      simp only [mem_ball] at hY hz ⊢
      calc
        dist z o
          ≤ dist z y + dist y o := by exact dist_triangle z y o
        _ < D^k + (4 * D^S - D^k) := by
          apply add_lt_add hz hY
        _ = 4 * D ^ S := by
          rw [add_sub_cancel]


variable (X) in
def property_set (k : ℤ) : Set (Set X) :=
  {s| s ⊆ ball o (4 * D^S - D^(k : ℝ)) ∧ s.PairwiseDisjoint (fun y => ball y (D^(k:ℝ)))}

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
      simp only [mem_setOf_eq] at hc
      exact hc.left
    . intro x hx y hy
      simp only [mem_iUnion, exists_prop] at hx hy
      obtain ⟨sx,hsx, hsx'⟩ := hx
      obtain ⟨sy,hsy, hsy'⟩ := hy
      obtain hxy|hyx := hchain.total hsx hsy
      . specialize hxy hsx'
        specialize hc hsy
        simp only [mem_setOf_eq] at hc
        exact hc.right hxy hsy'
      . specialize hyx hsy'
        specialize hc hsx
        simp only [mem_setOf_eq] at hc
        exact hc.right hsx' hyx
  . exact fun s a ↦ subset_iUnion₂_of_subset s a fun ⦃a⦄ a ↦ a

variable (X) in
def zorn_apply_maximal_set (k : ℤ):
    ∃ s ∈ property_set X k, ∀ s' ∈ property_set X k, s ⊆ s' → s' = s :=
  zorn_subset (property_set X k) (chain_property_set_has_bound X k)

variable (X) in
def Yk (k : ℤ): Set X := (zorn_apply_maximal_set X k).choose

lemma Yk_pairwise (k:ℤ) : (Yk X k).PairwiseDisjoint (fun (y:X) ↦ ball y (D^(k:ℝ))) :=
  (zorn_apply_maximal_set X k).choose_spec.left.right

lemma Yk_subset (k:ℤ) : Yk X k ⊆ ball o (4 * D^S - D^(k : ℝ)) :=
  (zorn_apply_maximal_set X k).choose_spec.left.left

lemma Yk_maximal (k : ℤ) {s :Set X} (hs_sub : s ⊆ ball o (4 * D^S - D^(k : ℝ)))
    (hs_pairwise : s.PairwiseDisjoint (fun y ↦ ball y (D^(k:ℝ)))) (hmax_sub : Yk X k ⊆ s):
    s = Yk X k :=
  (zorn_apply_maximal_set X k).choose_spec.right _ (And.intro hs_sub hs_pairwise) hmax_sub

lemma cover_big_ball (k : ℤ) : ball o (4 * D^S - D^k) ⊆ ⋃ y ∈ Yk X k, ball y (2 * D^k) := by
  rw [← Real.rpow_intCast D k]
  intro y hy
  have : ∃ z ∈ Yk X k, ¬Disjoint (ball y (D^(k:ℝ))) (ball z (D^(k:ℝ))) := by
    by_contra hcon
    apply hcon
    push_neg at hcon
    suffices hmem : y ∈ Yk X k by
      use y, hmem
      simp only [disjoint_self, bot_eq_empty, ball_eq_empty, not_le]
      apply Real.rpow_pos_of_pos (defaultD_pos a) k
    suffices (Yk X k) ∪ {y} = Yk X k by
      simp only [union_singleton, insert_eq_self] at this
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
  simp only [mem_ball] at hx hx'
  rw [dist_comm] at hx
  apply (dist_triangle y x z).trans_lt
  rw [two_mul]
  apply add_lt_add hx hx'

variable (X) in
lemma Yk_nonempty {k : ℤ} (hmin : 0 < 4 * D^S - D^k) : (Yk X k).Nonempty := by

  have : o ∈ ball o (4 * D^S - D^k) := mem_ball_self hmin
  have h1 : {o} ⊆ ball o (4 * D^S - D^k) := singleton_subset_iff.mpr this
  have h2 : ({o} : Set X).PairwiseDisjoint (fun y ↦ ball y (D^k)) :=
    pairwiseDisjoint_singleton o fun y ↦ ball y (D ^ k)
  rw [← Real.rpow_intCast D k] at h1 h2
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
  have hk_lower' : (-S : ℝ) ≤ k := by
    rw [← Int.cast_neg,Int.cast_le]
    exact hk_lower
  calc
    ((Yk X k).encard : ℝ≥0∞)
      ≤ C4_1_1 X := counting_balls hk_lower' (Yk_subset k) (Yk_pairwise k)
    _ < ⊤ := ENNReal.coe_lt_top

lemma Yk_countable {k:ℤ} : (Yk X k).Countable := by
  apply (Yk_pairwise k).countable_of_isOpen (fun y _ => isOpen_ball)
  simp only [nonempty_ball]
  exact fun y _ => Real.rpow_pos_of_pos (defaultD_pos a) k

variable (X) in
def Yk_encodable (k:ℤ) : Encodable (Yk X k) := (Yk_countable).toEncodable

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
      ball y (D^(-S))
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
      ball y (2 * D^(-S))
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
    nth_rw 1 [← one_mul (D^(-S))]
    exact mul_le_mul_of_nonneg_right (by linarith) (zpow_nonneg (defaultD_pos a).le _)
  else
    rw [dif_neg hk_s, dif_neg hk_s]
    simp only [iUnion_subset_iff]
    intro y' hy' z hz
    simp only [mem_iUnion, exists_prop, exists_and_left]
    use y'
    rw [and_iff_left hz]
    revert hy'
    apply ball_subset_ball
    nth_rw 1 [← one_mul (D^k)]
    apply mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg (defaultD_pos a).le _)

lemma I3_subset_I2 {k:ℤ} (hk : -S ≤ k) (y:Yk X k):
    I3 hk y ⊆ I2 hk y := by
  intro x hx
  rw [I3] at hx
  simp only [ mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
    not_and] at hx
  obtain l|r := hx
  . exact I1_subset_I2 hk y l
  . exact r.left

-- variable (X) in
-- lemma Yk_mono {k:ℤ} : Yk X k ⊆

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
      simp only [Real.rpow_intCast]
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
      simp only [Real.rpow_intCast]
      exact And.intro hz1 hz2
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
    exact mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg (defaultD_pos a).le _)
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
        rw [zpow_add₀ (defaultD_pos a).ne.symm _ 1,zpow_one,mul_comm _ D]
        apply mul_le_mul_of_nonneg_right (four_le_D X) (zpow_nonneg (defaultD_pos a).le _)
      _ ≤ 4 * D ^ k := by
        rw [sub_add_cancel,← right_distrib]
        apply mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg (defaultD_pos a).le _)
termination_by (S + k).toNat

mutual
  lemma I2_prop_2 {k:ℤ} (hk : -S ≤ k) :
      ball o (4 * D^S - 2 * D^k) ⊆ ⋃ (y:Yk X k), I2 hk y := by
    simp only [I2, mem_preimage, iUnion_coe_set]
    if hk_s : k = -S then
      simp_rw [dif_pos hk_s]
      subst hk_s
      calc
        ball o (4 * D^S - 2 * (D^(-S)))
          ⊆ ball o (4 * D^S - D^(-S)) := by
            apply ball_subset_ball
            rw [two_mul,tsub_le_iff_right,sub_add_add_cancel,le_add_iff_nonneg_right]
            exact zpow_nonneg (defaultD_pos a).le _
        _ ⊆ ⋃ (i ∈ Yk X (-S)), ball i (2 * D^(-S)) := cover_big_ball (-S)
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
              exact zpow_le_of_le (one_le_D X) (by linarith)
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
            exact mul_le_mul_of_nonneg_right (four_le_D X) (zpow_nonneg (defaultD_pos a).le _)
          _ = ball (y': X) (D^k) := by
            nth_rw 1 [← zpow_one D,← zpow_add₀ (defaultD_pos a).ne.symm,add_sub_cancel]
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
    nth_rw 2 [← one_mul (D^(-S))]
    exact mul_le_mul_of_nonneg_right (by norm_num) (zpow_nonneg (defaultD_pos a).le _)
  else
    rw [dif_neg hk_s]
    simp only [mem_preimage]
    have : (y:X) ∈ ball o (4 * D^S-D^k) := by
      nth_rw 2 [← Real.rpow_intCast]
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
            2⁻¹ * D ^ k + 2 * D ^ (k - 1)
              = 2⁻¹ * D^(k) + 2⁻¹ * 4 * D^(k-1) := by
                rw [add_right_inj]
                norm_num
            _ ≤ 2⁻¹ * (2 * D ^ k) := by
              rw [mul_assoc,← left_distrib]
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              rw [two_mul]
              apply add_le_add_left
              nth_rw 2 [← add_sub_cancel 1 k]
              rw [zpow_add₀ (defaultD_pos a).ne.symm,zpow_one]
              exact mul_le_mul_of_nonneg_right (four_le_D X) (zpow_nonneg (defaultD_pos a).le _)
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
          rw [zpow_add₀ (defaultD_pos a).ne.symm,zpow_one]
          exact mul_le_mul_of_nonneg_right (eight_le_D X) (zpow_nonneg (defaultD_pos a).le _)
        _ = D ^ k := by
          rw [← two_mul,← mul_assoc,inv_mul_cancel (by norm_num),one_mul]
    rw [mem_iUnion]
    use y'
    rw [mem_iUnion]
    use this

end basic_grid_structure

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
      rw [I2, dif_neg hk_not_neg_s] at hx_mem_i2
      simp only [mem_preimage, mem_iUnion, exists_prop,
        exists_and_left] at hx_mem_i2
      obtain ⟨u,hu,hxu⟩ := hx_mem_i2
      obtain rfl : y'' = u := by
        apply I3_prop_1 (I_induction_proof hk hk_not_neg_s)
        use hy''
      intro x' hx'
      rw [I3]
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and]
      right
      constructor
      . rw [I2, dif_neg hk_not_neg_s]
        simp only [mem_preimage, mem_iUnion, exists_prop,
          exists_and_left]
        use y''
      constructor
      . sorry
      intro u hu
      rw [I3]
      simp only [iUnion_coe_set, mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and, not_forall, Classical.not_imp, Decidable.not_not]
      constructor
      . rw [I1, dif_neg hk_not_neg_s]
        sorry

      sorry
  termination_by ((-l + k).toNat)


/-! Proof that there exists a grid structure. -/
-- Note: we might want to slightly adapt the construction so that there is only 1 tile at level S
-- with center `o` (then we might not cover all of `ball o (D ^ S)`, but most of it)
def grid_existence : GridStructure X D κ S o :=
  sorry

/-! Proof that there exists a tile structure on a grid structure. -/

variable [GridStructure X D κ S o] {I : 𝓓 X}


/-- Use Zorn's lemma to define this. -/
-- Note: we might want to adapt the construction so that 𝓩 is a subset of `range Q`.
-- We only need to cover `range Q`, not all the balls of radius 1 around it. If that works, that
-- should simplify it, and might mean that we don't need Lemma 2.1.1 here.
def 𝓩 (I : 𝓓 X) : Set (Θ X) := sorry

/-- The constant appearing in 4.2.2. -/
@[simp] def C𝓩 : ℝ := 3 / 10

lemma 𝓩_subset : 𝓩 I ⊆ ⋃ f ∈ range Q, ball_{I} f 1 := sorry
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
    (h𝓩' : 𝓩' ⊆ ⋃ f ∈ range Q, ball_{I} f 1)
    (h2𝓩' : ∀ {f g : Θ X} (hf : f ∈ 𝓩') (hg : g ∈ 𝓩') (hfg : f ≠ g),
      Disjoint (ball_{I} f C𝓩) (ball_{I} g C𝓩)) : Nat.card 𝓩' ≤ Nat.card (𝓩 I) := by
  sorry

lemma maximal_𝓩 {𝓩' : Set (Θ X)}
    (h𝓩' : 𝓩' ⊆ ⋃ f ∈ range Q, ball_{I} f 1)
    (h2𝓩' : ∀ {f g : Θ X} (hf : f ∈ 𝓩') (hg : g ∈ 𝓩') (hfg : f ≠ g),
      Disjoint (ball_{I} f C𝓩) (ball_{I} g C𝓩)) (h𝓩 : 𝓩 I ⊆ 𝓩') : 𝓩 I = 𝓩' := by
  sorry

instance : Fintype (𝓩 I) := sorry
instance : Inhabited (𝓩 I) := sorry

def C4_2_1 : ℝ := 7 / 10 /- 0.6 also works? -/

lemma frequency_ball_cover :
    ⋃ x : X, ball_{I} (Q x) 1 ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 := by
  intro θ hθ
  have : ∃ z, z ∈ 𝓩 I ∧ ¬ Disjoint (ball_{I} z C𝓩) (ball_{I} θ C𝓩) := by
    by_contra! h
    have hθ' : θ ∉ 𝓩 I := by
      intro hθ'
      have := h _ hθ'
      simp only [C𝓩, disjoint_self, bot_eq_empty, ball_eq_empty] at this
      norm_num at this
    let 𝓩' := insert θ (𝓩 I)
    have h𝓩' : 𝓩' ⊆ ⋃ f ∈ range Q, ball_{I} f 1 := by
      rw [insert_subset_iff]
      exact ⟨by simpa using hθ, 𝓩_subset⟩
    have h2𝓩' : 𝓩'.PairwiseDisjoint (ball_{I} · C𝓩) := by
      rw [pairwiseDisjoint_insert_of_not_mem hθ']
      refine ⟨𝓩_disj', ?_⟩
      intro j hj
      exact (h j hj).symm
    have := maximal_𝓩 h𝓩' (fun hf hg => h2𝓩' hf hg)
    simp only [subset_insert, true_implies, 𝓩'] at this
    rw [eq_comm, insert_eq_self] at this
    exact hθ' this
  obtain ⟨z, hz, hz'⟩ := this
  rw [Set.not_disjoint_iff] at hz'
  obtain ⟨z', h₁z', h₂z'⟩ := hz'
  simp only [mem_iUnion, mem_ball, exists_prop, C𝓩, C4_2_1] at h₁z' h₂z' ⊢
  exact ⟨z, hz, by linarith [dist_triangle_left θ z z']⟩

local instance tileData_existence [GridStructure X D κ S o] :
    PreTileStructure D κ S o where
  𝔓 := Σ I : 𝓓 X, 𝓩 I
  fintype_𝔓 := Sigma.instFintype
  𝓘 p := p.1
  surjective_𝓘 I := ⟨⟨I, default⟩, rfl⟩
  𝒬 p := p.2

namespace Construction

def Ω₁_aux (I : 𝓓 X) (k : ℕ) : Set (Θ X) :=
  if hk : k < Nat.card (𝓩 I) then
    let z : Θ X := (Finite.equivFin (𝓩 I) |>.symm ⟨k, hk⟩).1
    ball_{I} z C4_2_1 \ (⋃ i ∈ 𝓩 I \ {z}, ball_{I} z C𝓩) \ ⋃ i < k, Ω₁_aux I i
  else
    ∅

def Ω₁ (p : 𝔓 X) : Set (Θ X) := Ω₁_aux p.1 (Finite.equivFin (𝓩 p.1) p.2)

lemma disjoint_frequency_cubes {f g : 𝓩 I} (h : (Ω₁ ⟨I, f⟩ ∩ Ω₁ ⟨I, g⟩).Nonempty) : f = g := sorry

lemma iUnion_ball_subset_iUnion_Ω₁ :
  ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 ⊆ ⋃ f : 𝓩 I, Ω₁ ⟨I, f⟩ := sorry

lemma ball_subset_Ω₁ (p : 𝔓 X) : ball_(p) (𝒬 p) C𝓩 ⊆ Ω₁ p := sorry

lemma Ω₁_subset_ball (p : 𝔓 X) : Ω₁ p ⊆ ball_(p) (𝒬 p) C𝓩 := sorry

def CΩ : ℝ := 1 / 5

open Classical in
def Ω (p : 𝔓 X) : Set (Θ X) :=
  if h : IsMax p.1 then Ω₁ p else
  have := 𝓓.opSize_succ_lt h
  ball_(p) (𝒬 p) CΩ ∪ ⋃ (z : Θ X) (hz : z ∈ 𝓩 p.1.succ ∩ Ω₁ p), Ω ⟨p.1.succ, ⟨z, hz.1⟩⟩
termination_by p.1.opSize

end Construction

def tile_existence [GridStructure X D κ S o] :
    TileStructure Q D κ S o where
      Ω := Construction.Ω
      biUnion_Ω := sorry
      disjoint_Ω := sorry
      relative_fundamental_dyadic := sorry
      cdist_subset := sorry
      subset_cdist := sorry
