import Carleson.TileStructure

open Set MeasureTheory Metric Function Complex Bornology Notation
open scoped NNReal ENNReal ComplexConjugate

noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma realD_nonneg : 0 ≤ (D:ℝ) := (defaultD_pos a).le

lemma ball_bound {Y : Set X} (k : ℤ) (hk_lower : -S ≤ k)
    (hY : Y ⊆ ball o (4 * D ^ (S : ℤ) - D ^ k)) (y : X) (hy : y ∈ Y) :
    ball o (4 * D ^ (S : ℤ)) ⊆ ball y (8 * D ^ (2 * S : ℤ) * D ^ k) := by
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
        gcongr
        rw [← zpow_add₀ (defaultD_pos a).ne.symm]
        apply zpow_le_zpow_right₀ (one_le_realD X)
        linarith

-- lemma tsum_top_eq

variable (X) in def J' : ℕ := 3 + 2 * S * 𝕔 * a ^ 2

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
    (hY : Y ⊆ ball o (4 * D ^ S - D ^ k))
    (hYdisjoint : Y.PairwiseDisjoint (ball · (D ^ k))) :
    (Set.encard Y).toENNReal ≤ C4_1_1 X := by
  suffices (Set.encard Y).toENNReal * volume (ball o (4 * D ^ S)) ≤
      (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D ^ S)) by
    have volume_pos : 0 < volume (ball o (4 * D ^ S)) := by
      apply measure_ball_pos volume o
      simp only [defaultD, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      exact zpow_pos (by positivity) S
    rw [← ENNReal.mul_le_mul_left volume_pos.ne.symm (by finiteness), mul_comm,mul_comm (volume _)]
    exact this
  have val_ne_zero : (As (2 ^ a) (2 ^ J' X) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (As_pos' (volume : Measure X) (2 ^ J' X)).ne.symm
  calc
    (Y.encard).toENNReal * volume (ball o (4 * D ^ S))
      = ∑' (y : Y), volume (ball o (4 * D ^ S)) := by rw [ENNReal.tsum_const_eq']
    _ ≤ ∑' (y : Y), volume (ball (y : X) (8 * D ^ (2 * S) * D ^ k)) :=
      ENNReal.summable.tsum_le_tsum (fun ⟨y, hy⟩ ↦ volume.mono (ball_bound k hk_lower hY y hy))
        ENNReal.summable
    _ ≤ ∑' (y : Y), (As (2 ^ a) (2 ^ J' X)) * volume (ball (y : X) (D ^ k)) := by
      apply ENNReal.summable.tsum_le_tsum _ ENNReal.summable
      intro y hy
      rw_mod_cast [← twopow_J]
      apply measure_ball_le_same _ (by positivity) (le_refl _)
    _ ≤ (As (2 ^ a) (2 ^ J' X)) * ∑' (y : Y), volume (ball (y : X) (D ^ k)):= by
      rw [ENNReal.tsum_mul_left]
    _ = (As (2 ^ a) (2 ^ J' X)) * volume (⋃ y ∈ Y, ball y (D ^ k)) := by
      rw [ENNReal.mul_right_inj val_ne_zero ENNReal.coe_ne_top]
      · rw [measure_biUnion _ hYdisjoint (fun y _ => measurableSet_ball)]
        apply hYdisjoint.countable_of_isOpen (fun y _ => isOpen_ball)
        intro y _
        use y
        rw [mem_ball, dist_self]
        exact zpow_pos (defaultD_pos a) _
    _ ≤ (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D ^ S)) := by
        gcongr
        rw [iUnion₂_subset_iff]
        intro y hy z hz
        specialize hY hy
        simp only [mem_ball] at hY hz ⊢
        calc
          dist z o
          _ ≤ dist z y + dist y o := dist_triangle z y o
          _ < D ^ k + (4 * D ^ S - D ^ k) := add_lt_add hz hY
          _ = 4 * D ^ S := by rw [add_sub_cancel]

variable (X) in
def property_set (k : ℤ) : Set (Set X) :=
  {s | s ⊆ ball o (4 * D ^ S - D ^ k : ℝ) ∧
       s.PairwiseDisjoint (fun y => ball y (D^k:ℝ)) ∧ (k = S → o ∈ s)}

variable (X) in
lemma property_set_nonempty (k : ℤ) : (if k = S then {o} else ∅) ∈ property_set X k := by
  dsimp only [property_set]
  split
  · simp only [mem_setOf_eq, singleton_subset_iff, mem_ball, dist_self, sub_pos,
    pairwiseDisjoint_singleton, mem_singleton_iff, implies_true, and_self, and_true]
    rename_i hk
    rw [hk,zpow_natCast, lt_mul_iff_one_lt_left (pow_pos (defaultD_pos a) _)]
    norm_num
  simp only [mem_setOf_eq, empty_subset, pairwiseDisjoint_empty, mem_empty_iff_false, imp_false,
    true_and]
  assumption

variable (X) in
lemma chain_property_set_has_bound (k : ℤ) :
    ∀ c ⊆ property_set X k, IsChain (· ⊆ ·) c →
      ∃ ub ∈ property_set X k, ∀ s ∈ c, s ⊆ ub := by
  intro c hc hchain
  use (⋃ s ∈ c,s) ∪ (if k = S then {o} else ∅)
  if h : c = ∅ then
    simp only [h, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, defaultA, empty_union,
      false_implies, implies_true, and_true]
    exact property_set_nonempty X k
  else
  have h : ∃ z, z ∈ c := by
    rw [Set.ext_iff] at h
    push_neg at h
    simp only [mem_empty_iff_false, not_false_eq_true, and_true, and_false, or_false] at h
    exact h
  have : (⋃ s ∈ c,s) ∪ (if k = S then ({o}:Set X) else ∅) = (⋃ s ∈ c,s) := by
    ext x
    rw [mem_union,mem_iUnion]
    constructor
    · rintro (l|r)
      · exact l
      simp only [mem_ite_empty_right, mem_singleton_iff] at r
      obtain ⟨z,hz⟩ := h
      rw [r.right]
      simp only [mem_iUnion, exists_prop]
      use z, hz
      specialize hc hz
      dsimp only [property_set] at hc
      rw [mem_setOf_eq] at hc
      exact hc.right.right r.left
    · exact fun hex ↦ Or.intro_left (x ∈ if k = ↑S then {o} else ∅) hex
  simp_rw [this]
  dsimp only [property_set] at hc ⊢
  simp only [mem_setOf_eq, iUnion_subset_iff]
  constructor
  · constructor
    · intro i hi
      specialize hc hi
      rw [mem_setOf_eq] at hc
      exact hc.left
    constructor
    · intro x hx y hy
      simp only [mem_iUnion, exists_prop] at hx hy
      obtain ⟨sx,hsx, hsx'⟩ := hx
      obtain ⟨sy,hsy, hsy'⟩ := hy
      obtain hxy|hyx := hchain.total hsx hsy
      · specialize hxy hsx'
        specialize hc hsy
        rw [mem_setOf_eq] at hc
        exact hc.right.left hxy hsy'
      · specialize hyx hsy'
        specialize hc hsx
        rw [mem_setOf_eq] at hc
        exact hc.right.left hsx' hyx
    · obtain ⟨x,hx⟩ := h
      intro hk
      simp only [defaultA, mem_iUnion, exists_prop]
      use x, hx
      specialize hc hx
      rw [mem_setOf_eq] at hc
      exact hc.right.right hk
  · exact fun s a ↦ subset_iUnion₂_of_subset s a fun ⦃a⦄ a ↦ a

variable (X) in
lemma zorn_apply_maximal_set (k : ℤ) :
    ∃ s ∈ property_set X k, ∀ s' ∈ property_set X k, s ⊆ s' → s' = s := by
  have := zorn_subset (property_set X k) (chain_property_set_has_bound X k)
  simp_rw [maximal_iff] at this; convert this using 6; exact eq_comm

variable (X) in
def Yk (k : ℤ) : Set X := (zorn_apply_maximal_set X k).choose

lemma Yk_pairwise (k : ℤ) : (Yk X k).PairwiseDisjoint (ball · (D ^ k)) :=
  (zorn_apply_maximal_set X k).choose_spec.left.right.left

lemma Yk_subset (k : ℤ) : Yk X k ⊆ ball o (4 * D ^ S - D ^ k) :=
  (zorn_apply_maximal_set X k).choose_spec.left.left

lemma Yk_maximal (k : ℤ) {s : Set X} (hs_sub : s ⊆ ball o (4 * D ^ S - D ^ k))
    (hs_pairwise : s.PairwiseDisjoint (ball · (D ^ k))) (hmax_sub : Yk X k ⊆ s)
    (hk_s : k = S → o ∈ s) : s = Yk X k :=
  (zorn_apply_maximal_set X k).choose_spec.right _
    (And.intro hs_sub (And.intro hs_pairwise hk_s)) hmax_sub

lemma o_mem_Yk_S : o ∈ Yk X S :=
  (zorn_apply_maximal_set X S).choose_spec.left.right.right rfl

lemma cover_big_ball (k : ℤ) : ball o (4 * D ^ S - D ^ k) ⊆ ⋃ y ∈ Yk X k, ball y (2 * D ^ k) := by
  intro y hy
  have : ∃ z ∈ Yk X k, ¬Disjoint (ball y (D^k:ℝ)) (ball z (D^k:ℝ)) := by
    by_contra hcon
    apply hcon
    push_neg at hcon
    suffices hmem : y ∈ Yk X k by
      use y, hmem
      rw [disjoint_self, bot_eq_empty, ball_eq_empty, not_le]
      apply zpow_pos (by exact_mod_cast defaultD_pos a) k
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
      intro z hz _
      specialize hcon z hz
      exact hcon.symm
    · exact subset_union_left
    intro h
    rw [h]
    left
    exact o_mem_Yk_S
  obtain ⟨z,hz,hz'⟩ := this
  simp only [mem_iUnion, mem_ball, exists_prop]
  use z, hz
  rw [Set.not_disjoint_iff] at hz'
  obtain ⟨x,hx,hx'⟩ := hz'
  rw [mem_ball, dist_comm] at hx
  rw [two_mul]
  exact (dist_triangle y x z).trans_lt (add_lt_add hx hx')

variable (X) in
lemma Yk_nonempty {k : ℤ} (hmin : (0 : ℝ) < 4 * D ^ S - D ^ k) : (Yk X k).Nonempty := by
  have : o ∈ ball o (4 * D^S - D^k) := mem_ball_self hmin
  have h1 : {o} ⊆ ball o (4 * D^S - D^k) := singleton_subset_iff.mpr this
  have h2 : ({o} : Set X).PairwiseDisjoint (fun y ↦ ball y (D^k)) :=
    pairwiseDisjoint_singleton o fun y ↦ ball y (D ^ k)
  by_contra hcon
  apply hcon
  push_neg at hcon
  use o
  have hsuper : (Yk X k) ⊆ {o} := hcon ▸ empty_subset {o}
  have : {o} = Yk X k := Yk_maximal _ h1 h2 hsuper (fun _ => rfl)
  rw [← this]
  trivial

-- not sure if we actually need this; just countability seems quite good enough
lemma Yk_finite {k : ℤ} (hk_lower : -S ≤ k) : (Yk X k).Finite := by
  rw [← Set.encard_ne_top_iff]
  apply LT.lt.ne
  rw [← ENat.toENNReal_lt,ENat.toENNReal_top]
  calc
    ((Yk X k).encard : ℝ≥0∞)
      ≤ C4_1_1 X := counting_balls hk_lower (Yk_subset k) (Yk_pairwise k)
    _ < ⊤ := by finiteness

variable (X) in
lemma Yk_countable (k : ℤ) : (Yk X k).Countable := by
  apply (Yk_pairwise k).countable_of_isOpen (fun y _ => isOpen_ball)
  simp only [nonempty_ball]
  exact fun y _ ↦ zpow_pos (defaultD_pos a) k

variable (X) in
def Yk_encodable (k : ℤ) : Encodable (Yk X k) := (Yk_countable X k).toEncodable

def Encodable.linearOrder {α : Type*} (i : Encodable α) : LinearOrder α :=
  LinearOrder.lift' (i.encode) (i.encode_injective)

instance {k : ℤ} : LinearOrder (Yk X k) := (Yk_encodable X k).linearOrder
instance {k : ℤ} : WellFoundedLT (Yk X k) where
  wf := by
    apply (@OrderEmbedding.wellFounded (Yk X k) ℕ)
    · use ⟨(Yk_encodable X k).encode,(Yk_encodable X k).encode_injective⟩
      simp only [Embedding.coeFn_mk, Subtype.forall]
      exact fun i hi j hj ↦ by rfl
    exact wellFounded_lt

local instance {k : ℤ} : SizeOf (Yk X k) where
  sizeOf := (Yk_encodable X k).encode

lemma I_induction_proof {k : ℤ} (hk : -S ≤ k) (hneq : ¬k = -S) : -S ≤ k - 1 := by
  linarith [lt_of_le_of_ne hk fun a_1 ↦ hneq (id a_1.symm)]

-- Auxiliary lemma used in subsequent mutual blocks.
theorem aux {s k : ℤ} (h1 : 0 ≤ s + (k - 1)) :
    (s + (k - 1)).toNat < (s + k).toNat := by
  rw [Int.lt_toNat, Int.toNat_of_nonneg h1]
  linarith

mutual
  def I1 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) : Set X :=
    if hk': k = -S then
      ball y (D^(-S:ℤ))
    else
      let hk'' : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk' (id a_1.symm)
      have h1 : 0 ≤ S + (k - 1) := by linarith
      ⋃ (y': Yk X (k-1)),
        ⋃ (_ : y' ∈ Yk X (k-1) ↓∩ ball (y:X) (D^k)), I3 (I_induction_proof hk hk') y'
  termination_by (3 * (S+k).toNat, sizeOf y)

  def I2 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) : Set X :=
    if hk': k = -S then
      ball y (2 * D^(-S:ℤ))
    else
      ⋃ (y':Yk X (k-1)),
        ⋃ (_ : y' ∈ Yk X (k-1) ↓∩ ball y (2 * D^k)), I3 (I_induction_proof hk hk') y'
  termination_by (3 * (S+k).toNat, sizeOf y)

  def Xk {k:ℤ} (hk : -S ≤ k) : Set X := ⋃ (y' : Yk X k), I1 hk y'
  termination_by (3 * (S+k).toNat + 1, 0)

  def I3 {k:ℤ} (hk : -S ≤ k) (y:Yk X k) : Set X :=
    I1 hk y ∪ (I2 hk y \ (Xk hk ∪ ⋃ (y' < y), I3 hk y'))
  termination_by (3 * (S+k).toNat + 2, sizeOf y)
end

lemma I3_apply {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    I3 hk y = I1 hk y ∪ (I2 hk y \ (Xk hk ∪ ⋃ (y' < y), I3 hk y')) := by
  rw [I3]

lemma I1_subset_I3 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    I1 hk y ⊆ I3 hk y := by
  intro i hi
  rw [I3]
  left
  exact hi

lemma I1_subset_I2 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    I1 hk y ⊆ I2 hk y := by
  rw [I1, I2]
  split_ifs with hk_s
  · intro y'
    apply ball_subset_ball
    nth_rw 1 [← one_mul (D^(-S:ℤ):ℝ)]
    gcongr
    norm_num
  · simp only [iUnion_subset_iff]
    intro y' hy' z hz
    simp only [mem_iUnion, exists_prop]
    use y'
    rw [and_iff_left hz]
    apply ball_subset_ball _ hy'
    nth_rw 1 [← one_mul (D^k : ℝ)]
    gcongr
    norm_num

lemma I3_subset_I2 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    I3 hk y ⊆ I2 hk y := by
  intro x hx
  rw [I3] at hx
  simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
    not_and] at hx
  obtain l|r := hx
  · exact I1_subset_I2 hk y l
  · exact r.left

mutual
  lemma I1_measurableSet {k : ℤ} (hk : -S ≤ k) (y : Yk X k) : MeasurableSet (I1 hk y) := by
    if hk_s : k = -S then
      rw [I1, dif_pos hk_s]
      exact measurableSet_ball
    else
      let hk'' : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk_s (id a_1.symm)
      have h1: 0 ≤ S + (k - 1) := by linarith
      rw [I1, dif_neg hk_s]
      letI := (Yk_countable X (k - 1)).to_subtype
      refine MeasurableSet.biUnion (to_countable (Yk X (k - 1) ↓∩ ball y (D ^ k))) ?_
      simp only [mem_preimage]
      exact fun b _ ↦ I3_measurableSet (I_induction_proof hk hk_s) b
  termination_by (3 * (S+k).toNat, sizeOf y)

  lemma I2_measurableSet {k : ℤ} (hk : -S ≤ k) (y : Yk X k) : MeasurableSet (I2 hk y) := by
    if hk_s : k = -S then
      rw [I2, dif_pos hk_s]
      exact measurableSet_ball
    else
      let hk'' : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk_s (id a_1.symm)
      rw [I2, dif_neg hk_s]
      letI := (Yk_countable X (k - 1)).to_subtype
      refine MeasurableSet.biUnion (to_countable (Yk X (k - 1) ↓∩ ball (↑y) (2 * D ^ k))) ?_
      · simp only [mem_preimage]
        exact fun b _ ↦ I3_measurableSet (I_induction_proof hk hk_s) b
  termination_by (3 * (S+k).toNat, sizeOf y)

  lemma Xk_measurableSet {k : ℤ} (hk : -S ≤ k) : MeasurableSet (Xk hk) := by
    rw [Xk]
    letI := (Yk_countable X k).to_subtype
    apply MeasurableSet.iUnion fun b ↦ I1_measurableSet hk b
  termination_by (3 * (S+k).toNat + 1, 0)

  lemma I3_measurableSet {k : ℤ} (hk : -S ≤ k) (y : Yk X k) : MeasurableSet (I3 hk y) := by
    rw [I3]
    refine MeasurableSet.union (I1_measurableSet hk y) ?_
    refine (MeasurableSet.diff (I2_measurableSet hk y))
      (MeasurableSet.union (Xk_measurableSet hk) ?_)
    letI := (Yk_countable X k).to_subtype
    exact (MeasurableSet.iUnion fun b ↦ MeasurableSet.iUnion fun _ ↦ I3_measurableSet hk b)
  termination_by (3 * (S + k).toNat + 2, sizeOf y)
end

section basic_grid_structure

mutual
  lemma I1_prop_1 {k : ℤ} (hk : -S ≤ k) {x : X} {y1 y2 : Yk X k} :
      x ∈ I1 hk y1 ∩ I1 hk y2 → y1 = y2 := by
    rw [I1,I1]
    if hk_s : k = -S then
      rw [dif_pos hk_s,dif_pos hk_s]
      subst hk_s
      intro hx
      ext
      rw [(Yk_pairwise (-S)).elim (y1.property) (y2.property)]
      rw [not_disjoint_iff]
      exact ⟨x, hx⟩
    else
      have : -S ≤ k - 1 := I_induction_proof hk hk_s
      have : ((2 * (S + (k - 1))).toNat : ℤ) + 1 < 2 * (S + k) := by
        rw [Int.toNat_of_nonneg (by linarith)]
        linarith
      rw [dif_neg hk_s, dif_neg hk_s]
      intro hx
      simp only [mem_preimage, mem_inter_iff, mem_iUnion, exists_prop] at hx
      obtain ⟨⟨z1, hz1, hz1'⟩, ⟨z2, hz2, hz2'⟩⟩ := hx
      have hz_eq : z1 = z2 := I3_prop_1 (I_induction_proof hk hk_s) ⟨hz1', hz2'⟩
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
    have hx_notMem_i1 (y' : Yk X k): x ∉ I1 hk y' := by
      simp only [Xk, mem_iUnion, not_exists] at hx_mem_Xk
      exact hx_mem_Xk _
    rw [iff_false_intro (hx_notMem_i1 y1), iff_false_intro (hx_notMem_i1 y2)] at hx
    rw [false_or,false_or,iff_true_intro hx_mem_Xk,true_and,true_and] at hx
    apply Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt
    · exact fun h ↦ hx.right.right y1 h hl
    exact fun h ↦ hx.left.right y2 h hr
  termination_by (2 * (S + k)).toNat + 1
end

lemma I3_prop_3_2 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    I3 hk y ⊆ ball (y : X) (4 * D ^ k) := by
  intro x hx
  have : x ∈ I2 hk y := I3_subset_I2 hk y hx
  simp only [I2] at this
  if hk_s : k = -S then
    rw [dif_pos hk_s] at this
    subst hk_s
    revert this
    apply ball_subset_ball (by gcongr; norm_num)
  else
    rw [dif_neg hk_s] at this
    simp only [mem_preimage, mem_iUnion, exists_prop] at this
    obtain ⟨y',hy',hyi3⟩ := this
    have : -S ≤ k - 1 := I_induction_proof hk hk_s
    have : x ∈ ball (y' : X) (4 * D ^ (k-1)) := I3_prop_3_2 _ y' hyi3
    rw [mem_ball] at this hy' ⊢
    calc
      dist x (y:X)
        ≤ dist x (y' : X) + dist (y' : X) (y : X) := dist_triangle _ _ _
      _ <  4 * D ^ (k - 1) + 2 * D ^ k := add_lt_add this hy'
      _ ≤ 1 * D ^ (k - 1 + 1) + 2 * D ^ k := by
        simp only [one_mul, add_le_add_iff_right]
        rw [zpow_add₀ (defaultD_pos a).ne.symm _ 1,zpow_one,mul_comm _ (D:ℝ)]
        gcongr
        exact four_le_realD X
      _ ≤ 4 * D ^ k := by
        rw [sub_add_cancel, ← right_distrib]
        gcongr
        norm_num
termination_by (S + k).toNat

mutual
  lemma I2_prop_2 {k : ℤ} (hk : -S ≤ k) :
      ball o (4 * D ^ S - 2 * D ^ k) ⊆ ⋃ (y : Yk X k), I2 hk y := by
    simp only [I2, mem_preimage, iUnion_coe_set]
    if hk_s : k = -S then
      simp_rw [dif_pos hk_s]
      subst hk_s
      calc
        ball o (4 * D ^ S - 2 * (D ^ (-S : ℤ)))
          ⊆ ball o (4 * D ^ S - D ^ (-S : ℤ)) := by
            apply ball_subset_ball
            rw [two_mul,tsub_le_iff_right,sub_add_add_cancel,le_add_iff_nonneg_right]
            positivity
        _ ⊆ ⋃ (i ∈ Yk X (-S)), ball i (2 * D ^ (-S : ℤ)) := cover_big_ball (-S : ℤ)
    else
      simp_rw [dif_neg hk_s]
      intro x hx
      have : -S < k := lt_of_le_of_ne hk fun a_1 ↦ hk_s (id a_1.symm)
      have : ((2 * (S + (k - 1))).toNat : ℤ) + 1 < 2 * (S + k) := by
        rw [Int.toNat_of_nonneg (by linarith)]
        linarith
      have hsub1 : ball o (4 * D ^ S - 2 * D ^ k) ⊆ ⋃ y, I3 (I_induction_proof hk hk_s) y := by
        calc
          ball o (4 * D ^ S - 2 * D ^ k)
            ⊆ ball o (4 * D ^ S - 2 * D ^ (k - 1)) := by
              apply ball_subset_ball
              simp only [tsub_le_iff_right]
              rw [sub_eq_add_neg,add_assoc]
              simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero, Nat.ofNat_pos,
                mul_le_mul_left]
              gcongr
              exacts [one_le_realD X, by linarith]
          _ ⊆ ⋃ y, I3 _ y := I3_prop_2 _
      have hmem_i3 : x ∈ ⋃ y, I3 _ y := hsub1 hx
      simp only [mem_iUnion] at hmem_i3
      obtain ⟨y', hy''⟩ := hmem_i3
      have hy''' : x ∈ ball (y' : X) (D ^ k) := by
        apply (?_ : I3 _ y' ⊆ ball (y' : X) (D ^ k)) hy''
        calc
          I3 _ y'
            ⊆ ball y' (4 * D ^ (k - 1)) := I3_prop_3_2 _ y'
          _ ⊆ ball y' (D * D ^ (k - 1)) :=
              ball_subset_ball (by gcongr; exact (four_le_realD X))
          _ = ball (y': X) (D ^ k) := by
            nth_rw 1 [← zpow_one (D : ℝ),← zpow_add₀ (defaultD_pos a).ne.symm, add_sub_cancel]
      rw [mem_ball_comm] at hy'''
      have hyfin : (y' : X) ∈ ball o (4 * D ^ S - D ^ k) := by
        simp only [mem_ball] at hx hy''' ⊢
        calc
          dist ↑y' o
            ≤ dist (y' : X) x + dist x o := dist_triangle _ _ _
          _ < D ^ k + (4 * D ^ S - 2 * D ^ k) := add_lt_add hy''' hx
          _ ≤ 4 * D ^ S - D ^ k := by linarith
      have hyfin' : (y' : X) ∈ ⋃ (y'' ∈ Yk X k), ball (y'') (2 * D ^ k) := cover_big_ball k hyfin
      rw [← iUnion_coe_set (Yk X k) (fun z ↦ ball (z : X) (2 * D ^ k))] at hyfin'
      simp only [mem_iUnion] at hyfin'
      obtain ⟨y2,hy2'⟩ := hyfin'
      simp only [mem_iUnion, exists_prop, exists_and_left]
      use y2, y2.property, y', hy2', y'.property
  termination_by (2 * (S + k)).toNat

  lemma I3_prop_2 {k : ℤ} (hk : -S ≤ k) :
      ball o (4 * D ^ S - 2 * D ^ k) ⊆ ⋃ (y : Yk X k), I3 hk y := by
    intro x hx
    if hx_mem_Xk : x ∈ Xk hk then
      rw [Xk] at hx_mem_Xk
      simp only [mem_iUnion] at hx_mem_Xk ⊢
      refine hx_mem_Xk.elim (fun y hy ↦ ?_)
      use y
      rw [I3]
      exact mem_union_left _ hy
    else
      simp only [mem_iUnion]
      have : x ∈ ⋃ (y : Yk X k), I2 hk y := I2_prop_2 hk hx
      simp only [mem_iUnion] at this
      have : {i | x ∈ I2 hk i}.Nonempty := this
      have H := (@wellFounded_lt (Yk X k) _ _)
      let y := H.min {i | x ∈ I2 hk i} this
      have hy_i2 : x ∈ I2 hk y := H.min_mem {i|x ∈ I2 hk i} this
      have hy_is_min : ∀ y', x ∈ I2 hk y' → ¬ y' < y :=
        fun y' hy' ↦ H.not_lt_min {i | x ∈ I2 hk i} this hy'
      use y
      revert hy_i2 hy_is_min
      generalize y = y
      intro hy_i2 hy_min
      rw [I3]
      have hx_notMem_i1 : ∀ y',x ∉ I1 hk y' := by
        simp only [Xk,mem_iUnion, not_exists] at hx_mem_Xk
        exact hx_mem_Xk
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
        not_and]
      refine Or.inr ⟨hy_i2,hx_mem_Xk, fun y' hy' ↦ ?_⟩
      rw [I3]
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists, not_and]
      exact ⟨hx_notMem_i1 y', fun hy_i2' _ _ ↦ hy_min y' hy_i2' hy'⟩
  termination_by (2 * (S + k)).toNat + 1
end

lemma I3_prop_3_1 {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
    ball (y : X) (2⁻¹ * D ^ k) ⊆ I3 hk y := by
  rw [I3, I1]
  apply subset_trans _ subset_union_left
  if hk_s : k = -S then
    rw [dif_pos hk_s]
    subst hk_s
    apply ball_subset_ball
    nth_rw 2 [← one_mul (D ^ (-S : ℤ) : ℝ)]
    gcongr; norm_num
  else
    rw [dif_neg hk_s]
    simp only [mem_preimage]
    have : (y : X) ∈ ball o (4 * D ^ S - D ^ k : ℝ) := Yk_subset k y.property
    have : ball (y : X) (2⁻¹ * D ^ k) ⊆ ⋃ (y' : Yk X (k - 1)), I3 (I_induction_proof hk hk_s) y' := by
      calc
        ball (y : X) (2⁻¹ * D ^ k)
          ⊆ ball o (4 * D ^ S - D ^ k + 2⁻¹ * D ^ k) := by
            apply ball_subset
            ring_nf
            rw [mul_comm]
            rw [mem_ball] at this
            exact this.le
        _ ⊆ ball o (4 * D ^ S - 2 * D ^ (k - 1)) := by
          apply ball_subset_ball
          rw [sub_eq_add_neg,sub_eq_add_neg, add_assoc, add_le_add_iff_left]
          simp only [neg_add_le_iff_le_add, le_add_neg_iff_add_le]
          calc
            (2⁻¹ * D ^ k + 2 * D ^ (k - 1) : ℝ)
              = 2⁻¹ * D ^ k + 2⁻¹ * 4 * D ^ (k - 1) := by
                rw [add_right_inj]
                norm_num
            _ ≤ 2⁻¹ * (2 * D ^ k) := by
              rw [mul_assoc, ← left_distrib, two_mul]
              gcongr
              nth_rw 2 [← add_sub_cancel 1 k]
              rw [zpow_add₀ (defaultD_pos a).ne.symm, zpow_one]
              gcongr; exact four_le_realD X
            _ = D ^ k := by
              rw [← mul_assoc]
              norm_num
        _ ⊆ ⋃ (y' : Yk X (k - 1)), I3 (I_induction_proof hk hk_s) y' := I3_prop_2 (I_induction_proof hk hk_s)
    intro x hx
    have : x ∈ ⋃ (y' : Yk X (k - 1)), I3 _ y' := this hx
    rw [mem_iUnion] at this
    obtain ⟨y',hy'⟩ := this
    have : x ∈ ball (y' : X) (4 * D ^ (k - 1)) := I3_prop_3_2 _ y' hy'
    have : (y' : X) ∈ ball (y : X) (D ^ k) := by
      rw [mem_ball] at this hx ⊢
      rw [dist_comm] at this
      calc
        dist (y' : X) (y : X)
          ≤ dist (y' : X) x + dist x (y : X) := dist_triangle _ _ _
        _ < 4 * D ^ (k - 1) + 2⁻¹ * D ^ k := add_lt_add this hx
        _ = 2⁻¹ * 8 * D ^ (k - 1) + 2⁻¹ * D ^ k := by norm_num
        _ ≤ 2⁻¹ * (D ^ k + D ^ k) := by
          rw [mul_assoc, ← left_distrib]
          gcongr
          nth_rw 2 [← add_sub_cancel 1 k,]
          rw [zpow_add₀ (defaultD_pos a).ne.symm,zpow_one]
          gcongr
          exact eight_le_realD X
        _ = D ^ k := by ring
    rw [mem_iUnion]
    use y'
    rw [mem_iUnion]
    use this

end basic_grid_structure

lemma I3_nonempty {k : ℤ} (hk : -S ≤ k) (y : Yk X k) :
  (I3 hk y).Nonempty := by
  refine ⟨y, I3_prop_3_1 hk y ?_⟩
  rw [mem_ball,dist_self]
  simp only [inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
  exact zpow_pos (defaultD_pos a) k

-- the additional argument `hk` to get decent equality theorems
lemma cover_by_cubes {l : ℤ} (hl : -S ≤ l) :
    ∀ {k : ℤ}, l ≤ k → (hk : -S ≤ k) → ∀ y, I3 hk y ⊆ ⋃ (yl : Yk X l), I3 hl yl := by
  apply Int.le_induction
  · intro _ y x hx
    rw [mem_iUnion]
    use y
  intro k hlk hind
  rw [← add_sub_cancel_right k 1] at hind
  intro hk1 y x hx
  have h : -S < k + 1 := by linarith
  have : x ∈ I2 hk1 y := I3_subset_I2 hk1 y hx
  rw [I2,dif_neg h.ne.symm] at this
  simp only [mem_preimage, mem_iUnion, exists_prop] at this
  obtain ⟨z,_,hz'⟩ := this
  specialize hind (I_induction_proof hk1 h.ne.symm) z hz'
  exact hind

lemma dyadic_property {l : ℤ} (hl : -S ≤ l) {k : ℤ} (hl_k : l ≤ k) :
    (hk : -S ≤ k) → ∀ (y : Yk X k), ∀ (y' : Yk X l),
    ¬ Disjoint (I3 hl y') (I3 hk y) → I3 hl y' ⊆ I3 hk y := by
  simp_rw [not_disjoint_iff, forall_exists_index, and_imp]
  intro hk y y' x hxl hxk
  if hk_l : k = l then
    subst hk_l
    apply Eq.le (congr_heq _ _)
    · congr
    simp only [heq_eq_eq]
    exact I3_prop_1 hk (And.intro hxl hxk)
  else
    have : l < k := lt_of_le_of_ne hl_k fun a ↦ hk_l (id a.symm)
    have hk_not_neg_s : ¬ k = -S := by linarith
    have : x ∈ ⋃ (y'' : Yk X (k - 1)), I3 (I_induction_proof hk hk_not_neg_s) y'' :=
      cover_by_cubes (I_induction_proof hk hk_not_neg_s) (by linarith) hk y hxk
    simp only [mem_iUnion] at this
    obtain ⟨y'', hy''⟩ := this
    have : l + (-l + (k - 1)).toNat < k := by
      rw [Int.toNat_of_nonneg (by linarith)]
      linarith
    have : I3 hl y' ⊆ I3 (I_induction_proof hk hk_not_neg_s) y'' := by
      apply dyadic_property hl (by linarith) (I_induction_proof hk hk_not_neg_s)
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
      simp only [mem_preimage, mem_iUnion, exists_prop] at hx_i1
      obtain ⟨u, hu, hu'⟩ := hx_i1
      have hxy'' : x ∈ I3 _ y'' := this hxl
      have : y'' = u := by
        apply I3_prop_1
        use hxy''
      subst this
      apply Subset.trans _ (I1_subset_I3 _ _)
      rw [I1,dif_neg hk_not_neg_s]
      intro x' hx'
      simp only [mem_preimage, mem_iUnion, exists_prop]
      use y''
    else
      have hx_notMem_i1 (y_1 : Yk X k) : x ∉ I1 hk y_1 := by
        rw [Xk] at hx_mem_Xk
        simp only [mem_iUnion, not_exists] at hx_mem_Xk
        exact hx_mem_Xk y_1
      have hx_mem_i2_and : x ∈ I2 hk y ∧ ∀ u < y, x ∉ I3 hk u:= by
        rw [I3] at hxk
        simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists,
          not_and] at hxk
        rw [iff_false_intro (hx_notMem_i1 y), iff_true_intro hx_mem_Xk, false_or, true_and] at hxk
        exact hxk
      have hx_mem_i2 := hx_mem_i2_and.left
      have hx_notMem_i3_u := hx_mem_i2_and.right
      have hx_notMem_i2_u: ∀ u < y, x ∉ I2 hk u := by
        intro u hu
        specialize hx_notMem_i3_u u hu
        rw [I3] at hx_notMem_i3_u
        simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists, not_and,
          not_forall, not_not] at hx_notMem_i3_u
        rw [iff_true_intro (hx_notMem_i1 u),iff_true_intro hx_mem_Xk] at hx_notMem_i3_u
        rw [true_and,true_implies] at hx_notMem_i3_u
        intro h
        obtain ⟨v, hv, hv'⟩ := hx_notMem_i3_u h
        exact hx_mem_i2_and.right v (hv.trans hu) hv'

      rw [I2, dif_neg hk_not_neg_s] at hx_mem_i2
      simp only [mem_preimage, mem_iUnion, exists_prop] at hx_mem_i2
      obtain ⟨u, hu, hxu⟩ := hx_mem_i2
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
        obtain ⟨u, hu⟩ := hx_xk'
        use u
        rw [I1,dif_neg hk_not_neg_s] at hu ⊢
        simp only [mem_preimage, mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨u', hu', hu''⟩ := hu
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
        not_and,iff_true_intro hx_not_xk, true_and]
      right
      constructor
      · rw [I2, dif_neg hk_not_neg_s]
        simp only [mem_preimage, mem_iUnion, exists_prop]
        use y''
      intro u hu
      have hx_not_i1' : x' ∉ I1 hk u := by
        intro hx_i1'
        apply hx_not_xk
        rw [Xk]
        simp only [mem_iUnion]
        use u
      rw [I3]
      simp only [mem_union, mem_diff, mem_iUnion, exists_prop, not_or, not_exists, not_and,
        not_forall]
      rw [iff_true_intro hx_not_xk, iff_true_intro hx_not_i1', true_and, true_implies]
      intro hx_i2'
      by_contra
      apply hx_notMem_i2_u u hu
      rw [I2, dif_neg hk_not_neg_s] at hx_i2' ⊢
      simp only [mem_preimage, mem_iUnion] at hx_i2' ⊢
      obtain ⟨z,hz,hz'⟩ := hx_i2'
      use z, hz
      suffices z = y'' by
        subst this
        exact hy''
      apply I3_prop_1 (I_induction_proof hk hk_not_neg_s)
      exact mem_inter hz' hx'
  termination_by ((-l + k).toNat)

structure ClosenessProperty {k1 k2 : ℤ} (hk1 : -S ≤ k1) (hk2 : -S ≤ k2)
    (y1 : Yk X k1) (y2 : Yk X k2) : Prop where
  I3_subset : I3 hk1 y1 ⊆ I3 hk2 y2
  I3_infdist_lt : EMetric.infEdist (y1 : X) (I3 hk2 y2)ᶜ < (6 * D ^ k1 : ℝ≥0∞)

local macro "clProp(" hkl:term ", " y1:term " | " hkr:term ", " y2:term ")" : term =>
 `(ClosenessProperty $hkl $hkr $y1 $y2)

lemma transitive_boundary' {k1 k2 k3 : ℤ} (hk1 : -S ≤ k1) (hk2 : -S ≤ k2) (hk3 : -S ≤ k3)
  (hk1_2 : k1 < k2) (hk2_3 : k2 ≤ k3) (y1 : Yk X k1) (y2 : Yk X k2) (y3 : Yk X k3)
    (x : X) (hx : x ∈ I3 hk1 y1 ∩ I3 hk2 y2 ∩ I3 hk3 y3) :
    clProp(hk1,y1|hk3,y3) → (clProp(hk1,y1|hk2,y2) ∧ clProp(hk2,y2|hk3,y3)) := by
  rintro ⟨_, hx'⟩
  have hi3_1_2 : I3 hk1 y1 ⊆ I3 hk2 y2 := by
    apply dyadic_property hk1 hk1_2.le hk2 y2 y1
    rw [not_disjoint_iff]
    exact ⟨x, hx.left.left, hx.left.right⟩
  have hi3_2_3 : I3 hk2 y2 ⊆ I3 hk3 y3 := by
    apply dyadic_property hk2 hk2_3 hk3 y3 y2
    rw [not_disjoint_iff]
    exact ⟨x, hx.left.right, hx.right⟩
  have hx_4k2 : x ∈ ball (y2 : X) (4 * D ^ k2) := I3_prop_3_2 hk2 y2 hx.left.right
  have hx_4k2' : x ∈ ball (y1 : X) (4 * D ^ k1) := I3_prop_3_2 hk1 y1 hx.left.left
  have hd_nzero : (D : ℝ≥0∞) ≠ 0 := by
    apply LT.lt.ne'
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_pos]
    exact defaultD_pos a
  have hdp_nzero : ∀ (z:ℤ),(D ^ z :ℝ≥0∞) ≠ 0 := by
    intro z
    exact (ENNReal.zpow_pos hd_nzero (by finiteness) _).ne'
  have hdp_finit42 : (D ^ 42 : ℝ≥0∞) ≠ ⊤ := by finiteness
  refine ⟨⟨hi3_1_2, ?_⟩, ⟨hi3_2_3, ?_⟩⟩
  · apply lt_of_le_of_lt (EMetric.infEdist_anti _) hx'
    rw [compl_subset_compl]
    exact hi3_2_3
  · rw [← emetric_ball,EMetric.mem_ball] at hx_4k2 hx_4k2'
    rw [edist_comm] at hx_4k2'
    rw [← Real.rpow_intCast] at hx_4k2 hx_4k2'
    rw [ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast,ENNReal.rpow_intCast] at hx_4k2 hx_4k2'
    calc
      EMetric.infEdist (y2 : X) (I3 hk3 y3)ᶜ
        ≤ edist (y2 : X) (y1 : X) + EMetric.infEdist (y1 : X) (I3 hk3 y3)ᶜ :=
          EMetric.infEdist_le_edist_add_infEdist
      _ = EMetric.infEdist (y1 : X) (I3 hk3 y3)ᶜ + edist (y1 : X) (y2 : X) := by
        rw [add_comm,edist_comm]
      _ ≤ EMetric.infEdist (y1 : X) (I3 hk3 y3)ᶜ +
          (edist (y1:X) x + edist x y2) := by
        rw [ENNReal.add_le_add_iff_left hx'.ne_top]
        exact edist_triangle (↑y1) x ↑y2
      _ < EMetric.infEdist (y1 : X) (I3 hk3 y3)ᶜ + edist (y1 : X) x + 4 * D ^ k2 := by
        rw [← add_assoc, ENNReal.add_lt_add_iff_left (by finiteness)]
        exact hx_4k2
      _ < 6 * D ^ k1 + 4 * D ^ k1 + 4 * D ^ k2 := by
        rw [ENNReal.add_lt_add_iff_right]
        · apply ENNReal.add_lt_add hx' hx_4k2'
        · finiteness
      _ ≤ 2 * D ^ k2 + 4 * D ^ k2 := by
        rw [← right_distrib 6 4 (D ^ k1 : ℝ≥0∞)]
        have hz : (6 + 4 : ℝ≥0∞) = 2 * 5 := by norm_num
        rw [hz, ENNReal.add_le_add_iff_right, mul_assoc]
        · gcongr
          calc
            (5 * D ^ k1 : ℝ≥0∞)
              ≤ D * D ^ k1 := by
                gcongr
                rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_natCast,
                  ENNReal.ofReal_le_ofReal_iff realD_nonneg]
                exact five_le_realD X
            _ ≤ D ^ k2 := by
              nth_rw 1 [← zpow_one (D : ℝ≥0∞)]
              simp_rw [← ENNReal.rpow_intCast]
              rw [← ENNReal.rpow_add _ _ hd_nzero (by finiteness),← Int.cast_add]
              apply ENNReal.rpow_le_rpow_of_exponent_le
              · rw [← ENNReal.ofReal_one,← ENNReal.ofReal_natCast]
                rw [ENNReal.ofReal_le_ofReal_iff realD_nonneg]
                exact one_le_realD X
              simp only [Int.cast_le]
              linarith
        · finiteness
      _ = 6 * D ^ k2 := by
        rw [← right_distrib]
        norm_num

lemma transitive_boundary {k1 k2 k3 : ℤ} (hk1 : -S ≤ k1) (hk2 : -S ≤ k2) (hk3 : -S ≤ k3)
  (hk1_2 : k1 ≤ k2) (hk2_3 : k2 ≤ k3) (y1 : Yk X k1) (y2 : Yk X k2) (y3 : Yk X k3)
    (x : X) (hx : x ∈ I3 hk1 y1 ∩ I3 hk2 y2 ∩ I3 hk3 y3) :
    clProp(hk1,y1|hk3,y3) → (clProp(hk1,y1|hk2,y2) ∧ clProp(hk2,y2|hk3,y3)) := by
  if hk1_eq_2 : k1 = k2 then
    subst hk1_eq_2
    intro hcl
    have : y1 = y2 := by apply I3_prop_1; exact hx.left
    subst this
    constructor
    · exact ⟨le_refl _,by
        obtain hx := hcl.I3_infdist_lt
        apply lt_of_le_of_lt _ hx
        apply EMetric.infEdist_anti
        simp only [compl_subset_compl]
        exact hcl.I3_subset⟩
    exact hcl
  else
    have : k1 < k2 := lt_of_le_of_ne hk1_2 hk1_eq_2
    exact transitive_boundary' hk1 hk2 hk3 this hk2_3 y1 y2 y3 x hx

def const_K : ℕ := 2 ^ (4 * a + 1)

namespace ShortVariables
set_option hygiene false in
scoped notation "K'" => @const_K a
end ShortVariables

lemma K_pos : 0 < (K' : ℝ) := by
  rw [const_K]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.ofNat_pos, pow_pos]

variable (X) in
def C4_1_7 [ProofData a q K σ₁ σ₂ F G] : ℝ≥0 := As (defaultA a) (2 ^ 4)

variable (X) in
lemma C4_1_7_eq : C4_1_7 X = 2 ^ (4 * a) := by
  dsimp [C4_1_7, As]
  rw [← Real.rpow_natCast 2 4, Real.logb_rpow (by linarith : 0 < (2:ℝ)) (by norm_num)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.ceil_ofNat]
  group

lemma volume_tile_le_volume_ball (k : ℤ) (hk : -S ≤ k) (y : Yk X k) :
    volume (I3 hk y) ≤ C4_1_7 X * volume (ball (y : X) (4⁻¹ * D ^ k)) := by
  calc
    volume (I3 hk y)
      ≤ volume (ball (y : X) (2 ^ 4 * (4⁻¹ * D ^ k))) := by
        gcongr
        convert I3_prop_3_2 hk y using 2
        ring
    _ ≤ C4_1_7 X * volume (ball (y : X) (4⁻¹ * D ^ k : ℝ)):= by
      rw [C4_1_7]
      exact measure_ball_le_same (y : X) (by linarith) (le_refl _)

lemma le_s {k : ℤ} (hk_mK : -S ≤ k - K') (k' : Ioc (k - K') k) : (-S : ℤ) ≤ k' := by
  linarith [k'.property.left]

lemma small_boundary' (k : ℤ) (hk : -S ≤ k) (hk_mK : -S ≤ k - K') (y : Yk X k) :
    ∑' (z : Yk X (k - K')), volume (⋃ (_ : clProp(hk_mK,z|hk,y)), (I3 hk_mK z))
      ≤ 2⁻¹ * volume (I3 hk y) := by
  suffices
    (K') * ∑' (z : Yk X (k - K')), volume (⋃ (_:clProp(hk_mK,z|hk,y)),I3 hk_mK z)
      ≤ C4_1_7 X * volume (I3 hk y) by
    rw [C4_1_7_eq X] at this
    dsimp only [const_K] at this
    nth_rw 1 [pow_add 2 (4 * a) 1] at this
    rw [pow_one 2, Nat.cast_mul, Nat.cast_two, mul_comm _ 2, mul_assoc,
      ENNReal.mul_le_iff_le_inv (by norm_num) (by norm_num), ← mul_assoc,mul_comm 2⁻¹ _,
      mul_assoc] at this
    simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.coe_pow, ENNReal.coe_ofNat] at this
    rw [← ENNReal.mul_le_mul_left]
    · exact this
    · exact (NeZero.ne (2 ^ (4 * a)))
    · finiteness
  letI : Countable (Yk X (k - K')) := (Yk_countable X (k - K')).to_subtype
  calc
    K' * ∑' (z : ↑(Yk X (k - K'))), volume (⋃ (_ : clProp(hk_mK,z|hk,y)), I3 hk_mK z)
      = ∑ (_ : Ioc (k - K') k),
        ∑'(z : Yk X (k - K')),volume (⋃ (_ : clProp(hk_mK,z|hk,y)), I3 hk_mK z) := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_ofFinset, Int.card_Ioc, sub_sub_cancel,
          Int.toNat_natCast, nsmul_eq_mul]
    _ = ∑ (_ : Ioc (k - K') k), volume (
        ⋃ (z : Yk X (k - K')),⋃ (_ : clProp(hk_mK,z|hk,y)),I3 hk_mK z) := by
      apply Finset.sum_congr (rfl)
      intro x
      simp only [Finset.mem_univ, true_implies]
      symm
      refine measure_iUnion ?_ ?_
      · intro i i' hneq
        simp only [disjoint_iUnion_right, disjoint_iUnion_left]
        intro _ _
        rw [Set.disjoint_iff]
        intro x hx
        apply hneq
        exact I3_prop_1 hk_mK hx
      · intro i
        letI : Decidable (clProp(hk_mK,i|hk,y)):=
          Classical.propDecidable _
        rw [Set.iUnion_eq_if]
        if h:(clProp(hk_mK,i|hk,y)) then
          rw [if_pos h]
          exact I3_measurableSet hk_mK i
        else
          rw [if_neg h]
          exact MeasurableSet.empty
    _ ≤ ∑ (k' : Ioc (k - K') k),
          volume (⋃ (z ∈ {z' : Yk X k' | clProp((le_s hk_mK k'),z'|hk,y) }),
            I3 (le_s hk_mK k') z) := by
      apply Finset.sum_le_sum
      simp only [Finset.mem_univ, mem_setOf_eq, true_implies]
      intro k'
      apply volume.mono
      simp only [iUnion_subset_iff]
      intro z hz x hx
      have : x ∈ I3 hk y := hz.I3_subset hx
      have : x ∈ ⋃ z, I3 (le_s hk_mK k') z:=
        cover_by_cubes (le_s hk_mK k') (k'.property.right) hk y this
      simp only [mem_iUnion] at this
      obtain ⟨y', hy'⟩ := this
      simp only [mem_iUnion, exists_prop]
      use y'
      constructor
      · apply And.right
        apply transitive_boundary hk_mK (le_s hk_mK k') hk k'.property.left.le k'.property.right z y' y
        · simp only [mem_inter_iff]
          exact And.intro (And.intro hx hy') this
        · exact hz
      exact hy'
    _ = ∑ (k' : Ioc (k - K') k), ∑' (z : Yk X k'),
          volume (⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)), I3 (le_s hk_mK k') z) := by
      apply Finset.sum_congr (rfl)
      intro k'
      simp only [Finset.mem_univ, true_implies]
      letI := (Yk_countable X k').to_subtype
      refine measure_iUnion ?_ ?_
      · intro i i' hneq
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
    _ ≤ ∑ (k' : Ioc (k - K') k), ∑' (z : Yk X k'), C4_1_7 X *
          volume (⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)), ball (z : X) (4⁻¹ * D ^ (k' : ℤ))) := by
      apply Finset.sum_le_sum
      intro k'
      simp only [Finset.mem_univ, true_implies]
      apply ENNReal.summable.tsum_le_tsum _ (ENNReal.summable)
      intro z
      letI : Decidable (clProp(le_s hk_mK k',z|hk,y)) := Classical.propDecidable _
      simp_rw [iUnion_eq_if,apply_ite volume,measure_empty, mul_ite, mul_zero]
      if h : clProp(le_s hk_mK k',z|hk,y) then
        simp_rw [if_pos h]
        exact volume_tile_le_volume_ball (↑k') (le_s hk_mK k') z
      else
        repeat rw [if_neg h]
    _ = C4_1_7 X * ∑ (k' : Ioc (k - K') k), ∑' (z : Yk X k'),
          volume (⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)), ball (z : X) (4⁻¹ * D ^ (k' : ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr (rfl)
      simp only [Finset.mem_univ, true_implies]
      intro k'
      rw [ENNReal.tsum_mul_left]
    _ = C4_1_7 X * ∑ (k' : Ioc (k - K') k),
          volume (⋃ (z : Yk X k'), ⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)),
            ball (z : X) (4⁻¹ * D ^ (k' : ℤ))) := by
      congr
      ext k'
      symm
      letI := (Yk_countable X k').to_subtype
      apply measure_iUnion _ <| fun _ ↦ MeasurableSet.iUnion <| fun _ ↦ measurableSet_ball
      intro i i' hneq
      simp only [disjoint_iUnion_right, disjoint_iUnion_left]
      intro _ _
      apply Disjoint.mono
      · trans ball (i : X) (2⁻¹ * D ^ (k' : ℤ))
        · apply ball_subset_ball
          gcongr
          linarith
        apply I3_prop_3_1
        have := k'.property.left
        linarith
      · trans ball (i' : X) (2⁻¹ * D ^ (k' : ℤ))
        · apply ball_subset_ball
          gcongr
          norm_num
        apply I3_prop_3_1
        have := k'.property.left
        linarith
      rw [Set.disjoint_iff]
      intro x hx
      apply hneq
      apply I3_prop_1
      exact hx
    _ ≤ C4_1_7 X * ∑' (k' : Ioc (k - K') k),
          volume (⋃ (z : Yk X k'), ⋃ (_:clProp((le_s hk_mK k'),z|hk,y)),
            ball (z : X) (4⁻¹ * D ^ (k' : ℤ))) := by
      gcongr
      exact ENNReal.sum_le_tsum Finset.univ
    _ = C4_1_7 X * volume (⋃ (k' : Ioc (k - K') k), ⋃ (z:Yk X k'),
          ⋃ (_ : clProp((le_s hk_mK k'),z|hk,y)), ball (z : X) (4⁻¹ * D ^ (k' : ℤ))) := by
      congr
      symm
      apply measure_iUnion
      · rw [Symmetric.pairwise_on]
        · intro l' l hl
          simp only [disjoint_iUnion_right, disjoint_iUnion_left]
          intro u hu u' hu'
          rw [Set.disjoint_iff]
          obtain ⟨x,hx⟩ := EMetric.infEdist_lt_iff.mp hu'.I3_infdist_lt
          intro x' hx'
          have : x ∈ ball (u:X) (2⁻¹ * D^(l:ℤ)) := by
            simp only [mem_inter_iff, mem_compl_iff, mem_ball] at hx hx' ⊢
            calc
              dist x (u:X)
                ≤ dist x (u':X) + dist (u':X) x' + dist x' (u:X) := dist_triangle4 x (↑u') x' ↑u
              _ < 6 * D^(l':ℤ ) + 4⁻¹ * D^(l':ℤ) + 4⁻¹ * D^(l:ℤ) := by
                rw [← dist_comm x' u']
                apply add_lt_add _ hx'.right
                apply add_lt_add _ hx'.left
                rw [dist_edist]
                rw [← @ENNReal.toReal_ofReal (6 * D ^ (l':ℤ)), ← Real.rpow_intCast]
                · rw [ENNReal.toReal_lt_toReal (by finiteness) (by finiteness),
                    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
                    ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a), ENNReal.ofReal_natCast,
                    edist_comm, ENNReal.rpow_intCast]
                  exact hx.right
                positivity
              _ = 4⁻¹ * 25 * D^(l':ℤ) + 4⁻¹ * D^(l:ℤ) := by
                rw [← right_distrib]
                norm_num
              _ ≤ 4⁻¹ * D^(l:ℤ) + 4⁻¹ * D^(l:ℤ) := by
                rw [add_le_add_iff_right, mul_assoc]
                gcongr
                trans D * D^(l':ℤ)
                · gcongr
                  exact twentyfive_le_realD X
                nth_rw 1 [← zpow_one (D:ℝ)]
                rw [← zpow_add₀ (defaultD_pos a).ne.symm]
                have : (l':ℤ) < l := hl
                exact zpow_le_zpow_right₀ (one_le_realD X) (by linarith)
              _ = 2⁻¹ * D^(l:ℤ) := by
                rw [← two_mul _,← mul_assoc]
                norm_num
          have : x ∈ I3 hk y := by
            apply dyadic_property (le_s hk_mK l) (l.property.right) hk
            · rw [Set.not_disjoint_iff]
              use x, I3_prop_3_1 (le_s hk_mK l) u this
              apply hu.I3_subset
              exact I3_prop_3_1 (le_s hk_mK l) u this
            exact I3_prop_3_1 (le_s hk_mK l) u this
          exact hx.left this
        exact fun ⦃x y⦄ a ↦ id (Disjoint.symm a)
      intro k'
      letI := (Yk_countable X k').to_subtype
      apply MeasurableSet.iUnion <| fun _ ↦ MeasurableSet.iUnion <| fun _ ↦ measurableSet_ball
    _ ≤ C4_1_7 X * volume (I3 hk y) := by
      gcongr
      simp only [iUnion_subset_iff]
      intro k' y' hy' x
      apply Subset.trans _ hy'.I3_subset
      apply Subset.trans _ (I3_prop_3_1 _ _)
      apply ball_subset_ball
      gcongr
      norm_num

lemma small_boundary (k : ℤ) (hk : -S ≤ k) (hk_mK : -S ≤ k - K') (y : Yk X k) :
    ∑' (z : Yk X (k - K')), ∑ᶠ (_ : clProp(hk_mK,z|hk,y)), volume (I3 hk_mK z)
      ≤ 2⁻¹ * volume (I3 hk y) := by
  calc
    ∑' (z : Yk X (k - K')), ∑ᶠ (_ : clProp(hk_mK,z|hk,y)), volume (I3 hk_mK z)
    _ = ∑' (z : Yk X (k - K')), volume (⋃ (_ : clProp(hk_mK,z|hk,y)), I3 hk_mK z) := by
      apply tsum_congr
      intro z
      letI : Decidable clProp(hk_mK,z|hk,y):= Classical.propDecidable _
      rw [finsum_eq_if, iUnion_eq_if]
      if h : clProp(hk_mK,z|hk,y) then
        simp_rw [if_pos h]
      else
        simp_rw [if_neg h]
        rw [measure_empty]
    _ ≤ 2⁻¹ * volume (I3 hk y) := small_boundary' k hk hk_mK y

lemma le_s_1' (n : ℕ) {k : ℤ} (hk_mn1K : -S ≤ k - (n + 1 : ℕ) * K') : (-S ≤ (k - K') - n * K') := by
  simp only [Nat.cast_add, Nat.cast_one] at hk_mn1K
  linarith

lemma le_s_2' (n : ℕ) {k : ℤ} (hk_mn1K : -S ≤ k - (n + 1 : ℕ) * K') : (-S ≤ k - K') := by
  simp only [Nat.cast_add, Nat.cast_one] at hk_mn1K
  rw [right_distrib] at hk_mn1K
  apply hk_mn1K.trans
  simp only [one_mul, tsub_le_iff_right, sub_add_add_cancel, le_add_iff_nonneg_right]
  positivity

lemma boundary_sum_eq {k : ℤ} (hk : -S ≤ k) {k' : ℤ} (hk' : -S ≤ k') (y : Yk X k) :
    ∑'(y' : Yk X k'), ∑ᶠ (_ : clProp(hk',y'|hk,y)), volume (I3 hk' y') =
      volume (⋃ (y' : Yk X k'), ⋃ (_ : clProp(hk',y'|hk,y)), I3 hk' y') := by
  letI := (Yk_countable X k').to_subtype
  rw [measure_iUnion]
  · apply tsum_congr
    intro y'
    letI : Decidable clProp(hk',y'|hk,y) := Classical.propDecidable _
    rw [finsum_eq_if,iUnion_eq_if]
    if h : clProp(hk',y'|hk,y) then
      simp_rw [if_pos h]
    else
      simp_rw [if_neg h, measure_empty]
  · intro i i' hneq
    simp only [disjoint_iUnion_right, disjoint_iUnion_left]
    rw [Set.disjoint_iff]
    intro _ _ x hx
    exact hneq (I3_prop_1 _ hx)
  exact fun y' ↦ MeasurableSet.iUnion (fun _ ↦ I3_measurableSet hk' y')

lemma smaller_boundary (n : ℕ) :
    ∀ {k : ℤ}, (hk : -S ≤ k) → (hk_mnK : -S ≤ k - n * K') → ∀ (y : Yk X k),
      ∑' (y' : Yk X (k - n * K')), ∑ᶠ (_ : clProp(hk_mnK,y'|hk,y)), volume (I3 hk_mnK y') ≤
        2⁻¹ ^ n * volume (I3 hk y) := by
  induction n
  · intro k hk hk_mnK y
    rw [boundary_sum_eq hk hk_mnK y]
    simp only [Int.cast_ofNat_Int, defaultA, pow_zero, one_mul]
    gcongr
    simp only [iUnion_subset_iff]
    exact fun _ hy' => hy'.I3_subset
  rename_i n hinduction
  intro k hk hk_mnK y
  rw [boundary_sum_eq hk hk_mnK y]
  calc
    volume (⋃ (y'' : Yk X (k - (n + 1 : ℕ) * K')),
      ⋃ (_:clProp(hk_mnK,y''|hk,y)), I3 hk_mnK y'')
    ≤ volume (⋃ (y' : Yk X (k - K')), ⋃ (_ : clProp(le_s_2' n hk_mnK,y'|hk,y)),
        ⋃ (y'' : Yk X (k - (n + 1 : ℕ) * K')),
          ⋃ (_ : clProp(hk_mnK,y''|le_s_2' n hk_mnK,y')), I3 hk_mnK y'') := by
      apply volume.mono
      simp only [iUnion_subset_iff]
      intro y'' hy'' x hx
      simp only [mem_iUnion, exists_prop]
      have hx_y: x ∈ I3 hk y := hy''.I3_subset hx
      have : x ∈ ⋃ (y' : Yk X (k - K')), I3 (le_s_2' n hk_mnK) y' :=
        cover_by_cubes (le_s_2' n hk_mnK) (by linarith) hk y hx_y
      simp only [mem_iUnion] at this
      obtain ⟨y', hx_y'⟩ := this
      use y'
      have hz : clProp(hk_mnK,y''|(le_s_2' n hk_mnK),y') ∧ clProp((le_s_2' n hk_mnK),y'|hk,y):= by
        apply transitive_boundary hk_mnK (le_s_2' n hk_mnK) hk _ (by linarith) y'' y' y x _ hy''
        · simp only [Nat.cast_add, Nat.cast_one]
          rw [right_distrib, one_mul]
          gcongr
          trans 0 + ↑(@const_K a)
          · rw [zero_add]
          gcongr; positivity
        · simp only [mem_inter_iff, and_assoc]
          use hx
      use hz.right, y'', hz.left
    _ = ∑' (y' : Yk X (k - K')), ∑ᶠ (_ : clProp(le_s_2' n hk_mnK,y'|hk,y)),
          volume (⋃ (y'' : Yk X (k - (n + 1 : ℕ) * K')),
            ⋃ (_ : clProp(hk_mnK,y''|le_s_2' n hk_mnK,y')), I3 hk_mnK y'') := by
      letI := (Yk_countable X (k - K')).to_subtype
      rw [measure_iUnion]
      · apply tsum_congr
        intro y'
        letI : Decidable clProp(le_s_2' n hk_mnK,y'|hk,y) := Classical.propDecidable _
        rw [iUnion_eq_if, finsum_eq_if]
        if h : clProp(le_s_2' n hk_mnK,y'|hk,y) then
          simp_rw [if_pos h]
        else
          simp_rw [if_neg h, measure_empty]
      · intro i i' hneq
        simp only [disjoint_iUnion_right, disjoint_iUnion_left]
        intro _ y1 hy1i _ y2 hy2i'
        apply Disjoint.mono_left hy2i'.I3_subset
        apply Disjoint.mono_right hy1i.I3_subset
        rw [Set.disjoint_iff]
        intro x hx
        exact hneq (I3_prop_1 _ hx)
      intro y'
      apply MeasurableSet.iUnion
      intro _
      letI := (Yk_countable X (k-(n+1:ℕ)*K')).to_subtype
      apply MeasurableSet.iUnion
      intro y''
      apply MeasurableSet.iUnion (fun _ ↦ I3_measurableSet hk_mnK y'')
    _ = ∑' (y' : Yk X (k - K')), ∑ᶠ (_ : clProp(le_s_2' n hk_mnK,y'|hk,y)),
          ∑' (y'': Yk X (k - (n + 1 : ℕ) * K')), ∑ᶠ (_ : clProp(hk_mnK,y''|le_s_2' n hk_mnK,y')),
            volume (I3 hk_mnK y'') := by
      apply tsum_congr
      intro y'
      apply finsum_congr
      intro hcly'
      rw [boundary_sum_eq (le_s_2' n hk_mnK) hk_mnK y']
    _ = ∑' (y' : Yk X (k - K')), ∑ᶠ (_ : clProp(le_s_2' n hk_mnK,y'|hk,y)),
          ∑' (y'' : Yk X ((k - K') - n * K')), ∑ᶠ (_ : clProp(le_s_1' n hk_mnK,y''|le_s_2' n hk_mnK,y')),
            volume (I3 (le_s_1' n hk_mnK) y'') := by
      have : k - (n + 1 : ℕ) * K' = (k - K') - n * K' := by
        rw [Nat.cast_add, Nat.cast_one,add_comm,right_distrib,one_mul,Int.sub_sub]
      congr! 8
    _ ≤ ∑' (y' : Yk X (k - K')), ∑ᶠ (_ : clProp(le_s_2' n hk_mnK,y'|hk,y)),
          2⁻¹ ^ n * volume (I3 (le_s_2' n hk_mnK) y') := by
      apply ENNReal.summable.tsum_le_tsum _ (ENNReal.summable)
      intro y'
      letI : Decidable clProp(le_s_2' n hk_mnK,y'|hk,y) := Classical.propDecidable _
      rw [finsum_eq_if, finsum_eq_if]
      if h : clProp(le_s_2' n hk_mnK,y'|hk,y) then
        simp_rw [if_pos h]
        apply hinduction
      else
        simp_rw [if_neg h]
        exact le_refl _
    _ = 2⁻¹ ^ n * ∑' (y' : Yk X (k - K')), ∑ᶠ (_ : clProp(le_s_2' n hk_mnK,y'|hk,y)),
          volume (I3 (le_s_2' n hk_mnK) y') := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y'
      letI : Decidable clProp(le_s_2' n hk_mnK,y'|hk,y) := Classical.propDecidable _
      rw [finsum_eq_if,finsum_eq_if]
      if h : clProp(le_s_2' n hk_mnK,y'|hk,y) then
        simp_rw [if_pos h]
      else
        simp_rw [if_neg h, mul_zero]
    _ ≤ 2⁻¹ ^ n * (2⁻¹ * volume (I3 hk y)) := by
      gcongr
      apply _root_.small_boundary
    _ = 2⁻¹ ^ (n + 1) * volume (I3 hk y) := by
      rw [pow_add, pow_one, mul_assoc]

section ProofData
include q K σ₁ σ₂ F G

variable (a) in
def const_n {t : ℝ} (_ht : t ∈ Ioo 0 1) : ℕ := ⌊-Real.logb D t / K'⌋₊

variable {t : ℝ}

variable (X) in
theorem prefloor_nonneg (ht : t ∈ Ioo 0 1) :
    0 ≤ -Real.logb (↑D) t / K' := by
  apply div_nonneg _ (K_pos).le
  simp only [Left.nonneg_neg_iff]
  rw [Real.logb_nonpos_iff (one_lt_realD X) ht.left]
  exact ht.right.le

variable (X) in
lemma const_n_prop_1 (ht : t ∈ Ioo 0 1) : D ^ (const_n a ht * K') ≤ t⁻¹ := by
  simp only [mem_Ioo] at ht
  rw [← Real.rpow_logb (defaultD_pos a) (one_lt_realD X).ne.symm (inv_pos.mpr ht.left),
    ← Real.rpow_natCast,Real.rpow_le_rpow_left_iff (one_lt_realD X)]
  simp only [Nat.cast_mul, Real.logb_inv]
  rw [← le_div_iff₀ (K_pos), const_n]
  exact Nat.floor_le (prefloor_nonneg X ht)

variable (X) in
lemma const_n_prop_2 (ht : t ∈ Ioo 0 1) (k : ℤ) : t * D ^ k ≤ D ^ (k - const_n a ht * K') := by
  let _ : MulPosReflectLE ℝ := inferInstance -- perf: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/performance.20example.20with.20type-class.20inference
  rw [sub_eq_neg_add, zpow_add₀ (defaultD_pos a).ne.symm,
    mul_le_mul_right (zpow_pos (defaultD_pos a) _), zpow_neg,
    le_inv_comm₀ ht.left (zpow_pos (defaultD_pos a) _)]
  exact const_n_prop_1 X ht

variable (X) in
lemma const_n_is_max (ht : t ∈ Ioo 0 1) (n : ℕ) : D ^ (n * K') ≤ t⁻¹ → n ≤ const_n a ht := by
  simp only [mem_Ioo] at ht
  rw [← Real.rpow_logb (defaultD_pos a) (one_lt_realD X).ne.symm (inv_pos.mpr ht.left)]
  rw [← Real.rpow_natCast,Real.rpow_le_rpow_left_iff (one_lt_realD X)]
  simp only [Nat.cast_mul, Real.logb_inv]
  rw [← le_div_iff₀ (K_pos), const_n]
  exact fun h ↦ Nat.le_floor h

variable (X) in
lemma const_n_prop_3 (ht : t ∈ Ioo 0 1) :
    (t * D ^ K' : ℝ)⁻¹ ≤ ↑D ^ (const_n a ht * K') := by
  dsimp only [const_n]
  rw [mul_inv, ← div_eq_mul_inv, div_le_iff₀ (pow_pos (defaultD_pos a) _), ← pow_add]
  nth_rw 3 [← one_mul K']
  rw [← right_distrib]
  nth_rw 1 [← Real.rpow_logb (defaultD_pos a) (one_lt_realD X).ne.symm ht.left]
  rw [← Real.rpow_neg (realD_nonneg), ← Real.rpow_natCast, Real.rpow_le_rpow_left_iff (one_lt_realD X)]
  push_cast
  rw [← div_le_iff₀ (K_pos)]
  exact Nat.lt_floor_add_one (-Real.logb (↑D) t / ↑const_K) |>.le

variable (X) in
lemma const_n_nonneg (ht : t ∈ Ioo 0 1) : 0 ≤ const_n a ht := by
  apply const_n_is_max X ht 0
  simp only [zero_mul, pow_zero]
  exact one_le_inv_iff₀.mpr <| ⟨ht.left, ht.right.le⟩

variable (X) in
lemma kappa_le_log2D_inv_mul_K_inv : κ ≤ (Real.logb 2 D * K')⁻¹ := by
  have : 2 ≤ a := by linarith [four_le_a X]
  have 𝕔_pos : 0 < 𝕔 := by linarith [seven_le_c]
  rw [defaultD]
  simp only [Nat.cast_pow, Nat.cast_ofNat, mul_inv_rev]
  rw [← Real.rpow_natCast,Real.logb_rpow (by norm_num) (by norm_num)]
  rw [defaultκ, const_K, neg_mul, Real.rpow_neg (by positivity),
    ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]
  rw [mul_comm, pow_add, pow_one, ← mul_assoc, mul_comm _ 2, ← mul_assoc, ← mul_assoc,
    ← Real.rpow_natCast 2]
  norm_num
  calc
    (2 : ℝ) * 𝕔 * a ^ 2 * 2 ^ (4 * a : ℝ)
      ≤ 2 ^ 8 * (2 ^ (a : ℝ)) ^ 2 * 2 ^ (4 * a : ℝ) := by
      gcongr
      · norm_cast
        linarith [c_le_100]
      · exact (Real.self_lt_two_rpow (a : ℝ)).le
    _ ≤ 2 ^ (4 * a : ℝ) * 2 ^ (2 * a : ℝ) * 2 ^ (4 * a : ℝ) := by
      gcongr
      · rw [← Real.rpow_natCast, Real.rpow_le_rpow_left_iff (by norm_num)]
        norm_num
        trans 4 * 2
        · norm_num
        rw [mul_le_mul_left (by norm_num)]
        exact Nat.ofNat_le_cast.mpr this
      · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
        simp only [Nat.cast_ofNat, le_refl]
    _ ≤ 2 ^ (10 * a : ℝ) := by
      simp_rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), ← right_distrib]
      norm_num

end ProofData

lemma boundary_measure {k : ℤ} (hk : -S ≤ k) (y : Yk X k) {t : ℝ≥0} (ht : t ∈ Set.Ioo 0 1)
    (htD : (D ^ (-S : ℤ) : ℝ) ≤ t * D ^ k) :
    volume ({x | x ∈ I3 hk y ∧ EMetric.infEdist x (I3 hk y)ᶜ ≤ (↑t * ↑D ^ k)}) ≤
      2 * t ^ κ * volume (I3 hk y) := by
  have hconst_n : -S ≤ k - const_n a ht * K' := by
    suffices (D ^ (-S : ℤ) : ℝ) ≤ D ^ (k - const_n a ht * K' : ℤ) by
      simp_rw [← Real.rpow_intCast] at this
      rw [Real.rpow_le_rpow_left_iff (one_lt_realD X)] at this
      simp only [Int.cast_le] at this
      exact this
    exact htD.trans (const_n_prop_2 X ht k)
  have hconst_n_k : k - const_n a ht * K' ≤ k := by
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    positivity
  simp only [mem_Ioo] at ht
  calc
    volume ({x | x ∈ I3 hk y ∧ EMetric.infEdist x (I3 hk y)ᶜ ≤ (↑t * ↑D ^ k)})
    _ ≤ volume (⋃ (y' : Yk X (k - const_n a ht *K')), ⋃ (_ : clProp(hconst_n,y'|hk,y)),
          I3 hconst_n y') := by
      apply volume.mono
      intro x
      simp only [mem_setOf_eq, NNReal.val_eq_coe, and_imp]
      intro hxi3 hxb'
      have : x ∈ ⋃ (y' : Yk X (k - const_n a ht * K')), I3 hconst_n y' :=
        cover_by_cubes hconst_n hconst_n_k hk y hxi3
      simp only [mem_iUnion] at this ⊢
      obtain ⟨y', hy'⟩ := this
      have hxy' : x ∈ ball (y' : X) (4 * D ^ (k - const_n a ht * K')) := by
        apply I3_prop_3_2
        exact hy'
      refine ⟨y', ⟨?_, ?_⟩, hy'⟩
      · apply dyadic_property hconst_n hconst_n_k hk y y'
        rw [not_disjoint_iff]
        use x
      rw [← emetric_ball, EMetric.mem_ball,ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ← Real.rpow_intCast, ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a),
        ENNReal.ofReal_natCast,ENNReal.rpow_intCast,edist_comm] at hxy'
      have : 0 < (Nat.cast D : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast,ENNReal.ofReal_pos]
        exact defaultD_pos a
      calc
        EMetric.infEdist (y' : X) (I3 hk y)ᶜ
        _ ≤ EMetric.infEdist (x:X) (I3 hk y)ᶜ + edist (y':X) x :=
          EMetric.infEdist_le_infEdist_add_edist
        _ < t * D^k + 4 * D^(k-const_n a ht * K') := by
          apply ENNReal.add_lt_add_of_le_of_lt _ hxb' hxy'
          apply (hxb'.trans_lt _).ne
          finiteness
        _ ≤ D ^ (k - const_n a ht * K') + 4 * D ^ (k - const_n a ht * K') := by
          rw [ENNReal.add_le_add_iff_right]
          · have := const_n_prop_2 X ht k
            simp only at this
            nth_rw 1 [NNReal.val_eq_coe] at this
            simp_rw [← Real.rpow_intCast] at this
            rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
              ENNReal.ofReal_mul (by exact ht.left.le), ENNReal.ofReal_coe_nnreal,
              ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a),
              ← ENNReal.ofReal_rpow_of_pos (defaultD_pos a), ENNReal.ofReal_natCast,
              ENNReal.rpow_intCast, ENNReal.rpow_intCast] at this
            exact this
          finiteness
        _ ≤ 6 * ↑D ^ (k - const_n a ht * ↑const_K) := by
          nth_rw 1 [← one_mul (D ^ (k - const_n a ht * K') : ℝ≥0∞), ← right_distrib]
          rw [ENNReal.mul_le_mul_right]
          · norm_num
          · apply LT.lt.ne'
            rw [← ENNReal.rpow_intCast]
            exact ENNReal.rpow_pos this (by finiteness)
          finiteness
    _ = ∑' (y' : Yk X (k - const_n a ht * K')), ∑ᶠ(_ : clProp(hconst_n, y'|hk, y)),
          volume (I3 hconst_n y') := by rw [boundary_sum_eq hk hconst_n y]
    _ ≤ 2⁻¹ ^ (const_n a ht) * volume (I3 hk y) := by apply smaller_boundary
    _ ≤ 2 * t ^ κ * volume (I3 hk y) := by
      refine mul_le_mul' ?_ (le_refl _)
      suffices hsuf : ((2⁻¹ ^ (const_n a ht) : ℝ≥0) : ℝ≥0∞) ≤ (2 * t ^ κ : ℝ≥0) by
        push_cast at hsuf
        rw [ENNReal.coe_rpow_def]
        have : ¬(t = 0 ∧ κ < 0) := by
          push_neg
          intro h
          by_contra
          exact ht.left.ne h.symm
        rw [if_neg this]
        exact hsuf
      rw [ENNReal.coe_le_coe]
      suffices hsuf : (2⁻¹ ^ const_n a ht : ℝ) ≤ 2 * t ^ κ by
        exact hsuf -- TIL: things in ℝ≥0 are very defeq to things in ℝ
      calc
        (2⁻¹ ^ const_n a ht : ℝ)
        _ = 2 ^ (-const_n a ht : ℝ) := by
          rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast,Real.inv_rpow (by norm_num)]
        _ = (D ^ ((Real.logb 2 D)⁻¹)) ^ (-const_n a ht : ℝ) := by
          rw [Real.inv_logb, Real.rpow_logb (defaultD_pos a) (one_lt_realD X).ne' (by norm_num)]
        _ = D ^ ((const_n a ht * K' : ℝ) * -(Real.logb 2 D * K' : ℝ)⁻¹) := by
          rw [← Real.rpow_mul realD_nonneg]
          congr 1
          rw [mul_neg, mul_neg]
          congr 1
          rw [mul_inv, mul_assoc, mul_comm (K' : ℝ), mul_assoc, inv_mul_cancel₀ K_pos.ne',
            mul_one, mul_comm]
        _ = (D ^ (const_n a ht * K' : ℝ) : ℝ)⁻¹ ^ (Real.logb 2 D * K' : ℝ)⁻¹ := by
          rw [Real.rpow_mul (realD_nonneg), Real.rpow_neg (by positivity),
            Real.inv_rpow (by positivity)]
        _ ≤ (t * D ^(K' : ℝ)) ^ (Real.logb 2 D * K' : ℝ)⁻¹ := by
          rw [Real.rpow_le_rpow_iff]
          · rw [inv_le_comm₀]
            · rw [← Nat.cast_mul, Real.rpow_natCast, Real.rpow_natCast]
              exact const_n_prop_3 X ht
            · exact Real.rpow_pos_of_pos (defaultD_pos a) _
            · rw [mul_pos_iff_of_pos_right]
              · exact ht.left
              · exact Real.rpow_pos_of_pos (defaultD_pos a) _
          · positivity
          · positivity
          · rw [inv_pos,mul_pos_iff_of_pos_right (K_pos)]
            exact Real.logb_pos (by norm_num) (one_lt_realD X)
        _ = 2 * t ^ (Real.logb 2 D * K' : ℝ)⁻¹ := by
          rw [Real.mul_rpow,mul_comm, ← Real.rpow_mul (realD_nonneg), mul_comm (K' : ℝ)]
          · rw [mul_inv, mul_assoc, inv_mul_cancel₀ K_pos.ne', mul_one, Real.inv_logb,
              Real.rpow_logb (defaultD_pos a) (one_lt_realD X).ne' (by norm_num)]
          · exact ht.left.le
          positivity
        _ ≤ (2 * t ^ κ : ℝ) := by
          rw [mul_le_mul_left (by linarith)]
          have : (t : ℝ) ∈ Ioo 0 1 := ht
          rw [mem_Ioo] at this
          rw [Real.rpow_le_rpow_left_iff_of_base_lt_one (this.left) (this.right)]
          exact kappa_le_log2D_inv_mul_K_inv X

lemma boundary_measure' {k : ℤ} (hk : -S ≤ k) (y : Yk X k) {t : ℝ≥0} (ht : t ∈ Set.Ioo 0 1)
    (htD : (D ^ (-S : ℤ) : ℝ) ≤ t * D ^ k) :
    volume.real ({x | x ∈ I3 hk y ∧ EMetric.infEdist x (I3 hk y)ᶜ ≤ (↑t * ↑D ^ k)}) ≤
      2 * t ^ κ * volume.real (I3 hk y) := by
  dsimp only [Measure.real]
  calc
    volume ({x | x ∈ I3 hk y ∧ EMetric.infEdist x (I3 hk y)ᶜ ≤ (↑t * ↑D ^ k)}) |>.toReal
    _ ≤ ((2 : ℝ≥0∞) * t ^ κ : ℝ≥0∞).toReal * (volume (I3 hk y)).toReal := by
        rw [← ENNReal.toReal_mul]
        rw [ENNReal.toReal_le_toReal]
        · exact boundary_measure hk y ht htD
        · apply ne_of_lt
          apply volume.mono inter_subset_left |>.trans_lt
          apply volume.mono (I3_prop_3_2 hk y) |>.trans_lt
          simp only [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
          finiteness
        apply ENNReal.mul_ne_top
        · have : 0 ≤ κ := κ_nonneg
          finiteness
        exact volume.mono (I3_prop_3_2 hk y) |>.trans_lt measure_ball_lt_top |>.ne
    _ = 2 * t ^ κ * (volume (I3 hk y)).toReal := by
      congr
      rw [ENNReal.toReal_mul]
      simp only [ENNReal.toReal_ofNat, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
      rw [← ENNReal.toReal_rpow]
      simp only [ENNReal.coe_toReal]

variable (X) in
@[ext]
structure 𝓓 where
  k : ℤ
  hk : -S ≤ k
  hk_max : k ≤ S
  y : Yk X k
  hsub : I3 hk y ⊆ I3 (by trans 0 <;> simp : (-S : ℤ) ≤ S) ⟨o,o_mem_Yk_S⟩

variable (X) in
def max_𝓓 : 𝓓 X where
  k := S
  hk := by trans 0 <;> simp
  hk_max := Int.le_refl (S : ℤ)
  y := ⟨o,o_mem_Yk_S⟩
  hsub := fun ⦃a_1⦄ a ↦ a

def 𝓓.coe (z : 𝓓 X) : Set X := I3 z.hk z.y

variable (X) in
def forget_map (x : 𝓓 X) : (k : Set.Icc (-S : ℤ) S) × (Yk X k) := ⟨⟨x.k,And.intro x.hk x.hk_max⟩,x.y⟩

lemma forget_map_inj : Function.Injective (forget_map X) := by
  intro x1 x2 h
  dsimp only [forget_map] at h
  simp only [Sigma.mk.inj_iff, Subtype.mk.injEq] at h
  exact 𝓓.ext_iff.mpr h

variable (X) in
lemma 𝓓_finite : Finite (𝓓 X) := by
  have _ (k : Set.Icc (-S : ℤ) S) : Finite (Yk X k) :=
    Set.Finite.to_subtype (Yk_finite k.property.left)
  apply Finite.of_injective (forget_map X) forget_map_inj

-- Note: we might want to slightly adapt the construction so that there is only 1 tile at level S
-- with center `o` (then we might not cover all of `ball o (D ^ S)`, but most of it)
variable (X) in
/-- Proof that there exists a grid structure. -/
def grid_existence : GridStructure X D κ S o where
  Grid := 𝓓 X
  fintype_Grid := @Fintype.ofFinite (𝓓 X) (𝓓_finite X)
  coeGrid := fun z => z.coe
  s := fun z => z.k
  c := fun z => z.y
  inj := fun ⟨k,hk,hk_max,y,hsub⟩ ⟨k2,hk2,hk2_max,y2,hsub'⟩ h => by
    simp only [Prod.mk.injEq, 𝓓.mk.injEq] at h hsub hsub' ⊢
    dsimp [𝓓.coe] at h hsub hsub'
    obtain ⟨hl, hr⟩ := h
    subst hr
    simp only [heq_eq_eq, true_and]
    apply I3_prop_1 hk2 (x := y)
    have hl' := hl.symm
    rw [hl']
    simp only [inter_self]
    apply I3_prop_3_1
    simp only [mem_ball, dist_self, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    exact zpow_pos (defaultD_pos a) _
  range_s_subset := by
    intro i
    simp only [mem_range, mem_Icc, forall_exists_index]
    intro x hz
    subst hz
    use x.hk, x.hk_max
  topCube := max_𝓓 X
  s_topCube := rfl
  c_topCube := rfl
  subset_topCube := by
    intro i
    exact i.hsub
  Grid_subset_biUnion := by
    intro i l hl
    simp only [mem_Ico] at hl
    simp only [mem_preimage, mem_singleton_iff]
    have : i.coe ⊆ (max_𝓓 X).coe := i.hsub
    intro x hx
    simp only [mem_iUnion, exists_prop]
    have : i.coe ⊆ ⋃ y', I3 hl.left y' := cover_by_cubes hl.left hl.right.le i.hk i.y
    specialize this hx
    simp only [mem_iUnion] at this
    obtain ⟨y', hy'⟩ := this
    have : I3 (hl.left) y' ⊆ (max_𝓓 X).coe := by
      apply dyadic_property
      · exact hl.right.le.trans i.hk_max
      · rw [Set.not_disjoint_iff]
        exact ⟨x, hy', this hx⟩
    use ⟨l,hl.left,hl.right.le.trans i.hk_max,y',this⟩
    simp only [true_and]
    exact hy'
  fundamental_dyadic' := by
    intro i j hk
    if h : Disjoint i.coe j.coe then
      exact Or.inr h
    else
      exact Or.inl (dyadic_property i.hk hk j.hk j.y i.y h)
  ball_subset_Grid := by
    intro i
    apply Subset.trans (ball_subset_ball _) (I3_prop_3_1 i.hk i.y)
    rw [div_eq_mul_inv,mul_comm]
    gcongr
    norm_num
  Grid_subset_ball {i} := I3_prop_3_2 i.hk i.y
  small_boundary := by
    intro i t ht
    if ht' : t < 1 then
      apply boundary_measure' i.hk i.y
      · simp only [mem_Ioo]
        refine ⟨?_, ht'⟩
        apply lt_of_lt_of_le (zpow_pos (defaultD_pos a) _) ht
      rw [zpow_sub₀, div_le_iff₀] at ht
      · exact ht
      · exact zpow_pos (defaultD_pos a) _
      apply LT.lt.ne'
      exact defaultD_pos a
    else
      trans volume.real i.coe
      · apply measureReal_mono (fun x hx => hx.left) <|
          volume.mono (I3_prop_3_2 i.hk i.y) |>.trans_lt _ |>.ne
        simp only [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
        exact measure_ball_lt_top
      apply le_mul_of_one_le_left (measureReal_nonneg)
      have : 1 ≤ (t : ℝ) ^ κ := Real.one_le_rpow (le_of_not_gt ht') κ_nonneg
      linarith
  coeGrid_measurable {i} := I3_measurableSet i.hk i.y

/-! ## Proof that there exists a tile structure on a grid structure. -/

variable [GridStructure X D κ S o] {I : Grid X}

/-- The constant appearing in 4.2.2 (3 / 10). -/
@[simp] def C𝓩 : ℝ := 3 / 10

section
variable (I)

open scoped Classical in
def 𝓩_cands : Finset (Finset (Θ X)) :=
  Q.range.powerset.filter fun z ↦ z.toSet.PairwiseDisjoint (ball_{I} · C𝓩)

lemma exists_𝓩_max_card : ∃ zmax ∈ 𝓩_cands I, ∀ z ∈ 𝓩_cands I, z.card ≤ zmax.card :=
  (𝓩_cands I).exists_max_image Finset.card ⟨∅, by simp [𝓩_cands]⟩

/-- A finset of maximal cardinality satisfying (4.2.1) and (4.2.2). -/
def 𝓩 : Finset (Θ X) := (exists_𝓩_max_card I).choose

end

lemma 𝓩_spec : 𝓩 I ⊆ Q.range ∧ (𝓩 I).toSet.PairwiseDisjoint (ball_{I} · C𝓩) ∧
    ∀ z ∈ 𝓩_cands I, z.card ≤ (𝓩 I).card := by
  classical
  rw [← and_assoc]; convert (exists_𝓩_max_card I).choose_spec; change _ ↔ 𝓩 I ∈ _
  rw [𝓩_cands, Finset.mem_filter, Finset.mem_powerset]

lemma 𝓩_subset : 𝓩 I ⊆ Q.range := 𝓩_spec.1
lemma 𝓩_pairwiseDisjoint : (𝓩 I).toSet.PairwiseDisjoint (ball_{I} · C𝓩) := 𝓩_spec.2.1
lemma 𝓩_max_card : ∀ z ∈ 𝓩_cands I, z.card ≤ (𝓩 I).card := 𝓩_spec.2.2

lemma 𝓩_nonempty : (𝓩 I).Nonempty := by
  by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
  have j := 𝓩_max_card (I := I)
  simp_rw [h, Finset.card_empty, nonpos_iff_eq_zero, Finset.card_eq_zero] at j
  replace j : 𝓩_cands I = {∅} := Finset.eq_singleton_iff_unique_mem.mpr ⟨(by simp [𝓩_cands]), j⟩
  have k : {Q default} ∈ 𝓩_cands I := by simp [𝓩_cands]
  simp_all

instance : Inhabited (𝓩 I) := ⟨⟨_, 𝓩_nonempty.choose_spec⟩⟩

/-- 7 / 10 -/
@[simp] def C4_2_1 : ℝ := 7 / 10 /- 0.6 also works? -/

/-- Equation (4.2.3), Lemma 4.2.1 -/
lemma frequency_ball_cover : Q.range.toSet ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 := by
  intro θ hθ
  classical
  obtain ⟨z, hz, hz'⟩ : ∃ z, z ∈ 𝓩 I ∧ ¬Disjoint (ball_{I} z C𝓩) (ball_{I} θ C𝓩) := by
    by_contra! h
    have hθ' : θ ∉ (𝓩 I : Set (Θ X)) := fun hθ' ↦ by
      have := h _ hθ'; norm_num at this
    let 𝓩' := insert θ (𝓩 I)
    apply absurd (𝓩_max_card (I := I)) _; push_neg; refine ⟨𝓩', ?_, ?_⟩
    · simp_rw [𝓩', 𝓩_cands, Finset.mem_filter, Finset.mem_powerset, Finset.insert_subset_iff,
        Finset.coe_insert, pairwiseDisjoint_insert_of_notMem hθ', Finset.mem_coe]
      exact ⟨⟨hθ, 𝓩_subset⟩, 𝓩_pairwiseDisjoint, fun y hy ↦ (h y hy).symm⟩
    · rw [Finset.card_insert_of_notMem hθ']; exact lt_add_one _
  rw [not_disjoint_iff] at hz'; obtain ⟨z', h₁z', h₂z'⟩ := hz'
  simp only [mem_iUnion, mem_ball, exists_prop, C𝓩, C4_2_1] at h₁z' h₂z' ⊢
  use z, hz; linarith [dist_triangle_left (α := (WithFunctionDistance (c I) (D ^ s I / 4))) θ z z']

local instance tileData_existence [GridStructure X D κ S o] : PreTileStructure Q D κ S o where
  𝔓 := Σ I : Grid X, 𝓩 I
  fintype_𝔓 := Sigma.instFintype
  𝓘 p := p.1
  surjective_𝓘 I := ⟨⟨I, default⟩, rfl⟩
  𝒬 p := p.2
  range_𝒬 := by rintro _ ⟨p, rfl⟩; rw [← SimpleFunc.mem_range]; exact 𝓩_subset p.2.2

namespace Construction

def Ω₁_aux (I : Grid X) (k : ℕ) : Set (Θ X) :=
  if hk : k < Nat.card (𝓩 I) then
    let z : Θ X := (Finite.equivFin (𝓩 I) |>.symm ⟨k, hk⟩).1
    ball_{I} z C4_2_1 \ (⋃ i ∈ (𝓩 I).toSet \ {z}, ball_{I} i C𝓩) \ ⋃ i < k, Ω₁_aux I i
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
  · apply subset_biUnion_of_mem (show z' ∈ (𝓩 I).toSet \ {z} by tauto)

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
  rw [Ω₁, Ω₁_aux]; set z := p.2
  simp_rw [Fin.eta, Equiv.symm_apply_apply]
  set k := (Finite.equivFin ↑(𝓩 p.1)) z with h'k
  simp_rw [k.2, dite_true]
  change ball_{p.1} z.1 C𝓩 ⊆ _ \ ⋃ i < k.1, Ω₁_aux p.1 i
  refine subset_diff.mpr ⟨subset_diff.mpr ⟨ball_subset_ball (by norm_num), ?_⟩, ?_⟩
  · rw [disjoint_iUnion₂_right]; intro i hi; rw [mem_diff_singleton] at hi
    exact 𝓩_pairwiseDisjoint z.coe_prop hi.1 hi.2.symm
  · rw [disjoint_iUnion₂_right]; intro i hi
    let z' := (Finite.equivFin ↑(𝓩 p.1)).symm ⟨i, by omega⟩
    have zn : z ≠ z' := by simp only [ne_eq, Equiv.eq_symm_apply, z']; exact Fin.ne_of_gt hi
    simpa [z'] using disjoint_ball_Ω₁_aux p.1 z'.2 z.2 (Subtype.coe_ne_coe.mpr zn.symm)

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
  set f := Finite.equivFin (𝓩 I) with hf
  by_cases h : ∃ y ∈ 𝓩 I, ϑ ∈ ball_{I} y C𝓩
  · obtain ⟨z', mz', hz'⟩ := h
    exact subset_iUnion_of_subset _ subset_rfl (ball_subset_Ω₁ ⟨I, ⟨z', mz'⟩⟩ hz')
  · let L := {k : Fin (Nat.card (𝓩 I)) | ϑ ∈ ball_{I} (f.symm k).1 C4_2_1}
    have Ln : L.Nonempty := by use f ⟨z, mz⟩; rwa [mem_setOf, Equiv.symm_apply_apply]
    obtain ⟨k, mem_k, hk⟩ := L.exists_min_image id L.toFinite Ln
    simp_rw [L, mem_setOf_eq] at mem_k
    simp only [id_eq] at hk
    have q : ∀ i < k, ϑ ∉ Ω₁_aux I i := by
      by_contra! h; obtain ⟨i, li, hi⟩ := h
      have := Ω₁_subset_ball ⟨I, f.symm i⟩
      simp_rw [Ω₁, ← hf, Equiv.apply_symm_apply] at this
      replace this : ϑ ∈ ball_{I} (f.symm i).1 C4_2_1 := this hi
      replace this : i ∈ L := by simp only [L, mem_setOf_eq, this]
      exact absurd (hk i this) (not_le.mpr li)
    rw [mem_iUnion]; use f.symm k; rw [Ω₁, Ω₁_aux]; dsimp only
    rw [Equiv.apply_symm_apply]; simp_rw [k.2]; rw [dite_true, mem_diff, mem_diff]
    refine ⟨⟨mem_k, ?_⟩, ?_⟩
    · rw [mem_iUnion₂]; push_neg at h ⊢; exact fun i mi ↦ h i mi.1
    · rw [mem_iUnion₂]; push_neg; exact fun i mi ↦ q ⟨i, mi.trans k.2⟩ mi

/-- 1 / 5 -/
@[simp] def CΩ : ℝ := 1 / 5

open scoped Classical in
def Ω (p : 𝔓 X) : Set (Θ X) :=
  if h : IsMax p.1 then Ω₁ p else
  have := Grid.opSize_succ_lt h
  ball_(p) (𝒬 p) CΩ ∪ ⋃ (z : Θ X) (hz : z ∈ (𝓩 p.1.succ).toSet ∩ Ω₁ p), Ω ⟨p.1.succ, ⟨z, hz.1⟩⟩
termination_by p.1.opSize

lemma 𝔓_induction (P : 𝔓 X → Prop) (base : ∀ p, IsMax p.1 → P p)
    (ind : ∀ p, ¬IsMax p.1 → (∀ z : 𝓩 p.1.succ, P ⟨p.1.succ, by exact z⟩) → P p) :
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
    rw [Ω]; simp only [nmaxI, dite_false]
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
        gcongr; simpa using (Ω₁_subset_ball ⟨I, ⟨y, my⟩⟩) mz₂
      _ ≤ C2_1_2 a * dist_{J} ϑ z + C4_2_1 := by
        gcongr; refine Grid.dist_strictMono (lt_of_le_of_ne Grid.le_succ ?_)
        contrapose! nmaxI; exact Grid.max_of_le_succ nmaxI.symm.le
      _ < C2_1_2 a * 1 + C4_2_1 := by
        gcongr
        · rw [C2_1_2]; positivity
        · simpa only [mem_ball] using (ih ⟨z, mz₁⟩) hz
      _ < 2 ^ (-2 : ℝ) + C4_2_1 := by
        gcongr
        rw [mul_one, C2_1_2, Real.rpow_lt_rpow_left_iff one_lt_two, lt_neg]
        simp only [add_mul, neg_mul, neg_add_rev, neg_neg, lt_neg_add_iff_add_lt]
        norm_cast
        calc
        5 * a + 2
        _ < 6 * a := by linarith [four_le_a X]
        _ ≤ 𝕔 * a := by
          gcongr
          linarith [seven_le_c]
      _ < _ := by norm_num

lemma Ω_disjoint_aux {I : Grid X} (nmaxI : ¬IsMax I) {y z : 𝓩 I} (hn : y ≠ z) :
    Disjoint (ball_{I} y.1 CΩ) (⋃ z', ⋃ (x : z' ∈ (𝓩 I.succ).toSet ∩ Ω₁ ⟨I, z⟩),
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
      · simpa only using (Ω_subset_cball (p := ⟨I.succ, ⟨x, mx₁⟩⟩)) mϑ₂
    _ < CΩ + 2 ^ (-4 : ℝ) := by
      gcongr
      rw [mul_one, C2_1_2, Real.rpow_lt_rpow_left_iff one_lt_two, lt_neg]
      simp only [add_mul, neg_mul, neg_add_rev, neg_neg, lt_neg_add_iff_add_lt]
      norm_cast
      calc
      5 * a + 4
      _ < 7 * a := by linarith [four_le_a X]
      _ ≤ 𝕔 * a := by
        gcongr
        linarith [seven_le_c]
    _ ≤ _ := by norm_num
  replace u := (ball_subset_Ω₁ ⟨I, y⟩) u
  have := dj.ne_of_mem u mx₂; contradiction

lemma Ω_disjoint {p p' : 𝔓 X} (hn : p ≠ p') (h𝓘 : 𝓘 p = 𝓘 p') : Disjoint (Ω p) (Ω p') := by
  change p.1 = p'.1 at h𝓘; obtain ⟨I, y⟩ := p; obtain ⟨_, z⟩ := p'
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

lemma Ω_biUnion {I : Grid X} : Q.range.toSet ⊆ ⋃ p ∈ 𝓘 ⁻¹' ({I} : Set (Grid X)), Ω p := by
  induction I using Grid.induction with
  | base I maxI =>
    intro ϑ mϑ; simp only [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop]
    have l := ((frequency_ball_cover (I := I)).trans iUnion_ball_subset_iUnion_Ω₁) mϑ
    rw [mem_iUnion] at l; obtain ⟨z, mz⟩ := l; use ⟨I, z⟩
    exact ⟨rfl, by rw [Ω]; simp only [maxI, dite_true, mz]⟩
  | ind I nmaxI ih =>
    intro ϑ mϑ
    replace ih := ih mϑ
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at ih ⊢
    obtain ⟨⟨J, z⟩, (rfl : J = I.succ), h⟩ := ih
    have : z.1 ∈ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 :=
      ((Finset.coe_subset.mpr 𝓩_subset).trans frequency_ball_cover) z.2
    rw [mem_iUnion₂] at this; obtain ⟨z', mz', dz⟩ := this
    have zi : ball_{I} z' C4_2_1 ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 :=
      subset_iUnion₂_of_subset z' mz' (subset_refl _)
    replace zi : ↑z ∈ ⋃ f, Ω₁ ⟨I, f⟩ :=
      mem_of_mem_of_subset dz <| zi.trans iUnion_ball_subset_iUnion_Ω₁
    rw [mem_iUnion] at zi; obtain ⟨z'', mz''⟩ := zi
    use ⟨I, z''⟩, rfl
    rw [Ω]; simp only [nmaxI, dite_false, mem_union]; right
    rw [mem_iUnion₂]; use z.1, ⟨z.2, mz''⟩, h

lemma Ω_RFD {p q : 𝔓 X} (h𝓘 : 𝓘 p ≤ 𝓘 q) : Disjoint (Ω p) (Ω q) ∨ Ω q ⊆ Ω p := by
  by_cases h : 𝔰 q ≤ 𝔰 p
  · rw [or_iff_not_imp_left]; intro hi
    obtain ⟨I, y⟩ := p
    obtain ⟨J, z⟩ := q
    have hij : I = J := le_antisymm h𝓘 (Grid.le_dyadic h h𝓘 le_rfl)
    have k := Ω_disjoint (p := ⟨I, y⟩) (p' := ⟨J, z⟩)
    replace k : (⟨I, y⟩ : 𝔓 X) = ⟨J, z⟩ := by tauto
    rw [k]
  · obtain ⟨J, sJ, lbJ, ubJ⟩ :=
      Grid.exists_sandwiched h𝓘 (𝔰 q - 1) (by change 𝔰 p ≤ _ ∧ _ ≤ 𝔰 q; omega)
    have : q.2.1 ∈ ⋃ z ∈ 𝓩 J, ball_{J} z C4_2_1 :=
      ((Finset.coe_subset.mpr 𝓩_subset).trans frequency_ball_cover) q.2.2
    rw [mem_iUnion₂] at this; obtain ⟨z', mz', dz⟩ := this
    have zi' : ball_{J} z' C4_2_1 ⊆ ⋃ z ∈ 𝓩 J, ball_{J} z C4_2_1 :=
      subset_iUnion₂_of_subset z' mz' (subset_refl _)
    replace zi : ↑q.2 ∈ ⋃ f, Ω₁ ⟨J, f⟩ :=
      mem_of_mem_of_subset dz <| zi'.trans iUnion_ball_subset_iUnion_Ω₁
    clear! z'
    rw [mem_iUnion] at zi; obtain ⟨a, ma⟩ := zi -- Paper's `q'` is `⟨J, a⟩`
    have nmaxJ : ¬IsMax J := by
      by_contra maxJ; rw [Grid.isMax_iff] at maxJ
      rw [maxJ, show s topCube = S from s_topCube (X := X)] at sJ
      have : 𝔰 q ≤ S := scale_mem_Icc.2
      omega
    have succJ : J.succ = q.1 := (Grid.succ_def nmaxJ).mpr ⟨ubJ, by change 𝔰 q = _; omega⟩
    have key : Ω q ⊆ Ω ⟨J, a⟩ := by
      nth_rw 2 [Ω]; simp only [nmaxJ, dite_false]; intro ϑ mϑ; right; rw [mem_iUnion₂]
      refine ⟨q.2, ?_, ?_⟩
      · rw [succJ]; exact ⟨q.2.2, ma⟩
      · change ϑ ∈ Ω ⟨q.1, q.2⟩ at mϑ; convert mϑ
    let q' : 𝔓 X := ⟨J, a⟩
    change 𝓘 p ≤ 𝓘 q' at lbJ
    rcases Ω_RFD lbJ with c | c
    · exact Or.inl (disjoint_of_subset_right key c)
    · exact Or.inr (key.trans c)
termination_by (𝔰 q - 𝔰 p).toNat
decreasing_by
  rw [Int.lt_toNat]
  change (s J - 𝔰 p).toNat < 𝔰 q - 𝔰 p
  rw [sJ, Int.toNat_of_nonneg (by omega), sub_right_comm]
  exact sub_one_lt _

end Construction

variable (X) in
def tile_existence : TileStructure Q D κ S o where
  Ω := Construction.Ω
  biUnion_Ω {I} := by rw [← SimpleFunc.coe_range]; exact Construction.Ω_biUnion
  disjoint_Ω := Construction.Ω_disjoint
  relative_fundamental_dyadic {p q} := Construction.Ω_RFD
  cball_subset {p} := by
    rw [Construction.Ω]; split_ifs with h
    · have : ball_(p) (𝒬 p) 5⁻¹ ⊆ ball_(p) (𝒬 p) C𝓩 := ball_subset_ball (by norm_num)
      exact this.trans (Construction.ball_subset_Ω₁ p)
    · simp
  subset_cball {p} := Construction.Ω_subset_cball
