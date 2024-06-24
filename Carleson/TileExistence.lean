import Carleson.GridStructure
import Carleson.DoublingMeasure
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate

namespace ShortVariables
set_option hygiene false
notation "D'" => (Real.toNNReal D)

end ShortVariables

noncomputable section

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma ball_size_induction (r:ℝ) (x:X) (j : ℕ) :
    volume.real (ball x (2^j*r)) ≤ 2^(j*a) * volume.real (ball x r) := by
  induction j with
    | zero => rw [CharP.cast_eq_zero,zero_mul,pow_zero,Real.rpow_zero,one_mul,one_mul]
    | succ j' hj' =>
      calc
        volume.real (ball x (2 ^ (j' + 1) * r))
          = volume.real (ball x (2 * (2^j' * r))) := by
            rw [pow_add,pow_one,mul_comm _ 2,mul_assoc]
        _ ≤ 2 ^ a * volume.real (ball x (2^j' * r)) := by
          exact volume_ball_two_le_same x (2 ^ j' * r)
        _ ≤ 2 ^ a * (2 ^ (j' * a) * volume.real (ball x r)) := by
          apply OrderedSemiring.mul_le_mul_of_nonneg_left
          . exact hj'
          . apply Real.rpow_nonneg
            linarith
        _ = 2 ^ (↑(j' + 1) * a) * volume.real (ball x r) := by
          rw [Nat.cast_add, Nat.cast_one,right_distrib,one_mul,add_comm,
            Real.rpow_add (by linarith),mul_assoc]

section

-- #synth CompatibleFunctions ℝ X _
-- #synth Nonempty X -- should probably exist
variable (X) in
local instance nonempty_Space : Nonempty X := by
  obtain ⟨x,_⟩ := ‹ProofData a q K σ₁ σ₂ F G›.cf.eq_zero
  use x
end


lemma volume_closedBall_finite (r : ℝ) (x : X) : volume (closedBall x r) < ⊤ := by
  exact measure_closedBall_lt_top

lemma volume_ball_finite (r : ℝ) (x : X) : volume (ball x r) < ⊤ := by
  exact measure_ball_lt_top

lemma volume_ntrivial_closedball_pos (r : ℝ) (hr: 0 < r) (x : X) : 0 < volume (closedBall x r) := by
  exact measure_closedBall_pos volume x hr

-- lemma finite_disjoint_balls (r r2 : ℝ) (hr2 : 0 < r2) (x : X) (Y : Set X) (hY : Y ⊆ ball x r)
--     (hdisjoint : Y.PairwiseDisjoint (fun y ↦ ball y r2)): Y.Finite := by
--   sorry

-- lemma D_eq_two_pow : D = 2 ^ (100 * a ^ 2) := by
--   simp only [defaultD]


example (a b c : NNReal) (hapos : 0 < a) (hle : a * b ≤ a * c) : b ≤ c := by
  exact le_of_mul_le_mul_of_pos_left hle hapos

lemma le_of_mul_le_mul_of_finpos_left {a b c : ENNReal} (hapos : 0 < a) (hafin : a < ⊤) (hle : a * b ≤ a * c): b ≤ c := by
  refine ENNReal.le_of_top_imp_top_of_toNNReal_le ?h ?h_nnreal
  . intro hb
    rw [hb] at hle
    rw [ENNReal.mul_top hapos.ne.symm] at hle
    simp only [top_le_iff] at hle
    rw [ENNReal.mul_eq_top] at hle
    obtain l|r := hle
    . exact l.right
    . obtain r := r.left
      rw [r] at hafin
      contradiction
  intro hb hc
  have hapos' : (0 < a.toNNReal) := by
    exact ENNReal.toNNReal_pos_iff.mpr (And.intro hapos hafin)
  apply le_of_mul_le_mul_of_pos_left _ hapos'
  rw [← ENNReal.toNNReal_mul,← ENNReal.toNNReal_mul]
  rw [ENNReal.toNNReal_le_toNNReal]
  . exact hle
  . obtain hanetop := hafin.ne
    exact ENNReal.mul_ne_top hanetop hb
  . obtain hanetop := hafin.ne
    exact ENNReal.mul_ne_top hanetop hc

-- example (g : ℝ ) (z : ℤ) : g ^ z = g ^(z : ℝ) := by exact?

lemma D_ge_one : 1 ≤ D := by
  rw [← Real.rpow_zero 2]
  dsimp
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
  exact sq_nonneg a

-- lemma D_pos : 0 < D := by exact defaultD_pos a

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
      apply Real.rpow_le_rpow_of_exponent_le (D_ge_one)
      simp only [Int.cast_mul, Int.cast_ofNat]
      rw [two_mul,add_assoc]
      simp only [le_add_iff_nonneg_right]
      rw [← sub_self (↑S),sub_eq_add_neg]
      apply add_le_add_left hk_lower

section

lemma tsum_le_tsum_of_nonneg {ι : Type*} (f : ι → ℝ) (g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i)
    (hg : Summable g) :
    ∑' (n : ι), f n ≤ ∑' (n : ι), g n := by
  have : Summable f := by
    apply hg.of_nonneg_of_le hf hfg
  apply tsum_mono this hg
  exact hfg

-- #synth MeasurableSingletonClass X

def dist_closure (Y :Set X) : Set X := ⋃ y ∈ Y, closedBall y 0

@[simp]
lemma mem_dist_closure_iff (Y : Set X) (x : X) : x ∈ dist_closure Y ↔ ∃ y ∈ Y, dist x y = 0 := by
  dsimp only [dist_closure]
  simp only [mem_iUnion, mem_closedBall, exists_prop]
  apply exists_congr
  intro y
  simp only [and_congr_right_iff]
  intro _
  constructor
  . intro hxy
    apply le_antisymm hxy dist_nonneg
  . intro hxy
    exact hxy.le

lemma subset_dist_closure (Y : Set X) : Y ⊆ dist_closure Y := by
  intro y hy
  rw [mem_dist_closure_iff]
  use y, hy
  exact dist_self y


lemma dist_closure_le_ball_of_le_ball {x: X} {r : ℝ} {Y : Set X} (hY : Y ⊆ ball x r) :
  dist_closure Y ⊆ ball x r := by
  intro z hz
  simp only [mem_dist_closure_iff] at hz
  obtain ⟨y,hy,hyz⟩ := hz
  specialize hY hy
  simp only [mem_ball] at hY ⊢
  calc
    dist z x  ≤ dist z y + dist y x := dist_triangle z y x
    _ = dist y x := by rw [hyz,zero_add]
    _ < r := hY


lemma dist_closure_isClosed_of_fin {Y : Set X} (hY: Y.Finite) : IsClosed (dist_closure Y) := by
  exact Finite.isClosed_biUnion hY (fun y _ => isClosed_ball)

-- lemma dist_closure_le_closedBall_of_le_closedBall (x:X) (r : ℝ) (y : Set Y) (hy : )
lemma dist_closure_measurable_of_fin {Y : Set X} (hY : Y.Finite) : MeasurableSet (dist_closure Y) := by
  exact (dist_closure_isClosed_of_fin hY).measurableSet

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
  rw [ENNReal.tsum_mul_right]
  rw [tsum_one_eq']

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


-- example (k : ℝ) (y : X) : volume (ball y (8 * D ^(2 * S) * D^k)) ≤ (8 * D'^(2 * S)) ^ a

lemma counting_balls (k : ℝ) (hk_lower : -S ≤ k) (Y : Set X) (hY : Y ⊆ ball o (4*D^S-D^k))
    (hYdisjoint: Y.PairwiseDisjoint (fun y ↦ ball y (D^k))) :
    (Set.encard Y).toENNReal ≤ (As (2 ^ a) (2 ^ J' X)) := by
  letI := nonempty_Space X
  suffices (Set.encard Y).toENNReal * volume (ball o (4 * D^S)) ≤ (As (2 ^ a) (2 ^ J' X)) * volume (ball o (4 * D^S)) by
    have volume_pos : 0 < volume (ball o (4 * D^S)) := by
      apply measure_ball_pos volume o
      simp only [defaultD, gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      refine zpow_pos_of_pos ?ha S
      apply Real.rpow_pos_of_pos
      linarith
    have volume_finite : volume (ball o (4 * D^S)) < ⊤ :=
      volume_ball_finite (4 * D ^ S) o
    apply le_of_mul_le_mul_of_finpos_left volume_pos volume_finite
    rw [mul_comm,mul_comm (volume _)]
    exact this
  have val_ne_zero : (As (2 ^ a) (2 ^ J' X):ℝ≥0∞) ≠ 0 := by
    exact (As_pos' X (2 ^J' X)).ne.symm
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
        apply hc.right hxy hsy'
      . specialize hyx hsy'
        specialize hc hsx
        simp only [mem_setOf_eq] at hc
        exact hc.right hsx' hyx
  . exact fun s a ↦ subset_iUnion₂_of_subset s a fun ⦃a⦄ a ↦ a

variable (X) in
def zorn_apply_maximal_set (k : ℝ):
    ∃ s ∈ property_set X k, ∀ s' ∈ property_set X k, s ⊆ s' → s' = s :=
  zorn_subset (property_set X k) (chain_property_set_has_bound X k)

variable (X) in
def Yk (k : ℝ): Set X := (zorn_apply_maximal_set X k).choose

lemma Yk_pairwise (k:ℝ) : (Yk X k).PairwiseDisjoint (fun (y:X) ↦ ball y (D^k)) := by
  exact (zorn_apply_maximal_set X k).choose_spec.left.right

lemma Yk_subset (k:ℝ) : Yk X k ⊆ ball o (4 * D^S - D^k) := by
  exact (zorn_apply_maximal_set X k).choose_spec.left.left

lemma Yk_maximal (k : ℝ) {s :Set X} (hs_sub : s ⊆ ball o (4 * D^S - D^k))
  (hs_pairwise : s.PairwiseDisjoint (fun y ↦ ball y (D^k))) (hmax_sub : Yk X k ⊆ s): s = Yk X k := by
  apply (zorn_apply_maximal_set X k).choose_spec.right
  . exact And.intro hs_sub hs_pairwise
  . exact hmax_sub

lemma cover_big_ball (k : ℝ) : ball o (4 * D^S - D^k) ⊆ ⋃ y ∈ Yk X k, ball y (2 * D^k) := by
  intro y hy
  have : ∃ z ∈ Yk X k, ¬Disjoint (ball y (D^k)) (ball z (D^k)) := by
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





/-! Proof that there exists a grid structure. -/
def grid_existence : GridStructure X D κ S o :=
  sorry

/-! Proof that there exists a tile structure on a grid structure. -/

variable [GridStructure X D κ S o] {I : 𝓓 X}


/-- Use Zorn's lemma to define this. -/
def 𝓩 (I : 𝓓 X) : Set (Θ X) := sorry

/-- The constant appearing in 4.2.2. -/
@[simp] def C𝓩 : ℝ := 3 / 10

lemma 𝓩_subset : 𝓩 I ⊆ ⋃ f ∈ range Q, ball_{I} f 1 := sorry
lemma 𝓩_disj {f g : Θ X} (hf : f ∈ 𝓩 I) (hg : g ∈ 𝓩 I) (hfg : f ≠ g) :
    Disjoint (ball_{I} f C𝓩) (ball_{I} g C𝓩) :=
  sorry
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
  ⋃ x : X, ball_{I} (Q x) 1 ⊆ ⋃ z ∈ 𝓩 I, ball_{I} z C4_2_1 := sorry

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
