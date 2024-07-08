import Carleson.Defs

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

section Generic
universe u
variable {𝕜 : Type*} [_root_.RCLike 𝕜]
variable {X : Type u} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

variable (X) in
/-- A grid structure on `X`.
I expect we prefer `coeGrid : Grid → Set X` over `Grid : Set (Set X)`
Note: the `s` in this paper is `-s` of Christ's paper.
-/
class GridStructure
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X) where
  /-- indexing set for a grid structure -/
  Grid : Type u
  fintype_Grid : Fintype Grid
  /-- The collection of dyadic cubes -/
  coeGrid : Grid → Set X
  /-- scale functions -/
  s : Grid → ℤ
  /-- Center functions -/
  c : Grid → X
  inj : Injective (fun i ↦ (coeGrid i, s i))
  range_s_subset : range s ⊆ Icc (-S) S
  topCube : Grid
  s_topCube : s topCube = S
  c_topCube : c topCube = o
  subset_topCube {i} : coeGrid i ⊆ coeGrid topCube
  Grid_subset_biUnion {i} : ∀ k ∈ Ico (-S : ℤ) (s i), coeGrid i ⊆ ⋃ j ∈ s ⁻¹' {k}, coeGrid j
  fundamental_dyadic' {i j} : s i ≤ s j → coeGrid i ⊆ coeGrid j ∨ Disjoint (coeGrid i) (coeGrid j)
  ball_subset_Grid {i} : ball (c i) (D ^ s i / 4) ⊆ coeGrid i --2.0.10
  Grid_subset_ball {i} : coeGrid i ⊆ ball (c i) (4 * D ^ s i) --2.0.10
  small_boundary {i} {t : ℝ} (ht : D ^ (- S - s i) ≤ t) :
    volume.real { x ∈ coeGrid i | infDist x (coeGrid i)ᶜ ≤ t * D ^ s i } ≤ 2 * t ^ κ * volume.real (coeGrid i)
  coeGrid_measurable {i} : MeasurableSet (coeGrid i)

export GridStructure (range_s_subset Grid_subset_biUnion ball_subset_Grid Grid_subset_ball small_boundary
  topCube s_topCube c_topCube subset_topCube coeGrid_measurable) -- should `X` be explicit in topCube?

attribute [coe] GridStructure.coeGrid

variable {D : ℕ} {κ : ℝ} {S : ℕ} {o : X}
variable [GridStructure X D κ S o]

variable (X) in
/-- The indexing type of the grid structure. Elements are called (dyadic) cubes.
Note that this type has instances for both `≤` and `⊆`, but they do *not* coincide. -/
abbrev Grid : Type u := GridStructure.Grid X A

def s : Grid X → ℤ := GridStructure.s
def c : Grid X → X := GridStructure.c

variable {i j : Grid X}

instance : Fintype (Grid X) := GridStructure.fintype_Grid
instance : Coe (Grid X) (Set X) := ⟨GridStructure.coeGrid⟩
instance : Membership X (Grid X) := ⟨fun x i ↦ x ∈ (i : Set X)⟩
instance : PartialOrder (Grid X) := PartialOrder.lift _ GridStructure.inj
/- These should probably not/only rarely be used. I comment them out for now,
so that we don't accidentally use it. We can put it back if useful after all. -/
-- instance : HasSubset (Grid X) := ⟨fun i j ↦ (i : Set X) ⊆ (j : Set X)⟩
-- instance : HasSSubset (Grid X) := ⟨fun i j ↦ (i : Set X) ⊂ (j : Set X)⟩
-- @[simp] lemma Grid.subset_def : i ⊆ j ↔ (i : Set X) ⊆ (j : Set X) := .rfl
-- @[simp] lemma Grid.ssubset_def : i ⊂ j ↔ (i : Set X) ⊂ (j : Set X) := .rfl

lemma fundamental_dyadic :
    s i ≤ s j → (i : Set X) ⊆ (j : Set X) ∨ Disjoint (i : Set X) (j : Set X) :=
  GridStructure.fundamental_dyadic'

lemma le_or_disjoint (h : s i ≤ s j) : i ≤ j ∨ Disjoint (i : Set X) (j : Set X) :=
  fundamental_dyadic h |>.imp (⟨·, h⟩) id

lemma le_or_ge_or_disjoint : i ≤ j ∨ j ≤ i ∨ Disjoint (i : Set X) (j : Set X) := by
  rcases le_or_lt (s i) (s j) with h | h
  · have := le_or_disjoint h; tauto
  · have := le_or_disjoint h.le; tauto

namespace Grid

/- not sure whether these should be simp lemmas, but that might be required if we want to
  conveniently rewrite/simp with Set-lemmas -/
@[simp] lemma mem_def {x : X} : x ∈ i ↔ x ∈ (i : Set X) := .rfl
@[simp] lemma le_def : i ≤ j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i ≤ s j := .rfl

protected lemma inj : Injective (fun i : Grid X ↦ ((i : Set X), s i)) := GridStructure.inj

lemma le_topCube : i ≤ topCube :=
  ⟨subset_topCube, (range_s_subset ⟨i, rfl⟩).2.trans_eq s_topCube.symm⟩

lemma isTop_topCube : IsTop (topCube : Grid X) := fun _ ↦ le_topCube

lemma isMax_iff : IsMax i ↔ i = topCube := isTop_topCube.isMax_iff

/-- The set `I ↦ Iᵒ` in the blueprint. -/
def int (i : Grid X) : Set X := ball (c i) (D ^ s i / 4)

postfix:max "ᵒ" => Grid.int

/-- An auxiliary measure used in the well-foundedness of `Ω` in Lemma `tile_structure`. -/
def opSize (i : Grid X) : ℕ := (S - s i).toNat

lemma int_subset : i.int ⊆ i := by exact ball_subset_Grid

end Grid
end Generic

namespace Grid

open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]

variable [GridStructure X D κ S o]

notation "dist_{" I "}" => @dist (WithFunctionDistance (c I) (D ^ s I / 4)) _
notation "nndist_{" I "}" => @nndist (WithFunctionDistance (c I) (D ^ s I / 4)) _
notation "ball_{" I "}" => @ball (WithFunctionDistance (c I) (D ^ s I / 4)) _

lemma c_mem_Grid {i : Grid X} : c i ∈ (i : Set X) := by
  obtain ⟨hD⟩ := NeZero.of_pos <| zero_lt_one.trans_le one_le_D
  exact mem_of_mem_of_subset (Metric.mem_ball_self (by positivity)) ball_subset_Grid

lemma nonempty (i : Grid X) : (i : Set X).Nonempty := ⟨c i, c_mem_Grid⟩

lemma le_of_mem_of_mem {i j : Grid X} (h : s i ≤ s j) {c : X} (mi : c ∈ i) (mj : c ∈ j) : i ≤ j :=
  ⟨(fundamental_dyadic h).resolve_right (not_disjoint_iff.mpr ⟨c, mi, mj⟩), h⟩

lemma le_dyadic {i j k : Grid X} (h : s i ≤ s j) (li : k ≤ i) (lj : k ≤ j) : i ≤ j := by
  obtain ⟨c, mc⟩ := k.nonempty
  exact le_of_mem_of_mem h (mem_of_mem_of_subset mc li.1) (mem_of_mem_of_subset mc lj.1)

@[simp] lemma lt_def {i j : Grid X} : i < j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i < s j := by
  constructor <;> intro h
  · obtain ⟨a₁, a₂⟩ := h.le
    refine ⟨a₁, lt_of_le_of_ne a₂ ?_⟩
    by_contra a₃
    have l : i < i := h.trans_le (le_dyadic a₃.ge h.le le_rfl)
    rwa [lt_self_iff_false] at l
  · apply lt_of_le_of_ne (le_def.mpr ⟨h.1, h.2.le⟩)
    by_contra a; rw [a, lt_self_iff_false] at h; exact h.2

/-- There exists a unique successor of each non-maximal cube. -/
lemma exists_unique_succ (i : Grid X) (h : ¬IsMax i) :
    ∃! j ∈ Finset.univ, i < j ∧ ∀ j', i < j' → j ≤ j' := by
  simp_rw [Finset.mem_univ, true_and]
  classical let incs : Finset (Grid X) := Finset.univ.filter (i < ·)
  have ine : incs.Nonempty := by
    use topCube; simp only [incs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne le_topCube (isMax_iff.not.mp h)
  obtain ⟨j, mj, hj⟩ := incs.exists_minimal ine
  simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and, incs] at mj hj
  replace hj : ∀ (x : Grid X), i < x → j ≤ x := fun x mx ↦ by
    rcases lt_or_le (s x) (s j) with c | c
    · have := le_dyadic c.le mx.le mj.le
      exact (eq_of_le_of_not_lt this (hj x mx)).symm.le
    · exact le_dyadic c mj.le mx.le
  use j, ⟨mj, hj⟩, fun k ⟨hk₁, hk₂⟩ ↦ le_antisymm (hk₂ j mj) (hj k hk₁)

open Classical in
/-- If `i` is not a maximal element, this is the (unique) minimal element greater than i.
This is not a `SuccOrder` since an element can be the successor of multiple other elements. -/
def succ (i : Grid X) : Grid X := if h : IsMax i then i else Finset.choose (hp := exists_unique_succ i h)

variable {i j : Grid X}

lemma succ_spec (h : ¬IsMax i) : i < i.succ ∧ ∀ j, i < j → i.succ ≤ j := by
  simp only [succ, h, dite_false]
  classical exact Finset.choose_spec (hp := exists_unique_succ i h).2

lemma succ_unique (h : ¬IsMax i) : i < j → (∀ j', i < j' → j ≤ j') → i.succ = j := fun k₁ k₂ ↦
  ((exists_unique_succ i h).unique ⟨by simp, k₁, k₂⟩ ⟨by simp, succ_spec h⟩).symm

lemma le_succ : i ≤ i.succ := by
  by_cases h : IsMax i
  · simp [h, succ]
  · exact (succ_spec h).1.le

lemma max_of_le_succ : i.succ ≤ i → IsMax i := fun h ↦ by
  contrapose! h; by_contra! k; have l := (succ_spec h).1.trans_le k
  rwa [lt_self_iff_false] at l

lemma succ_le_of_lt (h : i < j) : i.succ ≤ j := by
  by_cases k : IsMax i
  · simp only [k, succ, dite_true]; exact h.le
  · exact (succ_spec k).2 j h

lemma exists_supercube (l : ℤ) (h : l ∈ Icc (s i) S) : ∃ j, s j = l ∧ i ≤ j := by
  obtain ⟨lb, ub⟩ := h
  rcases ub.eq_or_lt with ub | ub; · exact ⟨topCube, by simpa [ub] using s_topCube, le_topCube⟩
  obtain ⟨x, hx⟩ := i.nonempty
  have bound_i : -S ≤ s i ∧ s i ≤ S := mem_Icc.mp (range_s_subset ⟨i, rfl⟩)
  have ts := Grid_subset_biUnion (X := X) (i := topCube) l (by rw [s_topCube, mem_Ico]; omega)
  have := mem_of_mem_of_subset hx ((le_topCube (i := i)).1.trans ts)
  simp_rw [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at this
  obtain ⟨j, (sj : s j = l), mj⟩ := this; use j, sj
  exact le_of_mem_of_mem (by omega) hx mj

lemma exists_sandwiched (h : i ≤ j) (l : ℤ) (hl : l ∈ Icc (s i) (s j)) :
    ∃ k, s k = l ∧ i ≤ k ∧ k ≤ j := by
  have bound_q : -S ≤ s j ∧ s j ≤ S := mem_Icc.mp (range_s_subset ⟨j, rfl⟩)
  rw [mem_Icc] at hl
  obtain ⟨K, sK, lbK⟩ := exists_supercube l (by change s i ≤ _ ∧ _; omega)
  use K, sK, lbK
  exact le_dyadic (by omega) lbK h

lemma scale_succ (h : ¬IsMax i) : s i.succ = s i + 1 := by
  obtain ⟨h₁, h₂⟩ := succ_spec h
  rw [lt_def] at h₁; apply le_antisymm _ (by omega)
  by_contra! h₀
  obtain ⟨z, hz₁, hz₂, hz₃⟩ :=
    exists_sandwiched (le_succ (i := i)) (s i + 1) (by rw [mem_Icc]; omega)
  have l := (lt_def.mpr ⟨hz₃.1, hz₁.symm ▸ h₀⟩).trans_le (h₂ z (lt_def.mpr ⟨hz₂.1, by omega⟩))
  rwa [lt_self_iff_false] at l

lemma opSize_succ_lt (h : ¬IsMax i) : i.succ.opSize < i.opSize := by
  simp only [opSize, Int.lt_toNat]
  have : s i.succ ≤ S := (mem_Icc.mp (range_s_subset ⟨i.succ, rfl⟩)).2
  replace : 0 ≤ S - s i.succ := by omega
  rw [Int.toNat_of_nonneg this, scale_succ h]
  omega

@[elab_as_elim]
lemma induction (P : Grid X → Prop) (base : ∀ i, IsMax i → P i)
    (ind : ∀ i, ¬IsMax i → P i.succ → P i) : ∀ i, P i := fun i ↦ by
  by_cases h : IsMax i
  · exact base i h
  · have := opSize_succ_lt h
    exact ind i h (induction P base ind i.succ)
termination_by i => i.opSize

lemma succ_def (h : ¬IsMax i) : i.succ = j ↔ i ≤ j ∧ s j = s i + 1 := by
  refine ⟨fun k ↦ by subst k; exact ⟨le_succ, scale_succ h⟩, fun ⟨h₁, _⟩ ↦ ?_⟩
  replace h₁ : i < j := lt_def.mpr ⟨h₁.1, by omega⟩
  refine succ_unique h h₁ fun j' hj' ↦ ?_
  have : s i < s j' := (lt_def.mp hj').2
  exact le_dyadic (by omega) h₁.le hj'.le


lemma dist_congr {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X} (e₁ : x₁ = x₂) (e₂ : r₁ = r₂) :
    dist_{x₁, r₁} f g = dist_{x₂, r₂} f g := by congr

lemma le_cdist_iterate {x : X} {r : ℝ} (hr : 0 ≤ r) (f g : Θ X) (k : ℕ) :
    2 ^ k * dist_{x, r} f g ≤ dist_{x, (defaultA a) ^ k * r} f g := by
  induction k with
  | zero => rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans 2 * dist_{x, (defaultA a) ^ k * r} f g
    · rw [pow_succ', mul_assoc]
      exact (mul_le_mul_left zero_lt_two).mpr ih
    · convert le_cdist (ball_subset_ball _) using 1
      · exact dist_congr rfl (by rw [← mul_assoc, pow_succ'])
      · nth_rw 1 [← one_mul ((defaultA a) ^ k * r)]; gcongr
        rw [← Nat.cast_one, Nat.cast_le]; exact Nat.one_le_two_pow

lemma cdist_le_iterate {x : X} {r : ℝ} (hr : 0 < r) (f g : Θ X) (k : ℕ) :
    dist_{x, 2 ^ k * r} f g ≤ (defaultA a) ^ k * dist_{x, r} f g := by
  induction k with
  | zero => simp_rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans defaultA a * dist_{x, 2 ^ k * r} f g
    · convert cdist_le _ using 1
      · exact dist_congr rfl (by ring)
      · rw [dist_self]; positivity
    · replace ih := (mul_le_mul_left (show 0 < (defaultA a : ℝ) by positivity)).mpr ih
      rwa [← mul_assoc, ← pow_succ'] at ih

/-- The constant appearing in Lemma 2.1.2, `2 ^ {-95a}`. -/
def _root_.C2_1_2 (a : ℕ) : ℝ := 2 ^ (-95 * (a : ℝ))

variable (X) in
lemma _root_.C2_1_2_le_inv_512 : C2_1_2 a ≤ 1 / 512 := by
  rw [C2_1_2, show (1 / 512 : ℝ) = 2 ^ (-9 : ℝ) by norm_num,
    Real.rpow_le_rpow_left_iff one_lt_two, neg_mul, neg_le_neg_iff]
  norm_cast; linarith [four_le_a X]

variable (X) in
lemma _root_.C2_1_2_le_one : C2_1_2 a ≤ 1 :=
  (C2_1_2_le_inv_512 X).trans <| by norm_num

variable (X) in
lemma _root_.C2_1_2_lt_one : C2_1_2 a < 1 :=
  (C2_1_2_le_inv_512 X).trans_lt <| by norm_num

/-- Stronger version of Lemma 2.1.2. -/
lemma dist_strictMono {I J : Grid X} (hpq : I < J) {f g : Θ X} :
    dist_{I} f g ≤ C2_1_2 a * dist_{J} f g := by
  calc
    _ ≤ dist_{c I, 4 * D ^ s I} f g :=
      cdist_mono (ball_subset_ball (by simp_rw [div_eq_inv_mul, defaultD]; gcongr; norm_num))
    _ ≤ 2 ^ (-100 * (a : ℝ)) * dist_{c I, 4 * D ^ (s I + 1)} f g := by
      rw [← div_le_iff' (by positivity), neg_mul, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]
      convert le_cdist_iterate (x := c I) (r := 4 * D ^ s I) (by positivity) f g (100 * a) using 1
      · norm_cast
      · apply dist_congr rfl
        have : (defaultA a : ℝ) ^ (100 * a) = D := by
          simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat]
          rw [← pow_mul]; congr 1; ring
        rw [this, zpow_add_one₀ (defaultD_pos a).ne']; ring
    _ ≤ 2 ^ (-100 * (a : ℝ)) * dist_{c I, 4 * D ^ s J} f g := by
      gcongr
      have : s I < s J := (Grid.lt_def.mp hpq).2
      exact cdist_mono (ball_subset_ball (mul_le_mul_of_nonneg_left
        (zpow_le_of_le one_le_D (by omega)) zero_le_four))
    _ ≤ 2 ^ (-100 * (a : ℝ)) * dist_{c J, 8 * D ^ s J} f g := by
      gcongr
      have : c I ∈ ball (c J) (4 * D ^ s J) :=
        mem_of_mem_of_subset c_mem_Grid ((Grid.lt_def.mp hpq).1.trans Grid_subset_ball)
      rw [mem_ball] at this
      exact cdist_mono (ball_subset_ball' (by linarith))
    _ ≤ 2 ^ (-100 * (a : ℝ) + 5 * a) * dist_{J} f g := by
      rw [Real.rpow_add zero_lt_two, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [show (2 : ℝ) ^ (5 * (a : ℝ)) = (defaultA a) ^ 5 by norm_cast; ring]
      convert cdist_le_iterate _ f g 5 using 1
      · exact dist_congr rfl (by ring)
      · have := @one_le_D a; positivity
    _ = _ := by congr 1; rw [C2_1_2, ← add_mul]; norm_num

/-- Weaker version of Lemma 2.1.2. -/
lemma dist_mono {I J : Grid X} (hpq : I ≤ J) {f g : Θ X} : dist_{I} f g ≤ dist_{J} f g := by
  rcases hpq.eq_or_lt with h | h
  · subst h; rfl
  · exact (Grid.dist_strictMono h).trans (mul_le_of_le_one_left dist_nonneg (C2_1_2_le_one X))

/-! Maximal elements of finsets of dyadic cubes -/

variable (s : Finset (Grid X))

open Classical in
def maxCubes : Finset (Grid X) := s.filter fun i ↦ ∀ j ∈ s, i ≤ j → i = j

lemma exists_maximal_supercube : ∀ i ∈ s, ∃ j ∈ maxCubes s, i ≤ j := fun i hi ↦ by
  classical let C : Finset (Grid X) := s.filter (i ≤ ·)
  have Cn : C.Nonempty := ⟨i, by simp only [C, Finset.mem_filter, hi, le_rfl, true_and]⟩
  obtain ⟨j, hj, maxj⟩ := C.exists_maximal Cn
  simp_rw [C, maxCubes, Finset.mem_filter] at hj maxj ⊢
  refine ⟨j, ?_, hj.2⟩
  exact ⟨hj.1, fun k hk lk ↦ eq_of_le_of_not_lt lk (maxj k ⟨hk, hj.2.trans lk⟩)⟩

lemma maxCubes_pairwiseDisjoint :
    (maxCubes s).toSet.PairwiseDisjoint fun i ↦ (i : Set X) := fun i mi j mj hn ↦ by
  simp only [maxCubes, and_imp, Finset.coe_filter, mem_setOf_eq] at mi mj
  exact le_or_ge_or_disjoint.resolve_left ((mi.2 j mj.1).mt hn)
    |>.resolve_left ((mj.2 i mi.1).mt hn.symm)

end Grid
