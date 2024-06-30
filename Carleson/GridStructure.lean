import Carleson.Defs
import Carleson.Psi

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

section DoublingMeasure
universe u
variable {𝕜 : Type*} [_root_.RCLike 𝕜]
variable {X : Type u} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

variable (X) in
/-- A grid structure on `X`.
I expect we prefer `coe𝓓 : 𝓓 → Set X` over `𝓓 : Set (Set X)`
Note: the `s` in this paper is `-s` of Christ's paper.
-/
class GridStructure
    (D κ : outParam ℝ) (S : outParam ℤ) (o : outParam X) where
  /-- indexing set for a grid structure -/
  𝓓 : Type u
  fintype_𝓓 : Fintype 𝓓
  /-- The collection of dyadic cubes -/
  coe𝓓 : 𝓓 → Set X
  /-- scale functions -/
  s : 𝓓 → ℤ
  /-- Center functions -/
  c : 𝓓 → X
  inj : Injective (fun i ↦ (coe𝓓 i, s i))
  range_s_subset : range s ⊆ Icc (-S) S
  topCube : 𝓓
  s_topCube : s topCube = S
  c_topCube : c topCube = o
  subset_topCube {i} : coe𝓓 i ⊆ coe𝓓 topCube
  𝓓_subset_biUnion {i} : ∀ k ∈ Ico (-S) (s i), coe𝓓 i ⊆ ⋃ j ∈ s ⁻¹' {k}, coe𝓓 j
  fundamental_dyadic' {i j} : s i ≤ s j → coe𝓓 i ⊆ coe𝓓 j ∨ Disjoint (coe𝓓 i) (coe𝓓 j)
  c_mem_𝓓 {i} : c i ∈ coe𝓓 i --2.0.10
  ball_subset_𝓓 {i} : ball (c i) (D ^ s i / 4) ⊆ coe𝓓 i --2.0.10
  𝓓_subset_ball {i} : coe𝓓 i ⊆ ball (c i) (4 * D ^ s i) --2.0.10
  small_boundary {i} {t : ℝ} (ht : D ^ (- S - s i) ≤ t) :
    volume.real { x ∈ coe𝓓 i | infDist x (coe𝓓 i)ᶜ ≤ t * D ^ s i } ≤ 2 * t ^ κ * volume.real (coe𝓓 i)

export GridStructure (range_s_subset 𝓓_subset_biUnion c_mem_𝓓 ball_subset_𝓓 𝓓_subset_ball
  small_boundary topCube s_topCube c_topCube subset_topCube) -- should `X` be explicit in topCube?

variable {D κ C : ℝ} {S : ℤ} {o : X}

section GridStructure

variable [GridStructure X D κ S o]

variable (X) in
/-- The indexing type of the grid structure. Elements are called (dyadic) cubes.
Note that this type has instances for both `≤` and `⊆`, but they do *not* coincide. -/
abbrev 𝓓 : Type u := GridStructure.𝓓 X A

def s : 𝓓 X → ℤ := GridStructure.s
def c : 𝓓 X → X := GridStructure.c

instance : Fintype (𝓓 X) := GridStructure.fintype_𝓓
instance : Coe (𝓓 X) (Set X) := ⟨GridStructure.coe𝓓⟩
instance : Membership X (𝓓 X) := ⟨fun x i ↦ x ∈ (i : Set X)⟩
instance : PartialOrder (𝓓 X) := PartialOrder.lift _ GridStructure.inj
/- These should probably not/only rarely be used. I comment them out for now,
so that we don't accidentally use it. We can put it back if useful after all. -/
-- instance : HasSubset (𝓓 X) := ⟨fun i j ↦ (i : Set X) ⊆ (j : Set X)⟩
-- instance : HasSSubset (𝓓 X) := ⟨fun i j ↦ (i : Set X) ⊂ (j : Set X)⟩
-- @[simp] lemma 𝓓.subset_def {i j : 𝓓 X} : i ⊆ j ↔ (i : Set X) ⊆ (j : Set X) := .rfl
-- @[simp] lemma 𝓓.ssubset_def {i j : 𝓓 X} : i ⊂ j ↔ (i : Set X) ⊂ (j : Set X) := .rfl

lemma fundamental_dyadic {i j : 𝓓 X} :
    s i ≤ s j → (i : Set X) ⊆ (j : Set X) ∨ Disjoint (i : Set X) (j : Set X) :=
  GridStructure.fundamental_dyadic'

lemma le_or_disjoint {i j : 𝓓 X} (h : s i ≤ s j) : i ≤ j ∨ Disjoint (i : Set X) (j : Set X) :=
  fundamental_dyadic h |>.imp (⟨·, h⟩) id

namespace 𝓓

/- not sure whether these should be simp lemmas, but that might be required if we want to
  conveniently rewrite/simp with Set-lemmas -/
@[simp] lemma mem_def {x : X} {i : 𝓓 X} : x ∈ i ↔ x ∈ (i : Set X) := .rfl
@[simp] lemma le_def {i j : 𝓓 X} : i ≤ j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i ≤ s j := .rfl

protected lemma inj : Injective (fun i : 𝓓 X ↦ ((i : Set X), s i)) := GridStructure.inj

lemma nonempty (i : 𝓓 X) : (i : Set X).Nonempty := ⟨c i, c_mem_𝓓⟩

@[simp] lemma lt_def {i j : 𝓓 X} : i < j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i < s j := by
  constructor <;> intro h
  · obtain ⟨a₁, a₂⟩ := le_def.mp h.le
    refine ⟨a₁, lt_of_le_of_ne a₂ ?_⟩
    by_contra a₃
    have k : (j : Set X) ⊆ i := by
      apply (fundamental_dyadic a₃.ge).resolve_right
      obtain ⟨c, mc⟩ := i.nonempty
      rw [not_disjoint_iff]; use c, mem_of_mem_of_subset mc a₁, mc
    have l := h.trans_le (le_def.mpr ⟨k, a₃.ge⟩)
    rwa [lt_self_iff_false] at l
  · apply lt_of_le_of_ne (le_def.mpr ⟨h.1, h.2.le⟩)
    by_contra a; rw [a, lt_self_iff_false] at h; exact h.2

lemma le_topCube {i : 𝓓 X} : i ≤ topCube :=
  ⟨subset_topCube, (range_s_subset ⟨i, rfl⟩).2.trans_eq s_topCube.symm⟩

lemma isTop_topCube : IsTop (topCube : 𝓓 X) := fun _ ↦ le_topCube

lemma isMax_iff {i : 𝓓 X} : IsMax i ↔ i = topCube := isTop_topCube.isMax_iff

/-- The set `I ↦ Iᵒ` in the blueprint. -/
def int (i : 𝓓 X) : Set X := ball (c i) (D ^ s i / 4)

postfix:max "ᵒ" => 𝓓.int

/-- An auxiliary measure used in the well-foundedness of `Ω` in Lemma `tile_structure`. -/
def opSize (i : 𝓓 X) : ℕ := (S - s i).toNat

/-- There exists a unique successor of each non-maximal cube. -/
lemma exists_unique_succ (i : 𝓓 X) (h : ¬IsMax i) :
    ∃! j ∈ Finset.univ, i < j ∧ ∀ j', i < j' → j ≤ j' := by
  simp_rw [Finset.mem_univ, true_and]
  classical let incs : Finset (𝓓 X) := Finset.univ.filter (i < ·)
  have ine : incs.Nonempty := by
    use topCube; simp only [incs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne le_topCube (isMax_iff.not.mp h)
  obtain ⟨j, mj, hj⟩ := incs.exists_minimal ine
  simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and, incs] at mj hj
  replace hj : ∀ (x : 𝓓 X), i < x → j ≤ x := fun x mx ↦ by
    have nlt := hj x mx
    have nd : ¬Disjoint (j : Set X) x := by
      obtain ⟨c, mc⟩ := i.nonempty
      exact not_disjoint_iff.mpr ⟨c, mem_of_mem_of_subset mc (𝓓.le_def.mp mj.le).1,
        mem_of_mem_of_subset mc (𝓓.le_def.mp mx.le).1⟩
    rcases lt_or_le (s x) (s j) with c | c
    · have := (le_or_disjoint c.le).resolve_right (by rwa [disjoint_comm])
      exact (eq_of_le_of_not_lt this nlt).symm.le
    · exact (le_or_disjoint c).resolve_right nd
  use j, ⟨mj, hj⟩, fun k ⟨hk₁, hk₂⟩ ↦ le_antisymm (hk₂ j mj) (hj k hk₁)

open Classical in
/-- If `i` is not a maximal element, this is the (unique) minimal element greater than i.
This is not a `SuccOrder` since an element can be the successor of multiple other elements. -/
def succ (i : 𝓓 X) : 𝓓 X := if h : IsMax i then i else Finset.choose (hp := exists_unique_succ i h)

variable {i j : 𝓓 X}

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

lemma exists_supercube (i : 𝓓 X) (l : ℤ) (h : l ∈ Icc (s i) S) : ∃ j, s j = l ∧ i ≤ j := by
  obtain ⟨lb, ub⟩ := h
  rcases ub.eq_or_lt with ub | ub; · exact ⟨topCube, by simpa [ub] using s_topCube, 𝓓.le_topCube⟩
  obtain ⟨x, hx⟩ := i.nonempty
  have bound_i : -S ≤ s i ∧ s i ≤ S := mem_Icc.mp (range_s_subset ⟨i, rfl⟩)
  have ts := 𝓓_subset_biUnion (X := X) (i := topCube) l (by rw [s_topCube, mem_Ico]; omega)
  have := mem_of_mem_of_subset hx ((𝓓.le_topCube (i := i)).1.trans ts)
  simp_rw [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at this
  obtain ⟨j, (sj : s j = l), mj⟩ := this; use j, sj
  exact (le_or_disjoint (by omega)).resolve_right (not_disjoint_iff.mpr ⟨x, hx, mj⟩)

lemma exists_sandwiched {i j : 𝓓 X} (hij : i ≤ j) (l : ℤ) (hl : l ∈ Icc (s i) (s j)) :
    ∃ k, s k = l ∧ i ≤ k ∧ k ≤ j := by
  have bound_q : -S ≤ s j ∧ s j ≤ S := mem_Icc.mp (range_s_subset ⟨j, rfl⟩)
  rw [mem_Icc] at hl
  obtain ⟨K, sK, lbK⟩ := exists_supercube i l (by change s i ≤ _ ∧ _; omega)
  use K, sK, lbK
  apply (le_or_disjoint (by omega)).resolve_right
  rw [not_disjoint_iff]
  obtain ⟨x, hx⟩ := i.nonempty
  use x, mem_of_mem_of_subset hx lbK.1, mem_of_mem_of_subset hx hij.1

lemma scale_succ (h : ¬IsMax i) : s i.succ = s i + 1 := by
  obtain ⟨h₁, h₂⟩ := succ_spec h
  rw [lt_def] at h₁; apply le_antisymm _ (by omega)
  by_contra! h₀
  obtain ⟨z, hz₁, hz₂, hz₃⟩ :=
    exists_sandwiched (le_succ (i := i)) (s i + 1) (by rw [mem_Icc]; omega)
  have l := (lt_def.mpr ⟨(le_def.mp hz₃).1, hz₁.symm ▸ h₀⟩).trans_le
    (h₂ z (lt_def.mpr ⟨(le_def.mp hz₂).1, by omega⟩))
  rwa [lt_self_iff_false] at l

lemma opSize_succ_lt (h : ¬IsMax i) : i.succ.opSize < i.opSize := by
  simp only [opSize, Int.lt_toNat]
  have : s i.succ ≤ S := (mem_Icc.mp (range_s_subset ⟨i.succ, rfl⟩)).2
  replace : 0 ≤ S - s i.succ := by omega
  rw [Int.toNat_of_nonneg this, scale_succ h]
  omega

lemma induction (P : 𝓓 X → Prop) (base : ∀ i, IsMax i → P i)
    (ind : ∀ i, ¬IsMax i → P i.succ → P i) : ∀ i, P i := fun i ↦ by
  by_cases h : IsMax i
  · exact base i h
  · have := 𝓓.opSize_succ_lt h
    exact ind i h (induction P base ind i.succ)
termination_by i => i.opSize

lemma succ_def (h : ¬IsMax i) : i.succ = j ↔ i ≤ j ∧ s j = s i + 1 := by
  refine ⟨fun k ↦ by subst k; exact ⟨le_succ, scale_succ h⟩, fun ⟨h₁, _⟩ ↦ ?_⟩
  replace h₁ : i < j := lt_def.mpr ⟨(le_def.mp h₁).1, by omega⟩
  refine succ_unique h h₁ fun j' hj' ↦ ?_
  have b₁ : s i < s j' := (lt_def.mp hj').2
  have b₂ : s j ≤ s j' := by omega
  apply (le_or_disjoint b₂).resolve_right
  obtain ⟨c, mc⟩ := i.nonempty
  exact not_disjoint_iff.mpr ⟨c, mem_of_mem_of_subset mc (𝓓.le_def.mp h₁.le).1,
    mem_of_mem_of_subset mc (𝓓.le_def.mp hj'.le).1⟩

end 𝓓

variable {i : 𝓓 X}

lemma int_subset : i.int ⊆ i := by exact ball_subset_𝓓

end GridStructure

-- instance homogeneousMeasurableSpace [Inhabited X] : MeasurableSpace C(X, ℝ) :=
--   let m : PseudoMetricSpace C(X, ℝ) :=
--     homogeneousPseudoMetric (ball default 1) -- an arbitary ball
--   let t : TopologicalSpace C(X, ℝ) := m.toUniformSpace.toTopologicalSpace
--   @borel C(X, ℝ) t

/- The datain a tile structure, and some basic properties.
This is mostly separated out so that we can nicely define the notation `d_𝔭`.
Note: compose `𝓘` with `𝓓` to get the `𝓘` of the paper. -/
class PreTileStructure [FunctionDistances 𝕜 X] (Q : outParam (SimpleFunc X (Θ X)))
  (D κ : outParam ℝ) (S : outParam ℤ) (o : outParam X) extends GridStructure X D κ S o where
  protected 𝔓 : Type u
  fintype_𝔓 : Fintype 𝔓
  protected 𝓘 : 𝔓 → 𝓓
  surjective_𝓘 : Surjective 𝓘
  𝒬 : 𝔓 → Θ X
  range_𝒬 : range 𝒬 ⊆ range Q

export PreTileStructure (𝒬 range_𝒬)

section

variable [FunctionDistances 𝕜 X]  {Q : SimpleFunc X (Θ X)} [PreTileStructure Q D κ S o]

variable (X) in
def 𝔓 := PreTileStructure.𝔓 𝕜 X A
instance : Fintype (𝔓 X) := PreTileStructure.fintype_𝔓
def 𝓘 : 𝔓 X → 𝓓 X := PreTileStructure.𝓘
lemma surjective_𝓘 : Surjective (𝓘 : 𝔓 X → 𝓓 X) := PreTileStructure.surjective_𝓘
def 𝔠 (p : 𝔓 X) : X := c (𝓘 p)
def 𝔰 (p : 𝔓 X) : ℤ := s (𝓘 p)

end

local notation "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- A tile structure. -/
class TileStructure [FunctionDistances ℝ X] (Q : outParam (SimpleFunc X (Θ X)))
    (D κ : outParam ℝ) (S : outParam ℤ) (o : outParam X)
    extends PreTileStructure Q D κ S o where
  Ω : 𝔓 → Set (Θ X)
  biUnion_Ω {i} : range Q ⊆ ⋃ p ∈ 𝓘 ⁻¹' {i}, Ω p -- 2.0.13, union contains `Q`
  disjoint_Ω {p p'} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') : -- 2.0.13, union is disjoint
    Disjoint (Ω p) (Ω p')
  relative_fundamental_dyadic {p p'} (h : 𝓘 p ≤ 𝓘 p') : -- 2.0.14
    Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  cdist_subset {p} : ball_(D, p) (𝒬 p) 5⁻¹ ⊆ Ω p -- 2.0.15, first inclusion
  subset_cdist {p} : Ω p ⊆ ball_(D, p) (𝒬 p) 1 -- 2.0.15, second inclusion

export TileStructure (Ω biUnion_Ω disjoint_Ω relative_fundamental_dyadic cdist_subset subset_cdist)

end DoublingMeasure

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

section GridStructure

variable [GridStructure X D κ S o]

notation "dist_{" I "}" => @dist (WithFunctionDistance (c I) (D ^ s I / 4)) _
notation "nndist_{" I "}" => @nndist (WithFunctionDistance (c I) (D ^ s I / 4)) _
notation "ball_{" I "}" => @ball (WithFunctionDistance (c I) (D ^ s I / 4)) _
-- maybe we should delete the following three notations, and just use the previous three?
notation "dist_(" 𝔭 ")" => @dist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "nndist_(" 𝔭 ")" => @nndist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "ball_(" 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- Lemma 2.1.2, part 1. -/
lemma 𝓓.dist_mono {I J : 𝓓 X} (hpq : I ≤ J) {f g : Θ X} :
    dist_{I} f g ≤ dist_{J} f g := by
  rw [𝓓.le_def] at hpq
  obtain ⟨hpq, h'⟩ := hpq
  obtain h|h := h'.eq_or_lt
  · suffices I = J by
      rw [this]
    simp_rw [← 𝓓.inj.eq_iff, Prod.ext_iff, h, and_true]
    apply subset_antisymm hpq
    apply (fundamental_dyadic h.symm.le).resolve_right
    rw [Set.not_disjoint_iff_nonempty_inter, inter_eq_self_of_subset_right hpq]
    exact 𝓓.nonempty _
  simp only [not_le, ← Int.add_one_le_iff] at h
  sorry

def C2_1_2 (a : ℝ) : ℝ := 2 ^ (-95 * a)

/-- Lemma 2.1.2, part 2. -/
lemma 𝓓.dist_strictMono {I J : 𝓓 X} (hpq : I < J) {f g : Θ X} :
    dist_{I} f g ≤ C2_1_2 a * dist_{J} f g := by
  sorry

end GridStructure

variable [TileStructure Q D κ S o]

@[simp] lemma dist_𝓘 (p : 𝔓 X) {f g : Θ X} : dist_{𝓘 p} f g = dist_(p) f g := rfl
@[simp] lemma nndist_𝓘 (p : 𝔓 X) {f g : Θ X} : nndist_{𝓘 p} f g = nndist_(p) f g := rfl
@[simp] lemma ball_𝓘 (p : 𝔓 X) {f : Θ X} {r : ℝ} : ball_{𝓘 p} f r = ball_(p) f r := rfl

/-- The set `E` defined in Proposition 2.0.2. -/
def E (p : 𝔓 X) : Set X :=
  { x ∈ 𝓘 p | Q x ∈ Ω p ∧ 𝔰 p ∈ Icc (σ₁ x) (σ₂ x) }

section T

variable {p : 𝔓 X} {f : X → ℂ} {q : ℝ≥0∞}

/-- The operator `T_𝔭` defined in Proposition 2.0.2, considered on the set `F`.
It is the map `T ∘ (1_F * ·) : f ↦ T (1_F * f)`, also denoted `T1_F`
The operator `T` in Proposition 2.0.2 is therefore `applied to `(F := Set.univ)`. -/
def T (p : 𝔓 X) (f : X → ℂ) : X → ℂ :=
  indicator (E p)
    fun x ↦ ∫ y, exp (Q x x - Q x y) * K x y * ψ (D ^ (- 𝔰 p) * dist x y) * F.indicator f y

end T

variable (X) in
def TileLike : Type _ := 𝓓 X × OrderDual (Set (Θ X))

def TileLike.fst (x : TileLike X) : 𝓓 X := x.1
def TileLike.snd (x : TileLike X) : Set (Θ X) := x.2
instance : PartialOrder (TileLike X) := by dsimp [TileLike]; infer_instance
lemma TileLike.le_def (x y : TileLike X) : x ≤ y ↔ x.fst ≤ y.fst ∧ y.snd ⊆ x.snd := by rfl

@[simps]
def toTileLike (p : 𝔓 X) : TileLike X := (𝓘 p, Ω p)

lemma toTileLike_injective : Injective (fun p : 𝔓 X ↦ toTileLike p) := sorry

instance : PartialOrder (𝔓 X) := PartialOrder.lift toTileLike toTileLike_injective

/-- This is not defined as such in the blueprint, but `λp ≲ λ'p'` can be written using
`smul l p ≤ smul l' p'`.
Beware: `smul 1 p` is very different from `toTileLike p`. -/
def smul (l : ℝ) (p : 𝔓 X) : TileLike X :=
  (𝓘 p, ball_(p) (𝒬 p) l)

def TileLike.toTile (t : TileLike X) : Set (X × Θ X) :=
  (t.fst : Set X) ×ˢ t.snd

def E₁ (t : TileLike X) : Set X :=
  t.1 ∩ G ∩ Q ⁻¹' t.2

def E₂ (l : ℝ) (p : 𝔓 X) : Set X :=
  𝓘 p ∩ G ∩ Q ⁻¹' ball_(p) (𝒬 p) l

/-! `𝔓(𝔓')` in the blueprint is `lowerClosure 𝔓'` in Lean. -/

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₁ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (l ≥ (2 : ℝ≥0)), l ^ (-a) *
  ⨆ (p' ∈ lowerClosure 𝔓') (_h2 : smul l p ≤ smul l p'),
  volume (E₂ l p) / volume (𝓘 p : Set X)

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₂ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (r ≥ 4 * D ^ 𝔰 p),
  volume (F ∩ ball (𝔠 p) r) / volume (ball (𝔠 p) r)

-- a small characterization that might be useful
lemma isAntichain_iff_disjoint (𝔄 : Set (𝔓 X)) :
    IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄) ↔
    ∀ p p', p ∈ 𝔄 → p' ∈ 𝔄 → p ≠ p' →
    Disjoint (toTileLike (X := X) p).toTile (toTileLike p').toTile := sorry

namespace TileStructure
variable (X) in
structure Tree where
  carrier : Finset (𝔓 X)
  nonempty : Nonempty (𝔓 X)
  ordConnected : OrdConnected (carrier : Set (𝔓 X))

attribute [coe] Tree.carrier
instance : CoeTC (Tree X) (Finset (𝔓 X)) where coe := Tree.carrier
instance : CoeTC (Tree X) (Set (𝔓 X)) where coe p := ((p : Finset (𝔓 X)) : Set (𝔓 X))
instance : Membership (𝔓 X) (Tree X) := ⟨fun x p => x ∈ (p : Set _)⟩
instance : Preorder (Tree X) := Preorder.lift Tree.carrier

variable (X) in
/-- An `n`-forest -/
structure Forest (n : ℕ) where
  𝔘 : Finset (𝔓 X)
  𝔗 : 𝔓 X → Tree X -- Is it a problem that we totalized this function?
  smul_four_le {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : smul 4 p ≤ smul 1 u
  essSup_tsum_le : snorm (∑ u ∈ 𝔘, (𝓘 u : Set X).indicator (1 : X → ℝ)) ∞ volume ≤ 2 ^ n
  dens₁_𝔗_le {u} (hu : u ∈ 𝔘) : dens₁ (𝔗 u : Set (𝔓 X)) ≤ 2 ^ (4 * a + 1 - n)
  lt_dist {u u'} (hu : u ∈ 𝔘) (hu' : u' ∈ 𝔘) (huu' : u ≠ u') {p} (hp : p ∈ 𝔗 u')
    (h : 𝓘 p ≤ 𝓘 u) : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u)
  ball_subset {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u
  -- old conditions
  -- disjoint_I : ∀ {𝔗 𝔗'}, 𝔗 ∈ I → 𝔗' ∈ I → Disjoint 𝔗.carrier 𝔗'.carrier
  -- top_finite (x : X) : {𝔗 ∈ I | x ∈ 𝓓 (𝓘 𝔗.top)}.Finite
  -- card_top_le (x : X) : Nat.card {𝔗 ∈ I | x ∈ 𝓓 (𝓘 𝔗.top) } ≤ 2 ^ n * Real.log (n + 1)
  -- density_le {𝔗} (h𝔗 : 𝔗 ∈ I) : density G Q 𝔗 ≤ (2 : ℝ) ^ (-n : ℤ)
  -- delta_gt {j j'} (hj : j ∈ I) (hj' : j' ∈ I) (hjj' : j ≠ j') {p : 𝔓 X} (hp : p ∈ j)
  --   (h2p : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 j'.top)) : Δ p (Q j.top) > (2 : ℝ) ^ (3 * n / δ)

end TileStructure

--below is old

-- class Tree.IsThin (𝔗 : Tree X) : Prop where
--   thin {p : 𝔓 X} (hp : p ∈ 𝔗) : ball (𝔠 p) (8 * a/-fix-/ * D ^ 𝔰 p) ⊆ 𝓓 (𝓘 𝔗.top)

-- alias Tree.thin := Tree.IsThin.thin

-- def Δ (p : 𝔓 X) (Q' : C(X, ℝ)) : ℝ := localOscillation (𝓓 (𝓘 p)) (𝒬 p) Q' + 1

-- namespace Forest

/- Do we want to treat a forest as a set of trees, or a set of elements from `𝔓 X`? -/

-- instance : SetLike (Forest G Q δ n) (Tree X) where
--   coe s := s.I
--   coe_injective' p q h := by cases p; cases q; congr

-- instance : PartialOrder (Forest G Q δ n) := PartialOrder.lift (↑) SetLike.coe_injective

-- class IsThin (𝔉 : Forest G Q δ n) : Prop where
--   thin {𝔗} (h𝔗 : 𝔗 ∈ 𝔉.I) : 𝔗.IsThin

-- alias thin := Forest.IsThin.thin

-- /-- The union of all the trees in the forest. -/
-- def carrier (𝔉 : Forest G Q δ n) : Set (𝔓 X) := ⋃ 𝔗 ∈ 𝔉.I, 𝔗

--end Forest

-- set_option linter.unusedVariables false in
-- variable (X) in
-- class SmallBoundaryProperty (η : ℝ) : Prop where
--   volume_diff_le : ∃ (C : ℝ) (hC : C > 0), ∀ (x : X) r (δ : ℝ), 0 < r → 0 < δ → δ < 1 →
--     volume.real (ball x ((1 + δ) * r) \ ball x ((1 - δ) * r)) ≤ C * δ ^ η * volume.real (ball x r)

--def boundedTiles (F : Set X) (t : ℝ) : Set (𝔓 X) :=
--  { p : 𝔓 X | ∃ x ∈ 𝓘 p, maximalFunction volume (Set.indicator F (1 : X → ℂ)) x ≤ t }

-- set_option linter.unusedVariables false in
-- variable (X) in
-- class SmallBoundaryProperty (η : ℝ) : Prop where
--   volume_diff_le : ∃ (C : ℝ) (hC : C > 0), ∀ (x : X) r (δ : ℝ), 0 < r → 0 < δ → δ < 1 →
--     volume.real (ball x ((1 + δ) * r) \ ball x ((1 - δ) * r)) ≤ C * δ ^ η * volume.real (ball x r)

/- This is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
/- def MB_p {ι : Type*} [Fintype ι] (p : ℝ) (ℬ : ι → X × ℝ) (u : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (i : ι) , indicator (ball (ℬ i).1 (ℬ i).2) (1 : X → ℝ≥0∞) x / volume (ball (ℬ i).1 (ℬ i).2) *
    (∫⁻ y in (ball (ℬ i).1 (ℬ i).2), ‖u y‖₊^p)^(1/p)

abbrev MB {ι : Type*} [Fintype ι] (ℬ : ι → X × ℝ) (u : X → ℂ) (x : X) := MB_p 1 ℬ u x -/
