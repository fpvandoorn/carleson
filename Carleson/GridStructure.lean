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

export GridStructure (range_s_subset Grid_subset_biUnion ball_subset_Grid Grid_subset_ball small_boundary
  topCube s_topCube c_topCube subset_topCube) -- should `X` be explicit in topCube?

variable {D : ℕ} {κ C : ℝ} {S : ℕ} {o : X}

section GridStructure

variable [GridStructure X D κ S o]

variable (X) in
/-- The indexing type of the grid structure. Elements are called (dyadic) cubes.
Note that this type has instances for both `≤` and `⊆`, but they do *not* coincide. -/
abbrev Grid : Type u := GridStructure.Grid X A

def s : Grid X → ℤ := GridStructure.s
def c : Grid X → X := GridStructure.c

instance : Fintype (Grid X) := GridStructure.fintype_Grid
instance : Coe (Grid X) (Set X) := ⟨GridStructure.coeGrid⟩
instance : Membership X (Grid X) := ⟨fun x i ↦ x ∈ (i : Set X)⟩
instance : PartialOrder (Grid X) := PartialOrder.lift _ GridStructure.inj
/- These should probably not/only rarely be used. I comment them out for now,
so that we don't accidentally use it. We can put it back if useful after all. -/
-- instance : HasSubset (Grid X) := ⟨fun i j ↦ (i : Set X) ⊆ (j : Set X)⟩
-- instance : HasSSubset (Grid X) := ⟨fun i j ↦ (i : Set X) ⊂ (j : Set X)⟩

/- not sure whether these should be simp lemmas, but that might be required if we want to
  conveniently rewrite/simp with Set-lemmas -/
@[simp] lemma Grid.mem_def {x : X} {i : Grid X} : x ∈ i ↔ x ∈ (i : Set X) := .rfl
@[simp] lemma Grid.le_def {i j : Grid X} : i ≤ j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i ≤ s j := .rfl

/-- Beware: you *probably* want to use `i ≤ j`, and not `i ⊆ j`. -/
-- @[simp] lemma Grid.subset_def {i j : Grid X} : i ⊆ j ↔ (i : Set X) ⊆ (j : Set X) := .rfl
-- @[simp] lemma Grid.ssubset_def {i j : Grid X} : i ⊂ j ↔ (i : Set X) ⊂ (j : Set X) := .rfl

protected lemma Grid.inj : Injective (fun i : Grid X ↦ ((i : Set X), s i)) := GridStructure.inj

lemma fundamental_dyadic {i j : Grid X} :
    s i ≤ s j → (i : Set X) ⊆ (j : Set X) ∨ Disjoint (i : Set X) (j : Set X) :=
  GridStructure.fundamental_dyadic'

lemma le_or_disjoint {i j : Grid X} (h : s i ≤ s j) :
    i ≤ j ∨ Disjoint (i : Set X) (j : Set X) :=
  fundamental_dyadic h |>.imp (⟨·, h⟩) id

namespace Grid

lemma le_topCube {i : Grid X} : i ≤ topCube :=
  ⟨subset_topCube, (range_s_subset ⟨i, rfl⟩).2.trans_eq s_topCube.symm⟩

lemma isTop_topCube : IsTop (topCube : Grid X) := fun _ ↦ le_topCube

lemma isMax_iff {i : Grid X} : IsMax i ↔ i = topCube := isTop_topCube.isMax_iff

/-- The set `I ↦ Iᵒ` in the blueprint. -/
def int (i : Grid X) : Set X := ball (c i) (D ^ s i / 4)

postfix:max "ᵒ" => Grid.int

/-- An auxiliary measure used in the well-foundedness of `Ω` in Lemma `tile_structure`. -/
def opSize (i : Grid X) : ℕ := (S - s i).toNat

open Classical in
/-- If `i` is not a maximal element, this is the (unique) minimal element greater than i.
Note, this is not a `SuccOrder`, since an element can be the successor of multiple other elements.
-/
def succ (i : Grid X) : Grid X := if h : IsMax i then i else sorry

variable {i j : Grid X}

lemma le_succ : i ≤ i.succ := sorry
lemma max_of_le_succ : i.succ ≤ i → IsMax i := sorry
/-- The proof of this is between equations 4.2.7 and 4.2.8. -/
lemma succ_le_of_lt (h : i < j) : i.succ ≤ j := sorry
lemma opSize_succ_lt (h : ¬ IsMax i) : i.succ.opSize < i.opSize := sorry

end Grid

variable {i : Grid X}

lemma int_subset : i.int ⊆ i := by exact ball_subset_Grid

end GridStructure

-- instance homogeneousMeasurableSpace [Inhabited X] : MeasurableSpace C(X, ℝ) :=
--   let m : PseudoMetricSpace C(X, ℝ) :=
--     homogeneousPseudoMetric (ball default 1) -- an arbitary ball
--   let t : TopologicalSpace C(X, ℝ) := m.toUniformSpace.toTopologicalSpace
--   @borel C(X, ℝ) t

/- The datain a tile structure, and some basic properties.
This is mostly separated out so that we can nicely define the notation `d_𝔭`.
Note: compose `𝓘` with `Grid` to get the `𝓘` of the paper. -/
class PreTileStructure [FunctionDistances 𝕜 X] (Q : outParam (SimpleFunc X (Θ X)))
  (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X) extends GridStructure X D κ S o where
  protected 𝔓 : Type u
  fintype_𝔓 : Fintype 𝔓
  protected 𝓘 : 𝔓 → Grid
  surjective_𝓘 : Surjective 𝓘
  𝒬 : 𝔓 → Θ X
  range_𝒬 : range 𝒬 ⊆ range Q

export PreTileStructure (𝒬 range_𝒬)

section
variable [FunctionDistances 𝕜 X]  {Q : SimpleFunc X (Θ X)} [PreTileStructure Q D κ S o]

variable (X) in
def 𝔓 := PreTileStructure.𝔓 𝕜 X A
instance : Fintype (𝔓 X) := PreTileStructure.fintype_𝔓
def 𝓘 : 𝔓 X → Grid X := PreTileStructure.𝓘
lemma surjective_𝓘 : Surjective (𝓘 : 𝔓 X → Grid X) := PreTileStructure.surjective_𝓘
def 𝔠 (p : 𝔓 X) : X := c (𝓘 p)
def 𝔰 (p : 𝔓 X) : ℤ := s (𝓘 p)
end

local notation "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- A tile structure. -/
class TileStructure [FunctionDistances ℝ X] (Q : outParam (SimpleFunc X (Θ X)))
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X)
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
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
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

lemma Grid.nonempty (I : Grid X) : (I : Set X).Nonempty := by
  apply Set.Nonempty.mono ball_subset_Grid
  simp only [defaultA, defaultD, defaultκ, nonempty_ball, gt_iff_lt, Nat.ofNat_pos,
    div_pos_iff_of_pos_right]
  positivity

/-- Lemma 2.1.2, part 1. -/
lemma Grid.dist_mono {I J : Grid X} (hpq : I ≤ J) {f g : Θ X} :
    dist_{I} f g ≤ dist_{J} f g := by
  rw [Grid.le_def] at hpq
  obtain ⟨hpq, h'⟩ := hpq
  obtain h|h := h'.eq_or_lt
  · suffices I = J by
      rw [this]
    simp_rw [← Grid.inj.eq_iff, Prod.ext_iff, h, and_true]
    apply subset_antisymm hpq
    apply (fundamental_dyadic h.symm.le).resolve_right
    rw [Set.not_disjoint_iff_nonempty_inter, inter_eq_self_of_subset_right hpq]
    exact Grid.nonempty _
  simp only [not_le, ← Int.add_one_le_iff] at h
  sorry

def C2_1_2 (a : ℝ) : ℝ := 2 ^ (-95 * a)

/-- Lemma 2.1.2, part 2. -/
lemma Grid.dist_strictMono {I J : Grid X} (hpq : I < J) {f g : Θ X} :
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
def TileLike : Type _ := Grid X × OrderDual (Set (Θ X))

def TileLike.fst (x : TileLike X) : Grid X := x.1
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
  ⨆ (p ∈ 𝔓') (l ≥ (2 : ℝ≥0)), l ^ (-a : ℝ) *
  ⨆ (p' ∈ lowerClosure 𝔓') (_h2 : smul l p ≤ smul l p'),
  volume (E₂ l p) / volume (𝓘 p : Set X)

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₂ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (r ≥ 4 * (D ^ 𝔰 p : ℝ)),
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
  -- top_finite (x : X) : {𝔗 ∈ I | x ∈ Grid (𝓘 𝔗.top)}.Finite
  -- card_top_le (x : X) : Nat.card {𝔗 ∈ I | x ∈ Grid (𝓘 𝔗.top) } ≤ 2 ^ n * Real.log (n + 1)
  -- density_le {𝔗} (h𝔗 : 𝔗 ∈ I) : density G Q 𝔗 ≤ (2 : ℝ) ^ (-n : ℤ)
  -- delta_gt {j j'} (hj : j ∈ I) (hj' : j' ∈ I) (hjj' : j ≠ j') {p : 𝔓 X} (hp : p ∈ j)
  --   (h2p : Grid (𝓘 p) ⊆ Grid (𝓘 j'.top)) : Δ p (Q j.top) > (2 : ℝ) ^ (3 * n / δ)

end TileStructure

--below is old

-- class Tree.IsThin (𝔗 : Tree X) : Prop where
--   thin {p : 𝔓 X} (hp : p ∈ 𝔗) : ball (𝔠 p) (8 * a/-fix-/ * D ^ 𝔰 p) ⊆ Grid (𝓘 𝔗.top)

-- alias Tree.thin := Tree.IsThin.thin

-- def Δ (p : 𝔓 X) (Q' : C(X, ℝ)) : ℝ := localOscillation (Grid (𝓘 p)) (𝒬 p) Q' + 1

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
