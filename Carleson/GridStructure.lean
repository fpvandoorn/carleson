import Carleson.Defs

open Set MeasureTheory Metric Function Complex
open scoped ENNReal
noncomputable section

variable {𝕜 : Type*} {A : ℝ} [_root_.RCLike 𝕜]
variable {X : Type*} {A : ℝ} [PseudoMetricSpace X] [DoublingMeasure X A]

variable (X) in
/-- A grid structure on `X`.
I expect we prefer `𝓓 : ι → Set X` over `𝓓 : Set (Set X)`
Note: the `s` in this paper is `-s` of Christ's paper.
-/
class GridStructure (D κ C : outParam ℝ) (S : outParam ℤ) (o : outParam X) where
  /-- indexing set for a grid structure -/
  ι : Type*
  fintype_ι : Fintype ι
  /-- The collection of dyadic cubes -/
  𝓓 : ι → Set X
  /-- scale functions -/
  s : ι → ℤ
  /-- Center functions -/
  c : ι → X
  range_s_subset : range s ⊆ Icc (-S) S
  𝓓_subset_biUnion {i} : ∀ k ∈ Ico (-S) (s i), 𝓓 i ⊆ ⋃ j ∈ s ⁻¹' {k}, 𝓓 j
  fundamental_dyadic {i j} : s i ≤ s j → 𝓓 i ⊆ 𝓓 j ∨ Disjoint (𝓓 i) (𝓓 j)
  ball_subset_biUnion : ∀ k ∈ Icc (-S) S, ball o (D ^ S) ⊆ ⋃ i ∈ s ⁻¹' {k}, 𝓓 i
  ball_subset_𝓓 {i} : ball (c i) (D ^ s i / 4) ⊆ 𝓓 i
  𝓓_subset_ball {i} : 𝓓 i ⊆ ball (c i) (4 * D ^ s i)
  small_boundary {i} {t : ℝ} (ht : D ^ (- S - s i) ≤ t) :
    volume.real { x ∈ 𝓓 i | infDist x (𝓓 i)ᶜ ≤ t * D ^ s i } ≤ C * t ^ κ * volume.real (𝓓 i)

export GridStructure (range_s_subset 𝓓_subset_biUnion
  fundamental_dyadic ball_subset_biUnion ball_subset_𝓓 𝓓_subset_ball small_boundary)

variable {D κ C : ℝ} {S : ℤ} {o : X}

section GridStructure

variable [GridStructure X D κ C S o]

variable (X) in
def ι : Type* := GridStructure.ι X A
instance : Fintype (ι X) := GridStructure.fintype_ι
def s : ι X → ℤ := GridStructure.s
def 𝓓 : ι X → Set X := GridStructure.𝓓
def c : ι X → X := GridStructure.c


end GridStructure

-- def grid_existence {σ₁ σ₂ : X → ℤ} (hσ : σ₁ ≤ σ₂)
--     (hσ₁ : Measurable σ₁) (hσ₂ : Measurable σ₂)
--     (hσ₁S : range σ₁ ⊆ Icc (-S) S) (hσ₂S : range σ₂ ⊆ Icc (-S) S)
--     {Q : X → C(X, ℂ)} (hQΘ : range Q ⊆ Θ) :
--     GridStructure X D κ C S o :=
--   sorry

-- instance homogeneousMeasurableSpace [Inhabited X] : MeasurableSpace C(X, ℝ) :=
--   let m : PseudoMetricSpace C(X, ℝ) :=
--     homogeneousPseudoMetric (ball default 1) -- an arbitary ball
--   let t : TopologicalSpace C(X, ℝ) := m.toUniformSpace.toTopologicalSpace
--   @borel C(X, ℝ) t

/- Note: compose `𝓘` with `𝓓` to get the `𝓘` of the paper. -/
class TileStructureData.{u} [FunctionDistances 𝕜 X]
  (D κ C : outParam ℝ) (S : outParam ℤ) (o : outParam X) extends GridStructure X D κ C S o where
  protected 𝔓 : Type u
  fintype_𝔓 : Fintype 𝔓
  protected 𝓘 : 𝔓 → ι
  surjective_𝓘 : Surjective 𝓘
  Ω : 𝔓 → Set (ι' X)
  𝒬 : 𝔓 → ι' X

export TileStructureData (Ω 𝒬)

section
variable {Q : X → C(X, ℂ)} [FunctionDistances 𝕜 X] [TileStructureData D κ C S o]

variable (X) in
def 𝔓 := TileStructureData.𝔓 𝕜 X A
instance : Fintype (𝔓 X) := TileStructureData.fintype_𝔓
def 𝓘 : 𝔓 X → ι X := TileStructureData.𝓘
lemma surjective_𝓘 : Surjective (𝓘 : 𝔓 X → ι X) := TileStructureData.surjective_𝓘
def 𝔠 (p : 𝔓 X) : X := c (𝓘 p)
def 𝔰 (p : 𝔓 X) : ℤ := s (𝓘 p)
end

notation3 "dist_(" D "," 𝔭 ")" => @dist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation3 "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- A tile structure. -/
class TileStructure [FunctionDistances ℂ X] (Q : outParam (X → C(X, ℂ)))
    (D κ C : outParam ℝ) (S : outParam ℤ) (o : outParam X)
    extends TileStructureData D κ C S o where
  biUnion_Ω {i} : range Q ⊆ Θ '' ⋃ p ∈ 𝓘 ⁻¹' {i}, Ω p
  disjoint_Ω {p p'} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') : Disjoint (Ω p) (Ω p')
  relative_fundamental_dyadic {p p'} (h : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 p')) : Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  cdist_subset {p} : ball_(D, p) (𝒬 p) 5⁻¹ ⊆ Ω p
  subset_cdist {p} : Ω p ⊆ ball_(D, p) (𝒬 p) 1

export TileStructure (biUnion_Ω disjoint_Ω relative_fundamental_dyadic cdist_subset subset_cdist)

variable {Q : X → C(X, ℂ)} [FunctionDistances ℂ X] [TileStructure Q D κ C S o]

/- The set `E` defined in Proposition 2.1. -/
def E (σ σ' : X → ℤ) (p : 𝔓 X) : Set X :=
  { x ∈ 𝓓 (𝓘 p) | Q x ∈ Θ '' Ω p ∧ 𝔰 p ∈ Icc (σ x) (σ' x) }

section T

variable (K : X → X → ℂ) (σ σ' : X → ℤ) (ψ : ℝ → ℝ) (p : 𝔓 X) (F : Set X)

/- The operator `T` defined in Proposition 2.1, considered on the set `F`.
It is the map `T ∘ (1_F * ·) : f ↦ T (1_F * f)`, also denoted `T1_F`
The operator `T` in Proposition 2.1 is therefore `applied to `(F := Set.univ)`. -/
def T (f : X → ℂ) : X → ℂ :=
  indicator (E σ σ' p)
    fun x ↦ ∫ y, exp (Q x x - Q x y) * K x y * ψ (D ^ (- 𝔰 p) * dist x y) * F.indicator f y

lemma Memℒp_T {f : X → ℂ} {q : ℝ≥0∞} (hf : Memℒp f q) : Memℒp (T K σ σ' ψ p F f) q :=
  by sorry

/- The operator `T`, defined on `L^2` maps. -/
def T₂ (f : X →₂[volume] ℂ) : X →₂[volume] ℂ :=
  Memℒp.toLp (T K σ σ' ψ p F f) <| Memℒp_T K σ σ' ψ p F <| Lp.memℒp f

/- The operator `T`, defined on `L^2` maps as a continuous linear map. -/
def TL : (X →₂[volume] ℂ) →L[ℂ] (X →₂[volume] ℂ) where
    toFun := T₂ K σ σ' ψ p F
    map_add' := sorry
    map_smul' := sorry
    cont := by sorry

end T

variable (X) in
def TileLike : Type _ := Set X × OrderDual (Set (ι' X))

def TileLike.fst (x : TileLike X) : Set X := x.1
def TileLike.snd (x : TileLike X) : Set (ι' X) := x.2
instance : PartialOrder (TileLike X) := by dsimp [TileLike]; infer_instance
example (x y : TileLike X) : x ≤ y ↔ x.fst ⊆ y.fst ∧ y.snd ⊆ x.snd := by rfl

def toTileLike (p : 𝔓 X) : TileLike X := (𝓓 (𝓘 p), Ω p)

lemma toTileLike_injective : Injective (fun p : 𝔓 X ↦ toTileLike p) := sorry

instance : PartialOrder (𝔓 X) := PartialOrder.lift toTileLike toTileLike_injective

def smul (a : ℝ) (p : 𝔓 X) : TileLike X :=
  sorry --(𝓓 (𝓘 p), localOscillationBall (𝓓 (𝓘 p)) (Θ (𝒬 p)) a)

def TileLike.toTile (t : TileLike X) : Set (X × ι' X) :=
  t.fst ×ˢ t.snd

lemma isAntichain_iff_disjoint (𝔄 : Set (𝔓 X)) :
    IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄) ↔
    ∀ p p', p ∈ 𝔄 → p' ∈ 𝔄 → p ≠ p' →
    Disjoint (toTileLike (X := X) p).toTile (toTileLike p').toTile := sorry

def convexShadow (𝔓' : Set (𝔓 X)) : Set (ι X) :=
  { i | ∃ p p' : 𝔓 X, p ∈ 𝔓' ∧ p' ∈ 𝔓' ∧ (𝓓 (𝓘 p) : Set X) ⊆ 𝓓 i ∧ 𝓓 i ⊆ 𝓓 (𝓘 p') }

def EBar (G : Set X) (Q : X → ι' X) (t : TileLike X) : Set X :=
  { x ∈ t.fst ∩ G | Q x ∈ t.snd }

def density (G : Set X) (Q : X → ι' X) (𝔓' : Set (𝔓 X)) : ℝ :=
  ⨆ (p ∈ 𝔓') (l ≥ (2 : ℝ)), l ^ (-2 * Real.log A) *
  ⨆ (p' : 𝔓 X) (_h : 𝓘 p' ∈ convexShadow 𝔓') (_h2 : smul l p ≤ smul l p'),
  volume.real (EBar G Q (smul l p')) / volume.real (EBar G Q (toTileLike p))

/-- Hardy-Littlewood maximal function -/
def maximalFunction {E} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (f : X → E) (x : X) : ℝ :=
  ⨆ (x' : X) (δ : ℝ) (_hx : x ∈ ball x' δ),
  ⨍⁻ y, ‖f y‖₊ ∂volume.restrict (ball x' δ) |>.toReal

def boundedTiles (F : Set X) (t : ℝ) : Set (𝔓 X) :=
  { p : 𝔓 X | ∃ x ∈ 𝓓 (𝓘 p), maximalFunction (Set.indicator F (1 : X → ℂ)) x ≤ t }

set_option linter.unusedVariables false in
variable (X) in
class SmallBoundaryProperty (η : ℝ) : Prop where
  volume_diff_le : ∃ (C : ℝ) (hC : C > 0), ∀ (x : X) r (δ : ℝ), 0 < r → 0 < δ → δ < 1 →
    volume.real (ball x ((1 + δ) * r) \ ball x ((1 - δ) * r)) ≤ C * δ ^ η * volume.real (ball x r)


namespace TileStructure
variable (X) in
structure Tree where
  carrier : Set (𝔓 X)
  top : 𝔓 X
  le_top {p : 𝔓 X} (hp : p ∈ carrier): smul 4 p ≤ toTileLike top
  ordConnected : OrdConnected carrier -- the convexity condition

attribute [coe] Tree.carrier
instance : CoeTC (Tree X) (Set (𝔓 X)) where coe := Tree.carrier
instance : Membership (𝔓 X) (Tree X) := ⟨fun x p => x ∈ (p : Set _)⟩
instance : Preorder (Tree X) := Preorder.lift Tree.carrier

-- LaTeX note: $D ^ {s(p)}$ should be $D ^ {s(I(p))}$
class Tree.IsThin (𝔗 : Tree X) : Prop where
  thin {p : 𝔓 X} (hp : p ∈ 𝔗) : ball (𝔠 p) (8 * A ^ 3 * D ^ 𝔰 p) ⊆ 𝓓 (𝓘 𝔗.top)

alias Tree.thin := Tree.IsThin.thin

-- def Δ (p : 𝔓 X) (Q' : C(X, ℝ)) : ℝ := localOscillation (𝓓 (𝓘 p)) (𝒬 p) Q' + 1


-- /--
-- A forest is a set of pairwise disjoint trees
-- note(F): currently we allow that the tree with the empty carrier occurs (multiple times) in the
-- forest, I believe.
-- -/
-- structure Forest (G : Set X) (Q : X → C(X,ℝ)) (δ : ℝ) (n : ℕ) where
--   I : Set (Tree X)
--   disjoint_I : ∀ {𝔗 𝔗'}, 𝔗 ∈ I → 𝔗' ∈ I → Disjoint 𝔗.carrier 𝔗'.carrier
--   top_finite (x : X) : {𝔗 ∈ I | x ∈ 𝓓 (𝓘 𝔗.top)}.Finite
--   card_top_le (x : X) : Nat.card {𝔗 ∈ I | x ∈ 𝓓 (𝓘 𝔗.top) } ≤ 2 ^ n * Real.log (n + 1)
--   density_le {𝔗} (h𝔗 : 𝔗 ∈ I) : density G Q 𝔗 ≤ (2 : ℝ) ^ (-n : ℤ)
--   delta_gt {j j'} (hj : j ∈ I) (hj' : j' ∈ I) (hjj' : j ≠ j') {p : 𝔓 X} (hp : p ∈ j)
--     (h2p : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 j'.top)) : Δ p (Q j.top) > (2 : ℝ) ^ (3 * n / δ)

variable {G : Set X} {Q : X → C(X,ℝ)} {δ : ℝ} {n : ℕ}

namespace Forest

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

end Forest

end TileStructure
