import Carleson.TileStructure

open Set MeasureTheory Metric Function Complex Bornology Classical
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]
variable [TileStructure Q D κ S o] {u u' p p' : 𝔓 X} {f g : Θ X}
  {C C' : Set (𝔓 X)} {x x' : X}

namespace TileStructure
-- variable (X) in
-- structure Tree where
--   carrier : Set (𝔓 X)
--   nonempty : Nonempty carrier
--   ordConnected : OrdConnected carrier -- (2.0.33)

-- attribute [coe] Tree.carrier
-- instance : CoeTC (Tree X) (Set (𝔓 X)) where coe := Tree.carrier
-- -- instance : CoeTC (Tree X) (Finset (𝔓 X)) where coe := Tree.carrier
-- -- instance : CoeTC (Tree X) (Set (𝔓 X)) where coe p := ((p : Finset (𝔓 X)) : Set (𝔓 X))
-- instance : Membership (𝔓 X) (Tree X) := ⟨fun x p => x ∈ (p : Set _)⟩
-- instance : Preorder (Tree X) := Preorder.lift Tree.carrier

variable (X) in
/-- An `n`-forest -/
structure Forest (n : ℕ) where
  𝔘 : Set (𝔓 X)
  /-- The value of `𝔗 u` only matters when `u ∈ 𝔘`. -/
  𝔗 : 𝔓 X → Set (𝔓 X)
  nonempty' {u} (hu : u ∈ 𝔘) : (𝔗 u).Nonempty
  ordConnected' {u} (hu : u ∈ 𝔘) : OrdConnected (𝔗 u) -- (2.0.33)
  𝓘_ne_𝓘' {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : 𝓘 p ≠ 𝓘 u
  smul_four_le' {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : smul 4 p ≤ smul 1 u -- (2.0.32)
  stackSize_le' {x} : stackSize 𝔘 x ≤ 2 ^ n -- (2.0.34), we formulate this a bit differently.
  dens₁_𝔗_le' {u} (hu : u ∈ 𝔘) : dens₁ (𝔗 u) ≤ 2 ^ (4 * (a : ℝ) - n + 1) -- (2.0.35)
  lt_dist' {u u'} (hu : u ∈ 𝔘) (hu' : u' ∈ 𝔘) (huu' : u ≠ u') {p} (hp : p ∈ 𝔗 u')
    (h : 𝓘 p ≤ 𝓘 u) : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) -- (2.0.36)
  ball_subset' {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u -- (2.0.37)

namespace Forest

variable {n : ℕ} (t : Forest X n)

instance : CoeHead (Forest X n) (Set (𝔓 X)) := ⟨Forest.𝔘⟩
instance : Membership (𝔓 X) (Forest X n) := ⟨fun t x ↦ x ∈ (t : Set (𝔓 X))⟩
instance : CoeFun (Forest X n) (fun _ ↦ 𝔓 X → Set (𝔓 X)) := ⟨fun t x ↦ t.𝔗 x⟩

@[simp] lemma mem_mk (n 𝔘 𝔗 a b c d e f g h) (p : 𝔓 X) :
    p ∈ Forest.mk (n := n) 𝔘 𝔗 a b c d e f g h ↔ p ∈ 𝔘 := Iff.rfl

@[simp] lemma mem_𝔘 : u ∈ t.𝔘 ↔ u ∈ t := .rfl
@[simp] lemma mem_𝔗 : p ∈ t.𝔗 u ↔ p ∈ t u := .rfl

lemma nonempty (hu : u ∈ t) : (t u).Nonempty := t.nonempty' hu
lemma ordConnected (hu : u ∈ t) : OrdConnected (t u) := t.ordConnected' hu
lemma 𝓘_ne_𝓘 (hu : u ∈ t) (hp : p ∈ t u) : 𝓘 p ≠ 𝓘 u := t.𝓘_ne_𝓘' hu hp
lemma smul_four_le (hu : u ∈ t) (hp : p ∈ t u) : smul 4 p ≤ smul 1 u := t.smul_four_le' hu hp
lemma stackSize_le : stackSize t x ≤ 2 ^ n := t.stackSize_le'
lemma dens₁_𝔗_le (hu : u ∈ t) : dens₁ (t u) ≤ 2 ^ (4 * (a : ℝ) - n + 1) := t.dens₁_𝔗_le' hu
lemma lt_dist (hu : u ∈ t) (hu' : u' ∈ t) (huu' : u ≠ u') {p} (hp : p ∈ t u') (h : 𝓘 p ≤ 𝓘 u) :
    2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) := t.lt_dist' hu hu' huu' hp h
lemma ball_subset (hu : u ∈ t) (hp : p ∈ t u) : ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u :=
  t.ball_subset' hu hp

-- Used in the proof of Lemma 7.1.4
variable {t} in
lemma ball_subset_of_mem_𝓘 (hu : u ∈ t) {p : 𝔓 X} (hp : p ∈ t u) {x : X} (hx : x ∈ 𝓘 p) :
    ball x (4 * D ^ (𝔰 p)) ⊆ 𝓘 u := by
  refine (ball_subset_ball' ?_).trans (t.ball_subset hu hp)
  linarith [show dist x (𝔠 p) < 4 * D ^ (𝔰 p) from Grid_subset_ball hx]

lemma if_descendant_then_subset (hu : u ∈ t) (hp : p ∈ t u) : (𝓘 p : Set X) ⊆ 𝓘 u := by
  calc ↑(𝓘 p)
    _ ⊆ ball (𝔠 p) (4 * ↑D ^ 𝔰 p) := by
      exact GridStructure.Grid_subset_ball (i := 𝓘 p)
    _ ⊆ ↑(𝓘 u) := ball_subset_of_mem_𝓘 hu hp Grid.c_mem_Grid

end Forest

variable (X) in
/-- An `n`-row -/
structure Row (n : ℕ) extends Forest X n where
  pairwiseDisjoint' : 𝔘.PairwiseDisjoint (fun u ↦ (𝓘 u : Set X))

namespace Row

variable {n : ℕ} (t : Row X n)

instance : CoeHead (Row X n) (Set (𝔓 X)) := ⟨fun t ↦ t.𝔘⟩
instance : Membership (𝔓 X) (Row X n) := ⟨fun t x ↦ x ∈ (t : Set (𝔓 X))⟩
instance : CoeFun (Row X n) (fun _ ↦ 𝔓 X → Set (𝔓 X)) := ⟨fun t x ↦ t.𝔗 x⟩

@[simp] lemma mem_𝔘 : u ∈ t.𝔘 ↔ u ∈ t := .rfl
@[simp] lemma mem_𝔗 : p ∈ t.𝔗 u ↔ p ∈ t u := .rfl

lemma pairwiseDisjoint : Set.PairwiseDisjoint (t : Set (𝔓 X)) (fun u ↦ (𝓘 u : Set X)) :=
  t.pairwiseDisjoint'

end Row
end TileStructure
