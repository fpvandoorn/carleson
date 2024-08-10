import Carleson.TileStructure

-- https://github.com/leanprover/lean4/issues/4947
-- https://github.com/leanprover/lean4/pull/4968
attribute [-simp] Nat.reducePow

open Set MeasureTheory Metric Function Complex Bornology Classical
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]
variable [TileStructure Q D κ S o] {p p' : 𝔓 X} {f g : Θ X}
  {C C' : Set (𝔓 X)} {x x' : X}

/-- The number of tiles `p` in `s` whose underlying cube `𝓘 p` contains `x`. -/
def stackSize (C : Set (𝔓 X)) (x : X) : ℕ :=
  ∑ p ∈ Finset.univ.filter (· ∈ C), (𝓘 p : Set X).indicator 1 x

lemma stackSize_setOf_add_stackSize_setOf_not {P : 𝔓 X → Prop} :
    stackSize {p ∈ C | P p} x + stackSize {p ∈ C | ¬ P p} x = stackSize C x := by
  classical
  simp_rw [stackSize]
  conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not _ P]
  simp_rw [Finset.filter_filter]
  congr

lemma stackSize_congr (h : ∀ p ∈ C, x ∈ (𝓘 p : Set X) ↔ x' ∈ (𝓘 p : Set X)) :
    stackSize C x = stackSize C x' := by
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp_rw [indicator, h p hp, Pi.one_apply]

lemma stackSize_mono (h : C ⊆ C') : stackSize C x ≤ stackSize C' x := by
  apply Finset.sum_le_sum_of_subset (fun x ↦ ?_)
  simp [iff_true_intro (@h x)]

-- Simplify the cast of `stackSize C x` from `ℕ` to `ℝ`
lemma stackSize_real (C : Set (𝔓 X)) (x : X) : (stackSize C x : ℝ) =
    ∑ p ∈ Finset.univ.filter (· ∈ C), (𝓘 p : Set X).indicator (1 : X → ℝ) x := by
  rw [stackSize, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  by_cases hx : x ∈ (𝓘 u : Set X) <;> simp [hx]

lemma stackSize_measurable : Measurable fun x ↦ (stackSize C x : ℝ≥0∞) := by
  simp_rw [stackSize, Nat.cast_sum, indicator, Nat.cast_ite]
  refine Finset.measurable_sum _ fun _ _ ↦ Measurable.ite coeGrid_measurable ?_ ?_ <;> simp

/-! We might want to develop some API about partitioning a set.
But maybe `Set.PairwiseDisjoint` and `Set.Union` are enough.
Related, but not quite useful: `Setoid.IsPartition`. -/

-- /-- `u` is partitioned into subsets in `C`. -/
-- class Set.IsPartition {α ι : Type*} (u : Set α) (s : Set ι) (C : ι → Set α) : Prop :=
--   pairwiseDisjoint : s.PairwiseDisjoint C
--   iUnion_eq : ⋃ (i ∈ s), C i = u


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
  𝔗 : 𝔓 X → Set (𝔓 X) -- Is it a problem that we totalized this function?
  nonempty {u} (hu : u ∈ 𝔘) : (𝔗 u).Nonempty
  ordConnected {u} (hu : u ∈ 𝔘) : OrdConnected (𝔗 u) -- (2.0.33)
  𝓘_ne_𝓘 {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : 𝓘 p ≠ 𝓘 u
  smul_four_le {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : smul 4 p ≤ smul 1 u -- (2.0.32)
  stackSize_le {x} : stackSize 𝔘 x ≤ 2 ^ n -- (2.0.34), we formulate this a bit differently.
  dens₁_𝔗_le {u} (hu : u ∈ 𝔘) : dens₁ (𝔗 u : Set (𝔓 X)) ≤ 2 ^ (4 * a - n + 1) -- (2.0.35)
  lt_dist {u u'} (hu : u ∈ 𝔘) (hu' : u' ∈ 𝔘) (huu' : u ≠ u') {p} (hp : p ∈ 𝔗 u')
    (h : 𝓘 p ≤ 𝓘 u) : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) -- (2.0.36)
  ball_subset {u} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u -- (2.0.37)
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
