import Carleson.Forest
-- import Carleson.Proposition2
-- import Carleson.Proposition3

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
open Classical -- We use quite some `Finset.filter`
noncomputable section


open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

def aux𝓒 (k : ℕ) : Set (Grid X) :=
  {i : Grid X | ∃ j : Grid X, i ≤ j ∧ 2 ^ (- (k : ℤ)) * volume (j : Set X) < volume (G ∩ j) }

/-- The partition `𝓒(G, k)` of `Grid X` by volume, given in (5.1.1) and (5.1.2).
Note: the `G` is fixed with properties in `ProofData`. -/
def 𝓒 (k : ℕ) : Set (Grid X) :=
  aux𝓒 (k + 1) \ aux𝓒 k

/-- The definition `𝔓(k)` given in (5.1.3). -/
def TilesAt (k : ℕ) : Set (𝔓 X) := 𝓘 ⁻¹' 𝓒 k

def aux𝔐 (k n : ℕ) : Set (𝔓 X) :=
  {p ∈ TilesAt k | 2 ^ (- (n : ℤ)) * volume (𝓘 p : Set X) < volume (E₁ p) }

/-- The definition `𝔐(k, n)` given in (5.1.4) and (5.1.5). -/
def 𝔐 (k n : ℕ) : Set (𝔓 X) := maximals (·≤·) (aux𝔐 k n)

/-- The definition `dens'_k(𝔓')` given in (5.1.6). -/
def dens' (k : ℕ) (P' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ p' ∈ P', ⨆ (l : ℝ≥0), ⨆ (_hl : 2 ≤ l),
  ⨆ (p : 𝔓 X) (_h1p : p ∈ TilesAt k) (_h2p : smul l p' ≤ smul l p),
  l ^ (- (a : ℤ)) * volume (E₂ l p) / volume (𝓘 p : Set X)

def auxℭ (k n : ℕ) : Set (𝔓 X) :=
  { p ∈ TilesAt k | 2 ^ (4 * a - n) < dens' k {p} }

/-- The partition `ℭ(k, n)` of `𝔓(k)` by density, given in (5.1.7). -/
def ℭ (k n : ℕ) : Set (𝔓 X) :=
  { p ∈ TilesAt k | dens' k {p} ∈ Ioc (2 ^ (4 * a - n)) (2 ^ (4 * a - (n + 1))) }

/-- The subset `𝔅(p)` of `𝔐(k, n)`, given in (5.1.8). -/
def 𝔅 (k n : ℕ) (p : 𝔓 X) : Set (𝔓 X) :=
  { m ∈ 𝔐 k n | smul 100 p ≤ smul 1 m }

def preℭ₁ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ k n | 2 ^ j ≤ (Finset.univ.filter (· ∈ 𝔅 k n p)).card }

/-- The subset `ℭ₁(k, n, j)` of `ℭ(k, n)`, given in (5.1.9).
Together with `𝔏₀(k, n)` this forms a partition. -/
def ℭ₁ (k n j : ℕ) : Set (𝔓 X) :=
  preℭ₁ k n j \ preℭ₁ k n (j + 1)

/-- The subset `𝔏₀(k, n, j)` of `ℭ(k, n)`, given in (5.1.10). -/
def 𝔏₀ (k n : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ k n | 𝔅 k n p = ∅ }

/-- `𝔏₁(k, n, j, l)` consists of the minimal elements in `ℭ₁(k, n, j)` not in
  `𝔏₁(k, n, j, l')` for some `l' < l`. Defined near (5.1.11). -/
def 𝔏₁ (k n j l : ℕ) : Set (𝔓 X) :=
  minimals (·≤·) (ℭ₁ k n j \ ⋃ (l' < l), 𝔏₁ k n j l')

/-- The subset `ℭ₂(k, n, j)` of `ℭ₁(k, n, j)`, given in (5.1.13).
To check: the current definition assumes that `𝔏₁ k n j (Z * (n + 1)) = ∅`,
otherwise we need to add an upper bound. -/
def ℭ₂ (k n j : ℕ) : Set (𝔓 X) :=
  ℭ₁ k n j \ ⋃ (l ≤ Z * (n + 1)), 𝔏₁ k n j l

/-- The subset `𝔘₁(k, n, j)` of `ℭ₁(k, n, j)`, given in (5.1.14). -/
def 𝔘₁ (k n j : ℕ) : Set (𝔓 X) :=
  { u ∈ ℭ₁ k n j | ∀ p ∈ ℭ₁ k n j, 𝓘 u < 𝓘 p → Disjoint (ball_(u) (𝒬 u) 100) (ball_(p) (𝒬 p) 100) }

/-- The subset `𝔏₂(k, n, j)` of `ℭ₂(k, n, j)`, given in (5.1.15). -/
def 𝔏₂ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ₂ k n j | ¬ ∃ u ∈ 𝔘₁ k n j, 𝓘 p ≠ 𝓘 u ∧ smul 2 p ≤ smul 1 u }

/-- The subset `ℭ₃(k, n, j)` of `ℭ₂(k, n, j)`, given in (5.1.16). -/
def ℭ₃ (k n j : ℕ) : Set (𝔓 X) :=
  ℭ₂ k n j \ 𝔏₂ k n j

/-- `𝔏₃(k, n, j, l)` consists of the maximal elements in `ℭ₃(k, n, j)` not in
  `𝔏₃(k, n, j, l')` for some `l' < l`. Defined near (5.1.17). -/
def 𝔏₃ (k n j l : ℕ) : Set (𝔓 X) :=
  maximals (·≤·) (ℭ₃ k n j \ ⋃ (l' < l), 𝔏₃ k n j l')

/-- The subset `ℭ₄(k, n, j)` of `ℭ₃(k, n, j)`, given in (5.1.19).
To check: the current definition assumes that `𝔏₃ k n j (Z * (n + 1)) = ∅`,
otherwise we need to add an upper bound. -/
def ℭ₄ (k n j : ℕ) : Set (𝔓 X) :=
  ℭ₃ k n j \ ⋃ (l : ℕ), 𝔏₃ k n j l

/-- The subset `𝓛(u)` of `Grid X`, given near (5.1.20).
Note: It seems to also depend on `n`. -/
def 𝓛 (n : ℕ) (u : 𝔓 X) : Set (Grid X) :=
  { i : Grid X | i ≤ 𝓘 u ∧ s i + Z * (n + 1) + 1 = 𝔰 u ∧ ¬ ball (c i) (8 * D ^ s i) ⊆ 𝓘 u }

/-- The subset `𝔏₄(k, n, j)` of `ℭ₄(k, n, j)`, given near (5.1.22).
Todo: we may need to change the definition to say that `p`
is at most the least upper bound of `𝓛 n u` in `Grid X`. -/
def 𝔏₄ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ₄ k n j | ∃ u ∈ 𝔘₁ k n j, (𝓘 p : Set X) ⊆ ⋃ (i ∈ 𝓛 (X := X) n u), i }

/-- The subset `ℭ₅(k, n, j)` of `ℭ₄(k, n, j)`, given in (5.1.23). -/
def ℭ₅ (k n j : ℕ) : Set (𝔓 X) :=
  ℭ₄ k n j \ 𝔏₄ k n j

/-- The set $\mathcal{P}_{F,G}$, defined in (5.1.24). -/
def highDensityTiles : Set (𝔓 X) :=
  { p : 𝔓 X | 2 ^ (2 * a + 5) * volume F / volume G ≤ dens₂ {p} }

/-- The exceptional set `G₁`, defined in (5.1.25). -/
def G₁ : Set X := ⋃ (p : 𝔓 X) (_ : p ∈ highDensityTiles), 𝓘 p

/-- The set `A(λ, k, n)`, defined in (5.1.26). -/
def setA (l k n : ℕ) : Set X :=
  {x : X | l * 2 ^ (n + 1) < ∑ p ∈ Finset.univ.filter (· ∈ 𝔐 (X := X) k n),
    (𝓘 p : Set X).indicator 1 x }

/-- The set `G₂`, defined in (5.1.27). -/
def G₂ : Set X := ⋃ (n : ℕ) (k < n), setA (2 * n + 6) k n

/-- The set `G₃`, defined in (5.1.28). -/
def G₃ : Set X := ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3) (p ∈ 𝔏₄ (X := X) k n j), 𝓘 p

/-- The set `G'`, defined below (5.1.28). -/
def G' : Set X := G₁ ∪ G₂ ∪ G₃

/-- The set `𝔓₁`, defined in (5.1.30). -/
def 𝔓₁ : Set (𝔓 X) := ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3), ℭ₅ k n j

variable {k n j l : ℕ} {p p' : 𝔓 X} {x : X}

/-! ## Section 5.2 and Lemma 5.1.1 -/

/-- Lemma 5.2.1 -/
lemma first_exception : volume (G₁ : Set X) ≤ 2 ^ (- 4 : ℤ) * volume G := by
  sorry

/-- Lemma 5.2.2 -/
lemma dense_cover (k : ℕ) :
    2 ^ (k + 1) * volume G ≤ volume (⋃ p ∈ 𝓒 (X := X) k, (p : Set X)) := by
  sorry

/-- Lemma 5.2.3 -/
lemma pairwiseDisjoint_E1 : (𝔐 (X := X) k n).PairwiseDisjoint E₁ := fun p mp p' mp' h ↦ by
  change Disjoint _ _
  contrapose! h
  have h𝓘 := (Disjoint.mono (E₁_subset p) (E₁_subset p')).mt h
  wlog hs : s (𝓘 p') ≤ s (𝓘 p) generalizing p p'
  · rw [disjoint_comm] at h h𝓘; rw [not_le] at hs; rw [this p' mp' p mp h h𝓘 hs.le]
  obtain ⟨x, ⟨-, mxp⟩, ⟨-, mxp'⟩⟩ := not_disjoint_iff.mp h
  rw [mem_preimage] at mxp mxp'
  have l𝓘 := Grid.le_def.mpr ⟨(fundamental_dyadic hs).resolve_right (disjoint_comm.not.mpr h𝓘), hs⟩
  have sΩ := (relative_fundamental_dyadic l𝓘).resolve_left <| not_disjoint_iff.mpr ⟨_, mxp', mxp⟩
  exact (eq_of_mem_maximals mp' (mem_of_mem_of_subset mp (maximals_subset ..)) ⟨l𝓘, sΩ⟩).symm

/-- Lemma 5.2.4 -/
lemma dyadic_union (hx : x ∈ setA l k n) : ∃ i : Grid X, x ∈ i ∧ (i : Set X) ⊆ setA l k n := by
  let M : Finset (𝔓 X) := Finset.univ.filter (fun p ↦ p ∈ 𝔐 k n ∧ x ∈ 𝓘 p)
  simp_rw [setA, mem_setOf, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
    Finset.filter_filter] at hx ⊢
  obtain ⟨b, memb, minb⟩ := M.exists_min_image 𝔰 (Finset.card_pos.mp (zero_le'.trans_lt hx))
  simp_rw [M, Finset.mem_filter, Finset.mem_univ, true_and] at memb minb
  use 𝓘 b, memb.2; intro c mc; rw [mem_setOf]
  refine hx.trans_le (Finset.card_le_card fun y hy ↦ ?_)
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  have : (𝓘 b : Set X) ⊆ 𝓘 y := (fundamental_dyadic (minb y hy)).resolve_right
    (disjoint_comm.not.mpr (not_disjoint_iff.mpr ⟨x, hy.2, memb.2⟩))
  exact ⟨hy.1, mem_of_mem_of_subset mc this⟩

/-- Lemma 5.2.5 -/
lemma john_nirenberg : volume (setA (X := X) l k n) ≤ 2 ^ (k + 1 - l : ℤ) * volume G := by
  sorry

/-- Lemma 5.2.6 -/
lemma second_exception : volume (G₂ (X := X)) ≤ 2 ^ (- 4 : ℤ) * volume G := by
  sorry

/-- Lemma 5.2.7 -/
lemma top_tiles : ∑ m ∈ Finset.univ.filter (· ∈ 𝔐 (X := X) k n), volume (𝓘 m : Set X) ≤
    2 ^ (n + k + 3) * volume G := by
  sorry

/-- Lemma 5.2.8 -/
lemma tree_count : ∑ u ∈ Finset.univ.filter (· ∈ 𝔘₁ (X := X) k n j), (𝓘 u : Set X).indicator 1 x ≤
    2 ^ (9 * a - j) * ∑ m ∈ Finset.univ.filter (· ∈ 𝔐 (X := X) k n), (𝓘 m : Set X).indicator 1 x
    := by
  sorry

variable (X) in
/-- The constant in Lemma 5.2.9, with value `D ^ (1 - κ * Z * (n + 1))` -/
def C5_2_9 [ProofData a q K σ₁ σ₂ F G] (n : ℕ) : ℝ≥0 := D ^ (1 - κ * Z * (n + 1))

/-- Lemma 5.2.9 -/
lemma boundary_exception {u : 𝔓 X} (hu : u ∈ 𝔘₁ k n l) :
  volume (⋃ i ∈ 𝓛 (X := X) n u, (i : Set X)) ≤ C5_2_9 X n * volume (𝓘 u : Set X) := by
  sorry

/-- Lemma 5.2.10 -/
lemma third_exception : volume (G₃ (X := X)) ≤ 2 ^ (- 4 : ℤ) * volume G := by
  sorry

/-- Lemma 5.1.1 -/
lemma exceptional_set : volume (G' : Set X) ≤ 2 ^ (- 2 : ℤ) * volume G := by
  sorry

/-! ## Section 5.3 -/

/-! Note: the lemmas 5.3.1-5.3.3 are in `TileStructure`. -/

/-- Lemma 5.3.4 -/
lemma ordConnected_tilesAt : OrdConnected (TilesAt k : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.5 -/
lemma ordConnected_C : OrdConnected (ℭ k n : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.6 -/
lemma ordConnected_C1 : OrdConnected (ℭ₁ k n j : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.7 -/
lemma ordConnected_C2 : OrdConnected (ℭ₂ k n j : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.8 -/
lemma ordConnected_C3 : OrdConnected (ℭ₃ k n j : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.9 -/
lemma ordConnected_C4 : OrdConnected (ℭ₄ k n j : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.10 -/
lemma ordConnected_C5 : OrdConnected (ℭ₅ k n j : Set (𝔓 X)) := by
  sorry

/-- Lemma 5.3.11 -/
lemma dens1_le_dens' {P : Set (𝔓 X)} (hP : P ⊆ TilesAt k) :
    dens₁ P ≤ dens' k P := by
  sorry

/-- Lemma 5.3.12 -/
lemma dens1_le {A : Set (𝔓 X)} (hA : A ⊆ ℭ k n) : dens₁ A ≤ 2 ^ (4 * a - n + 1) := by
  sorry

/-! ## Section 5.4 and Lemma 5.1.2 -/

/-- The constant used in Lemma 5.1.2, with value `2 ^ (235 * a ^ 3) / (q - 1) ^ 4` -/
def C5_1_2 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (235 * a ^ 3) / (q - 1) ^ 4

lemma C5_1_2_pos : C5_1_2 a nnq > 0 := sorry

lemma forest_union {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
  ∫⁻ x in G \ G', ‖∑ p ∈ Finset.univ.filter (· ∈ 𝔓₁), T p f x‖₊ ≤
    C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹  := by
  sorry


/-- The constant used in Lemma 5.1.3, with value `2 ^ (210 * a ^ 3) / (q - 1) ^ 5` -/
def C5_1_3 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (210 * a ^ 3) / (q - 1) ^ 5

lemma C5_1_3_pos : C5_1_3 a nnq > 0 := sorry

lemma forest_complement {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
  ∫⁻ x in G \ G', ‖∑ p ∈ Finset.univ.filter (· ∉ 𝔓₁), T p f x‖₊ ≤
    C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹  := by
  sorry


/-! We might want to develop some API about partitioning a set.
But maybe `Set.PairwiseDisjoint` and `Set.Union` are enough.
Related, but not quite useful: `Setoid.IsPartition`. -/

-- /-- `u` is partitioned into subsets in `C`. -/
-- class Set.IsPartition {α ι : Type*} (u : Set α) (s : Set ι) (C : ι → Set α) : Prop :=
--   pairwiseDisjoint : s.PairwiseDisjoint C
--   iUnion_eq : ⋃ (i ∈ s), C i = u


/-- The constant used in Proposition 2.0.2,
which has value `2 ^ (440 * a ^ 3) / (q - 1) ^ 5` in the blueprint. -/
def C2_0_2 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := C5_1_2 a q + C5_1_2 a q

lemma C2_0_2_pos : C2_0_2 a nnq > 0 := sorry

theorem discrete_carleson :
    ∃ G', Measurable G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖∑ p, T p f x‖₊ ≤
    C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by sorry
