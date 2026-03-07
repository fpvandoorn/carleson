module

public import Carleson.TileStructure
public import Carleson.ToMathlib.MinLayer

@[expose] public section

open MeasureTheory Measure NNReal Metric Set
open scoped ENNReal
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

def aux𝓒 (k : ℕ) : Set (Grid X) :=
  {i : Grid X | ∃ j : Grid X, i ≤ j ∧ 2 ^ (-k : ℤ) * volume (j : Set X) < volume (G ∩ j) }

/-- The partition `𝓒(G, k)` of `Grid X` by volume, given in (5.1.1) and (5.1.2).
Note: the `G` is fixed with properties in `ProofData`. -/
def 𝓒 (k : ℕ) : Set (Grid X) :=
  aux𝓒 (k + 1) \ aux𝓒 k

/-- The definition `𝔓(k)` given in (5.1.3). -/
def TilesAt (k : ℕ) : Set (𝔓 X) := 𝓘 ⁻¹' 𝓒 k

lemma disjoint_TilesAt_of_ne {m n : ℕ} (h : m ≠ n) : Disjoint (TilesAt (X := X) m) (TilesAt n) := by
  wlog hl : m < n generalizing m n; · exact (this h.symm (by lia)).symm
  by_contra! h; rw [not_disjoint_iff] at h; obtain ⟨p, mp₁, mp₂⟩ := h
  simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at mp₁ mp₂
  apply absurd _ mp₂.2; obtain ⟨j, lj, vj⟩ := mp₁.1; use j, lj; apply lt_of_le_of_lt _ vj
  exact mul_le_mul_left (ENNReal.zpow_le_of_le one_le_two (by lia)) _

lemma pairwiseDisjoint_TilesAt : univ.PairwiseDisjoint (TilesAt (X := X)) := fun _ _ _ _ ↦
  disjoint_TilesAt_of_ne

def aux𝔐 (k n : ℕ) : Set (𝔓 X) :=
  {p ∈ TilesAt k | 2 ^ (-n : ℤ) * volume (𝓘 p : Set X) < volume (E₁ p) }

/-- The definition `𝔐(k, n)` given in (5.1.4) and (5.1.5). -/
def 𝔐 (k n : ℕ) : Set (𝔓 X) := {m | Maximal (· ∈ aux𝔐 k n) m}

/-- The definition `dens'_k(𝔓')` given in (5.1.6). -/
def dens' (k : ℕ) (P' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ p' ∈ P', ⨆ (l : ℝ≥0), ⨆ (_hl : 2 ≤ l),
  ⨆ (p : 𝔓 X) (_h1p : p ∈ TilesAt k) (_h2p : smul l p' ≤ smul l p),
  l ^ (-a : ℤ) * volume (E₂ l p) / volume (𝓘 p : Set X)

lemma dens'_iSup {k : ℕ} {P : Set (𝔓 X)} : dens' k P = ⨆ p ∈ P, dens' k {p} := by
  simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left]

def auxℭ (k n : ℕ) : Set (𝔓 X) :=
  { p ∈ TilesAt k | 2 ^ (4 * a - n) < dens' k {p} }

/-- The partition `ℭ(k, n)` of `𝔓(k)` by density, given in (5.1.7). -/
def ℭ (k n : ℕ) : Set (𝔓 X) :=
  { p ∈ TilesAt k | dens' k {p} ∈ Ioc (2 ^ (4 * a - n : ℤ)) (2 ^ (4 * a - n + 1 : ℤ)) }

lemma ℭ_subset_TilesAt {k n : ℕ} : ℭ k n ⊆ TilesAt (X := X) k := fun t mt ↦ by
  rw [ℭ, mem_setOf] at mt; exact mt.1

lemma disjoint_ℭ_of_ne {k m n : ℕ} (h : m ≠ n) : Disjoint (ℭ (X := X) k m) (ℭ k n) := by
  wlog hl : m < n generalizing m n; · exact (this h.symm (by lia)).symm
  by_contra! h; rw [not_disjoint_iff] at h; obtain ⟨p, mp₁, mp₂⟩ := h
  apply absurd _ (not_disjoint_iff.mpr ⟨_, mp₁.2, mp₂.2⟩)
  rw [Ioc_disjoint_Ioc, le_max_iff]; left; rw [min_le_iff]; right
  exact ENNReal.zpow_le_of_le one_le_two (by lia)

lemma pairwiseDisjoint_ℭ :
    (univ : Set (ℕ × ℕ)).PairwiseDisjoint (fun kn ↦ ℭ (X := X) kn.1 kn.2) :=
  fun ⟨k₁, n₁⟩ _ ⟨k₂, n₂⟩ _ hn ↦ by
    change Disjoint (ℭ k₁ n₁) (ℭ k₂ n₂)
    by_cases hk : k₁ = k₂
    · rw [ne_eq, Prod.mk.injEq, not_and] at hn; exact hk ▸ disjoint_ℭ_of_ne (hn hk)
    · exact disjoint_of_subset ℭ_subset_TilesAt ℭ_subset_TilesAt (disjoint_TilesAt_of_ne hk)

lemma exists_bound_ℭ : ∃ (n : ℕ × ℕ),
    ∀ x ∈ {kn : ℕ × ℕ | (ℭ (X := X) kn.1 kn.2).Nonempty}, Prod.snd x ≤ Prod.snd n := by
  apply exists_upper_bound_image
  have : Set.Finite (⋃ kn : ℕ × ℕ, ℭ (X := X) kn.1 kn.2) := toFinite _
  exact ((Set.finite_iUnion_iff (fun i j hij ↦ pairwiseDisjoint_ℭ (mem_univ i) (mem_univ j) hij)).1
    this).2

variable (X) in
def maxℭ : ℕ := (exists_bound_ℭ (X := X)).choose.2

lemma le_maxℭ_of_nonempty {k n : ℕ} (h : (ℭ (X := X) k n).Nonempty) : n ≤ maxℭ X :=
  (exists_bound_ℭ (X := X)).choose_spec (k, n) h

lemma eq_empty_of_maxℭ_lt {k n : ℕ} (hn : maxℭ X < n) : ℭ (X := X) k n = ∅ := by
  contrapose! hn
  exact (exists_bound_ℭ (X := X)).choose_spec (k, n) hn

/-- Lemma 5.3.11 -/
lemma dens1_le_dens' {k : ℕ} {P : Set (𝔓 X)} (hP : P ⊆ TilesAt k) : dens₁ P ≤ dens' k P := by
  rw [dens₁, dens']; gcongr with p' mp' l hl
  simp_rw [ENNReal.mul_iSup, iSup_le_iff, mul_div_assoc]; intro p mp sl
  suffices p ∈ TilesAt k by
    exact le_iSup_of_le p (le_iSup₂_of_le this sl (mul_le_mul' (by norm_cast) le_rfl))
  simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf]
  constructor
  · rw [mem_lowerCubes] at mp; obtain ⟨p'', mp'', lp''⟩ := mp
    have hp'' := mem_of_mem_of_subset mp'' hP
    simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at hp''
    obtain ⟨J, lJ, vJ⟩ := hp''.1; use J, lp''.trans lJ
  · by_contra h; obtain ⟨J, lJ, vJ⟩ := h
    have hp' := mem_of_mem_of_subset mp' hP
    simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at hp'
    apply absurd _ hp'.2; use J, sl.1.trans lJ

/-- Lemma 5.3.12 -/
lemma dens1_le {k n : ℕ} {A : Set (𝔓 X)} (hA : A ⊆ ℭ k n) : dens₁ A ≤ 2 ^ (4 * (a : ℝ) - n + 1) :=
  calc
    _ ≤ dens' k A := dens1_le_dens' (hA.trans ℭ_subset_TilesAt)
    _ ≤ dens' k (ℭ (X := X) k n) := iSup_le_iSup_of_subset hA
    _ ≤ _ := by
      rw [dens'_iSup, iSup₂_le_iff]; intro p mp
      rw [ℭ, mem_setOf] at mp; exact_mod_cast mp.2.2

/-- The subset `𝔅(p)` of `𝔐(k, n)`, given in (5.1.8). -/
def 𝔅 (k n : ℕ) (p : 𝔓 X) : Set (𝔓 X) :=
  { m ∈ 𝔐 k n | smul 100 p ≤ smul 1 m }

open scoped Classical in
def preℭ₁ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ k n | 2 ^ j ≤ Finset.card { q | q ∈ 𝔅 k n p } }

/-- The subset `ℭ₁(k, n, j)` of `ℭ(k, n)`, given in (5.1.9).
Together with `𝔏₀(k, n)` this forms a partition. -/
def ℭ₁ (k n j : ℕ) : Set (𝔓 X) :=
  preℭ₁ k n j \ preℭ₁ k n (j + 1)

lemma ℭ₁_subset_ℭ {k n j : ℕ} : ℭ₁ k n j ⊆ ℭ (X := X) k n := fun t mt ↦ by
  rw [ℭ₁, preℭ₁, mem_diff, mem_setOf] at mt; exact mt.1.1

lemma disjoint_ℭ₁_of_ne {k n j l : ℕ} (h : j ≠ l) : Disjoint (ℭ₁ (X := X) k n j) (ℭ₁ k n l) := by
  wlog hl : j < l generalizing j l; · exact (this h.symm (by lia)).symm
  by_contra! h; rw [not_disjoint_iff] at h; obtain ⟨p, mp₁, mp₂⟩ := h
  simp_rw [ℭ₁, mem_diff, preℭ₁, mem_setOf, mp₁.1.1, true_and, not_le] at mp₁ mp₂
  have := mp₂.1.trans_lt mp₁.2
  rw [pow_lt_pow_iff_right₀ one_lt_two] at this; lia

lemma pairwiseDisjoint_ℭ₁ {k n : ℕ} : univ.PairwiseDisjoint (ℭ₁ (X := X) k n) := fun _ _ _ _ ↦
  disjoint_ℭ₁_of_ne

lemma pairwiseDisjoint_ℭ₁' :
    (univ : Set (ℕ × ℕ × ℕ)).PairwiseDisjoint (fun knj ↦ ℭ₁ (X := X) knj.1 knj.2.1 knj.2.2) := by
  rintro ⟨k, n, j⟩ - ⟨k', n', j'⟩ - h
  rcases ne_or_eq k k' with hkk' | rfl
  · have := pairwiseDisjoint_ℭ (X := X) (mem_univ (k, n)) (mem_univ (k', n')) (by simp [hkk'])
    exact this.mono ℭ₁_subset_ℭ ℭ₁_subset_ℭ
  rcases ne_or_eq n n' with hnn' | rfl
  · have := pairwiseDisjoint_ℭ (X := X) (mem_univ (k, n)) (mem_univ (k, n')) (by simp [hnn'])
    exact this.mono ℭ₁_subset_ℭ ℭ₁_subset_ℭ
  exact disjoint_ℭ₁_of_ne (by simpa using h)

lemma card_𝔅_of_mem_ℭ₁ {k n j : ℕ} {p : 𝔓 X} (hp : p ∈ ℭ₁ k n j) [Fintype (𝔅 k n p)] :
    (𝔅 k n p).toFinset.card ∈ Ico (2 ^ j) (2 ^ (j + 1)) := by
  simp_rw [ℭ₁, mem_diff, preℭ₁, mem_setOf, hp.1.1, true_and, not_le] at hp
  constructor
  · convert hp.1; ext; simp
  · convert hp.2; ext; simp

/-- The subset `𝔏₀(k, n)` of `ℭ(k, n)`, given in (5.1.10).
Not to be confused with `𝔏₀(k, n, j)` which is called `𝔏₀'` in Lean. -/
def 𝔏₀ (k n : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ k n | 𝔅 k n p = ∅ }

/-- `𝔏₁(k, n, j, l)` consists of the minimal elements in `ℭ₁(k, n, j)` not in
  `𝔏₁(k, n, j, l')` for some `l' < l`. Defined near (5.1.11). -/
def 𝔏₁ (k n j l : ℕ) : Set (𝔓 X) :=
  (ℭ₁ k n j).minLayer l

/-- The subset `ℭ₂(k, n, j)` of `ℭ₁(k, n, j)`, given in (5.1.13). -/
def ℭ₂ (k n j : ℕ) : Set (𝔓 X) :=
  (ℭ₁ k n j).layersAbove (Z * (n + 1))

lemma ℭ₂_subset_ℭ₁ {k n j : ℕ} : ℭ₂ k n j ⊆ ℭ₁ (X := X) k n j := layersAbove_subset

/-- The subset `𝔘₁(k, n, j)` of `ℭ₁(k, n, j)`, given in (5.1.14). -/
def 𝔘₁ (k n j : ℕ) : Set (𝔓 X) :=
  { u ∈ ℭ₁ k n j | ∀ p ∈ ℭ₁ k n j, 𝓘 u < 𝓘 p → Disjoint (ball_(u) (𝒬 u) 100) (ball_(p) (𝒬 p) 100) }

lemma 𝔘₁_subset_ℭ₁ {k n j : ℕ} : 𝔘₁ k n j ⊆ ℭ₁ (X := X) k n j := fun _ mu ↦ mu.1

/-- The subset `𝔏₂(k, n, j)` of `ℭ₂(k, n, j)`, given in (5.1.15). -/
def 𝔏₂ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ₂ k n j | ¬ ∃ u ∈ 𝔘₁ k n j, 𝓘 p ≠ 𝓘 u ∧ smul 2 p ≤ smul 1 u }

lemma 𝔏₂_subset_ℭ₂ {k n j : ℕ} : 𝔏₂ k n j ⊆ ℭ₂ (X := X) k n j := fun _ mu ↦ mu.1

/-- The subset `ℭ₃(k, n, j)` of `ℭ₂(k, n, j)`, given in (5.1.16). -/
def ℭ₃ (k n j : ℕ) : Set (𝔓 X) :=
  ℭ₂ k n j \ 𝔏₂ k n j

lemma ℭ₃_def {k n j : ℕ} {p : 𝔓 X} :
    p ∈ ℭ₃ k n j ↔ p ∈ ℭ₂ k n j ∧ ∃ u ∈ 𝔘₁ k n j, 𝓘 p ≠ 𝓘 u ∧ smul 2 p ≤ smul 1 u := by
  rw [ℭ₃, mem_diff, 𝔏₂, mem_setOf, not_and, and_congr_right_iff]; intro h
  simp_rw [h, true_implies, not_not]

lemma ℭ₃_subset_ℭ₂ {k n j : ℕ} : ℭ₃ k n j ⊆ ℭ₂ (X := X) k n j := fun t mt ↦ by
  rw [ℭ₃, mem_diff] at mt; exact mt.1

/-- `𝔏₃(k, n, j, l)` consists of the maximal elements in `ℭ₃(k, n, j)` not in
  `𝔏₃(k, n, j, l')` for some `l' < l`. Defined near (5.1.17). -/
def 𝔏₃ (k n j l : ℕ) : Set (𝔓 X) :=
 (ℭ₃ k n j).maxLayer l

/-- The subset `ℭ₄(k, n, j)` of `ℭ₃(k, n, j)`, given in (5.1.19). -/
def ℭ₄ (k n j : ℕ) : Set (𝔓 X) :=
  (ℭ₃ k n j).layersBelow (Z * (n + 1))

lemma ℭ₄_subset_ℭ₃ {k n j : ℕ} : ℭ₄ k n j ⊆ ℭ₃ (X := X) k n j := layersBelow_subset

/-- The subset `𝓛(u)` of `Grid X`, given near (5.1.20).
Note: It seems to also depend on `n`. -/
def 𝓛 (n : ℕ) (u : 𝔓 X) : Set (Grid X) :=
  { i : Grid X | i ≤ 𝓘 u ∧ s i + (Z * (n + 1) : ℕ) + 1 = 𝔰 u ∧ ¬ ball (c i) (8 * D ^ s i) ⊆ 𝓘 u }

/-- The subset `𝔏₄(k, n, j)` of `ℭ₄(k, n, j)`, given near (5.1.22).
Todo: we may need to change the definition to say that `p`
is at most the least upper bound of `𝓛 n u` in `Grid X`. -/
def 𝔏₄ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ₄ k n j | ∃ u ∈ 𝔘₁ k n j, (𝓘 p : Set X) ⊆ ⋃ (i ∈ 𝓛 (X := X) n u), i }

lemma 𝔏₄_subset_ℭ₄ {k n j : ℕ} : 𝔏₄ k n j ⊆ ℭ₄ (X := X) k n j := fun _ mu ↦ mu.1

/-- The subset `ℭ₅(k, n, j)` of `ℭ₄(k, n, j)`, given in (5.1.23). -/
def ℭ₅ (k n j : ℕ) : Set (𝔓 X) :=
  ℭ₄ k n j \ 𝔏₄ k n j

lemma ℭ₅_def {k n j : ℕ} {p : 𝔓 X} :
    p ∈ ℭ₅ k n j ↔ p ∈ ℭ₄ k n j ∧ ∀ u ∈ 𝔘₁ k n j, ¬(𝓘 p : Set X) ⊆ ⋃ (i ∈ 𝓛 (X := X) n u), i := by
  rw [ℭ₅, mem_diff, 𝔏₄, mem_setOf, not_and, and_congr_right_iff]; intro h
  simp_rw [h, true_implies]; push_neg; rfl

lemma ℭ₅_subset_ℭ₄ {k n j : ℕ} : ℭ₅ k n j ⊆ ℭ₄ (X := X) k n j := fun t mt ↦ by
  rw [ℭ₅, mem_diff] at mt; exact mt.1

lemma ℭ₅_subset_ℭ₁ {k n j : ℕ} : ℭ₅ k n j ⊆ ℭ₁ (X := X) k n j :=
  ℭ₅_subset_ℭ₄.trans <| ℭ₄_subset_ℭ₃.trans <| ℭ₃_subset_ℭ₂.trans ℭ₂_subset_ℭ₁

lemma pairwiseDisjoint_ℭ₅ :
    (univ : Set (ℕ × ℕ × ℕ)).PairwiseDisjoint (fun knj ↦ ℭ₅ (X := X) knj.1 knj.2.1 knj.2.2) :=
  pairwiseDisjoint_ℭ₁'.mono (fun _ ↦ ℭ₅_subset_ℭ₁)

-- These inclusion and disjointness lemmas are only used in `antichain_decomposition`
section AntichainDecomp

variable {k n j l : ℕ}

lemma 𝔏₀_subset_ℭ : 𝔏₀ (X := X) k n ⊆ ℭ k n := fun _ mu ↦ mu.1
lemma 𝔏₀_disjoint_ℭ₁ : Disjoint (𝔏₀ (X := X) k n) (ℭ₁ k n j) := by
  by_contra h; rw [not_disjoint_iff] at h; obtain ⟨p, ⟨_, b0⟩, ⟨⟨_, bp⟩ , _⟩⟩ := h
  simp [b0] at bp

lemma 𝔏₁_subset_ℭ₁ : 𝔏₁ (X := X) k n j l ⊆ ℭ₁ k n j := minLayer_subset
lemma 𝔏₁_subset_ℭ : 𝔏₁ (X := X) k n j l ⊆ ℭ k n := minLayer_subset.trans ℭ₁_subset_ℭ

lemma 𝔏₂_subset_ℭ₁ : 𝔏₂ k n j ⊆ ℭ₁ (X := X) k n j := 𝔏₂_subset_ℭ₂.trans ℭ₂_subset_ℭ₁
lemma 𝔏₂_subset_ℭ : 𝔏₂ k n j ⊆ ℭ (X := X) k n := 𝔏₂_subset_ℭ₁.trans ℭ₁_subset_ℭ
lemma 𝔏₂_disjoint_ℭ₃ : Disjoint (𝔏₂ (X := X) k n j) (ℭ₃ k n j) := disjoint_sdiff_right

lemma 𝔏₃_subset_ℭ₁ : 𝔏₃ k n j l ⊆ ℭ₁ (X := X) k n j :=
  maxLayer_subset.trans ℭ₃_subset_ℭ₂ |>.trans ℭ₂_subset_ℭ₁
lemma 𝔏₃_subset_ℭ : 𝔏₃ k n j l ⊆ ℭ (X := X) k n := 𝔏₃_subset_ℭ₁.trans ℭ₁_subset_ℭ

lemma 𝔏₄_subset_ℭ₁ : 𝔏₄ k n j ⊆ ℭ₁ (X := X) k n j :=
  𝔏₄_subset_ℭ₄.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂ |>.trans ℭ₂_subset_ℭ₁
lemma 𝔏₄_subset_ℭ : 𝔏₄ k n j ⊆ ℭ (X := X) k n := 𝔏₄_subset_ℭ₁.trans ℭ₁_subset_ℭ

lemma ℭ₅_subset_ℭ : ℭ₅ k n j ⊆ ℭ (X := X) k n := ℭ₅_subset_ℭ₁.trans ℭ₁_subset_ℭ

end AntichainDecomp

/-- The set $\mathcal{P}_{F,G}$, defined in (5.1.24). -/
def highDensityTiles : Set (𝔓 X) :=
  { p : 𝔓 X | 2 ^ (2 * a + 5) * volume F / volume G < dens₂ {p} }

lemma highDensityTiles_empty (hF : volume F = 0) : highDensityTiles = (∅ : Set (𝔓 X)) := by
  suffices ∀ (p : 𝔓 X), dens₂ {p} = 0 by simp [highDensityTiles, this]
  simp_rw [dens₂, ENNReal.iSup_eq_zero, ENNReal.div_eq_zero_iff]
  exact fun _ _ _ r _ ↦ Or.inl <| measure_inter_null_of_null_left (ball (𝔠 _) r) hF

lemma highDensityTiles_empty' (hG : volume G = 0) :
    highDensityTiles = (∅ : Set (𝔓 X)) := by
  by_cases hF : volume F = 0
  · exact highDensityTiles_empty hF
  suffices 2 ^ (2 * a + 5) * volume F / volume G = ⊤ by simp [highDensityTiles, this]
  exact hG ▸ ENNReal.div_zero (mul_ne_zero (by simp) hF)

/-- The exceptional set `G₁`, defined in (5.1.25). -/
def G₁ : Set X := ⋃ (p : 𝔓 X) (_ : p ∈ highDensityTiles), 𝓘 p

lemma G₁_empty (hF : volume F = 0) : G₁ = (∅ : Set X) := by
  simp [G₁, highDensityTiles_empty hF]

lemma G₁_empty' (hG : volume G = 0) : G₁ = (∅ : Set X) := by
  simp [G₁, highDensityTiles_empty' hG]

lemma measurable_G₁ : MeasurableSet (G₁ (X := X)) :=
  Finite.measurableSet_biUnion highDensityTiles.toFinite fun _ _ ↦ coeGrid_measurable

/-- The set `A(λ, k, n)`, defined in (5.1.26). -/
def setA (l k n : ℕ) : Set X :=
  {x : X | l * 2 ^ (n + 1) < stackSize (𝔐 (X := X) k n) x }

lemma setA_subset_iUnion_𝓒 {l k n : ℕ} :
    setA (X := X) l k n ⊆ ⋃ i ∈ 𝓒 (X := X) k, i := by
  classical
  intro x mx
  simp_rw [setA, mem_setOf, stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
    Finset.filter_filter] at mx
  replace mx := (zero_le _).trans_lt mx
  rw [Finset.card_pos] at mx
  obtain ⟨p, hp⟩ := mx
  simp_rw [Finset.mem_filter_univ, 𝔐, mem_setOf, maximal_iff, aux𝔐, mem_setOf, TilesAt,
    mem_preimage] at hp
  rw [mem_iUnion₂]; use 𝓘 p, hp.1.1.1, hp.2

lemma setA_subset_setA {l k n : ℕ} : setA (X := X) (l + 1) k n ⊆ setA l k n := by
  refine setOf_subset_setOf.mpr fun x hx ↦ ?_
  calc
    _ ≤ _ := by gcongr; lia
    _ < _ := hx

lemma measurable_setA {l k n : ℕ} : MeasurableSet (setA (X := X) l k n) :=
  measurableSet_lt measurable_const (Finset.measurable_sum _ fun _ _ ↦ measurable_one.indicator coeGrid_measurable)

open scoped Classical in
/-- Finset of cubes in `setA`. Appears in the proof of Lemma 5.2.5. -/
def MsetA (l k n : ℕ) : Finset (Grid X) := { j | (j : Set X) ⊆ setA l k n }

/-- The set `G₂`, defined in (5.1.27). -/
def G₂ : Set X := ⋃ (n : ℕ) (k ≤ n), setA (2 * n + 6) k n

lemma measurable_G₂ : MeasurableSet (G₂ (X := X)) := by
  iterate 3 refine MeasurableSet.iUnion fun _ ↦ ?_
  exact measurable_setA

/-- The set `G₃`, defined in (5.1.28). -/
def G₃ : Set X := ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3) (p ∈ 𝔏₄ (X := X) k n j), 𝓘 p

lemma measurable_G₃ : MeasurableSet (G₃ (X := X)) := by
  iterate 7 refine MeasurableSet.iUnion fun _ ↦ ?_
  exact coeGrid_measurable

/-- The set `G'`, defined below (5.1.28). -/
def G' : Set X := G₁ ∪ G₂ ∪ G₃

lemma measurable_G' : MeasurableSet (G' (X := X)) :=
  (measurable_G₁.union measurable_G₂).union measurable_G₃

/-- The set `𝔓₁`, defined in (5.1.30). -/
def 𝔓₁ : Set (𝔓 X) := ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3), ℭ₅ k n j
