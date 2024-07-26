import Carleson.TileStructure

namespace Set

variable {α : Type*} [PartialOrder α]

/-- The `n`th minimal layer of `A`. -/
def minLayer (A : Set α) (n : ℕ) : Set α :=
  minimals (· ≤ ·) (A \ ⋃ (k < n), A.minLayer k)

/-- The `n`th maximal layer of `A`. -/
def maxLayer (A : Set α) (n : ℕ) : Set α :=
  A.minLayer (α := αᵒᵈ) n

/-- The elements above `A`'s `n` minimal layers. -/
def layersAbove (A : Set α) (n : ℕ) : Set α :=
  A \ ⋃ (k ≤ n), A.minLayer k

/-- The elements below `A`'s `n` maximal layers. -/
def layersBelow (A : Set α) (n : ℕ) : Set α :=
  A \ ⋃ (k ≤ n), A.maxLayer k

variable {A : Set α} {m n : ℕ} {a : α}

lemma maxLayer_def : A.maxLayer n = maximals (· ≤ ·) (A \ ⋃ (k < n), A.maxLayer k) := by
  rw [maxLayer, minLayer]; rfl

lemma minLayer_subset : A.minLayer n ⊆ A :=
  calc
    _ ⊆ A \ ⋃ (k < n), A.minLayer k := by rw [minLayer]; exact minimals_subset ..
    _ ⊆ A := diff_subset

lemma maxLayer_subset : A.maxLayer n ⊆ A := minLayer_subset

lemma layersAbove_subset : A.layersAbove n ⊆ A := diff_subset

lemma layersBelow_subset : A.layersBelow n ⊆ A := diff_subset

lemma minLayer_zero : A.minLayer 0 = minimals (· ≤ ·) A := by rw [minLayer]; simp

lemma maxLayer_zero : A.maxLayer 0 = maximals (· ≤ ·) A := by rw [maxLayer_def]; simp

lemma disjoint_minLayer_of_ne (h : m ≠ n) : Disjoint (A.minLayer m) (A.minLayer n) := by
  wlog hl : m < n generalizing m n; · exact (this h.symm (by omega)).symm
  rw [disjoint_right]; intro p hp
  rw [minLayer, mem_minimals_iff, mem_diff] at hp; replace hp := hp.1.2; contrapose! hp
  exact mem_iUnion₂_of_mem hl hp

lemma disjoint_maxLayer_of_ne (h : m ≠ n) : Disjoint (A.maxLayer m) (A.maxLayer n) :=
  disjoint_minLayer_of_ne h

lemma pairwiseDisjoint_minLayer : univ.PairwiseDisjoint A.minLayer := fun _ _ _ _ ↦
  disjoint_minLayer_of_ne

lemma pairwiseDisjoint_maxLayer : univ.PairwiseDisjoint A.maxLayer := fun _ _ _ _ ↦
  disjoint_minLayer_of_ne

lemma exists_le_in_minLayer_of_le (ha : a ∈ A.minLayer n) (hm : m ≤ n) :
    ∃ c ∈ A.minLayer m, c ≤ a := by
  induction n, hm using Nat.le_induction generalizing a with
  | base => use a
  | succ n _ ih =>
    have nma : a ∉ A.minLayer n :=
      disjoint_right.mp (disjoint_minLayer_of_ne (by omega)) ha
    rw [minLayer, mem_minimals_iff] at ha nma
    have al : a ∈ A \ ⋃ (l < n), A.minLayer l := by
      refine mem_of_mem_of_subset ha.1 (diff_subset_diff_right ?_)
      refine biUnion_subset_biUnion_left fun k hk ↦ ?_
      rw [mem_def, Nat.le_eq] at hk ⊢; omega
    simp_rw [al, true_and] at nma; push_neg at nma; obtain ⟨a', ha', la⟩ := nma
    have ma' : a' ∈ A.minLayer n := by
      by_contra h
      have a'l : a' ∈ A \ ⋃ (l < n + 1), A.minLayer l := by
        have : ∀ l, l < n + 1 ↔ l < n ∨ l = n := by omega
        simp_rw [this, iUnion_or, iUnion_union_distrib]
        simp only [iUnion_iUnion_eq_left, mem_diff, mem_union, mem_iUnion, exists_prop, not_or,
          not_exists, not_and] at ha' ⊢
        tauto
      exact absurd (ha.2 a'l la.1) (ne_eq _ _ ▸ la.2)
    obtain ⟨c, mc, lc⟩ := ih ma'; use c, mc, lc.trans la.1

lemma exists_le_in_maxLayer_of_le (ha : a ∈ A.maxLayer n) (hm : m ≤ n) :
    ∃ c ∈ A.maxLayer m, a ≤ c := exists_le_in_minLayer_of_le (α := αᵒᵈ) ha hm

open Classical

variable [Fintype α]

lemma exists_le_in_layersAbove_of_le (ha : a ∈ A.layersAbove n) (hm : m ≤ n) :
    ∃ c ∈ A.minLayer m, c ≤ a := by
  have ma : a ∈ A \ ⋃ (l' < n), A.minLayer l' := by
    refine mem_of_mem_of_subset ha (diff_subset_diff_right ?_)
    refine biUnion_subset_biUnion_left fun k hk ↦ ?_
    rw [mem_def, Nat.le_eq] at hk ⊢; omega
  let C : Finset α :=
    (A.toFinset \ (Finset.range n).biUnion fun l ↦ (A.minLayer l).toFinset).filter (· ≤ a)
  have Cn : C.Nonempty := by
    use a
    simp_rw [C, Finset.mem_filter, le_rfl, and_true, Finset.mem_sdiff,
      Finset.mem_biUnion, Finset.mem_range, not_exists, not_and, mem_toFinset]
    simp_rw [mem_diff, mem_iUnion, exists_prop, not_exists, not_and] at ma
    exact ma
  obtain ⟨a', ma', mina'⟩ := C.exists_minimal Cn
  simp_rw [C, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, not_exists,
    not_and, mem_toFinset] at ma' mina'
  conv at mina' => enter [x]; rw [and_imp]
  have ma'₁ : a' ∈ A.minLayer n := by
    rw [minLayer, mem_minimals_iff]
    simp_rw [mem_diff, mem_iUnion, exists_prop, not_exists, not_and]
    exact ⟨ma'.1, fun y hy ly ↦ (eq_of_le_of_not_lt ly (mina' y hy (ly.trans ma'.2))).symm⟩
  obtain ⟨c, mc, lc⟩ := exists_le_in_minLayer_of_le ma'₁ hm
  use c, mc, lc.trans ma'.2

lemma exists_le_in_layersBelow_of_le (ha : a ∈ A.layersBelow n) (hm : m ≤ n) :
    ∃ c ∈ A.maxLayer m, a ≤ c := exists_le_in_layersAbove_of_le (α := αᵒᵈ) ha hm

end Set

noncomputable section

open Set
open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
variable {A : Set (𝔓 X)} {p : 𝔓 X} {n : ℕ}

lemma exists_scale_add_le_of_mem_minLayer (hp : p ∈ A.minLayer n) :
    ∃ p' ∈ A.minLayer 0, p' ≤ p ∧ 𝔰 p' + n ≤ 𝔰 p := by
  induction n generalizing p with
  | zero => use p, hp, le_rfl, by omega
  | succ n ih =>
    obtain ⟨p', mp', lp'⟩ := exists_le_in_minLayer_of_le hp (show n ≤ n + 1 by omega)
    obtain ⟨q, mq, lq, _⟩ := ih mp'; use q, mq, lq.trans lp'; suffices 𝔰 p' < 𝔰 p by omega
    have l : 𝓘 p' < 𝓘 p := by
      refine lt_of_le_of_ne lp'.1 (not_lt_of_𝓘_eq_𝓘.mt ?_); rw [not_not]
      exact lt_of_le_of_ne lp' <| (disjoint_minLayer_of_ne (by omega)).ne_of_mem mp' hp
    rw [Grid.lt_def] at l; exact l.2

lemma exists_le_add_scale_of_mem_maxLayer (hp : p ∈ A.maxLayer n) :
    ∃ p' ∈ A.maxLayer 0, p ≤ p' ∧ 𝔰 p + n ≤ 𝔰 p' := by
  induction n generalizing p with
  | zero => use p, hp, le_rfl, by omega
  | succ n ih =>
    obtain ⟨p', mp', lp'⟩ := exists_le_in_maxLayer_of_le hp (show n ≤ n + 1 by omega)
    obtain ⟨q, mq, lq, _⟩ := ih mp'; use q, mq, lp'.trans lq; suffices 𝔰 p < 𝔰 p' by omega
    have l : 𝓘 p < 𝓘 p' := by
      refine lt_of_le_of_ne lp'.1 (not_lt_of_𝓘_eq_𝓘.mt ?_); rw [not_not]
      exact lt_of_le_of_ne lp' <| (disjoint_maxLayer_of_ne (by omega)).ne_of_mem hp mp'
    rw [Grid.lt_def] at l; exact l.2

lemma exists_scale_add_le_of_mem_layersAbove (hp : p ∈ A.layersAbove n) :
    ∃ p' ∈ A.minLayer 0, p' ≤ p ∧ 𝔰 p' + n ≤ 𝔰 p := by
  obtain ⟨p', mp', lp'⟩ := exists_le_in_layersAbove_of_le hp le_rfl
  obtain ⟨q, mq, lq, sq⟩ := exists_scale_add_le_of_mem_minLayer mp'
  use q, mq, lq.trans lp', sq.trans lp'.1.2

lemma exists_le_add_scale_of_mem_layersBelow (hp : p ∈ A.layersBelow n) :
    ∃ p' ∈ A.maxLayer 0, p ≤ p' ∧ 𝔰 p + n ≤ 𝔰 p' := by
  obtain ⟨p', mp', lp'⟩ := exists_le_in_layersBelow_of_le hp le_rfl
  obtain ⟨q, mq, lq, sq⟩ := exists_le_add_scale_of_mem_maxLayer mp'
  use q, mq, lp'.trans lq, (add_le_add_right lp'.1.2 _).trans sq

end
