import Carleson.Discrete.ExceptionalSet

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
open Classical -- We use quite some `Finset.filter`
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

variable {k n j l : ℕ} {p p' u u' : 𝔓 X} {x : X}

/-! ## Section 5.3 -/

/-! Note: the lemmas 5.3.1-5.3.3 are in `TileStructure`. -/

/-- Lemma 5.3.4 -/
lemma ordConnected_tilesAt : OrdConnected (TilesAt k : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at mp mp'' ⊢
  constructor
  · obtain ⟨J, hJ, _⟩ := mp''.1
    use J, mp'.2.1.trans hJ
  · push_neg at mp ⊢
    exact fun J hJ ↦ mp.2 J (mp'.1.1.trans hJ)

/-- Lemma 5.3.5 -/
lemma ordConnected_C : OrdConnected (ℭ k n : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  rw [ℭ, mem_setOf] at mp mp'' ⊢
  have z := mem_of_mem_of_subset mp' (ordConnected_tilesAt.out mp.1 mp''.1)
  refine ⟨z, ?_⟩
  have : ∀ q' ∈ TilesAt (X := X) k, ∀ q ≤ q', dens' k {q'} ≤ dens' k {q} := fun q' _ q hq ↦ by
    simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left]; gcongr with l hl a _
    exact iSup_const_mono fun h ↦
      wiggle_order_11_10 hq (C5_3_3_le (X := X).trans (by norm_num) |>.trans hl) |>.trans h
  exact ⟨mp''.2.1.trans_le (this _ mp''.1 _ mp'.2), (this _ z _ mp'.1).trans mp.2.2⟩

/-- Lemma 5.3.6 -/
lemma ordConnected_C1 : OrdConnected (ℭ₁ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp'₁ : p' ∈ ℭ (X := X) k n := mem_of_mem_of_subset mp'
    (ordConnected_C.out (mem_of_mem_of_subset mp ℭ₁_subset_ℭ)
      (mem_of_mem_of_subset mp'' ℭ₁_subset_ℭ))
  simp_rw [ℭ₁, mem_diff, preℭ₁, mem_setOf, not_and, not_le] at mp mp'' ⊢
  simp_rw [mp.1.1, true_and, true_implies] at mp
  simp_rw [mp'₁, true_and, true_implies]
  simp_rw [mp''.1.1, true_and, true_implies] at mp''
  constructor
  · refine mp''.1.trans (Finset.card_le_card fun b mb ↦ ?_)
    simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, 𝔅, mem_setOf] at mb ⊢
    have := wiggle_order_11_10 (n := 100) mp'.2 (C5_3_3_le (X := X).trans (by norm_num))
    exact ⟨mb.1, this.trans mb.2⟩
  · refine (Finset.card_le_card fun b mb ↦ ?_).trans_lt mp.2
    simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, 𝔅, mem_setOf] at mb ⊢
    have := wiggle_order_11_10 (n := 100) mp'.1 (C5_3_3_le (X := X).trans (by norm_num))
    exact ⟨mb.1, this.trans mb.2⟩

/-- Lemma 5.3.7 -/
lemma ordConnected_C2 : OrdConnected (ℭ₂ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp₁ := mem_of_mem_of_subset mp ℭ₂_subset_ℭ₁
  have mp'₁ : p' ∈ ℭ₁ (X := X) k n j := mem_of_mem_of_subset mp'
    (ordConnected_C1.out mp₁ (mem_of_mem_of_subset mp'' ℭ₂_subset_ℭ₁))
  by_cases e : p = p'; · rwa [e] at mp
  simp_rw [ℭ₂, layersAbove, mem_diff, mp'₁, true_and]
  by_contra h; rw [mem_iUnion₂] at h; obtain ⟨l', bl', p'm⟩ := h
  rw [minLayer, mem_setOf, minimal_iff] at p'm
  have pnm : p ∉ ⋃ l'', ⋃ (_ : l'' < l'), 𝔏₁ k n j l'' := by
    replace mp := mp.2; contrapose! mp
    exact mem_of_mem_of_subset mp
      (iUnion_mono'' fun i ↦ iUnion_subset_iUnion_const fun hi ↦ (hi.trans_le bl').le)
  exact absurd (p'm.2 ⟨mp.1, pnm⟩ mp'.1).symm e

/-- Lemma 5.3.8 -/
lemma ordConnected_C3 : OrdConnected (ℭ₃ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp₁ := mem_of_mem_of_subset mp ℭ₃_subset_ℭ₂
  have mp''₁ := mem_of_mem_of_subset mp'' ℭ₃_subset_ℭ₂
  have mp'₁ : p' ∈ ℭ₂ (X := X) k n j := mem_of_mem_of_subset mp' (ordConnected_C2.out mp₁ mp''₁)
  rw [ℭ₃_def] at mp'' ⊢
  obtain ⟨-, u, mu, 𝓘nu, su⟩ := mp''; refine ⟨mp'₁, ⟨u, mu, ?_⟩⟩
  exact ⟨(mp'.2.1.trans_lt (lt_of_le_of_ne su.1 𝓘nu)).ne,
    (wiggle_order_11_10 mp'.2 (C5_3_3_le (X := X).trans (by norm_num))).trans su⟩

/-- Lemma 5.3.9 -/
lemma ordConnected_C4 : OrdConnected (ℭ₄ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp''₁ := mem_of_mem_of_subset mp'' ℭ₄_subset_ℭ₃
  have mp'₁ : p' ∈ ℭ₃ (X := X) k n j := mem_of_mem_of_subset mp'
    (ordConnected_C3.out (mem_of_mem_of_subset mp ℭ₄_subset_ℭ₃) mp''₁)
  by_cases e : p' = p''; · rwa [← e] at mp''
  simp_rw [ℭ₄, layersBelow, mem_diff, mp'₁, true_and]
  by_contra h; simp_rw [mem_iUnion] at h; obtain ⟨l', hl', p'm⟩ := h
  rw [maxLayer_def, mem_setOf, maximal_iff] at p'm
  simp_rw [mem_diff] at p'm
  have p''nm : p'' ∉ ⋃ l'', ⋃ (_ : l'' < l'), 𝔏₃ k n j l'' := by
    replace mp'' := mp''.2; contrapose! mp''
    refine mem_of_mem_of_subset mp'' <| iUnion₂_mono' fun i hi ↦ ⟨i, hi.le.trans hl', subset_rfl⟩
  exact absurd (p'm.2 ⟨mp''₁, p''nm⟩ mp'.2) e

/-- Lemma 5.3.10 -/
lemma ordConnected_C5 : OrdConnected (ℭ₅ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp₁ := mem_of_mem_of_subset mp ℭ₅_subset_ℭ₄
  have mp'₁ : p' ∈ ℭ₄ (X := X) k n j := mem_of_mem_of_subset mp'
    (ordConnected_C4.out mp₁ (mem_of_mem_of_subset mp'' ℭ₅_subset_ℭ₄))
  simp_rw [ℭ₅, mem_diff, mp₁, mp'₁, true_and, 𝔏₄, mem_setOf,
    mp₁, mp'₁, true_and] at mp ⊢
  contrapose! mp; obtain ⟨u, mu, s𝓘u⟩ := mp; use u, mu, mp'.1.1.1.trans s𝓘u

/-- Lemma 5.3.11 -/
lemma dens1_le_dens' {P : Set (𝔓 X)} (hP : P ⊆ TilesAt k) : dens₁ P ≤ dens' k P := by
  rw [dens₁, dens']; gcongr with p' mp' l hl
  simp_rw [ENNReal.mul_iSup, iSup_le_iff, mul_div_assoc]; intro p mp sl
  suffices p ∈ TilesAt k by
    exact le_iSup_of_le p (le_iSup₂_of_le this sl (mul_le_mul' (by norm_cast) le_rfl))
  simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf]
  constructor
  · rw [mem_lowerClosure] at mp; obtain ⟨p'', mp'', lp''⟩ := mp
    have := mem_of_mem_of_subset mp'' hP
    simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at this
    obtain ⟨J, lJ, vJ⟩ := this.1; use J, lp''.1.trans lJ
  · by_contra h; obtain ⟨J, lJ, vJ⟩ := h
    have := mem_of_mem_of_subset mp' hP
    simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at this
    apply absurd _ this.2; use J, sl.1.trans lJ

/-- Lemma 5.3.12 -/
lemma dens1_le {A : Set (𝔓 X)} (hA : A ⊆ ℭ k n) : dens₁ A ≤ 2 ^ (4 * a - n + 1 : ℤ) :=
  calc
    _ ≤ dens' k A := dens1_le_dens' (hA.trans ℭ_subset_TilesAt)
    _ ≤ dens' k (ℭ (X := X) k n) := iSup_le_iSup_of_subset hA
    _ ≤ _ := by
      rw [dens'_iSup, iSup₂_le_iff]; intro p mp
      rw [ℭ, mem_setOf] at mp; exact mp.2.2

/-! ## Section 5.4 and Lemma 5.1.2 -/

/-- The subset `ℭ₆(k, n, j)` of `ℭ₅(k, n, j)`, given above (5.4.1). -/
def ℭ₆ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ₅ k n j | ¬ (𝓘 p : Set X) ⊆ G' }

lemma ℭ₆_subset_ℭ₅ : ℭ₆ (X := X) k n j ⊆ ℭ₅ k n j := sep_subset ..
lemma ℭ₆_subset_ℭ : ℭ₆ (X := X) k n j ⊆ ℭ k n :=
  ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂ |>.trans
    ℭ₂_subset_ℭ₁ |>.trans ℭ₁_subset_ℭ

/-- The subset `𝔗₁(u)` of `ℭ₁(k, n, j)`, given in (5.4.1).
In lemmas, we will assume `u ∈ 𝔘₁ k n l` -/
def 𝔗₁ (k n j : ℕ) (u : 𝔓 X) : Set (𝔓 X) :=
  { p ∈ ℭ₁ k n j | 𝓘 p ≠ 𝓘 u ∧ smul 2 p ≤ smul 1 u }

lemma 𝓘_lt_of_mem_𝔗₁ (h : p ∈ 𝔗₁ k n j p') : 𝓘 p < 𝓘 p' := by
  rw [𝔗₁, mem_setOf] at h; exact lt_of_le_of_ne h.2.2.1 h.2.1

/-- The subset `𝔘₂(k, n, j)` of `𝔘₁(k, n, j)`, given in (5.4.2). -/
def 𝔘₂ (k n j : ℕ) : Set (𝔓 X) :=
  { u ∈ 𝔘₁ k n j | ¬ Disjoint (𝔗₁ k n j u) (ℭ₆ k n j) }

lemma 𝔘₂_subset_𝔘₁ : 𝔘₂ k n j ⊆ 𝔘₁ (X := X) k n j := fun _ mu ↦ mu.1

/-- The relation `∼` defined below (5.4.2). It is an equivalence relation on `𝔘₂ k n j`. -/
def URel (k n j : ℕ) (u u' : 𝔓 X) : Prop :=
  u = u' ∨ ∃ p ∈ 𝔗₁ k n j u, smul 10 p ≤ smul 1 u'

nonrec lemma URel.rfl : URel k n j u u := Or.inl rfl

/-- Lemma 5.4.1, part 2. -/
lemma URel.not_disjoint (hu : u ∈ 𝔘₂ k n j) (hu' : u' ∈ 𝔘₂ k n j) (huu' : URel k n j u u') :
    ¬Disjoint (ball_(u) (𝒬 u) 100) (ball_(u') (𝒬 u') 100) := by
  by_cases e : u = u'; · rw [e]; simp
  simp_rw [URel, e, false_or, 𝔗₁, mem_setOf] at huu'; obtain ⟨p, ⟨mp, np, sl₁⟩, sl₂⟩ := huu'
  by_cases e' : 𝓘 p = 𝓘 u'
  · refine not_disjoint_iff.mpr ⟨𝒬 u, mem_ball_self (by positivity), ?_⟩
    rw [@mem_ball]
    have i1 : ball_{𝓘 u} (𝒬 u) 1 ⊆ ball_{𝓘 p} (𝒬 p) 2 := sl₁.2
    have i2 : ball_{𝓘 u'} (𝒬 u') 1 ⊆ ball_{𝓘 p} (𝒬 p) 10 := sl₂.2
    replace i1 : 𝒬 u ∈ ball_{𝓘 p} (𝒬 p) 2 := i1 (mem_ball_self zero_lt_one)
    replace i2 : 𝒬 u' ∈ ball_{𝓘 p} (𝒬 p) 10 := i2 (mem_ball_self zero_lt_one)
    rw [e', @mem_ball] at i1 i2
    calc
      _ ≤ dist_{𝓘 u'} (𝒬 u) (𝒬 p) + dist_{𝓘 u'} (𝒬 u') (𝒬 p) := dist_triangle_right ..
      _ < 2 + 10 := add_lt_add i1 i2
      _ < 100 := by norm_num
  have plu : smul 100 p ≤ smul 100 u := wiggle_order_100 (smul_mono sl₁ le_rfl (by norm_num)) np
  have plu' : smul 100 p ≤ smul 100 u' := wiggle_order_100 sl₂ e'
  by_contra h
  have 𝔅dj : Disjoint (𝔅 k n u) (𝔅 k n u') := by
    simp_rw [𝔅, disjoint_left, mem_setOf, not_and]; intro q ⟨_, sl⟩ _
    simp_rw [TileLike.le_def, smul_fst, smul_snd, not_and_or] at sl ⊢; right
    have := disjoint_left.mp (h.mono_left sl.2) (mem_ball_self zero_lt_one)
    rw [not_subset]; use 𝒬 q, mem_ball_self zero_lt_one
  have usp : 𝔅 k n u ⊆ 𝔅 k n p := fun q mq ↦ by
    rw [𝔅, mem_setOf] at mq ⊢; exact ⟨mq.1, plu.trans mq.2⟩
  have u'sp : 𝔅 k n u' ⊆ 𝔅 k n p := fun q mq ↦ by
    rw [𝔅, mem_setOf] at mq ⊢; exact ⟨mq.1, plu'.trans mq.2⟩
  rw [𝔘₂, mem_setOf, 𝔘₁, mem_setOf] at hu hu'
  apply absurd (card_𝔅_of_mem_ℭ₁ mp).2; rw [not_lt]
  calc
    _ = 2 ^ j + 2 ^ j := Nat.two_pow_succ j
    _ ≤ (𝔅 k n u).toFinset.card + (𝔅 k n u').toFinset.card :=
      add_le_add (card_𝔅_of_mem_ℭ₁ hu.1.1).1 (card_𝔅_of_mem_ℭ₁ hu'.1.1).1
    _ = (𝔅 k n u ∪ 𝔅 k n u').toFinset.card := by
      rw [toFinset_union]; refine (Finset.card_union_of_disjoint ?_).symm
      simpa using 𝔅dj
    _ ≤ _ := by
      apply Finset.card_le_card
      simp_rw [toFinset_union, subset_toFinset, Finset.coe_union, coe_toFinset, union_subset_iff]
      exact ⟨usp, u'sp⟩

/-- Lemma 5.4.1, part 1. -/
lemma URel.eq (hu : u ∈ 𝔘₂ k n j) (hu' : u' ∈ 𝔘₂ k n j) (huu' : URel k n j u u') : 𝓘 u = 𝓘 u' := by
  by_cases e : u = u'; · rw [e]
  have ndj := not_disjoint hu hu' huu'
  have n₁ := (hu.1.2 _ hu'.1.1).mt ndj
  rw [disjoint_comm] at ndj
  have n₂ := (hu'.1.2 _ hu.1.1).mt ndj
  simp_rw [URel, e, false_or, 𝔗₁, mem_setOf] at huu'; obtain ⟨p, ⟨_, _, sl₁⟩, sl₂⟩ := huu'
  rcases le_or_lt (𝔰 u) (𝔰 u') with h | h
  · exact eq_of_le_of_not_lt (Grid.le_dyadic h sl₁.1 sl₂.1) n₁
  · exact (eq_of_le_of_not_lt (Grid.le_dyadic h.le sl₂.1 sl₁.1) n₂).symm

/-- Helper for 5.4.2 that is also used in 5.4.9. -/
lemma urel_of_not_disjoint {x y : 𝔓 X} (my : y ∈ 𝔘₂ k n j) (xny : x ≠ y) (xye : 𝓘 x = 𝓘 y)
    (nd : ¬Disjoint (ball_(x) (𝒬 x) 100) (ball_(y) (𝒬 y) 100)) : URel k n j y x := by
  rw [not_disjoint_iff] at nd
  obtain ⟨(ϑ : Θ X), (ϑx : ϑ ∈ ball_{𝓘 x} (𝒬 x) 100), (ϑy : ϑ ∈ ball_{𝓘 y} (𝒬 y) 100)⟩ := nd
  rw [𝔘₂, mem_setOf, not_disjoint_iff] at my; obtain ⟨p, hp, _⟩ := my.2
  suffices w : ball_(x) (𝒬 x) 1 ⊆ ball_(y) (𝒬 y) 500 by
    right; use p, hp; obtain ⟨_, np, sl⟩ := hp
    have : smul 10 p ≤ smul 500 y := (smul_mono_left (by norm_num)).trans (wiggle_order_500 sl np)
    exact ⟨(xye ▸ sl.1 : 𝓘 p ≤ 𝓘 x), this.2.trans w⟩
  intro (q : Θ X) (mq : q ∈ ball_{𝓘 x} (𝒬 x) 1)
  rw [@mem_ball] at mq ⊢
  calc
    _ ≤ dist_(y) q ϑ + dist_(y) ϑ (𝒬 y) := dist_triangle ..
    _ ≤ dist_(y) q (𝒬 x) + dist_(y) ϑ (𝒬 x) + dist_(y) ϑ (𝒬 y) := by
      gcongr; apply dist_triangle_right
    _ < 1 + 100 + 100 := by
      gcongr
      · rwa [xye] at mq
      · rwa [@mem_ball, xye] at ϑx
      · rwa [@mem_ball] at ϑy
    _ < _ := by norm_num

/-- Lemma 5.4.2. -/
lemma equivalenceOn_urel : EquivalenceOn (URel (X := X) k n j) (𝔘₂ k n j) where
  refl _ _ := .rfl
  trans {x y z} mx my mz xy yz := by
    by_cases xny : x = y; · rwa [xny]
    have xye := URel.eq mx my xy
    have := URel.not_disjoint mx my xy
    rw [not_disjoint_iff] at this
    obtain ⟨(ϑ : Θ X), (ϑx : ϑ ∈ ball_{𝓘 x} (𝒬 x) 100), (ϑy : ϑ ∈ ball_{𝓘 y} (𝒬 y) 100)⟩ := this
    have yze := URel.eq my mz yz
    have := URel.not_disjoint my mz yz
    rw [not_disjoint_iff] at this
    obtain ⟨(θ : Θ X), (θy : θ ∈ ball_{𝓘 y} (𝒬 y) 100), (θz : θ ∈ ball_{𝓘 z} (𝒬 z) 100)⟩ := this
    simp_rw [URel, xny, false_or] at xy; obtain ⟨p, mp, sp⟩ := xy
    suffices ball_(z) (𝒬 z) 1 ⊆ ball_(x) (𝒬 x) 500 by
      right; use p, mp; obtain ⟨_, np, sl⟩ := mp
      have w : ball_(x) (𝒬 x) 500 ⊆ ball_(p) (𝒬 p) 4 := (wiggle_order_500 sl np).2
      exact ⟨(yze ▸ xye ▸ sl.1 : 𝓘 p ≤ 𝓘 z), (this.trans w).trans (ball_subset_ball (by norm_num))⟩
    intro (q : Θ X) (mq : q ∈ ball_{𝓘 z} (𝒬 z) 1)
    rw [@mem_ball] at mq ⊢
    calc
      _ ≤ dist_(x) q ϑ + dist_(x) ϑ (𝒬 x) := dist_triangle ..
      _ < dist_(x) q ϑ + 100 := by gcongr; rwa [@mem_ball] at ϑx
      _ ≤ dist_(x) q (𝒬 y) + dist_(x) ϑ (𝒬 y) + 100 := by gcongr; exact dist_triangle_right ..
      _ < dist_(x) q (𝒬 y) + 100 + 100 := by gcongr; rwa [@mem_ball, ← xye] at ϑy
      _ ≤ dist_(x) q θ + dist_(x) θ (𝒬 y) + 100 + 100 := by gcongr; exact dist_triangle ..
      _ < dist_(x) q θ + 100 + 100 + 100 := by gcongr; rwa [@mem_ball, ← xye] at θy
      _ ≤ dist_(x) q (𝒬 z) + dist_(x) θ (𝒬 z) + 100 + 100 + 100 := by
        gcongr; exact dist_triangle_right ..
      _ < 1 + 100 + 100 + 100 + 100 := by
        gcongr
        · rwa [← yze, ← xye] at mq
        · rwa [@mem_ball, ← yze, ← xye] at θz
      _ < _ := by norm_num
  symm {x y} mx my xy := by
    by_cases xny : x = y; · rw [xny]; exact .rfl
    exact urel_of_not_disjoint my xny (URel.eq mx my xy) (URel.not_disjoint mx my xy)

/-- `𝔘₃(k, n, j) ⊆ 𝔘₂ k n j` is an arbitary set of representatives of `URel` on `𝔘₂ k n j`,
given above (5.4.5). -/
def 𝔘₃ (k n j : ℕ) : Set (𝔓 X) :=
  (equivalenceOn_urel (k := k) (n := n) (j := j)).reprs

lemma 𝔘₃_subset_𝔘₂ : 𝔘₃ k n j ⊆ 𝔘₂ (X := X) k n j := EquivalenceOn.reprs_subset

/-- The subset `𝔗₂(u)` of `ℭ₆(k, n, j)`, given in (5.4.5).
In lemmas, we will assume `u ∈ 𝔘₃ k n l` -/
def 𝔗₂ (k n j : ℕ) (u : 𝔓 X) : Set (𝔓 X) :=
  ℭ₆ k n j ∩ ⋃ (u' ∈ 𝔘₂ k n j) (_ : URel k n j u u'), 𝔗₁ k n j u'

lemma 𝔗₂_subset_ℭ₆ : 𝔗₂ k n j u ⊆ ℭ₆ k n j := inter_subset_left ..

/-- Lemma 5.4.3 -/
lemma C6_forest : ℭ₆ (X := X) k n j = ⋃ u ∈ 𝔘₃ k n j, 𝔗₂ k n j u := by
  ext p; constructor <;> intro h
  · have : p ∈ ℭ₃ k n j := (ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃) h
    rw [ℭ₃, mem_diff, 𝔏₂, mem_setOf] at this
    have mp := this.1
    simp_rw [this.1, true_and, not_not] at this
    obtain ⟨u, mu, np, sl⟩ := this
    have mp' : p ∈ 𝔗₁ k n j u := by
      rw [𝔗₁, mem_setOf]; exact ⟨ℭ₂_subset_ℭ₁ mp, np, sl⟩
    have mu' : u ∈ 𝔘₂ k n j := by
      rw [𝔘₂, mem_setOf]; exact ⟨mu, not_disjoint_iff.mpr ⟨_, mp', h⟩⟩
    let rr := equivalenceOn_urel (X := X) (k := k) (n := n) (j := j)
    rw [mem_iUnion₂]; use rr.out u, (rr.out_mem_reprs mu')
    refine ⟨h, ?_⟩; rw [mem_iUnion₂]; use u, mu'; rw [mem_iUnion]; use rr.out_rel mu'
  · rw [mem_iUnion₂] at h; obtain ⟨_, _, mp, _⟩ := h; exact mp

/-- Lemma 5.4.4, verifying (2.0.32) -/
lemma forest_geometry (hu : u ∈ 𝔘₃ k n j) (hp : p ∈ 𝔗₂ k n j u) : smul 4 p ≤ smul 1 u := by
  rw [𝔗₂, mem_inter_iff, mem_iUnion₂] at hp
  obtain ⟨_, u', mu', w⟩ := hp; rw [mem_iUnion] at w; obtain ⟨ru, mp'⟩ := w
  rw [𝔗₁, mem_setOf] at mp'; obtain ⟨_, np, sl⟩ := mp'
  have xye := URel.eq (EquivalenceOn.reprs_subset hu) mu' ru
  have := URel.not_disjoint (EquivalenceOn.reprs_subset hu) mu' ru
  rw [not_disjoint_iff] at this
  obtain ⟨(ϑ : Θ X), (ϑx : ϑ ∈ ball_{𝓘 u} (𝒬 u) 100), (ϑy : ϑ ∈ ball_{𝓘 u'} (𝒬 u') 100)⟩ := this
  suffices ball_(u) (𝒬 u) 1 ⊆ ball_(u') (𝒬 u') 500 by
    have w : smul 4 p ≤ smul 500 u' := (wiggle_order_500 sl np)
    exact ⟨(xye ▸ sl.1 : 𝓘 p ≤ 𝓘 u), w.2.trans this⟩
  intro (q : Θ X) (mq : q ∈ ball_{𝓘 u} (𝒬 u) 1)
  rw [@mem_ball] at mq ⊢
  calc
    _ ≤ dist_(u') q ϑ + dist_(u') ϑ (𝒬 u') := dist_triangle ..
    _ ≤ dist_(u') q (𝒬 u) + dist_(u') ϑ (𝒬 u) + dist_(u') ϑ (𝒬 u') := by
      gcongr; apply dist_triangle_right
    _ < 1 + 100 + 100 := by
      gcongr
      · rwa [xye] at mq
      · rwa [@mem_ball, xye] at ϑx
      · rwa [@mem_ball] at ϑy
    _ < _ := by norm_num

/-- Lemma 5.4.5, verifying (2.0.33) -/
lemma forest_convex : OrdConnected (𝔗₂ k n j u) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp'₅ : p' ∈ ℭ₅ (X := X) k n j :=
    (ordConnected_C5.out ((𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ₅) mp)
      ((𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ₅) mp'')) mp'
  have mp'₆ : p' ∈ ℭ₆ k n j := by
    have := 𝔗₂_subset_ℭ₆ mp; rw [ℭ₆, mem_setOf] at this ⊢
    refine ⟨mp'₅, ?_⟩; replace this := this.2; contrapose! this
    exact mp'.1.1.1.trans this
  simp_rw [𝔗₂, mem_inter_iff, mp'₆, true_and, mem_iUnion₂, mem_iUnion] at mp'' ⊢
  obtain ⟨u', mu', ru, _, np'', sl⟩ := mp''.2
  have pnu : 𝓘 p' < 𝓘 u' := (mp'.2.1).trans_lt (lt_of_le_of_ne sl.1 np'')
  use u', mu', ru; rw [𝔗₁, mem_setOf]
  use (ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂ |>.trans ℭ₂_subset_ℭ₁) mp'₅, pnu.ne
  exact (wiggle_order_11_10 mp'.2 (C5_3_3_le (X := X).trans (by norm_num))).trans sl

/-- Lemma 5.4.6, verifying (2.0.36)
Note: swapped `u` and `u'` to match (2.0.36) -/
lemma forest_separation (hu : u ∈ 𝔘₃ k n j) (hu' : u' ∈ 𝔘₃ k n j) (huu' : u ≠ u')
    (hp : p ∈ 𝔗₂ k n j u') (h : 𝓘 p ≤ 𝓘 u) : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) := by
  simp_rw [𝔗₂, mem_inter_iff, mem_iUnion₂, mem_iUnion] at hp
  obtain ⟨mp₆, v, mv, rv, ⟨-, np, sl⟩⟩ := hp
  obtain ⟨p', mp', lp', sp'⟩ := exists_scale_add_le_of_mem_layersAbove <|
    (ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂) mp₆
  have np'u : ¬URel k n j v u := by
    by_contra h; apply absurd (Eq.symm _) huu'
    replace h := equivalenceOn_urel.trans (𝔘₃_subset_𝔘₂ hu') mv (𝔘₃_subset_𝔘₂ hu) rv h
    exact EquivalenceOn.reprs_inj hu' hu h
  have vnu : v ≠ u := by by_contra h; subst h; exact absurd URel.rfl np'u
  simp_rw [URel, vnu, false_or, not_exists, not_and] at np'u
  have mpt : p' ∈ 𝔗₁ k n j v := by
    refine ⟨minLayer_subset mp', ?_, ?_⟩
    · exact (lp'.1.trans_lt (lt_of_le_of_ne sl.1 np)).ne
    · exact (wiggle_order_11_10 lp' (C5_3_3_le (X := X).trans (by norm_num))).trans sl
  specialize np'u p' mpt
  have 𝓘p'u : 𝓘 p' ≤ 𝓘 u := lp'.1.trans h
  simp_rw [TileLike.le_def, smul_fst, smul_snd, 𝓘p'u, true_and,
    not_subset_iff_exists_mem_not_mem] at np'u
  obtain ⟨(q : Θ X), mq, nq⟩ := np'u
  simp_rw [mem_ball, not_lt] at mq nq
  have d8 : 8 < dist_(p') (𝒬 p) (𝒬 u) :=
    calc
      _ = 10 - 1 - 1 := by norm_num
      _ < 10 - 1 - dist_(u) q (𝒬 u) := by gcongr
      _ ≤ 10 - 1 - dist_(p') q (𝒬 u) := tsub_le_tsub_left (Grid.dist_mono 𝓘p'u) _
      _ ≤ dist_(p') q (𝒬 p') - 1 - dist_(p') q (𝒬 u) := by gcongr
      _ < dist_(p') q (𝒬 p') - dist_(p') (𝒬 p) (𝒬 p') - dist_(p') q (𝒬 u) := by
        gcongr; rw [← @mem_ball]; exact subset_cball (lp'.2 𝒬_mem_Ω)
      _ ≤ _ := by
        rw [sub_le_iff_le_add', sub_le_iff_le_add]
        nth_rw 3 [dist_comm]; apply dist_triangle4
  have Znpos : 0 < Z * (n + 1) := by rw [defaultZ]; positivity
  let d : ℕ := (𝔰 p - 𝔰 p').toNat
  have sd : 𝔰 p' + d = 𝔰 p := by simp_rw [d]; rw [Int.toNat_sub_of_le] <;> omega
  have d1 : dist_(p') (𝒬 p) (𝒬 u) ≤ C2_1_2 a ^ d * dist_(p) (𝒬 p) (𝒬 u) :=
    Grid.dist_strictMono_iterate lp'.1 sd
  have Cdpos : 0 < C2_1_2 a ^ d := by rw [C2_1_2]; positivity
  have Cidpos : 0 < (C2_1_2 a)⁻¹ ^ d := by rw [C2_1_2]; positivity
  calc
    _ ≤ (C2_1_2 a)⁻¹ ^ (Z * (n + 1)) := by
      refine pow_le_pow_left zero_le_two ?_ _
      nth_rw 1 [C2_1_2, ← Real.inv_rpow zero_le_two, ← Real.rpow_neg_one,
        ← Real.rpow_mul zero_le_two, neg_one_mul, neg_mul, neg_neg, ← Real.rpow_one 2]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      norm_cast; linarith [four_le_a X]
    _ ≤ (C2_1_2 a)⁻¹ ^ d := by
      refine pow_le_pow_right ?_ (by omega)
      simp_rw [one_le_inv_iff, C2_1_2_le_one (X := X), and_true, C2_1_2]; positivity
    _ ≤ (C2_1_2 a)⁻¹ ^ d * 8 := by nth_rw 1 [← mul_one (_ ^ d)]; gcongr; norm_num
    _ < (C2_1_2 a)⁻¹ ^ d * dist_(p') (𝒬 p) (𝒬 u) := by gcongr
    _ ≤ _ := by
      rwa [← mul_le_mul_iff_of_pos_left Cdpos, inv_pow, ← mul_assoc, mul_inv_cancel₀ Cdpos.ne',
        one_mul]

/-- Lemma 5.4.7, verifying (2.0.37) -/
lemma forest_inner (hu : u ∈ 𝔘₃ k n j) (hp : p ∈ 𝔗₂ k n j u) :
    ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u := by
  have p₄ := (𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄) hp
  have p₁ := (ℭ₄_subset_ℭ₃.trans ℭ₃_subset_ℭ₂ |>.trans ℭ₂_subset_ℭ₁) p₄
  obtain ⟨q, mq, lq, sq⟩ := exists_le_add_scale_of_mem_layersBelow p₄
  obtain ⟨-, u'', mu'', nu'', sl⟩ := ℭ₃_def.mp (maxLayer_subset mq)
  replace nu'' : 𝓘 q < 𝓘 u'' := lt_of_le_of_ne sl.1 nu''
  have s2 : smul 2 p ≤ smul 2 q := wiggle_order_11_10 lq (C5_3_3_le (X := X).trans (by norm_num))
  have s2' : smul 2 p ≤ smul 1 u'' := s2.trans sl
  have s10 : smul 10 p ≤ smul 1 u'' := smul_mono s2' le_rfl (by norm_num)
  simp_rw [𝔗₂, mem_inter_iff, mem_iUnion₂, mem_iUnion] at hp
  obtain ⟨p₆, u', mu', ru', pu'⟩ := hp
  have ur : URel k n j u' u'' := Or.inr ⟨p, pu', s10⟩
  have hu'' : u'' ∈ 𝔘₂ k n j := by
    rw [𝔘₂, mem_setOf, not_disjoint_iff]
    refine ⟨mu'', ⟨p, ?_, p₆⟩⟩
    simpa [𝔗₁, p₁, s2'] using (lq.1.trans_lt nu'').ne
  have ru'' : URel k n j u u'' := equivalenceOn_urel.trans (𝔘₃_subset_𝔘₂ hu) mu' hu'' ru' ur
  have qlu : 𝓘 q < 𝓘 u := URel.eq (𝔘₃_subset_𝔘₂ hu) hu'' ru'' ▸ nu''
  have squ : 𝔰 q < 𝔰 u := (Grid.lt_def.mp qlu).2
  have spu : 𝔰 p ≤ 𝔰 u - (Z * (n + 1) : ℕ) - 1 := by omega
  have : ∃ I, s I = 𝔰 u - (Z * (n + 1) : ℕ) - 1 ∧ 𝓘 p ≤ I ∧ I ≤ 𝓘 u := by
    apply Grid.exists_sandwiched (lq.1.trans qlu.le) (𝔰 u - (Z * (n + 1) : ℕ) - 1)
    refine ⟨spu, ?_⟩; change _ ≤ 𝔰 u; suffices 0 ≤ Z * (n + 1) by omega
    exact Nat.zero_le _
  obtain ⟨I, sI, plI, Ilu⟩ := this
  have bI : I ∉ 𝓛 n u := by
    have p₅ := ℭ₆_subset_ℭ₅ p₆
    rw [ℭ₅_def] at p₅; replace p₅ := p₅.2; contrapose! p₅
    use u, (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁) hu, plI.1.trans (subset_biUnion_of_mem p₅)
  rw [𝓛, mem_setOf, not_and] at bI; specialize bI Ilu
  rw [not_and, not_not] at bI; specialize bI (by omega); rw [← sI] at spu
  rcases spu.eq_or_lt with h | h
  · have : 𝓘 p = I := by
      apply eq_of_le_of_not_lt plI; rw [Grid.lt_def, not_and_or, not_lt]; exact Or.inr h.symm.le
    rwa [← this] at bI
  · apply subset_trans (ball_subset_ball' _) bI
    have ds : c (𝓘 p) ∈ ball (c I) (4 * D ^ s I) := (plI.1.trans Grid_subset_ball) Grid.c_mem_Grid
    rw [mem_ball] at ds
    calc
      _ ≤ 4 * D * (D : ℝ) ^ 𝔰 p + 4 * D ^ s I := by
        gcongr
        · linarith [four_le_realD X]
        · exact ds.le
      _ = 4 * D ^ (𝔰 p + 1) + 4 * D ^ s I := by
        rw [mul_assoc]; congr; rw [mul_comm, ← zpow_add_one₀ (defaultD_pos _).ne']
      _ ≤ 4 * D ^ s I + 4 * D ^ s I := by
        gcongr
        · exact one_le_D
        · omega
      _ = _ := by ring

def C5_4_8 (n : ℕ) : ℕ := (4 * n + 12) * 2 ^ n

lemma exists_smul_le_of_𝔘₃ (u : 𝔘₃ k n j) : ∃ m : 𝔐 (X := X) k n, smul 100 u.1 ≤ smul 1 m.1 := by
  obtain ⟨u, mu⟩ := u
  replace mu := (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁ |>.trans 𝔘₁_subset_ℭ₁) mu
  rw [ℭ₁, mem_diff, preℭ₁, mem_setOf, filter_mem_univ_eq_toFinset] at mu
  replace mu := (show 0 < 2 ^ j by positivity).trans_le mu.1.2
  rw [Finset.card_pos] at mu; obtain ⟨m, hm⟩ := mu
  rw [mem_toFinset, 𝔅] at hm; exact ⟨⟨m, hm.1⟩, hm.2⟩

variable (k n j) in
def mf (u : 𝔘₃ (X := X) k n j) : 𝔐 (X := X) k n := (exists_smul_le_of_𝔘₃ u).choose

lemma mf_injOn : InjOn (mf k n j) {u | x ∈ 𝓘 u.1} := fun u mu u' mu' e ↦ by
  set m := mf k n j u
  have iu : smul 100 u.1 ≤ smul 1 m.1 := (exists_smul_le_of_𝔘₃ u).choose_spec
  have iu' : smul 100 u'.1 ≤ smul 1 m.1 := e ▸ (exists_smul_le_of_𝔘₃ u').choose_spec
  have su : ball_{𝓘 m.1} (𝒬 m.1) 1 ⊆ ball_{𝓘 u.1} (𝒬 u.1) 100 := iu.2
  have su' : ball_{𝓘 m.1} (𝒬 m.1) 1 ⊆ ball_{𝓘 u'.1} (𝒬 u'.1) 100 := iu'.2
  have nd : ¬Disjoint (ball_{𝓘 u.1} (𝒬 u.1) 100) (ball_{𝓘 u'.1} (𝒬 u'.1) 100) := by
    rw [not_disjoint_iff]
    use 𝒬 m.1, su (mem_ball_self zero_lt_one), su' (mem_ball_self zero_lt_one)
  by_contra! h; rw [← Subtype.coe_ne_coe] at h; apply absurd _ nd
  have nr : ¬URel k n j u.1 u'.1 := by contrapose! h; exact EquivalenceOn.reprs_inj u.2 u'.2 h
  have n𝓘 : 𝓘 u.1 ≠ 𝓘 u'.1 := by
    contrapose! nr; rw [disjoint_comm] at nd
    exact urel_of_not_disjoint (𝔘₃_subset_𝔘₂ u.2) h.symm nr.symm nd
  rcases le_or_lt (s (𝓘 u.1)) (s (𝓘 u'.1)) with hs | hs
  · have := lt_of_le_of_ne ((le_or_disjoint hs).resolve_right
      (not_disjoint_iff.mpr ⟨_, mu, mu'⟩)) n𝓘
    have u₁ := (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁) u.2
    exact u₁.2 u' ((𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁ |>.trans 𝔘₁_subset_ℭ₁) u'.2) this
  · have := lt_of_le_of_ne ((le_or_disjoint hs.le).resolve_right
      (not_disjoint_iff.mpr ⟨_, mu', mu⟩)) n𝓘.symm
    have u'₁ := (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁) u'.2
    exact (u'₁.2 u ((𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁ |>.trans 𝔘₁_subset_ℭ₁) u.2) this).symm

lemma stackSize_𝔘₃_le_𝔐 (x : X) : stackSize (𝔘₃ k n j) x ≤ stackSize (𝔐 k n) x := by
  let mf' : 𝔓 X → 𝔓 X := fun u ↦ if mu : u ∈ 𝔘₃ k n j then mf k n j ⟨u, mu⟩ else default
  simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
  refine Finset.card_le_card_of_injOn mf' (fun u mu ↦ ?_) (fun u mu u' mu' e ↦ ?_)
  · simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mu ⊢
    simp_rw [mf', mu.1, dite_true]
    have : 𝓘 u ≤ 𝓘 (mf k n j ⟨u, mu.1⟩) := (exists_smul_le_of_𝔘₃ ⟨u, mu.1⟩).choose_spec.1
    exact ⟨(mf k n j ⟨u, mu.1⟩).2, this.1 mu.2⟩
  · simp_rw [Finset.coe_filter, mem_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at mu mu'
    simp_rw [mf', mu.1, mu'.1, dite_true, Subtype.val_inj] at e
    simpa using mf_injOn mu.2 mu'.2 e

/-- Lemma 5.4.8, used to verify that 𝔘₄ satisfies 2.0.34. -/
lemma forest_stacking (x : X) (hkn : k ≤ n) : stackSize (𝔘₃ (X := X) k n j) x ≤ C5_4_8 n := by
  by_contra! h
  let C : Finset (𝔓 X) := { u | u ∈ 𝔘₃ (X := X) k n j ∧ x ∈ 𝓘 u }
  have Cc : C.card = stackSize (𝔘₃ k n j) x := by
    simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
      C, Grid.mem_def, Finset.filter_filter]
  have Cn : C.Nonempty := by
    by_contra! Ce; rw [Finset.not_nonempty_iff_eq_empty] at Ce
    simp_rw [← Cc, Ce, Finset.card_empty, not_lt_zero'] at h
  let C' : Finset (Grid X) := C.image 𝓘
  have C'n : C'.Nonempty := by rwa [Finset.image_nonempty]
  obtain ⟨i, mi, li⟩ := C'.exists_minimal C'n
  simp_rw [C', Finset.mem_image, C, Finset.mem_filter, Finset.mem_univ, true_and] at mi
  obtain ⟨u, ⟨mu, mx⟩, uei⟩ := mi; subst uei
  have uA : (𝓘 u : Set X) ⊆ setA (2 * n + 6) k n := fun y my ↦
    calc
      _ = (4 * n + 12) * 2 ^ n := by ring
      _ < stackSize (𝔘₃ k n j) x := h
      _ ≤ stackSize (𝔘₃ k n j) y := by
        simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
        apply Finset.card_le_card fun v mv ↦ ?_
        simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mv ⊢
        have mvC' : 𝓘 v ∈ C' := by
          simp_rw [C', Finset.mem_image]; use v
          simp_rw [C, Finset.mem_filter, Finset.mem_univ, true_and, and_true]; exact mv
        specialize li _ mvC'
        have inc := (or_assoc.mpr (le_or_ge_or_disjoint (i := 𝓘 u) (j := 𝓘 v))).resolve_right
          (not_disjoint_iff.mpr ⟨_, mx, mv.2⟩)
        simp_rw [le_iff_eq_or_lt] at inc
        replace inc : 𝓘 u = 𝓘 v ∨ 𝓘 u < 𝓘 v := by tauto
        rw [← le_iff_eq_or_lt] at inc
        exact ⟨mv.1, inc.1 my⟩
      _ ≤ _ := stackSize_𝔘₃_le_𝔐 _
  refine absurd (disjoint_left.mpr fun v mv ↦ ?_) (𝔘₃_subset_𝔘₂ mu).2
  rw [𝔗₁, mem_setOf] at mv; rw [ℭ₆, mem_setOf, not_and, not_not]
  refine fun _ ↦ (mv.2.2.1).1.trans ?_
  calc
    _ ⊆ setA (2 * n + 6) k n := uA
    _ ⊆ G₂ := subset_iUnion₂_of_subset n k (subset_iUnion_of_subset hkn subset_rfl)
    _ ⊆ _ := subset_union_of_subset_left subset_union_right G₃

/-- Pick a maximal subset of `s` satisfying `∀ x, stackSize s x ≤ 2 ^ n` -/
def aux𝔘₄ (s : Set (𝔓 X)) : Set (𝔓 X) := by
  revert s; sorry

/-- The sets `(𝔘₄(k, n, j, l))_l` form a partition of `𝔘₃ k n j`. -/
def 𝔘₄ (k n j l : ℕ) : Set (𝔓 X) :=
  aux𝔘₄ <| 𝔘₃ k n j \ ⋃ (l' < l), 𝔘₄ k n j l'

lemma iUnion_𝔘₄ : ⋃ l, 𝔘₄ (X := X) k n j l = 𝔘₃ k n j := by
  sorry

lemma 𝔘₄_subset_𝔘₃ : 𝔘₄ (X := X) k n j l ⊆ 𝔘₃ k n j := by
  sorry

lemma le_of_nonempty_𝔘₄ (h : (𝔘₄ (X := X) k n j l).Nonempty) : l < 4 * n + 13 := by
  sorry

lemma pairwiseDisjoint_𝔘₄ : univ.PairwiseDisjoint (𝔘₄ (X := X) k n j) := by
  sorry

lemma stackSize_𝔘₄_le (x : X) : stackSize (𝔘₄ (X := X) k n j l) x ≤ 2 ^ n := by
  sorry

open TileStructure
variable (k n j l) in
def forest : Forest X n where
  𝔘 := 𝔘₄ k n j l
  𝔗 := 𝔗₂ k n j
  nonempty {u} hu := sorry
  ordConnected {u} hu := forest_convex
  𝓘_ne_𝓘 hu hp := sorry
  smul_four_le {u} hu := forest_geometry <| 𝔘₄_subset_𝔘₃ hu
  stackSize_le {x} := stackSize_𝔘₄_le x
  dens₁_𝔗_le {u} hu := dens1_le <| 𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ
  lt_dist hu hu' huu' p hp := forest_separation (𝔘₄_subset_𝔘₃ hu) (𝔘₄_subset_𝔘₃ hu') huu' hp
  ball_subset hu p hp := forest_inner (𝔘₄_subset_𝔘₃ hu) hp

/-- The constant used in Lemma 5.1.2, with value `2 ^ (235 * a ^ 3) / (q - 1) ^ 4` -/
-- todo: redefine in terms of other constants
def C5_1_2 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (235 * a ^ 3) / (q - 1) ^ 4

lemma C5_1_2_pos : C5_1_2 a nnq > 0 := sorry

lemma forest_union {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
  ∫⁻ x in G \ G', ‖∑ p ∈ { p | p ∈ 𝔓₁ }, carlesonOn p f x‖₊ ≤
    C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹  := by
  sorry

/-! ## Section 5.5 and Lemma 5.1.3 -/

/-- The set 𝔓_{G\G'} in the blueprint -/
def 𝔓pos : Set (𝔓 X) := { p : 𝔓 X | 0 < volume (𝓘 p ∩ G ∩ G'ᶜ) }

lemma exists_mem_aux𝓒 {i : Grid X} (hi : 0 < volume (G ∩ i)) : ∃ k, i ∈ aux𝓒 (k + 1) := by
  have vlt : volume (i : Set X) < ⊤ := volume_coeGrid_lt_top
  have one_le_quot : 1 ≤ volume (i : Set X) / volume (G ∩ i) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hi.ne') (Or.inr vlt.ne), one_mul]
    exact measure_mono inter_subset_right
  have quot_ne_top : volume (i : Set X) / volume (G ∩ i) ≠ ⊤ := by
    rw [Ne, ENNReal.div_eq_top, not_or, not_and_or, not_and_or]
    exact ⟨Or.inr hi.ne', Or.inl vlt.ne⟩
  have ornz : 0 < (volume (i : Set X) / volume (G ∩ i)).toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le one_le_quot).ne' quot_ne_top
  let k : ℝ := Real.logb 2 (volume (i : Set X) / volume (G ∩ i)).toReal
  use ⌊k⌋₊, i, le_rfl
  nth_rw 1 [← ENNReal.mul_lt_mul_left (show 2 ^ (⌊k⌋₊ + 1) ≠ 0 by simp) (by simp), ← mul_assoc,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_intCast, ← ENNReal.rpow_add _ _ (by simp) (by simp)]
  rw [Int.cast_neg, Int.cast_natCast, add_neg_cancel, ENNReal.rpow_zero, one_mul,
    ← ENNReal.div_lt_iff (Or.inl hi.ne') (Or.inr vlt.ne), ← ENNReal.ofReal_toReal quot_ne_top,
    ← @ENNReal.ofReal_toReal (2 ^ (⌊k⌋₊ + 1)) (by simp), ENNReal.ofReal_lt_ofReal_iff (by simp),
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← Real.rpow_natCast,
    ← Real.logb_lt_iff_lt_rpow one_lt_two ornz]
  exact Nat.lt_succ_floor k

lemma exists_k_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : ∃ k, p ∈ TilesAt k := by
  let C : Set ℕ := {k | 𝓘 p ∈ aux𝓒 k}
  have Cn : C.Nonempty := by
    rw [𝔓pos, mem_setOf] at h
    have vpos : 0 < volume (G ∩ 𝓘 p) := by
      rw [inter_comm]; exact h.trans_le (measure_mono inter_subset_left)
    obtain ⟨k, hk⟩ := exists_mem_aux𝓒 vpos; exact ⟨_, hk⟩
  let s : ℕ := WellFounded.min wellFounded_lt _ Cn
  have s_mem : s ∈ C := WellFounded.min_mem ..
  have s_min : ∀ t ∈ C, s ≤ t := fun t mt ↦ WellFounded.min_le _ mt _
  have s_pos : 0 < s := by
    by_contra! h; rw [nonpos_iff_eq_zero] at h
    simp_rw [h, C, aux𝓒, mem_setOf] at s_mem; apply absurd s_mem; push_neg; intro _ _
    rw [Int.neg_ofNat_zero, zpow_zero, one_mul]; exact measure_mono inter_subset_right
  use s - 1; rw [TilesAt, mem_preimage, 𝓒, mem_diff, Nat.sub_add_cancel s_pos]
  have : ∀ t < s, t ∉ C := fun t mt ↦ by contrapose! mt; exact s_min t mt
  exact ⟨s_mem, this (s - 1) (Nat.sub_one_lt_of_lt s_pos)⟩

lemma dens'_le_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : dens' k {p} ≤ 2 ^ (-k : ℤ) := by
  simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left, iSup_le_iff]; intro l hl p' mp' sl
  have vpos : 0 < volume (𝓘 p' : Set X) := by
    refine lt_of_lt_of_le ?_ (measure_mono sl.1.1)
    rw [𝔓pos, mem_setOf, inter_assoc] at h; exact h.trans_le (measure_mono inter_subset_left)
  rw [ENNReal.div_le_iff vpos.ne' volume_coeGrid_lt_top.ne]
  calc
    _ ≤ volume (E₂ l p') := by
      nth_rw 2 [← one_mul (volume _)]; apply mul_le_mul_right'
      rw [show 1 = (l : ℝ≥0∞) ^ (0 : ℤ) by simp]; apply ENNReal.zpow_le_of_le
      · rw [ENNReal.one_le_coe_iff]; exact one_le_two.trans hl
      · linarith [four_le_a X]
    _ ≤ _ := by
      have E : E₂ l p' ⊆ 𝓘 p' ∩ G := inter_subset_left
      rw [TilesAt, mem_preimage, 𝓒, mem_diff] at mp'; replace mp' := mp'.2
      rw [aux𝓒, mem_setOf] at mp'; push_neg at mp'; specialize mp' (𝓘 p') le_rfl
      rw [inter_comm] at E; exact (measure_mono E).trans mp'

lemma exists_E₂_volume_pos_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : ∃ r : ℕ, 0 < volume (E₂ r p) := by
  apply exists_measure_pos_of_not_measure_iUnion_null
  change volume (⋃ n : ℕ, 𝓘 p ∩ G ∩ Q ⁻¹' ball_(p) (𝒬 p) n) ≠ 0
  rw [← inter_iUnion]
  suffices ⋃ i : ℕ, Q ⁻¹' ball_(p) (𝒬 p) i = univ by
    rw [this, inter_univ, ← pos_iff_ne_zero]
    rw [𝔓pos, mem_setOf] at h; exact h.trans_le (measure_mono inter_subset_left)
  simp_rw [iUnion_eq_univ_iff, mem_preimage, mem_ball]
  exact fun x ↦ exists_nat_gt (dist_(p) (Q x) (𝒬 p))

lemma dens'_pos_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) (hp : p ∈ TilesAt k) : 0 < dens' k {p} := by
  simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left, lt_iSup_iff]
  obtain ⟨l, hl⟩ := exists_E₂_volume_pos_of_mem_𝔓pos h
  use max 2 l, le_max_left _ _, p, hp, le_rfl
  simp_rw [ENNReal.div_pos_iff, ne_eq, mul_eq_zero, not_or, ← ne_eq, ← pos_iff_ne_zero]
  refine ⟨⟨ENNReal.zpow_pos (by simp) (by simp) _, ?_⟩, volume_coeGrid_lt_top.ne⟩
  refine hl.trans_le <| measure_mono <| inter_subset_inter_right _ <| preimage_mono ?_
  change ball_(p) (𝒬 p) _ ⊆ ball_(p) (𝒬 p) _
  exact ball_subset_ball (by simp)

lemma exists_k_n_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) : ∃ k n, p ∈ ℭ k n ∧ k ≤ n := by
  obtain ⟨k, mp⟩ := exists_k_of_mem_𝔓pos h; use k
  have dens'_pos : 0 < dens' k {p} := dens'_pos_of_mem_𝔓pos h mp
  have dens'_le : dens' k {p} ≤ 2 ^ (-k : ℤ) := dens'_le_of_mem_𝔓pos h
  have dens'_lt_top : dens' k {p} < ⊤ :=
    dens'_le.trans_lt (ENNReal.zpow_lt_top (by simp) (by simp) _)
  have dens'_toReal_pos : 0 < (dens' k {p}).toReal :=
    ENNReal.toReal_pos dens'_pos.ne' dens'_lt_top.ne
  -- 2 ^ (4 * a - n) < dens' k {p} ≤ 2 ^ (4 * a - n + 1)
  -- 4 * a - n < log_2 dens' k {p} ≤ 4 * a - n + 1
  -- -n < log_2 dens' k {p} - 4 * a ≤ -n + 1
  -- n - 1 ≤ 4 * a - log_2 dens' k {p} < n
  -- n ≤ 4 * a - log_2 dens' k {p} + 1 < n + 1
  -- n = 4 * a + ⌊-log_2 dens' k {p}⌋ + 1
  let v : ℝ := -Real.logb 2 (dens' k {p}).toReal
  have klv : k ≤ v := by
    rw [le_neg, Real.logb_le_iff_le_rpow one_lt_two dens'_toReal_pos,
      show (2 : ℝ) = (2 : ℝ≥0∞).toReal by rfl, ENNReal.toReal_rpow,
      ENNReal.toReal_le_toReal dens'_lt_top.ne (by simp)]
    exact_mod_cast dens'_le
  have klq : k ≤ ⌊v⌋₊ := Nat.le_floor klv
  let n : ℕ := 4 * a + ⌊v⌋₊ + 1; use n; refine ⟨⟨mp, ?_⟩, by omega⟩
  rw [show 4 * (a : ℤ) - (4 * a + ⌊v⌋₊ + 1 : ℕ) = (-⌊v⌋₊ - 1 : ℤ) by omega, sub_add_cancel, mem_Ioc,
    ← ENNReal.ofReal_toReal dens'_lt_top.ne, ← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast,
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_cast,
    ENNReal.ofReal_rpow_of_pos zero_lt_two, ENNReal.ofReal_rpow_of_pos zero_lt_two,
    ENNReal.ofReal_lt_ofReal_iff dens'_toReal_pos, ENNReal.ofReal_le_ofReal_iff (by positivity),
    ← Real.logb_le_iff_le_rpow one_lt_two dens'_toReal_pos,
    ← Real.lt_logb_iff_rpow_lt one_lt_two dens'_toReal_pos,
    Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_sub_left, neg_lt, le_neg]
  constructor
  · rw [add_comm]; exact_mod_cast Nat.lt_succ_floor _
  · exact Nat.floor_le ((Nat.cast_nonneg' k).trans klv)

private lemma two_mul_n_add_six_lt : 2 * n + 6 < 2 ^ (n + 3) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      _ = 2 * n + 6 + 2 := by ring
      _ < 2 ^ (n + 3) + 2 := by gcongr
      _ < 2 ^ (n + 3) + 2 ^ (n + 3) := by omega
      _ = _ := by ring

lemma exists_k_n_j_of_mem_𝔓pos (h : p ∈ 𝔓pos (X := X)) :
    ∃ k n, k ≤ n ∧ (p ∈ 𝔏₀ k n ∨ ∃ j ≤ 2 * n + 3, p ∈ ℭ₁ k n j) := by
  obtain ⟨k, n, mp, hkn⟩ := exists_k_n_of_mem_𝔓pos h; use k, n, hkn
  rw [𝔓pos, mem_setOf, inter_comm _ G'ᶜ, ← inter_assoc] at h
  replace h : 0 < volume (G'ᶜ ∩ (𝓘 p : Set X)) := h.trans_le (measure_mono inter_subset_left)
  rw [inter_comm, G', compl_union, compl_union, inter_comm G₁ᶜ, ← inter_assoc, ← inter_assoc] at h
  replace h : 0 < volume ((𝓘 p : Set X) ∩ G₂ᶜ) :=
    h.trans_le (measure_mono (inter_subset_left.trans inter_subset_left))
  obtain ⟨x, mx, nx⟩ := nonempty_of_measure_ne_zero h.ne'
  simp_rw [G₂, mem_compl_iff, mem_iUnion] at nx; push_neg at nx; specialize nx n k hkn
  let B : ℕ := Finset.card { q | q ∈ 𝔅 k n p }
  have Blt : B < 2 ^ (2 * n + 4) := by
    calc
      _ ≤ Finset.card { m | m ∈ 𝔐 k n ∧ x ∈ 𝓘 m } :=
        Finset.card_le_card (Finset.monotone_filter_right _ (Pi.le_def.mpr fun m ⟨m₁, m₂⟩ ↦
          ⟨m₁, m₂.1.1 mx⟩))
      _ = stackSize (𝔐 k n) x := by
        simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
          Finset.filter_filter]; rfl
      _ ≤ (2 * n + 6) * 2 ^ (n + 1) := by rwa [setA, mem_setOf, not_lt] at nx
      _ < _ := by
        rw [show 2 * n + 4 = (n + 3) + (n + 1) by omega, pow_add _ (n + 3)]
        exact mul_lt_mul_of_pos_right two_mul_n_add_six_lt (by positivity)
  rcases B.eq_zero_or_pos with Bz | Bpos
  · simp_rw [B, filter_mem_univ_eq_toFinset, Finset.card_eq_zero, toFinset_eq_empty] at Bz
    exact Or.inl ⟨mp, Bz⟩
  · right; use Nat.log 2 B; rw [Nat.lt_pow_iff_log_lt one_lt_two Bpos.ne'] at Blt
    refine ⟨by omega, (?_ : _ ∧ _ ≤ B), (?_ : ¬(_ ∧ _ ≤ B))⟩
    · exact ⟨mp, Nat.pow_log_le_self 2 Bpos.ne'⟩
    · rw [not_and, not_le]; exact fun _ ↦ Nat.lt_pow_succ_log_self one_lt_two _

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₀ -/
def ℜ₀ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n), 𝔏₀ k n

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₁ -/
def ℜ₁ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3) (l ≤ Z * (n + 1)), 𝔏₁ k n j l

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₂ -/
def ℜ₂ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3), 𝔏₂ k n j

/-- The union occurring in the statement of Lemma 5.5.1 containing 𝔏₃ -/
def ℜ₃ : Set (𝔓 X) := 𝔓pos ∩ ⋃ (n : ℕ) (k ≤ n) (j ≤ 2 * n + 3) (l ≤ Z * (n + 1)), 𝔏₃ k n j l

/-- Lemma 5.5.1 -/
lemma antichain_decomposition : 𝔓pos (X := X) ∩ 𝔓₁ᶜ ⊆ ℜ₀ ∪ ℜ₁ ∪ ℜ₂ ∪ ℜ₃ := by
  unfold ℜ₀ ℜ₁ ℜ₂ ℜ₃; simp_rw [← inter_union_distrib_left]; intro p ⟨h, mp'⟩
  refine ⟨h, ?_⟩; simp_rw [mem_union, mem_iUnion, or_assoc]
  have nG₃ : ¬(𝓘 p : Set X) ⊆ G₃ := by
    suffices ¬(𝓘 p : Set X) ⊆ G' by contrapose! this; exact subset_union_of_subset_right this _
    by_contra hv
    rw [𝔓pos, mem_setOf, inter_comm _ G'ᶜ, ← inter_assoc, ← diff_eq_compl_inter,
      diff_eq_empty.mpr hv] at h
    simp at h
  obtain ⟨k, n, hkn, mp⟩ := exists_k_n_j_of_mem_𝔓pos h
  rcases mp with ml0 | ⟨j, hj, mc1⟩
  · exact Or.inl ⟨n, k, hkn, ml0⟩
  · right; by_cases mc2 : p ∉ ℭ₂ k n j
    · simp_rw [ℭ₂, layersAbove, mem_diff, not_and, mc1, true_implies, not_not_mem] at mc2
      simp_rw [mem_iUnion] at mc2; obtain ⟨l, hl, f⟩ := mc2
      exact Or.inl ⟨n, k, hkn, j, hj, l, hl, f⟩
    · right; rw [not_not_mem] at mc2; by_cases ml2 : p ∈ 𝔏₂ k n j
      · exact Or.inl ⟨n, k, hkn, j, hj, ml2⟩
      · have mc3 : p ∈ ℭ₃ k n j := ⟨mc2, ml2⟩
        right; by_cases mc4 : p ∉ ℭ₄ k n j
        · simp_rw [ℭ₄, layersBelow, mem_diff, not_and, mc3, true_implies, not_not_mem] at mc4
          simp_rw [mem_iUnion] at mc4; obtain ⟨l, hl, f⟩ := mc4
          exact ⟨n, k, hkn, j, hj, l, hl, f⟩
        · apply absurd mp'; simp_rw [mem_compl_iff, not_not_mem, 𝔓₁, mem_iUnion]
          refine ⟨n, k, hkn, j, hj, not_not_mem.mp mc4, ?_⟩
          contrapose! nG₃
          exact le_iSup₂_of_le n k <| le_iSup₂_of_le hkn j <| le_iSup₂_of_le hj p <|
            le_iSup_of_le nG₃ subset_rfl

/-- The subset `𝔏₀(k, n, l)` of `𝔏₀(k, n)`, given in Lemma 5.5.3.
  We use the name `𝔏₀'` in Lean. The indexing is off-by-one w.r.t. the blueprint -/
def 𝔏₀' (k n l : ℕ) : Set (𝔓 X) := (𝔏₀ k n).minLayer l

/-- Part of Lemma 5.5.2 -/
lemma iUnion_L0' : ⋃ (l ≤ n), 𝔏₀' (X := X) k n l = 𝔏₀ k n := by
  refine iUnion_minLayer_iff_bounded_series.mpr fun p ↦ ?_
  sorry

/-- Part of Lemma 5.5.2 -/
lemma pairwiseDisjoint_L0' : univ.PairwiseDisjoint (𝔏₀' (X := X) k n) := pairwiseDisjoint_minLayer

/-- Part of Lemma 5.5.2 -/
lemma antichain_L0' : IsAntichain (· ≤ ·) (𝔏₀' (X := X) k n l) := isAntichain_minLayer

section L2Antichain

/-- Type synonym of `ℭ₁` to apply the `Preorder` of the proof of Lemma 5.5.3 on. -/
private def ℭ₁' (k n j : ℕ) : Type _ := ℭ₁ (X := X) k n j

private instance : Fintype (ℭ₁' (X := X) k n j) := inferInstanceAs (Fintype (ℭ₁ k n j))

private instance : Preorder (ℭ₁' (X := X) k n j) where
  le x y := smul 200 x.1 ≤ smul 200 y.1
  le_refl := by simp
  le_trans _ _ _ xy yz := by
    change smul _ _ ≤ smul _ _ at xy yz ⊢
    exact xy.trans yz

/-- Lemma 5.5.3 -/
lemma antichain_L2 : IsAntichain (· ≤ ·) (𝔏₂ (X := X) k n j) := by
  by_contra h; rw [isAntichain_iff_forall_not_lt] at h; push_neg at h
  obtain ⟨p', mp', p, mp, l⟩ := h
  have p200 : smul 2 p' ≤ smul 200 p := by
    calc
      _ ≤ smul (11 / 10 + C2_1_2 a * 200) p' := by
        apply smul_mono_left
        calc
          _ ≤ 11 / 10 + 1 / 512 * (200 : ℝ) := by gcongr; exact C2_1_2_le_inv_512 X
          _ ≤ _ := by norm_num
      _ ≤ _ := by
        refine smul_C2_1_2 _ (by norm_num) ?_ (wiggle_order_11_10 l.le (C5_3_3_le (X := X)))
        apply not_lt_of_𝓘_eq_𝓘.mt; rwa [not_not]
  have cp : p ∈ ℭ₁ k n j := (𝔏₂_subset_ℭ₂.trans ℭ₂_subset_ℭ₁) mp
  let C : Finset (LTSeries (ℭ₁' k n j)) := { s | s.head = ⟨p, cp⟩ }
  have Cn : C.Nonempty := by
    use RelSeries.singleton _ ⟨p, cp⟩
    simp_rw [C, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  obtain ⟨z, mz, maxz⟩ := C.exists_max_image (·.length) Cn
  simp_rw [C, Finset.mem_filter, Finset.mem_univ, true_and] at mz
  by_cases mu : z.last.1 ∈ 𝔘₁ k n j
  · have px : z.head ≤ z.last := z.monotone (Fin.zero_le _)
    rw [mz] at px
    apply absurd mp'; rw [𝔏₂, mem_setOf, not_and_or, not_not]; right; use z.last.1, mu
    have : 𝓘 p' < 𝓘 p := lt_of_le_of_ne l.le.1 (not_lt_of_𝓘_eq_𝓘.mt (by rwa [not_not]))
    exact ⟨(this.trans_le px.1).ne, (p200.trans px).trans (smul_mono_left (by norm_num))⟩
  · simp_rw [𝔘₁, mem_setOf, not_and, z.last.2, true_implies, not_forall, exists_prop] at mu
    obtain ⟨q, mq, lq, ndjq⟩ := mu; rw [not_disjoint_iff] at ndjq; obtain ⟨ϑ, mϑ₁, mϑ₂⟩ := ndjq
    have cpos : 0 < C2_1_2 a := by rw [C2_1_2]; positivity
    have s200 : smul 200 z.last.1 ≤ smul 200 q := by
      refine ⟨lq.le, (?_ : ball_(q) (𝒬 q) 200 ⊆ ball_(z.last.1) (𝒬 z.last.1) 200)⟩
      intro (r : Θ X) mr
      rw [@mem_ball] at mr mϑ₁ mϑ₂ ⊢
      calc
        _ ≤ dist_(z.last.1) r (𝒬 q) + dist_(z.last.1) (𝒬 q) ϑ + dist_(z.last.1) ϑ (𝒬 z.last.1) :=
          dist_triangle4 ..
        _ ≤ C2_1_2 a * dist_(q) r (𝒬 q) + C2_1_2 a * dist_(q) (𝒬 q) ϑ + 100 := by
          gcongr <;> exact Grid.dist_strictMono lq
        _ ≤ C2_1_2 a * (200 + 100) + 100 := by rw [mul_add]; gcongr; rw [dist_comm]; exact mϑ₂.le
        _ ≤ (1 / 512) * 300 + 100 := by
          rw [show (200 : ℝ) + 100 = 300 by norm_num]; gcongr
          exact C2_1_2_le_inv_512 X
        _ < _ := by norm_num
    have : z.last < ⟨q, mq⟩ := by
      refine ⟨s200, (?_ : ¬(smul 200 q ≤ smul 200 z.last.1))⟩
      rw [TileLike.le_def, not_and_or]; exact Or.inl (not_le_of_gt lq)
    apply absurd maxz; push_neg; use z.snoc ⟨q, mq⟩ this, by simp [C, mz], by simp

end L2Antichain

/-- Part of Lemma 5.5.4 -/
lemma antichain_L1 : IsAntichain (· ≤ ·) (𝔏₁ (X := X) k n j l) := isAntichain_minLayer

/-- Part of Lemma 5.5.4 -/
lemma antichain_L3 : IsAntichain (· ≤ ·) (𝔏₃ (X := X) k n j l) := isAntichain_maxLayer

/-- The constant used in Lemma 5.1.3, with value `2 ^ (210 * a ^ 3) / (q - 1) ^ 5` -/
-- todo: redefine in terms of other constants
def C5_1_3 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (210 * a ^ 3) / (q - 1) ^ 5

lemma C5_1_3_pos : C5_1_3 a nnq > 0 := sorry

lemma forest_complement {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
  ∫⁻ x in G \ G', ‖∑ p ∈ { p | p ∉ 𝔓₁ }, carlesonOn p f x‖₊ ≤
    C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹  := by
  sorry

/-! ## Proposition 2.0.2 -/

/-- The constant used in Proposition 2.0.2,
which has value `2 ^ (440 * a ^ 3) / (q - 1) ^ 5` in the blueprint. -/
def C2_0_2 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := C5_1_2 a q + C5_1_3 a q

lemma C2_0_2_pos : C2_0_2 a nnq > 0 := add_pos C5_1_2_pos C5_1_3_pos

variable (X) in
theorem discrete_carleson :
    ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖∑ p, carlesonOn p f x‖₊ ≤
    C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by sorry
