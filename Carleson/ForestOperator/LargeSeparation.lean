import Carleson.ForestOperator.AlmostOrthogonality

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.5 -/

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := 𝓙 (𝔖₀ t u₁ u₂) ∩ Iic (𝓘 u₁)

/-- The definition of χ-tilde, defined in the proof of Lemma 7.5.2 -/
def χtilde (J : Grid X) (x : X) : ℝ≥0 :=
  8 - D ^ (- s J) * dist x (c J) |>.toNNReal

variable (t u₁ u₂) in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J x / ∑ J' ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χtilde J' x

-- /-- The definition of `B`, defined in (7.5.1) -/
-- protected def _root_.Grid.ball (I : Grid X) : Set X := ball (c I) (8 * D ^ s I)

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ)  (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

/-- Part of Lemma 7.5.1. -/
lemma union_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    ⋃ J ∈ 𝓙₅ t u₁ u₂, (J : Set X) = 𝓘 u₁ := by
  sorry

/-- Part of Lemma 7.5.1. -/
lemma pairwiseDisjoint_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
  (h : ¬ Disjoint (J : Set X) J') : s J + 1 ≤ s J' := by
  sorry

/-- The constant used in `dist_χ_χ_le`.
Has value `2 ^ (226 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_2 (a : ℕ) : ℝ≥0 := 2 ^ (226 * (a : ℝ) ^ 3)

/-- Part of Lemma 7.5.2. -/
lemma sum_χ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (x : X) :
    ∑ J ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χ t u₁ u₂ J x = (𝓘 u₁ : Set X).indicator 1 x := by
  sorry

/-- Part of Lemma 7.5.2. -/
lemma χ_mem_Icc (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hx : x ∈ 𝓘 u₁) :
    χ t u₁ u₂ J x ∈ Icc 0 ((ball (c I) (8 * D ^ s I)).indicator 1 x) := by
  sorry

/-- Part of Lemma 7.5.2. -/
lemma dist_χ_χ_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hx : x ∈ 𝓘 u₁) (hx' : x' ∈ 𝓘 u₁) :
    dist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x) ≤ C7_5_2 a * dist x x' / D ^ s J := by
  sorry


/-! ### Subsection 7.5.2 and Lemma 7.5.4 -/

/-- The constant used in `holder_correlation_tile`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_5 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.5.5. -/
lemma holder_correlation_tile (hu : u ∈ t) (hp : p ∈ t u)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    nndist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
      (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
    (nndist x x' / D ^ (𝔰 p : ℝ)) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖₊ := by
  sorry

/-- Lemma 7.5.6. -/
lemma limited_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ∈ Icc (s J) (s J + 3) := by
  sorry

/-- The constant used in `local_tree_control`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_7 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.5.7. -/
lemma local_tree_control (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    C7_5_7 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

lemma calculations (d : ℝ) (s sFancy : ℤ) (h1: sFancy < s) (h2: 1 < d) : 8 * d ^ (s : ℝ) + 8 * d ^ (sFancy : ℝ) < 16 * d ^ s := by
  have woah : 8 * d ^ s + 8 * d ^ sFancy < 16 * d ^ s := by
    calc 8 * d ^ s + 8 * d ^ sFancy
      _ < 8 * d ^ s + 8 * d ^ s := by
          gcongr
          exact h2
      _ = 16 * d ^ s := by
        rw [← Real.commRing.proof_8]
        norm_num
  norm_cast

lemma calcme (d : ℝ) (n m : ℤ) (h1: m < n) (h2: 1 < d) : 4 * d ^ m + 16 * d ^ n < 100 * d ^ (n + 1) := by
  have help_1 : 0 < d := by positivity
  have help_3 : 0 < d ^ (n : ℝ) := by positivity

  have hey :  d ^ n > d ^ m := by
    gcongr
    exact h2

  have yes : 25 * d - 4 > 1 := by linarith

  have aha : d ^ n * (25 * d - 4) > d ^ n := by
    have sure := lt_mul_left (ha := help_3) (b := (25 * d - 4)) yes
    apply LT.lt.gt
    norm_cast at sure
    linarith

  have lets := gt_trans aha hey

  have h_pos : 0 < (4 : ℝ) := by norm_num
  have h_div := div_lt_div_right h_pos (a := 4 * d ^ m + 16 * d ^ n) (b := 100 * d ^ (n + 1))
  apply h_div.mp

  ring_nf

  clear h_div h_pos

  let theor := lt_tsub_iff_left (a := d ^ m) (b := d ^ (1 + n) * 25) (c := d ^ n * 4)
  rewrite (config := {occs := .pos [2]}) [add_comm] at theor

  apply theor.mp
  clear theor

  clear aha

  have letsss := GT.gt.lt lets
  clear lets

  have th := mul_sub (a := d ^ n) (b := 25 * d) (c := 4)
  rw [th] at letsss
  clear th

  have well := mul_comm 25 d
  rw [well] at letsss
  clear well

  have well := mul_assoc (a := d ^ n) (b := d) (c := 25)
  rw [← well] at letsss
  clear well

  have powers := Real.rpow_add help_1 (x := d) (y := n) (z := 1)
  rewrite (config := {occs := .pos [3]}) [← Real.rpow_one d] at letsss
  norm_cast at powers

  rw [add_comm]
  rw [powers]

  norm_cast at letsss

lemma smallerThan16
  (middleX : X)
  (xxx: dist middleX (𝔠 p) < 8 * (2 ^ (100 * a ^ 2)) ^ 𝔰 p)
  (yyy: dist middleX (c J) < 8 * (2 ^ (100 * a ^ 2)) ^ s J)
  (contr: 𝔰 p < s J)
  : dist (𝔠 p) (c J) < 16 * ↑D ^ s J := by
  calc dist (𝔠 p) (c J)
    _ ≤ dist middleX (𝔠 p) + dist middleX (c J) := by
      rewrite (config := {occs := .pos [2]}) [dist_comm]
      apply dist_triangle (𝔠 p) middleX (c J)
    _ < 8 * (2 ^ (100 * a ^ 2)) ^ 𝔰 p + 8 * (2 ^ (100 * a ^ 2)) ^ s J := by
      exact add_lt_add xxx yyy
    _ = 8 * ↑D ^ 𝔰 p + 8 * ↑D ^ s J := by
      have hD : (D : ℝ) = 2 ^ (100 * a^2) := by simp
      rw [← hD]
    _ < 16 * ↑D ^ s J := by
      have well := calculations D (s J) (𝔰 p) contr (one_lt_D (X := X))
      norm_cast at well
      rw [add_comm] at well
      exact well

/-- Lemma 7.5.8. -/
lemma scales_impacting_interval (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
  (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
  (hp : p ∈ (t u₁ ∪ (t u₂ ∩ 𝔖₀ t u₁ u₂)))
  (h : ¬ Disjoint
        (ball (𝔠 p) (8 * D ^ 𝔰 p))
        (ball (c J) (8 * D ^ s J))
  )
  : s J ≤ 𝔰 p := by
  rcases hJ with ⟨hJ_left, _nothing⟩
  apply 𝓙_subset_𝓙₀ at hJ_left
  apply Set.mem_or_mem_of_mem_union at hp

  have belongs : p ∈ t.𝔖₀ u₁ u₂ := by
    cases' hp with hi hello
    exact 𝔗_subset_𝔖₀ hu₁ hu₂ hu h2u hi
    exact Set.mem_of_mem_inter_right hello

  cases' hJ_left with wow hm

  have bound_i : -S ≤ 𝔰 p ∧ 𝔰 p ≤ S := scale_mem_Icc
  cases' bound_i with aaa bbbb
  rw [←wow] at aaa
  exact aaa



  --
  --
  -- We only need to refactor stuff below this line
  --
  --
  have hmm := hm p belongs
  clear hm

  rw [not_subset] at hmm
  rcases hmm with ⟨ x, ⟨ xInTile, xNotInBall ⟩ ⟩

  by_contra contr
  apply lt_of_not_ge at contr

  clear hp _nothing
  simp [not_disjoint_iff] at h
  rcases h with ⟨middleX, ⟨xxx, yyy⟩⟩

  have smallerThan16 := smallerThan16 middleX xxx yyy contr



  rw [Metric.mem_ball' (y := x) (ε := 100 * ↑D ^ (s J + 1)) (x := (c J))] at xNotInBall

  have interesting := Grid_subset_ball (X := X) (i := 𝓘 p)
  rw [subset_def] at interesting
  have interestingWithX := interesting x xInTile
  clear interesting

  have betterTheorem := Metric.mem_ball' (y := x) (x := 𝔠 p) (ε := 4 * ↑D ^ 𝔰 p)

  have x_and_p_arePrettyClose := betterTheorem.mp interestingWithX

  clear interestingWithX betterTheorem

  rw [dist_comm] at x_and_p_arePrettyClose

  have triangle : dist x (c J) ≤ dist x (𝔠 p) + dist (𝔠 p) (c J) := by
    exact dist_triangle (x := x) (y := 𝔠 p) (z := c J)

  have numbers : dist x (𝔠 p) + dist (𝔠 p) (c J) < 4 * ↑D ^ 𝔰 p + 16 * ↑D ^ s J := by
    exact add_lt_add x_and_p_arePrettyClose smallerThan16

  have rrr := trans triangle numbers
  clear numbers triangle x_and_p_arePrettyClose smallerThan16
  rw [dist_comm] at rrr
  have result := calcme D (s J) (𝔰 p) contr (one_lt_D (X := X))
  have blue := Trans.trans rrr result

  exact xNotInBall blue

/-- The constant used in `global_tree_control1_1`.
Has value `2 ^ (154 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_9_1 (a : ℕ) : ℝ≥0 := 2 ^ (154 * (a : ℝ) ^ 3)

/-- The constant used in `global_tree_control1_2`.
Has value `2 ^ (153 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_9_2 (a : ℕ) : ℝ≥0 := 2 ^ (153 * (a : ℝ) ^ 3)

/-- Part 1 of Lemma 7.5.9 -/
lemma global_tree_control1_1 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊) +
    C7_5_9_1 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- Part 2 of Lemma 7.5.9 -/
lemma global_tree_control1_2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f)
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
    nndist (exp (.I * 𝒬 u x) * adjointCarlesonSum ℭ f x)
      (exp (.I * 𝒬 u x') * adjointCarlesonSum ℭ f x') ≤
    C7_5_9_1 a * (nndist x x' / D ^ (𝔰 p : ℝ)) ^ (a : ℝ)⁻¹ *
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- The constant used in `global_tree_control2`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_10 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- Lemma 7.5.10 -/
lemma global_tree_control2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : AEStronglyMeasurable f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    ⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖₊ +
    C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- The constant used in `holder_correlation_tree`.
Has value `2 ^ (535 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_4 (a : ℕ) : ℝ≥0 := 2 ^ (535 * (a : ℝ) ^ 3)

/-- Lemma 7.5.4. -/
lemma holder_correlation_tree (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    HolderOnWith (C7_5_4 a *
    ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖₊) +
    (⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f₁ ·‖) x).toNNReal) *
    ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖₊) +
    (⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f₂ ·‖) x).toNNReal))
    nnτ (holderFunction t u₁ u₂ f₁ f₂ J) (ball (c J) (8 * D ^ s J)) := by
  sorry


/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/

/-- The constant used in `lower_oscillation_bound`.
Has value `2 ^ (Z * n / 2 - 201 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_11 (a n : ℕ) : ℝ≥0 := 2 ^ (Z * n / 2 - 201 * (a : ℝ) ^ 3)

/-- Lemma 7.5.11 -/
lemma lower_oscillation_bound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    C7_5_11 a n ≤ dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
  sorry

/-- The constant used in `correlation_distant_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_5 (a n : ℕ) : ℝ≥0 := 2 ^ (541 * (a : ℝ) ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))

/-- Lemma 7.4.5 -/
lemma correlation_distant_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

end TileStructure.Forest
