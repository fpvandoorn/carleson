import Carleson.TwoSidedCarleson.Basic
import Carleson.ToMathlib.HardyLittlewood

open MeasureTheory Set Bornology Function ENNReal Metric Filter Topology
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable {f : X → ℂ} {α : ℝ≥0∞}

/-! ## Section 10.2 and Lemma 10.0.3

Question: -/

/-- The constant used in `nontangential_from_simple`.
I(F) think the constant needs to be fixed in the blueprint. -/
irreducible_def C10_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (4 * a)

/-- Lemma 10.2.1, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem maximal_theorem [Nonempty X] :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  apply HasWeakType.hasBoundedWeakType
  have : C10_2_1 a = C_weakType_globalMaximalFunction (defaultA a) 1 1 := by
    unfold C_weakType_globalMaximalFunction C_weakType_maximalFunction
    split_ifs with h; swap; simp at h
    simp_rw [C10_2_1_def, defaultA, coe_pow, coe_ofNat, Nat.cast_pow, Nat.cast_ofNat,
        NNReal.coe_one, div_one, rpow_ofNat, pow_mul', ← npow_add,
        two_add_two_eq_four]; rfl
  rw [this]
  apply hasWeakType_globalMaximalFunction (μ := volume) le_rfl le_rfl

-- Lemma 10.2.1, as formulated in the blueprint
variable (α) in
private theorem maximal_theorem' [Nonempty X] (hf : BoundedFiniteSupport f) :
    α * volume {x | α < ‖globalMaximalFunction volume 1 f x‖ₑ} ≤
    (C10_2_1 a) * eLpNorm f 1 volume := by
  by_cases hα : α = ∞
  · simp [hα]
  have h := (maximal_theorem f hf).2
  simp only [wnorm, one_ne_top, reduceIte, wnorm', toReal_one, inv_one, rpow_one, iSup_le_iff] at h
  exact coe_toNNReal hα ▸ h α.toNNReal

-- Alternate version of `maximal_theorem'`
private theorem maximal_theorem'' [Nonempty X] (hα : α > 0) (hf : BoundedFiniteSupport f) :
    volume {x | α < ‖globalMaximalFunction volume 1 f x‖ₑ} ≤
    (C10_2_1 a) * eLpNorm f 1 volume / α := by
  by_cases α_top : α = ∞
  · simp [α_top]
  apply ENNReal.le_div_iff_mul_le (Or.inl hα.ne') (Or.inl α_top) |>.mpr
  exact mul_comm α _ ▸ maximal_theorem' α hf

variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-- Lemma 10.2.2.
Should be an easy consequence of `VitaliFamily.ae_tendsto_average`. -/
theorem lebesgue_differentiation
    {f : X → ℂ} (hf : BoundedFiniteSupport f) :
    ∀ᵐ x ∂volume, ∃ (c : ℕ → X) (r : ℕ → ℝ),
    Tendsto (fun i ↦ ⨍ y in ball (c i) (r i), f y ∂volume) atTop (𝓝 (f x)) ∧
    Tendsto r atTop (𝓝[>] 0) ∧
    ∀ i, x ∈ ball (c i) (r i) := by
  sorry


/-! Lemma 10.2.3 is in Mathlib: `Pairwise.countable_of_isOpen_disjoint`. -/

/-- Lemma 10.2.4
This is very similar to `Vitali.exists_disjoint_subfamily_covering_enlargement`.
Can we use that (or adapt it so that we can use it)? -/
theorem ball_covering (ha : 4 ≤ a) {O : Set X} (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ closedBall (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, ¬ Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, Cardinal.mk { i | x ∈ ball (c i) (3 * r i)} ≤ (2 ^ (6 * a) : ℕ) := by
  sorry

/-! ### Lemma 10.2.5

Lemma 10.2.5 has an annoying case distinction between the case `E_α ≠ X` (general case) and
`E_α = X` (finite case). It isn't easy to get rid of this case distinction.

In the formalization we state most properties of Lemma 10.2.5 twice, once for each case
(in some cases the condition is vacuous in the finite case, and then we omit it)

We could have tried harder to uniformize the cases, but in the finite case there is really only set
`B*_j`, and in the general case it is convenient to index `B*_j` by the natural numbers.
-/

/-- The property specifying whether we are in the "general case". -/
def GeneralCase (f : X → ℂ) (α : ℝ≥0∞) : Prop :=
  ∃ x, α ≥ globalMaximalFunction (X := X) volume 1 f x

omit [IsCancellative X (defaultτ a)] in
/-- In the finite case, the volume of `X` is finite. -/
lemma volume_lt_of_not_GeneralCase (hf : BoundedFiniteSupport f) (h : ¬ GeneralCase f α)
    (hα : 0 < α) : volume (univ : Set X) < ∞ := by
  simp only [GeneralCase, not_exists, not_le] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hα.ne'
  refine lt_of_le_of_lt (eq_univ_iff_forall.mpr h ▸ maximal_theorem' α hf) ?_ |>.ne
  exact mul_lt_top coe_lt_top (hf.memLp 1).eLpNorm_lt_top

omit [IsCancellative X (defaultτ a)] in
private lemma isFiniteMeasure_finite (hf : BoundedFiniteSupport f) (h : ¬ GeneralCase f α)
    (hα : 0 < α) : IsFiniteMeasure (volume : Measure X) :=
  (isFiniteMeasure_iff _).mpr <| volume_lt_of_not_GeneralCase hf h hα

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
lemma isOpen_MB_preimage_Ioi (hX : GeneralCase f α) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α) ∧
    globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ :=
  have ⟨x, hx⟩ := hX
  ⟨lowerSemiContinuous_globalMaximalFunction.isOpen_preimage _,
    (ne_univ_iff_exists_notMem _).mpr ⟨x, by simpa using hx⟩⟩

/-- The center of B_j in the proof of Lemma 10.2.5 (general case). -/
def czCenter (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : X :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose i

/-- The radius of B_j in the proof of Lemma 10.2.5 (general case). -/
def czRadius (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : ℝ :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose i

/-- The ball B_j in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (czRadius ha hX i)

/-- The ball B_j' introduced below Lemma 10.2.5 (general case). -/
abbrev czBall2 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (2 * czRadius ha hX i)

/-- The ball B_j* in Lemma 10.2.5 (general case). -/
abbrev czBall3 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (3 * czRadius ha hX i)

/-- The ball B_j** in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall7 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (7 * czRadius ha hX i)

lemma czBall_pairwiseDisjoint (ha : 4 ≤ a) {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ closedBall (czCenter ha hX i) (czRadius ha hX i) :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.1

lemma iUnion_czBall3 (ha : 4 ≤ a) (hX : GeneralCase f α) :
    ⋃ i, czBall3 ha hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_czBall7 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    ¬ Disjoint (czBall7 ha hX i) (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.1 i

private lemma czRadius_pos (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : 0 < czRadius ha hX i := by
  suffices (ball (czCenter ha hX i) (7 * czRadius ha hX i)).Nonempty by
    have := this.ne_empty; contrapose! this; exact Metric.ball_eq_empty.mpr (by linarith)
  have ⟨x, hx⟩ := not_disjoint_iff.mp <| not_disjoint_czBall7 ha hX i
  exact ⟨x, hx.1⟩

private lemma czRadius_ineq {ha : 4 ≤ a} {hX : GeneralCase f α} {i : ℕ} {b c : ℝ}
    (hbc : b ≤ c := by norm_num) : b * czRadius ha hX i ≤ c * czRadius ha hX i :=
  mul_le_mul_iff_of_pos_right (czRadius_pos ha hX i) |>.mpr hbc

/-- Part of Lemma 10.2.5 (general case). -/
lemma cardinalMk_czBall3_le (ha : 4 ≤ a) {hX : GeneralCase f α}
    {y : X} (hy : α < globalMaximalFunction volume 1 f y) :
    Cardinal.mk { i | y ∈ czBall3 ha hX i} ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.2 y hy

lemma mem_czBall3_finite (ha : 4 ≤ a) {hX : GeneralCase f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    { i | y ∈ czBall3 ha hX i}.Finite := by
  rw [← Cardinal.lt_aleph0_iff_set_finite]
  exact lt_of_le_of_lt (cardinalMk_czBall3_le ha hy) (Cardinal.nat_lt_aleph0 _)

/-- `Q_i` in the proof of Lemma 10.2.5 (general case). -/
def czPartition (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  czBall3 ha hX i \ ((⋃ j < i, czPartition ha hX j) ∪ ⋃ j > i, czBall ha hX j)

@[measurability]
private lemma MeasurableSet.czPartition (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    MeasurableSet (czPartition ha hX i) := by
  refine i.strong_induction_on (fun j hj ↦ ?_)
  unfold _root_.czPartition
  apply measurableSet_ball.diff ∘ (MeasurableSet.biUnion (to_countable _) hj).union
  exact MeasurableSet.biUnion (to_countable _) (fun _ _ ↦ measurableSet_ball)

lemma czBall_subset_czPartition (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    czBall ha hX i ⊆ czPartition ha hX i := by
  intro r hr
  rw [mem_ball] at hr
  unfold czPartition
  refine mem_diff_of_mem ?_ ?_
  · rw [mem_ball]; linarith [czRadius_pos ha hX i]
  simp only [mem_union, mem_iUnion, mem_ball, not_or, not_exists, not_lt]
  refine ⟨?_, fun j hj ↦ by
    refine le_of_not_ge (disjoint_left.mp (czBall_pairwiseDisjoint ha ?_ ?_ hj.ne) hr.le) <;> tauto⟩
  unfold czPartition
  simp only [mem_diff, mem_ball, mem_union, mem_iUnion, not_or, not_and, not_not]
  exact fun _ _ _ _ ↦ by use i

lemma czPartition_subset_czBall3 (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    czPartition ha hX i ⊆ czBall3 ha hX i := by
  rw [czPartition]; exact diff_subset

private lemma czPartition_subset_czBall7 (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    czPartition ha hX i ⊆ czBall7 ha hX i :=
  (czPartition_subset_czBall3 ha).trans <| ball_subset_ball <| czRadius_ineq

lemma czPartition_pairwiseDisjoint (ha : 4 ≤ a) {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ czPartition ha hX i := by
  simp only [pairwiseDisjoint_iff, mem_univ, forall_const]
  intro i k hik
  have ⟨x, hxi, hxk⟩ := inter_nonempty.mp hik
  have (t d) (hx : x ∈ czPartition ha hX t) (hd : t < d) : x ∉ czPartition ha hX d := by
    have : czPartition ha hX t ⊆ ⋃ j < d, czPartition ha hX j := subset_biUnion_of_mem hd
    rw [czPartition]
    exact notMem_diff_of_mem <| mem_union_left _ (this hx)
  have : _ ∧ _ := ⟨this i k hxi |>.mt (· hxk), this k i hxk |>.mt (· hxi)⟩
  omega

lemma czPartition_pairwiseDisjoint' (ha : 4 ≤ a) {hX : GeneralCase f α}
    {x : X} {i j : ℕ} (hi : x ∈ czPartition ha hX i) (hj : x ∈ czPartition ha hX j) :
    i = j := by
  have := czPartition_pairwiseDisjoint ha (hX := hX)
  apply pairwiseDisjoint_iff.mp this (mem_univ i) (mem_univ j)
  exact inter_nonempty.mp <| .intro x ⟨hi, hj⟩

private lemma czPartition_pairwise_disjoint_on (ha : 4 ≤ a) {hX : GeneralCase f α} :
    Pairwise (Disjoint on czPartition ha hX) :=
  fun i j ↦ czPartition_pairwiseDisjoint ha (mem_univ i) (mem_univ j)

lemma iUnion_czPartition (ha : 4 ≤ a) {hX : GeneralCase f α} :
    ⋃ i, czPartition ha hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α := by
  rw [← iUnion_czBall3 ha hX]
  refine ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have : ⋃ i, czPartition ha hX i ⊆ ⋃ i, czBall3 ha hX i := fun y hy ↦
      have ⟨r, hr⟩ := mem_iUnion.mp hy
      mem_iUnion_of_mem r (czPartition_subset_czBall3 ha hr)
    exact this hx
  · rw [mem_iUnion] at hx ⊢
    by_contra! hp
    obtain ⟨g, hg⟩ := hx
    have ⟨t, ht⟩ : ∃ i, x ∈ (⋃ j < i, czPartition ha hX j) ∪ ⋃ j > i, czBall ha hX j := by
      by_contra! hb
      absurd hp g
      rw [czPartition, mem_diff]
      exact ⟨hg, hb g⟩
    have : ⋃ j > t, czBall ha hX j ⊆ ⋃ j > t, czPartition ha hX j :=
      iUnion₂_mono fun i j ↦ czBall_subset_czPartition ha (i := i)
    have := (mem_or_mem_of_mem_union ht).imp_right (this ·)
    simp_all

private lemma volume_czPartition_lt_top (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    volume (czPartition ha hX i) < ∞ :=
  lt_of_le_of_lt (measure_mono <| czPartition_subset_czBall3 ha) measure_ball_lt_top

private lemma volume_czBall7_le (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    volume (czBall7 ha hX i) ≤ 2 ^ (3 * a) * volume (czPartition ha hX i) := calc
  _ ≤ volume (ball (czCenter ha hX i) (2 ^ 3 * czRadius ha hX i)) :=
    measure_mono <| ball_subset_ball czRadius_ineq
  _ ≤ (defaultA a) ^ 3 * volume (ball (czCenter ha hX i) (czRadius ha hX i)) :=
    measure_ball_two_le_same_iterate _ _ 3
  _ ≤ _ := by rw [Nat.cast_pow, ← pow_mul, mul_comm a 3]; gcongr; exact czBall_subset_czPartition ha

private lemma volume_czBall3_le (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    volume (czBall3 ha hX i) ≤ 2 ^ (2 * a) * volume (czBall ha hX i) := calc
  _ ≤ volume (ball (czCenter ha hX i) (2 ^ 2 * czRadius ha hX i)) :=
    measure_mono <| ball_subset_ball czRadius_ineq
  _ ≤ 2 ^ (2 * a) * volume (czBall ha hX i) :=
    le_of_le_of_eq (measure_ball_two_le_same_iterate _ _ 2) <| by simp [← pow_mul, mul_comm a 2]

-- Inequality (10.2.30)
private lemma laverage_czBall7_le (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    ⨍⁻ x in czBall7 ha hX i, ‖f x‖ₑ ∂volume ≤ α := by
  have ⟨y, hy7, hy⟩ := not_disjoint_iff.mp <| not_disjoint_czBall7 ha hX i
  simp only [mem_compl_iff, mem_preimage, Nat.cast_pow, Nat.cast_ofNat, mem_Ioi, not_lt] at hy
  refine le_trans ?_ hy
  simpa using laverage_le_globalMaximalFunction (μ := volume) hy7

open scoped Classical in
variable (f) in
/-- The function `g` in Lemma 10.2.5. (both cases) -/
def czApproximation (ha : 4 ≤ a) (α : ℝ≥0∞) (x : X) : ℂ :=
  if hX : GeneralCase f α then
    if hx : ∃ j, x ∈ czPartition ha hX j then ⨍ y in czPartition ha hX hx.choose, f y else f x
  else ⨍ y, f y

lemma czApproximation_def_of_mem (ha : 4 ≤ a) {hX : GeneralCase f α} {x : X}
    {i : ℕ} (hx : x ∈ czPartition ha hX i) :
    czApproximation f ha α x = ⨍ y in czPartition ha hX i, f y := by
  have : ∃ i, x ∈ czPartition ha hX i := ⟨i, hx⟩
  simp [czApproximation, hX, this, czPartition_pairwiseDisjoint' ha this.choose_spec hx]

lemma czApproximation_def_of_notMem (ha : 4 ≤ a) {x : X} (hX : GeneralCase f α)
    (hx : x ∉ globalMaximalFunction volume 1 f ⁻¹' Ioi α) :
    czApproximation f ha α x = f x := by
  rw [← iUnion_czPartition ha (hX := hX), mem_iUnion, not_exists] at hx
  simp only [czApproximation, hX, ↓reduceDIte, hx, exists_const]

lemma czApproximation_def_of_volume_lt (ha : 4 ≤ a) {x : X}
    (hX : ¬ GeneralCase f α) : czApproximation f ha α x = ⨍ y, f y := by
  simp [czApproximation, hX]

private lemma lintegral_czPartition_le (ha : 4 ≤ a) {hX : GeneralCase f α} (i : ℕ) :
    ∫⁻ x in czPartition ha hX i, ‖czApproximation f ha α x‖ₑ ≤
    ∫⁻ x in czPartition ha hX i, ‖f x‖ₑ := calc
  _ = ∫⁻ x in czPartition ha hX i, ‖⨍ y in czPartition ha hX i, f y‖ₑ := by
    apply setLIntegral_congr_fun (MeasurableSet.czPartition ha hX i)
    exact Eventually.of_forall fun x hx ↦ by rw [czApproximation_def_of_mem ha hx]
  _ = ‖⨍ y in czPartition ha hX i, f y‖ₑ * volume (czPartition ha hX i) := setLIntegral_const _ _
  _ ≤ (⨍⁻ y in czPartition ha hX i, ‖f y‖ₑ ∂volume) * volume (czPartition ha hX i) :=
    mul_le_mul_right' (enorm_integral_le_lintegral_enorm f) _
  _ = _ := by rw [mul_comm, measure_mul_setLAverage _ (volume_czPartition_lt_top ha hX i).ne]

/-- The function `b_i` in Lemma 10.2.5 (general case). -/
def czRemainder' (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) (x : X) : ℂ :=
  (czPartition ha hX i).indicator (f - czApproximation f ha α) x

variable (f) in
/-- The function `b = ∑ⱼ bⱼ` introduced below Lemma 10.2.5.
In the finite case, we also use this as the function `b = b₁` in Lemma 10.2.5.
We choose a more convenient definition, but prove in `tsum_czRemainder'` that this is the same. -/
def czRemainder (ha : 4 ≤ a) (α : ℝ≥0∞) (x : X) : ℂ :=
  f x - czApproximation f ha α x

/-- Part of Lemma 10.2.5, this is essentially (10.2.16) (both cases). -/
def tsum_czRemainder' (ha : 4 ≤ a) (hX : GeneralCase f α) (x : X) :
    ∑ᶠ i, czRemainder' ha hX i x = czRemainder f ha α x := by
  simp only [czRemainder', czRemainder]
  by_cases hx : ∃ j, x ∈ czPartition ha hX j
  · have ⟨j, hj⟩ := hx
    rw [finsum_eq_single _ j, indicator_of_mem hj]
    · rfl
    · refine fun i hi ↦ indicator_of_notMem ?_ _
      exact (czPartition_pairwise_disjoint_on ha hi).notMem_of_mem_right hj
  · simp only [czApproximation, hX, reduceDIte, hx, sub_self]
    exact finsum_eq_zero_of_forall_eq_zero fun i ↦ indicator_of_notMem (fun hi ↦ hx ⟨i, hi⟩) _

open scoped Classical in
/-- Part of Lemma 10.2.5 (both cases). -/
lemma aemeasurable_czApproximation (ha : 4 ≤ a) {hf : AEMeasurable f} :
    AEMeasurable (czApproximation f ha α) := by
  by_cases hX : GeneralCase f α; swap
  · unfold czApproximation; simp [hX]
  let czA (x : X) := -- Measurable version of `czApproximation f ha α`
    if hx : ∃ j, x ∈ czPartition ha hX j then ⨍ y in czPartition ha hX hx.choose, f y else hf.mk f x
  refine ⟨czA, fun T hT ↦ ?_, hf.ae_eq_mk.mono fun x h ↦ by simp [czApproximation, czA, hX, h]⟩
  let S := {x : X | ∃ j, x ∈ czPartition ha hX j}ᶜ ∩ (hf.mk f) ⁻¹' T
  have : czA ⁻¹' T = S ∪ ⋃₀ (czPartition ha hX '' {i | ⨍ y in czPartition ha hX i, f y ∈ T}) := by
    refine ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_cases hx : ∃ j, x ∈ czPartition ha hX j
      · refine Or.inr ⟨czPartition ha hX hx.choose, ⟨mem_image_of_mem _ ?_, hx.choose_spec⟩⟩
        simpa [czA, hx] using h
      · exact Or.inl ⟨hx, by simpa [czA, hx, hX] using h⟩
    · cases h with
      | inl h => simpa [czA, mem_setOf_eq ▸ mem_setOf_eq ▸ h.1] using h.2
      | inr h => obtain ⟨_, ⟨⟨i, ⟨hi, rfl⟩⟩, hxi⟩⟩ := h
                 have hx : ∃ j, x ∈ czPartition ha hX j := ⟨i, hxi⟩
                 simpa [czA, hx, czPartition_pairwiseDisjoint' ha hx.choose_spec hxi] using hi
  rw [this]
  have := Measurable.exists (MeasurableSet.czPartition ha hX · |>.mem)
  apply MeasurableSet.union (by measurability) ∘ MeasurableSet.sUnion ((to_countable _).image _)
  simp [MeasurableSet.czPartition ha hX]

/-- Part of Lemma 10.2.5, equation (10.2.16) (both cases).
This is true by definition, the work lies in `tsum_czRemainder'` -/
lemma czApproximation_add_czRemainder (ha : 4 ≤ a) {x : X} :
    czApproximation f ha α x + czRemainder f ha α x = f x := by
  simp [czApproximation, czRemainder]

private lemma α_le_mul_α : α ≤ 2 ^ (3 * a) * α := by
  nth_rw 1 [← one_mul α]; gcongr; exact_mod_cast Nat.one_le_two_pow

-- Equation (10.2.17), finite case
private lemma enorm_czApproximation_le_finite {ha : 4 ≤ a} (hα : ⨍⁻ x, ‖f x‖ₑ ≤ α)
    (hX : ¬ GeneralCase f α) : ∀ᵐ x, ‖czApproximation f ha α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  simp only [czApproximation, hX, reduceDIte, eventually_const]
  exact le_trans (enorm_integral_le_lintegral_enorm f) <| hα.trans α_le_mul_α

/-- Equation (10.2.17) specialized to the general case. -/
lemma enorm_czApproximation_le_infinite (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hX : GeneralCase f α) :
    ∀ᵐ x, ‖czApproximation f ha α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  have h₁ (x : X) (hx : ∃ i, x ∈ czPartition ha hX i) : ‖czApproximation f ha α x‖ₑ ≤ 2^(3*a) * α :=
    have ⟨i, hi⟩ := hx
    calc ‖czApproximation f ha α x‖ₑ
      _ = ‖⨍ x in czPartition ha hX i, f x‖ₑ := by rw [czApproximation_def_of_mem ha hi]
      _ ≤ ⨍⁻ x in czPartition ha hX i, ‖f x‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
      _ ≤ (volume (czPartition ha hX i))⁻¹ * ∫⁻ x in czPartition ha hX i, ‖f x‖ₑ := by
        simp [laverage]
      _ ≤ 2 ^ (3 * a) * (volume (czBall7 ha hX i))⁻¹ * ∫⁻ x in czPartition ha hX i, ‖f x‖ₑ := by
        apply mul_le_mul_right'
        have := (ENNReal.inv_mul_le_iff (by simp) (by simp)).mpr <| volume_czBall7_le ha hX i
        rwa [← ENNReal.inv_le_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv] at this
      _ ≤ 2 ^ (3 * a) * (volume (czBall7 ha hX i))⁻¹ * ∫⁻ x in czBall7 ha hX i, ‖f x‖ₑ :=
        mul_le_mul_left' (lintegral_mono_set (czPartition_subset_czBall7 ha)) _
      _ ≤ 2 ^ (3 * a) * α := by
        rw [mul_assoc]; gcongr; simpa [laverage] using laverage_czBall7_le ha hX i
  have h₂ : ∀ᵐ x, ¬(∃ i, x ∈ czPartition ha hX i) → ‖czApproximation f ha α x‖ₑ ≤ 2 ^ (3 * a) * α :=
    (lebesgue_differentiation hf).mono fun x ⟨c, r, lim, _, x_mem_ball⟩ hx ↦ by
      have le_α := hx
      rw [← mem_iUnion, iUnion_czPartition, mem_preimage, mem_Ioi, not_lt] at le_α
      simp only [czApproximation, hX, reduceDIte, hx]
      refine le_of_tendsto lim.enorm <| Eventually.of_forall fun i ↦ ?_
      apply le_trans (enorm_integral_le_lintegral_enorm f)
      exact le_trans (laverage_le_globalMaximalFunction (x_mem_ball i)) <| le_α.trans α_le_mul_α
  simpa only [← or_imp, em, forall_const] using eventually_and.mpr ⟨Eventually.of_forall h₁, h₂⟩

/-- Part of Lemma 10.2.5, equation (10.2.17) (both cases). -/
lemma enorm_czApproximation_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ ≤ α) :
    ∀ᵐ x, ‖czApproximation f ha α x‖ₑ ≤ 2 ^ (3 * a) * α :=
  by_cases (enorm_czApproximation_le_infinite ha (hf := hf)) (enorm_czApproximation_le_finite hα)

-- Equation (10.2.18), finite case
private lemma eLpNorm_czApproximation_le_finite {ha : 4 ≤ a} (hf : BoundedFiniteSupport f)
    (hα : 0 < α) (hX : ¬ GeneralCase f α) :
    eLpNorm (czApproximation f ha α) 1 volume ≤ eLpNorm f 1 volume := calc
  _ = ‖⨍ x, f x‖ₑ * volume univ := by
    unfold czApproximation; simp [hX, eLpNorm_const _ one_pos.ne' (NeZero.ne volume)]
  _ ≤ (⨍⁻ x, ‖f x‖ₑ ∂volume) * volume (univ : Set X) :=
    mul_le_mul_right' (enorm_integral_le_lintegral_enorm f) _
  _ = eLpNorm f 1 volume := by
    simp [mul_comm _ (volume univ), eLpNorm, eLpNorm', laverage, ← mul_assoc,
      ENNReal.mul_inv_cancel (NeZero.ne (volume univ)) (volume_lt_of_not_GeneralCase hf hX hα).ne]

-- Equation (10.2.18), infinite case
private lemma eLpNorm_czApproximation_le_infinite {ha : 4 ≤ a} (hX : GeneralCase f α) :
    eLpNorm (czApproximation f ha α) 1 volume ≤ eLpNorm f 1 volume := by
  simp only [eLpNorm, one_ne_zero, reduceIte, one_ne_top, eLpNorm', toReal_one, rpow_one,
    ne_eq, not_false_eq_true, div_self]
  have hmeas : MeasurableSet (univ \ ⋃ i, czPartition ha hX i) := by measurability
  have := union_univ _ ▸ @union_diff_self X (⋃ i, czPartition ha hX i) univ
  repeat rw [← setLIntegral_univ (μ := volume), ← this, lintegral_union hmeas disjoint_sdiff_right,
    lintegral_iUnion (MeasurableSet.czPartition ha hX) <| czPartition_pairwise_disjoint_on ha]
  gcongr tsum ?_ + ?_
  · apply lintegral_czPartition_le
  · simp only [union_diff_self, union_univ]
    apply le_of_eq ∘ setLIntegral_congr_fun (by measurability)
    exact Eventually.of_forall (fun x hx ↦ by simp_all [czApproximation, hX])

/-- Part of Lemma 10.2.5, equation (10.2.18) (both cases). -/
lemma eLpNorm_czApproximation_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : 0 < α) :
    eLpNorm (czApproximation f ha α) 1 volume ≤ eLpNorm f 1 volume :=
  by_cases eLpNorm_czApproximation_le_infinite (eLpNorm_czApproximation_le_finite hf hα)

/-- Part of Lemma 10.2.5, equation (10.2.19) (general case). -/
lemma support_czRemainder'_subset (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    support (czRemainder' ha hX i) ⊆ czBall3 ha hX i := by
  refine subset_trans (fun x hx ↦ ?_) (czPartition_subset_czBall3 ha)
  rw [mem_support, czRemainder', ne_eq, indicator_apply_eq_zero, Classical.not_imp] at hx
  exact hx.1

/-- Part of Lemma 10.2.5, equation (10.2.20) (general case). -/
lemma integral_czRemainder' (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    ∫ x, czRemainder' ha hX i x = 0 := by
  unfold czRemainder'
  rw [integral_indicator (MeasurableSet.czPartition ha hX i)]
  rw [← setAverage_sub_setAverage (volume_czPartition_lt_top ha hX i).ne f]
  refine setIntegral_congr_fun (MeasurableSet.czPartition ha hX i) <| fun x hx ↦ ?_
  rw [Pi.sub_apply, czApproximation_def_of_mem ha hx]

/-- Part of Lemma 10.2.5, equation (10.2.20) (finite case). -/
lemma integral_czRemainder (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) : ∫ x, czRemainder f ha α x = 0 := by
  have := isFiniteMeasure_finite hf hX hα
  simpa [czRemainder, czApproximation, hX] using integral_sub_average volume f

-- Inequality (10.2.32)
private lemma ineq_10_2_32 (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) {hX : GeneralCase f α}
    {i : ℕ} :
    eLpNorm (czRemainder' ha hX i) 1 volume ≤ 2 * (∫⁻ x in czPartition ha hX i, ‖f x‖ₑ) := calc
  _ = ∫⁻ x in czPartition ha hX i, ‖f x - czApproximation f ha α x‖ₑ := by
    simp [czRemainder', eLpNorm, eLpNorm', enorm_indicator_eq_indicator_enorm,
      lintegral_indicator <| MeasurableSet.czPartition ha hX i]
  _ ≤ ∫⁻ x in czPartition ha hX i, ‖f x‖ₑ + ‖czApproximation f ha α x‖ₑ :=
    lintegral_mono_fn (fun x ↦ enorm_sub_le)
  _ = (∫⁻ x in _, ‖f x‖ₑ) + ∫⁻ x in _, ‖_‖ₑ := lintegral_add_left' hf.aemeasurable.enorm.restrict _
  _ ≤ 2 * (∫⁻ x in czPartition ha hX i, ‖f x‖ₑ) := by
    rw [two_mul]; exact add_le_add_left (lintegral_czPartition_le ha i) _

/-- Part of Lemma 10.2.5, equation (10.2.21) (general case). -/
lemma eLpNorm_czRemainder'_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {i : ℕ} :
    eLpNorm (czRemainder' ha hX i) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 ha hX i) := calc
  _ ≤ 2 * (∫⁻ x in czPartition ha hX i, ‖f x‖ₑ) := ineq_10_2_32 ha hf
  _ ≤ 2 * (volume (czBall7 ha hX i) * α) := by
    apply mul_le_mul_left' ∘ (le_trans <| lintegral_mono_set <| czPartition_subset_czBall7 ha)
    have h : volume (czBall7 ha hX i) ≠ 0 :=
      measure_ball_pos _ _ (mul_pos Nat.ofNat_pos (czRadius_pos ha hX i)) |>.ne'
    simpa [laverage, ENNReal.inv_mul_le_iff h measure_ball_ne_top] using laverage_czBall7_le ha hX i
  _ ≤ 2 * ((volume (ball (czCenter ha hX i) (2 ^ 2 * (3 * czRadius ha hX i)))) * α) := by
    gcongr; exact ball_subset_ball <| by linarith [czRadius_pos ha hX i]
  _ ≤ 2 * (2 ^ (2 * a) * volume (czBall3 ha hX i) * α) := by
    gcongr; exact (measure_ball_two_le_same_iterate _ _ 2).trans_eq <| by simp [pow_mul, mul_comm 2]
  _ = 2 ^ (2 * a + 1) * α * volume (czBall3 ha hX i) := by ring

-- Used to prove `eLpNorm_czRemainder_le` and `tsum_eLpNorm_czRemainder_le`
private lemma eLpNorm_czRemainder_le' {ha : 4 ≤ a} (hf : BoundedFiniteSupport f)
    (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f ha α) 1 volume ≤ 2 * ∫⁻ x, ‖f x‖ₑ :=
  have := isFiniteMeasure_finite hf hX (lt_of_le_of_lt (zero_le _) hα)
  calc
    _ = ∫⁻ x, ‖f x - ⨍ y, f y‖ₑ := by simp [czRemainder, eLpNorm, eLpNorm', czApproximation, hX]
    _ ≤ ∫⁻ x, (‖f x‖ₑ + ‖⨍ y, f y‖ₑ) := lintegral_mono (fun x ↦ enorm_sub_le)
    _ = (∫⁻ x, ‖f x‖ₑ) + ∫⁻ (x : X), ‖⨍ y, f y‖ₑ := lintegral_add_right' _ aemeasurable_const
    _ ≤ (∫⁻ x, ‖f x‖ₑ) + ∫⁻ (x : X), ⨍⁻ y, ‖f y‖ₑ := by
      gcongr; apply enorm_integral_le_lintegral_enorm
    _ = 2 * ∫⁻ x, ‖f x‖ₑ := by rw [two_mul, lintegral_laverage]

/-- Part of Lemma 10.2.5, equation (10.2.21) (finite case). -/
lemma eLpNorm_czRemainder_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f ha α) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
  have := isFiniteMeasure_finite hf hX (lt_of_le_of_lt (zero_le _) hα)
  calc
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ := eLpNorm_czRemainder_le' hf hX hα
    _ ≤ 2 * (α * volume (univ : Set X)) := by
      rw [laverage_eq] at hα
      exact mul_le_mul_left' (a := 2) <| ENNReal.div_lt_iff (Or.inl (NeZero.ne _))
        (Or.inl this.measure_univ_lt_top.ne) |>.mp hα |>.le
    _ ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
      rw [← mul_assoc]; gcongr; simpa using pow_le_pow_right' one_le_two (Nat.le_add_left 1 (2 * a))

/-- Part of Lemma 10.2.5, equation (10.2.22) (general case). -/
lemma tsum_volume_czBall3_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∑' i, volume (czBall3 ha hX i) ≤ 2 ^ (6 * a) / α * eLpNorm f 1 volume := calc
  _ ≤ ∑' i, 2 ^ (2 * a) * volume (czBall ha hX i) := ENNReal.tsum_le_tsum (volume_czBall3_le ha hX)
  _ ≤ 2 ^ (2 * a) * volume (globalMaximalFunction volume 1 f ⁻¹' Ioi α) := by
    simp_rw [← smul_eq_mul, ENNReal.tsum_const_smul]
    gcongr
    rw [← measure_iUnion ?_ (fun i ↦ measurableSet_ball), ← iUnion_czPartition]
    · exact measure_mono <| iUnion_mono (fun i ↦ czBall_subset_czPartition ha)
    · exact (pairwise_disjoint_on (czBall ha hX)).mpr fun i j h ↦ (czBall_pairwiseDisjoint ha).mono
        (fun _ ↦ ball_subset_closedBall) (mem_univ i) (mem_univ j) h.ne
  _ ≤ 2 ^ (2 * a) * ((C10_2_1 a) * eLpNorm f 1 volume / α) :=
    mul_le_mul_left' (maximal_theorem'' hα hf) _
  _ = 2 ^ (6 * a) / α * eLpNorm f 1 volume := by
    rw [C10_2_1_def, mul_div_assoc', mul_comm (_ / α), mul_div, ← mul_assoc]; norm_cast; ring_nf

omit [IsCancellative X (defaultτ a)] in
/-- Part of Lemma 10.2.5, equation (10.2.22) (finite case). -/
lemma volume_univ_le {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    volume (univ : Set X) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  convert maximal_theorem'' hα hf using 1
  · simp_all [GeneralCase]
  · rw [ENNReal.mul_div_right_comm, C10_2_1_def]; rfl

/-- Part of Lemma 10.2.5, equation (10.2.23) (general case). -/
lemma tsum_eLpNorm_czRemainder'_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hX : GeneralCase f α) :
    ∑' i, eLpNorm (czRemainder' ha hX i) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  apply le_trans <| ENNReal.tsum_le_tsum (fun i ↦ ineq_10_2_32 ha hf)
  simp_rw [← smul_eq_mul, ENNReal.tsum_const_smul]
  gcongr
  rw [← lintegral_iUnion (MeasurableSet.czPartition ha hX) (czPartition_pairwise_disjoint_on ha)]
  simpa [eLpNorm, eLpNorm'] using (lintegral_mono_set (subset_univ _))

/-- Part of Lemma 10.2.5, equation (10.2.23) (finite case). -/
lemma tsum_eLpNorm_czRemainder_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f ha α) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  simpa [eLpNorm, eLpNorm'] using (eLpNorm_czRemainder_le' hf hX hα)

/- ### Lemmas 10.2.6 - 10.2.9 -/

/-- The constant `c` introduced below Lemma 10.2.5. -/
irreducible_def c10_0_3 (a : ℕ) : ℝ≥0 := (2 ^ (a ^ 3 + 12 * a + 4))⁻¹

open scoped Classical in
variable (f) in
/-- The set `Ω` introduced below Lemma 10.2.5. -/
def Ω (ha : 4 ≤ a) (α : ℝ≥0∞) : Set X :=
  if hX : GeneralCase f α then ⋃ i, czBall2 ha hX i else univ

/-- The constant used in `estimate_good`. -/
irreducible_def C10_2_6 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a ^ 3 + 3 * a + 2) * c10_0_3 a

/-- Lemma 10.2.6 -/
lemma estimate_good (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) :
    distribution (czOperator K r (czApproximation f ha α)) (α / 2) volume ≤
    C10_2_6 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `czOperatorBound`. -/
irreducible_def C10_2_7 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1) * c10_0_3 a

/-- The function `F` defined in Lemma 10.2.7. -/
def czOperatorBound (ha : 4 ≤ a) (hX : GeneralCase f α) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * ∑' i, ((czRadius ha hX i).toNNReal / nndist x (czCenter ha hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 ha hX i) / volume (ball x (dist x (czCenter ha hX i)))

/-- Lemma 10.2.7.
Note that `hx` implies `hX`, but we keep the superfluous hypothesis to shorten the statement. -/
lemma estimate_bad_partial (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hx : x ∈ (Ω f ha α)ᶜ) (hX : GeneralCase f α) :
    ‖czOperator K r (czRemainder f ha α) x‖ₑ ≤ 3 * czOperatorBound ha hX x + α / 8 := by
  sorry

/-- The constant used in `distribution_czOperatorBound`. -/
irreducible_def C10_2_8 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.8 -/
lemma distribution_czOperatorBound (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    volume ((Ω f ha α)ᶜ ∩ czOperatorBound ha hX ⁻¹' Ioi (α / 8)) ≤
    C10_2_8 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `estimate_bad`. -/
irreducible_def C10_2_9 (a : ℕ) : ℝ≥0 := 2 ^ (5 * a) / c10_0_3 a + 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.9 -/
-- In the proof, case on `GeneralCase f α`, noting in the finite case that `Ω = univ`
lemma estimate_bad (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    distribution (czOperator K r (czRemainder f ha α)) (α / 2) volume ≤
    C10_2_9 a / α * eLpNorm f 1 volume := by
  sorry


/- ### Lemmas 10.0.3 -/

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
-- in proof: do cases on `α ≤ ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a`.
-- If true, use the argument directly below (10.2.37)
theorem czoperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
