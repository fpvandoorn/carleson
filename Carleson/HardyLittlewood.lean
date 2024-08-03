import Carleson.DoublingMeasure
import Carleson.RealInterpolation
import Mathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter
open scoped NNReal ENNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

-- #check VitaliFamily
-- Note: Lemma 9.0.2 is roughly Vitali.exists_disjoint_covering_ae

variable {X E : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsDoubling A] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f : X → E} {x : X} {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ}
  [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
  -- feel free to assume `A ≥ 16` or similar

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑.
M_{𝓑, p} in the blueprint. -/
def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ)
  (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
  fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖u y‖₊ ^ p ∂μ) ^ p⁻¹

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑 with exponent 1.
M_𝓑 in the blueprint. -/
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) :=
  maximalFunction μ 𝓑 c r 1 u x

lemma covering_separable_space (X : Type*) [PseudoMetricSpace X] [SeparableSpace X] :
    ∃ C : Set X, C.Countable ∧ ∀ r > 0, ⋃ c ∈ C, ball c r = univ := by
  simp_rw [← Metric.dense_iff_iUnion_ball, exists_countable_dense]

-- this can be removed next Mathlib bump
/-- A slight generalization of Mathlib's version, with 5 replaced by τ. Already PR'd -/
theorem Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall' {α ι} [MetricSpace α]
    (t : Set ι) (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases ht : ∀ a ∈ t, r a < 0
  · exact ⟨t, Subset.rfl, fun a ha b _ _ => by
      #adaptation_note /-- nightly-2024-03-16
      Previously `Function.onFun` unfolded in the following `simp only`,
      but now needs a separate `rw`.
      This may be a bug: a no import minimization may be required. -/
      rw [Function.onFun]
      simp only [Function.onFun, closedBall_eq_empty.2 (ht a ha), empty_disjoint],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset]⟩⟩
  push_neg at ht
  let t' := { a ∈ t | 0 ≤ r a }
  rcases exists_disjoint_subfamily_covering_enlargment (fun a => closedBall (x a) (r a)) t' r
      ((τ - 1) / 2) (by linarith) (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closedBall_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) ≤ r a + r b := dist_le_add_of_nonempty_closedBall_inter_closedBall hb
    apply closedBall_subset_closedBall'
    linarith
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases le_or_lt 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _⟩
    exact ⟨c, cu, by simp only [closedBall_eq_empty.2 h'a, empty_subset]⟩

theorem Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall'' {α ι} [MetricSpace α]
    (t : Set ι) (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        (∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b)) ∧
        ∀ a ∈ t, ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases ht : ∀ a ∈ t, r a < 0
  · exact ⟨t, Subset.rfl, fun a ha b _ _ => by
      #adaptation_note /-- nightly-2024-03-16
      Previously `Function.onFun` unfolded in the following `simp only`,
      but now needs a separate `rw`.
      This may be a bug: a no import minimization may be required. -/
      rw [Function.onFun]
      simp only [Function.onFun, closedBall_eq_empty.2 (ht a ha), empty_disjoint],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset]⟩,
      fun a ha ↦ ⟨a, ha, by simp only [ball_eq_empty.mpr (le_of_lt (ht a ha)), empty_subset]⟩⟩
  push_neg at ht
  let t' := { a ∈ t | 0 ≤ r a }
  rcases exists_disjoint_subfamily_covering_enlargment (fun a => closedBall (x a) (r a)) t' r
      ((τ - 1) / 2) (by linarith) (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closedBall_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, r a + dist (x a) (x b) ≤ τ * r b := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    linarith [dist_le_add_of_nonempty_closedBall_inter_closedBall hb]
  have Ac : ∀ a ∈ t', ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) := by
    intro a ha
    rcases A a ha with ⟨b, bu, hb⟩
    refine ⟨b, bu, closedBall_subset_closedBall' hb⟩
  have Ao : ∀ a ∈ t', ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
    intro a ha
    rcases A a ha with ⟨b, bu, hb⟩
    refine ⟨b, bu, ball_subset_ball' hb⟩
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_, fun a ha => ?_⟩
  · rcases le_or_lt 0 (r a) with (h'a | h'a)
    · exact Ac a ⟨ha, h'a⟩
    · rcases ht with ⟨b, rb⟩
      rcases Ac b ⟨rb.1, rb.2⟩ with ⟨c, cu, _⟩
      exact ⟨c, cu, by simp only [closedBall_eq_empty.2 h'a, empty_subset]⟩
  · rcases le_total 0 (r a) with (h'a | h'a)
    · exact Ao a ⟨ha, h'a⟩
    · rcases ht with ⟨b, rb⟩
      rcases Ao b ⟨rb.1, rb.2⟩ with ⟨c, cu, _⟩
      exact ⟨c, cu, by simp only [ball_eq_empty.2 h'a, empty_subset]⟩

/- NOTE: This was changed to use `ℝ≥0∞` rather than `ℝ≥0` because that was more convenient for the
proof of `first_exception` in DiscreteCarleson.lean. But everything involved there is finite, so
you can prove this with `ℝ≥0` and deal with casting between `ℝ≥0` and `ℝ≥0∞` there, if that turns
out to be easier. -/
theorem Set.Countable.measure_biUnion_le_lintegral (h𝓑 : 𝓑.Countable) {l : ℝ≥0∞} (hl : 0 < l)
    {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  -- obtain ⟨B, hB𝓑, hB, h2B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall'
  --   𝓑 c r R hR (2 ^ 2) (by norm_num)
  obtain ⟨B, hB𝓑, hB, h2B, h3B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall''
    𝓑 c r R hR (2 ^ 2) (by norm_num)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
      -- it was need to use the strongest thesis `Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall''`
      gcongr l * μ ?_
      refine iUnion₂_subset fun i hi ↦ ?_
      obtain ⟨j, hj, hj'⟩ := h3B i hi
      exact Set.Subset.trans hj' (Set.subset_iUnion_of_subset j
        (Set.subset_iUnion_of_subset hj fun _ a ↦ a))
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) := by
      gcongr; exact measure_biUnion_le _ (mono hB𝓑 h𝓑) _
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
      gcongr; exact measure_ball_le_pow_two'
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := by
      rw [ENNReal.tsum_mul_left, ← mul_assoc, mul_comm l, mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := by
      gcongr with i ; exact h2u i (hB𝓑 i.2)
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := by
      congr
      sorry -- does this exist in Mathlib?
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := by
      sorry

protected theorem Finset.measure_biUnion_le_lintegral (𝓑 : Finset ι) {l : ℝ≥0∞} (hl : 0 < l)
    {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  :=
  let ⟨c, hc⟩ := (𝓑.image r).exists_le
  𝓑.countable_toSet.measure_biUnion_le_lintegral hl hu c (by simpa using hc) h2u

protected theorem MeasureTheory.AEStronglyMeasurable.maximalFunction {p : ℝ}
    {u : X → E} (h𝓑 : 𝓑.Countable) : AEStronglyMeasurable (maximalFunction μ 𝓑 c r p u) μ :=
  (aemeasurable_biSup 𝓑 h𝓑 fun _ _ ↦ aemeasurable_const.indicator measurableSet_ball).pow
    aemeasurable_const |>.aestronglyMeasurable

theorem MeasureTheory.AEStronglyMeasurable.maximalFunction_toReal
    {p : ℝ} {u : X → E} (h𝓑 : 𝓑.Countable) :
    AEStronglyMeasurable (fun x ↦ maximalFunction μ 𝓑 c r p u x |>.toReal) μ :=
  AEStronglyMeasurable.maximalFunction h𝓑 |>.ennreal_toReal

theorem MB_le_snormEssSup {u : X → E} {x : X} : MB μ 𝓑 c r u x ≤ snormEssSup u μ :=
  calc MB μ 𝓑 c r u x ≤
    ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
        fun _x ↦ ⨍⁻ _y in ball (c i) (r i), snormEssSup u μ ∂μ := by
        simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one]
        gcongr
        exact setLAverage_mono_ae <| coe_nnnorm_ae_le_snormEssSup u μ
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x) fun _x ↦ snormEssSup u μ := by
      gcongr; apply setLaverage_const_le
    _ ≤ ⨆ i ∈ 𝓑, snormEssSup u μ := by gcongr; apply indicator_le_self
    _ ≤ snormEssSup u μ := by
      simp_rw [iSup_le_iff, le_refl, implies_true]

protected theorem HasStrongType.MB_top (h𝓑 : 𝓑.Countable) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) ⊤ ⊤ μ μ 1 := by
  intro f _
  use AEStronglyMeasurable.maximalFunction_toReal h𝓑
  simp only [ENNReal.coe_one, one_mul, snorm_exponent_top]
  refine essSup_le_of_ae_le _ (eventually_of_forall fun x ↦ ?_)
  simp_rw [ENNReal.nnorm_toReal]
  refine ENNReal.coe_toNNReal_le_self |>.trans ?_
  apply MB_le_snormEssSup

/- Prove this by proving that
* suprema of sublinear maps are sublinear,
* the indicator of a sublinear map is sublinear
* constant maps are sublinear -/
protected theorem MeasureTheory.SublinearOn.maximalFunction {p : ℝ} (hp₁ : 1 ≤ p) :
    SublinearOn (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
      (fun f ↦ Memℒp f ∞ μ ∨ Memℒp f 1 μ) 1 := by
  sorry

/- The proof is roughly between (9.0.12)-(9.0.22). -/
variable (μ) in
protected theorem HasWeakType.MB_one [μ.IsDoubling A] (h𝓑 : 𝓑.Countable) :
    HasWeakType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) 1 1 μ μ (A ^ 2) := by
  intro f hf
  use AEStronglyMeasurable.maximalFunction_toReal h𝓑
  sorry

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
irreducible_def CMB (A p : ℝ≥0) : ℝ≥0 := sorry

/- The proof is given between (9.0.12)-(9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
lemma hasStrongType_MB (h𝓑 : 𝓑.Countable) {p : ℝ≥0}
    (hp : 1 < p) {u : X → E} (hu : AEStronglyMeasurable u μ) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
      p p μ μ (CMB A p) := by
  have h2p : 0 < p := zero_lt_one.trans hp
  have := exists_hasStrongType_real_interpolation
    (T := fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
    ⟨le_top, le_rfl⟩ ⟨le_rfl, le_rfl⟩ (by norm_num) (by simp [inv_lt_one_iff, hp, h2p] : p⁻¹ ∈ _)
    zero_lt_one (pow_pos (A_pos μ) 2)
    (p := p) (q := p) (A := 1)
    (by simp [ENNReal.coe_inv h2p.ne']) (by simp [ENNReal.coe_inv h2p.ne'])
    (fun f hf ↦ AEStronglyMeasurable.maximalFunction_toReal h𝓑)
    (.maximalFunction hp.le)
    (HasStrongType.MB_top h𝓑 |>.hasWeakType le_top)
    (HasWeakType.MB_one μ h𝓑)
  convert this using 1
  sorry -- let's deal with the constant later

/-- The constant factor in the statement that `M_{𝓑, p}` has strong type. -/
irreducible_def C2_0_6 (A p₁ p₂ : ℝ≥0) : ℝ≥0 := sorry -- todo: define in terms of `CMB`.

/- The proof is given between (9.0.34)-(9.0.36). -/
theorem hasStrongType_maximalFunction {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : AEStronglyMeasurable u μ) :
    HasStrongType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x |>.toReal)
      p₂ p₂ μ μ (C2_0_6 A p₁ p₂) := by
  sorry

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6.
`p` is `1` in the blueprint, and `globalMaximalFunction μ p u = (M (u ^ p)) ^ p⁻¹ ` -/
@[nolint unusedArguments]
def globalMaximalFunction [μ.IsDoubling A] (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  A ^ 2 * maximalFunction μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
    (fun z ↦ z.1) (fun z ↦ 2 ^ z.2) p u x

variable (X) in
lemma countable_globalMaximalFunction :
    (covering_separable_space X).choose ×ˢ (univ : Set ℤ) |>.Countable :=
  (covering_separable_space X).choose_spec.1.prod countable_univ

-- prove only if needed. Use `MB_le_snormEssSup`
theorem globalMaximalFunction_lt_top {p : ℝ≥0} (hp₁ : 1 ≤ p)
    {u : X → E} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u)) {x : X} :
    globalMaximalFunction μ p u  x < ∞ := by
  sorry

protected theorem MeasureTheory.AEStronglyMeasurable.globalMaximalFunction {p : ℝ}
    {u : X → E} : AEStronglyMeasurable (globalMaximalFunction μ p u) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <|
    AEStronglyMeasurable.maximalFunction
      (countable_globalMaximalFunction X) |>.aemeasurable.const_mul _

theorem laverage_le_globalMaximalFunction {u : X → E} (hu : AEStronglyMeasurable u μ)
    (hu : IsBounded (range u)) {z x : X} {r : ℝ} (h : dist x z < r) :
    ⨍⁻ y, ‖u y‖₊ ∂μ.restrict (ball z r) ≤ globalMaximalFunction μ 1 u x := by
  sorry

/-- The constant factor in the statement that `M` has strong type. -/
def C2_0_6' (A p₁ p₂ : ℝ≥0) : ℝ≥0 := A ^ 2 * C2_0_6 A p₁ p₂

/- easy from `hasStrongType_maximalFunction`. Ideally prove separately
`HasStrongType.const_smul` and `HasStrongType.const_mul`. -/
theorem hasStrongType_globalMaximalFunction {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} :
    HasStrongType (fun (u : X → E) (x : X) ↦ globalMaximalFunction μ p₁ u x |>.toReal)
      p₂ p₂ μ μ (C2_0_6' A p₁ p₂) := by
  sorry
