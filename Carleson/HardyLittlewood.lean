import Carleson.DoublingMeasure
import Carleson.RealInterpolation
import Mathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter
open scoped NNReal ENNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

-- #check VitaliFamily
-- Note: Lemma 9.0.2 is roughly Vitali.exists_disjoint_covering_ae

variable {X E : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
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

lemma covering_separable_space (X : Type*) [MetricSpace X] [SeparableSpace X] :
    ∃ C : Set X, C.Countable ∧ ∀ r > 0, ⋃ c ∈ C, ball c r = univ := by
  obtain ⟨C, hC, h2C⟩ := exists_countable_dense X
  use C, hC
  simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop, mem_ball]
  intro r hr x
  simp_rw [Dense, Metric.mem_closure_iff] at h2C
  exact h2C x r hr

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

/- NOTE: This was changed to use `ℝ≥0∞` rather than `ℝ≥0` because that was more convenient for the
proof of `first_exception` in DiscreteCarleson.lean. But everything involved there is finite, so
you can prove this with `ℝ≥0` and deal with casting between `ℝ≥0` and `ℝ≥0∞` there, if that turns
out to be easier. -/
theorem measure_biUnion_le_lintegral (h𝓑 : 𝓑.Countable) {l : ℝ≥0∞} (hl : 0 < l)
    {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  obtain ⟨B, hB𝓑, hB, h2B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall'
    𝓑 c r R hR (2 ^ 2) (by norm_num)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := sorry
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) := sorry
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := sorry
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := sorry
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := sorry
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := sorry -- does this exist in Mathlib?
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := sorry

theorem measure_biUnion_le_lintegral' (𝓑 : Finset ι) {l : ℝ≥0∞} (hl : 0 < l)
    {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  :=
  let ⟨c, hc⟩ := (𝓑.image r).exists_le
  measure_biUnion_le_lintegral 𝓑.countable_toSet hl hu c (by simpa using hc) h2u

attribute [gcongr] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
attribute [simp] MeasureTheory.laverage_const


namespace MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
  {F : Type*} [NormedAddCommGroup F]
lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ := by
  exact lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

lemma setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ := by
  refine laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self

lemma setLaverage_const_le {c : ℝ≥0∞} : ⨍⁻ _x in s, c ∂μ ≤ c := by
  simp_rw [setLaverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc]
  conv_rhs => rw [← mul_one c]
  gcongr
  exact ENNReal.mul_inv_le_one (μ s)

theorem snormEssSup_lt_top_of_ae_ennnorm_bound {f : α → F} {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    snormEssSup f μ ≤ C :=
  essSup_le_of_ae_le C hfC

@[simp]
lemma ENNReal.nnorm_toReal {x : ℝ≥0∞} : ‖x.toReal‖₊ = x.toNNReal := by
  ext; simp [ENNReal.toReal]

end MeasureTheory

protected theorem MeasureTheory.AEStronglyMeasurable.maximalFunction {p : ℝ}
    {u : X → E} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (maximalFunction μ 𝓑 c r p u) μ := by
  sorry

theorem MeasureTheory.AEStronglyMeasurable.ennreal_toReal
    {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x ↦ (u x).toReal) μ := by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable

theorem MeasureTheory.AEStronglyMeasurable.maximalFunction_toReal {p : ℝ}
    {u : X → E} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x ↦ maximalFunction μ 𝓑 c r p u x |>.toReal) μ :=
  hu.maximalFunction.ennreal_toReal

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

protected theorem HasStrongType.MB_top :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) ⊤ ⊤ μ μ 1 := by
  intro f hf
  use hf.1.maximalFunction_toReal
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
      (fun f ↦ Memℒp f ∞ μ ∨ Memℒp f 1 μ) := by
  sorry

/- The proof is roughly between (9.0.12)-(9.0.22). -/
variable (μ) in
protected theorem HasWeakType.MB_one [μ.IsDoubling A] :
    HasWeakType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) 1 1 μ μ (A ^ 2) := by
  intro f hf
  use hf.1.maximalFunction_toReal
  sorry

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
irreducible_def CMB (A p : ℝ≥0) : ℝ≥0 := sorry

/- The proof is given between (9.0.12)-(9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
lemma hasStrongType_MB {p : ℝ≥0}
    (hp : 1 < p) {u : X → E} (hu : AEStronglyMeasurable u μ) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
      p p μ μ (CMB A p) := by
  have h2p : 0 < p := zero_lt_one.trans hp
  have := exists_hasStrongType_real_interpolation
    (T := fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
    ⟨le_top, le_rfl⟩ ⟨le_rfl, le_rfl⟩ (by norm_num) (by simp [inv_lt_one_iff, hp, h2p] : p⁻¹ ∈ _)
    zero_lt_one (pow_pos (A_pos μ) 2)
    (p := p) (q := p)
    (by simp [ENNReal.coe_inv h2p.ne']) (by simp [ENNReal.coe_inv h2p.ne'])
    (fun f hf ↦ .maximalFunction_toReal (hf.elim (·.1) (·.1)))
    (.maximalFunction hp.le)
    (HasStrongType.MB_top.hasWeakType le_top)
    (HasWeakType.MB_one μ)
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
/-- Auxiliary definition for `supMB`. -/
@[nolint unusedArguments]
def auxM [μ.IsDoubling A] (c : ℕ → X) (r : ℕ → ℝ) (u : X → ℂ) (x : X) : ℝ≥0∞ := by
  exact A ^ 2 * ⨆ n : ℕ, MB μ (Iic n) c r u x

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6. -/
irreducible_def supMB (u : X → ℂ) (x : X) : ℝ≥0∞ := by
  choose C h1C _ using covering_separable_space X
  let B := Set.enumerateCountable (h1C.prod countable_univ (β := ℤ)) (Classical.choice ⟨x, 0⟩)
  exact auxM μ (fun n ↦ (B n).1) (fun n ↦ 2 ^ (B n).2) u x

theorem supMB_lt_top {p₁ p₂ : ℝ≥0} (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u)) {x : X} :
    supMB μ u x < ∞ := by
  sorry

theorem laverage_le_supMB {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} : ⨍⁻ y, ‖u y‖₊ ∂μ.restrict (ball z r) ≤ supMB μ u x := by
  sorry

theorem snorm_supMB_le {p₁ p₂ : ℝ≥0}
    (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂)
    {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u))
    {z x : X} {r : ℝ} :
    snorm (fun x ↦ (supMB μ (fun x ↦ u x ^ (p₁ : ℂ)) x).toReal ^ (p₁⁻¹ : ℝ)) p₂ μ ≤
    A ^ 4  * p₂ / (p₂ - p₁) * snorm u p₂ μ := by
  sorry
