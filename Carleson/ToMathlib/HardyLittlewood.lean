module

public import Carleson.Defs
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Indexed
public import Carleson.ToMathlib.RealInterpolation.Main
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Average
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.Field

@[expose] public section

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter Pointwise
open ENNReal hiding one_lt_two
open scoped NNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

-- Upstreaming status: aside from getting the real interpolation theorem merged,
-- this file needs a bunch of clean-up before it can be upstreamed:
-- moving preliminary lemmas to their appropriate homes (some of these lemmas do not belong in
-- mathlib) and improving the code quality. Follow mathlib style (line length!), can use dot
-- notation more, and the code can sometimes also be golfed.

section Prelude

variable {X : Type*} [PseudoMetricSpace X] [SeparableSpace X]

variable (X) in
/-- Lemma 9.0.2 -/
-- maybe not suited for Mathlib in this form
lemma covering_separable_space :
    ∃ C : Set X, C.Countable ∧ ∀ r > 0, ⋃ c ∈ C, ball c r = univ := by
  simp_rw [← Metric.dense_iff_iUnion_ball, exists_countable_dense]

-- maybe not suited for Mathlib in this form
lemma countable_globalMaximalFunction :
    (covering_separable_space X).choose ×ˢ (univ : Set ℤ) |>.Countable :=
  (covering_separable_space X).choose_spec.1.prod countable_univ

-- probably not suited for Mathlib in this form
lemma exists_ball_subset_ball_two (c : X) {r : ℝ} (hr : 0 < r) :
    ∃ c' ∈ (covering_separable_space X).choose,
      ∃ m : ℤ, ball c r ⊆ ball c' (2 ^ m) ∧ 2 ^ m ≤ 2 * r ∧ ball c' (2 ^ m) ⊆ ball c (4 * r) := by
  obtain ⟨_, hCr⟩ := (covering_separable_space X).choose_spec
  let m := ⌊Real.logb 2 r⌋
  have hm : 2 ^ m ≤ r := by
    calc _ ≤ (2 : ℝ) ^ (Real.logb 2 r) := by
          convert Real.monotone_rpow_of_base_ge_one one_le_two (Int.floor_le _)
          exact (Real.rpow_intCast 2 m).symm
      _ = _ := Real.rpow_logb zero_lt_two (OfNat.one_ne_ofNat 2).symm hr
  have hm' : r < 2 ^ (m + 1) := by
    calc _ = (2 : ℝ) ^ Real.logb 2 r := (Real.rpow_logb zero_lt_two (OfNat.one_ne_ofNat 2).symm hr).symm
      _ < _ := by
        rw [← Real.rpow_intCast 2 (m + 1)]
        refine Real.strictMono_rpow_of_base_gt_one one_lt_two ?_
        simp [m]
  let a := ((2 : ℝ) ^ (m + 1) - r) / 2
  have h_univ := hCr a (by simp [a, hm'])
  obtain ⟨c', hc', hcc'⟩ := mem_iUnion₂.mp <| h_univ ▸ Set.mem_univ c
  refine ⟨c', hc', m + 1, ball_subset_ball_of_le ?_, ?_, ?_⟩
  · calc
      _ ≤ a + r := by gcongr; exact (dist_comm c c' ▸ mem_ball.mp hcc').le
      _ ≤ _ := by simp only [a, sub_div]; linarith
  · rw [← Real.rpow_intCast 2 (m + 1)]
    push_cast
    rw [Real.rpow_add_one two_ne_zero m, mul_comm]
    gcongr
    exact_mod_cast hm
  · refine ball_subset_ball_of_le ?_
    calc
      _ ≤ a + 2 ^ (m + 1) := by gcongr; exact (mem_ball.mp hcc').le
      _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) := by
        gcongr
        simp only [a]
        linarith
      _ ≤ 2 * r + 2 * r := by
        rw [← Real.rpow_intCast 2 (m + 1)]
        push_cast
        rw [Real.rpow_add_one two_ne_zero m, mul_comm]
        gcongr <;> simp [hm]
      _ = 4 * r := by ring

end Prelude

variable {X E : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsDoubling A] [NormedAddCommGroup E]
  {f : X → E} {x : X} {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ}
  -- feel free to assume `A ≥ 16` or similar

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑.
M_{𝓑, p} in the blueprint. -/
def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ)
    (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ (⨍⁻ y in ball (c i) (r i), ‖u y‖ₑ ^ p ∂μ) ^ p⁻¹

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑 with exponent 1.
M_𝓑 in the blueprint. -/
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ 𝓑 c r 1 u x

lemma MB_def : MB μ 𝓑 c r f x = (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖f y‖ₑ ∂μ) := by
  unfold MB maximalFunction; simp_rw [inv_one, rpow_one]

lemma indicator_rpow {α : Type*} {p : ℝ} (hp : 0 < p) {s : Set α} {f : α → ℝ≥0∞} :
    s.indicator (fun y ↦ f y ^ p) = (s.indicator f) ^ p :=
  indicator_comp_of_zero (g := fun a => a ^ p) (ENNReal.zero_rpow_of_pos hp)

lemma maximalFunction_eq_MB
    {μ : Measure X} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ} {p : ℝ} {u : X → E} {x : X} (hp : 0 < p) :
    maximalFunction μ 𝓑 c r p u x = (MB μ 𝓑 c r (‖u ·‖ ^ p) x) ^ p⁻¹ := by
  simp only [maximalFunction, indicator_rpow (inv_pos_of_pos hp), Pi.pow_apply, MB_def,
    iSup_rpow (inv_pos_of_pos hp)]
  congr! 8
  rw [Real.enorm_rpow_of_nonneg (by positivity) hp.le, enorm_norm]

-- We will replace the criterion `P` used in `MeasureTheory.AESublinearOn.maximalFunction` with the
-- weaker criterion `LocallyIntegrable` that is closed under addition and scalar multiplication.

-- The average that appears in the definition of `MB`
variable (μ c r) in
private def T (i : ι) (u : X → E) := ⨍⁻ (y : X) in ball (c i) (r i), ‖u y‖ₑ ∂μ

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_of_isBounded [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : IsBounded s) : IntegrableOn f s μ :=
  hf.integrableOn_isCompact hs.isCompact_closure |>.mono_set subset_closure

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_ball [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {x : X} {r : ℝ} : IntegrableOn f (ball x r) μ :=
  hf.integrableOn_of_isBounded isBounded_ball

-- probably unsuitable for Mathlib
lemma MeasureTheory.LocallyIntegrable.laverage_ball_lt_top [ProperSpace X] {f : X → E}
    (hf : LocallyIntegrable f μ) {x₀ : X} {r : ℝ} :
    ⨍⁻ x in ball x₀ r, ‖f x‖ₑ ∂μ < ⊤ :=
  laverage_lt_top hf.integrableOn_ball.2.ne

private lemma T.add_le [MeasurableSpace E] [BorelSpace E] [BorelSpace X] [ProperSpace X]
    (i : ι) {f g : X → E} (hf : LocallyIntegrable f μ) :
    ‖T μ c r i (f + g)‖ₑ ≤ ‖T μ c r i f‖ₑ + ‖T μ c r i g‖ₑ := by
  simp only [T, Pi.add_apply, enorm_eq_self]
  rw [← laverage_add_left hf.integrableOn_ball.aemeasurable.enorm]
  exact laverage_mono (fun x ↦ enorm_add_le (f x) (g x))

-- move to `ENNReal.Basic` or similar
lemma NNReal.smul_ennreal_eq_mul (x : ℝ≥0) (y : ℝ≥0∞) : x • y = x * y := rfl

private lemma T.smul [NormedSpace ℝ E] (i : ι) {f : X → E} {d : ℝ≥0} :
    T μ c r i (d • f) = d • T μ c r i f := by
  simp_rw [T, Pi.smul_apply, NNReal.smul_def, NNReal.smul_ennreal_eq_mul,
    laverage_const_mul ENNReal.coe_ne_top]
  simp [_root_.enorm_smul]

-- move near `exists_disjoint_subfamily_covering_enlargement_closedBall`
-- slightly more general than the Mathlib version
-- the extra conclusion says that if there is a nonnegative radius, then we can choose `r b` to be
-- larger than `r a` (up to a constant)
theorem exists_disjoint_subfamily_covering_enlargement_closedBall' {α} [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) ∧
        (∀ u ∈ t, 0 ≤ r u → r a ≤ (τ - 1) / 2 * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases! ht : ∀ a ∈ t, r a < 0
  · refine ⟨t, .rfl, fun a ha b _ _ ↦ by
      simp only [Function.onFun, closedBall_eq_empty.2 (ht a ha), empty_disjoint],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset],
      fun u hut hu ↦ (ht u hut).not_ge hu |>.elim⟩⟩
  let t' := { a ∈ t | 0 ≤ r a }
  have h2τ : 1 < (τ - 1) / 2 := by linarith
  rcases exists_disjoint_subfamily_covering_enlargement (fun a => closedBall (x a) (r a)) t' r
      ((τ - 1) / 2) h2τ (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closedBall_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) ∧
    ∀ u ∈ t, 0 ≤ r u → r a ≤ (τ - 1) / 2 * r b := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) ≤ r a + r b := dist_le_add_of_nonempty_closedBall_inter_closedBall hb
    exact ⟨closedBall_subset_closedBall' <| by linarith, fun _ _ _ ↦ rb⟩
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases le_or_gt 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _, hc⟩
    refine ⟨c, cu, by simp only [closedBall_eq_empty.2 h'a, empty_subset], fun _ _ _ ↦ ?_⟩
    have : 0 ≤ r c := nonneg_of_mul_nonneg_right (rb.2.trans <| hc b rb.1 rb.2) (by positivity)
    exact h'a.le.trans <| by positivity

-- move to Vitali
theorem Vitali.exists_disjoint_subfamily_covering_enlargement_ball {α} [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => ball (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
  obtain ⟨σ, hσ, hστ⟩ := exists_between hτ
  obtain ⟨u, hut, hux, hu⟩ :=
    exists_disjoint_subfamily_covering_enlargement_closedBall' t x r R hr σ hσ
  refine ⟨u, hut, fun i hi j hj hij ↦ ?_, fun a ha => ?_⟩
  · exact (hux hi hj hij).mono ball_subset_closedBall ball_subset_closedBall
  obtain ⟨b, hbu, hb⟩ := hu a ha
  refine ⟨b, hbu, ?_⟩
  obtain h2a | h2a := le_or_gt (r a) 0
  · simp_rw [ball_eq_empty.mpr h2a, empty_subset]
  refine ball_subset_closedBall.trans hb.1 |>.trans <| closedBall_subset_ball ?_
  gcongr
  apply pos_of_mul_pos_right <| h2a.trans_le <| hb.2 a ha h2a.le
  linarith

-- move next to Finset.exists_le
lemma Finset.exists_image_le {α β} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)]
    (s : Finset α) (f : α → β) : ∃ b : β, ∀ a ∈ s, f a ≤ b := by
  classical
  simpa using s.image f |>.exists_le

-- move
lemma Set.Finite.exists_image_le {α β} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)]
    {s : Set α} (hs : s.Finite) (f : α → β) : ∃ b : β, ∀ a ∈ s, f a ≤ b := by
  simpa using hs.toFinset.exists_image_le f

theorem Set.Countable.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (h𝓑 : 𝓑.Countable)
    (l : ℝ≥0∞) (u : X → ℝ≥0∞) (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  obtain ⟨B, hB𝓑, hB, h2B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    𝓑 c r R hR (2 ^ 2) (by norm_num)
  have : Countable B := h𝓑.mono hB𝓑
  have disj := fun i j hij ↦
    hB (Subtype.coe_prop i) (Subtype.coe_prop j) (Subtype.coe_ne_coe.mpr hij)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
          refine mul_right_mono (μ.mono fun x hx ↦ ?_)
          push _ ∈ _ at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑
          exact mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) :=
          mul_right_mono <| measure_biUnion_le μ (h𝓑.mono hB𝓑) fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
          refine mul_right_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
          rw [sq, sq, mul_assoc, mul_assoc]
          apply (measure_ball_two_le_same (c i) (2 * r i)).trans
          gcongr; exact measure_ball_two_le_same (c i) (r i)
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc, mul_comm l]
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := by
          gcongr; exact h2u _ (hB𝓑 (Subtype.coe_prop _))
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := by
          congr; simpa using (lintegral_iUnion (fun i ↦ measurableSet_ball) disj u).symm
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := by
          gcongr; exact Measure.restrict_le_self

protected theorem Finset.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (𝓑 : Finset ι)
    (l : ℝ≥0∞) (u : X → ℝ≥0∞)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  :=
  let ⟨c, hc⟩ := 𝓑.exists_image_le r
  𝓑.countable_toSet.measure_biUnion_le_lintegral l u c hc h2u

lemma lowerSemiContinuous_maximalFunction {p : ℝ} :
    LowerSemicontinuous (maximalFunction μ 𝓑 c r p f) := by
  intro x s hxr
  have ⟨i, hi, hxr'⟩ := exists_lt_of_lt_ciSup₂' hxr
  have hx : x ∈ ball (c i) (r i) :=
    mem_of_indicator_ne_zero (hxr'.trans_le' bot_le |>.ne.symm)
  rw [indicator_of_mem hx] at hxr'
  apply eventually_of_mem (U := ball (c i) (r i))
  · exact isOpen_ball.mem_nhds hx
  · intro y hy
    apply LT.lt.trans_le _ (le_iSup₂ i hi)
    rwa [indicator_of_mem hy]

protected theorem MeasureTheory.Measurable.maximalFunction [BorelSpace X] {p : ℝ}
    {u : X → E} : Measurable (maximalFunction μ 𝓑 c r p u) :=
  lowerSemiContinuous_maximalFunction.measurable

theorem MeasureTheory.Measurable.maximalFunction_toReal [BorelSpace X] {p : ℝ} {u : X → E} :
    Measurable (fun x ↦ maximalFunction μ 𝓑 c r p u x |>.toReal) :=
  Measurable.maximalFunction |>.ennreal_toReal

theorem MB_le_eLpNormEssSup {u : X → E} {x : X} : MB μ 𝓑 c r u x ≤ eLpNormEssSup u μ :=
  calc MB μ 𝓑 c r u x ≤
    ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
        fun _x ↦ ⨍⁻ _y in ball (c i) (r i), eLpNormEssSup u μ ∂μ := by
        simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one]
        gcongr
        exact MeasureTheory.enorm_ae_le_eLpNormEssSup u μ
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x) fun _x ↦ eLpNormEssSup u μ := by
      gcongr; apply setLaverage_const_le
    _ ≤ ⨆ i ∈ 𝓑, eLpNormEssSup u μ := by gcongr; apply indicator_le_self
    _ ≤ eLpNormEssSup u μ := by
      simp_rw [iSup_le_iff, le_refl, implies_true]

protected theorem HasStrongType.MB_top [BorelSpace X] :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) ⊤ ⊤ μ μ 1 := by
  intro f _
  use Measurable.maximalFunction.aestronglyMeasurable
  simp only [one_mul, eLpNorm_exponent_top]
  exact essSup_le_of_ae_le _ (Eventually.of_forall fun x ↦ MB_le_eLpNormEssSup)

/- The proof is roughly between (9.0.12)-(9.0.22). -/
protected theorem HasWeakType.MB_one [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    HasWeakType (MB (E := E) μ 𝓑 c r) 1 1 μ μ (A ^ 2) := by
  intro f _
  use Measurable.maximalFunction.aestronglyMeasurable
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖ₑ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, wnorm', toReal_one, inv_one, ENNReal.rpow_one, reduceIte, eLpNorm,
    one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self, iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hBₗ : (Bₗ t).Countable := h𝓑.mono (fun i hi ↦ mem_of_mem_inter_left hi)
  refine le_trans ?_ (hBₗ.measure_biUnion_le_lintegral (c := c) (r := r) (l := t)
    (u := fun x ↦ ‖f x‖ₑ) (R := R) ?_ ?_)
  · refine mul_right_mono <| μ.mono (fun x hx ↦ mem_iUnion₂.mpr ?_)
    -- We need a ball in `Bₗ t` containing `x`. Since `MB μ 𝓑 c r f x` is large, such a ball exists
    simp only [mem_setOf_eq] at hx
    -- replace hx := lt_of_lt_of_le hx coe_toNNReal_le_self
    simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one] at hx
    obtain ⟨i, ht⟩ := lt_iSup_iff.mp hx
    replace hx : x ∈ ball (c i) (r i) :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le (a := t)) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    refine ⟨i, ?_, hx⟩
    -- It remains only to confirm that the chosen ball is actually in `Bₗ t`
    simp only [ge_iff_le, mem_setOf_eq, Bₗ]
    have hi : i ∈ 𝓑 :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le (a := t)) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    exact ⟨hi, mul_le_of_le_div <| le_of_lt (by simpa [setLAverage_eq, hi, hx] using ht)⟩
  · exact fun i hi ↦ hR i (mem_of_mem_inter_left hi)
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

include A in
theorem MB_ae_ne_top [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R)
    {u : X → E} (hu : MemLp u 1 μ) : ∀ᵐ x : X ∂μ, MB μ 𝓑 c r u x ≠ ∞ := by
  simpa only [enorm_eq_self] using HasWeakType.MB_one h𝓑 hR |>.memWLp hu coe_lt_top |>.ae_ne_top

-- move
lemma MeasureTheory.MemLp.eLpNormEssSup_lt_top {α} [MeasurableSpace α] {μ : Measure α}
    {u : α → E} (hu : MemLp u ⊤ μ) : eLpNormEssSup u μ < ⊤ := by
  simp_rw [MemLp, eLpNorm_exponent_top] at hu
  exact hu.2

include A in
theorem MB_ae_ne_top' [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R)
    ⦃u : X → E⦄ (hu : MemLp u ∞ μ ∨ MemLp u 1 μ) : ∀ᵐ x : X ∂μ, MB μ 𝓑 c r u x ≠ ∞ := by
  obtain hu|hu := hu
  · refine .of_forall fun x ↦ ?_
    simp_rw [← lt_top_iff_ne_top, MB, maximalFunction, inv_one, rpow_one]
    calc
      _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator
        (fun x ↦ ⨍⁻ (y : X) in ball (c i) (r i), eLpNormEssSup u μ ∂μ) x := by
          gcongr; exact ENNReal.ae_le_essSup fun y ↦ ‖u y‖ₑ
      _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (fun x ↦ eLpNormEssSup u μ) x := by
          gcongr; exact setLaverage_const_le
      _ ≤ ⨆ i ∈ 𝓑, eLpNormEssSup u μ := by gcongr; exact indicator_le_self ..
      _ ≤ ⨆ i : ι, eLpNormEssSup u μ := by gcongr; exact iSup_const_le
      _ ≤ eLpNormEssSup u μ := iSup_const_le
      _ < ∞ := hu.eLpNormEssSup_lt_top
  · exact MB_ae_ne_top h𝓑 hR hu

include A in
protected theorem MeasureTheory.AESublinearOn.maximalFunction
    [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    AESublinearOn (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x)
    (fun f ↦ MemLp f ∞ μ ∨ MemLp f 1 μ) 1 μ := by
  let P := fun g ↦ g ∈ {f : X → E | MemLp f ∞ μ} + {f | MemLp f 1 μ}
  have hP : ∀ {g}, P g → LocallyIntegrable g μ := by
    rintro _ ⟨f, hf, g, hg, rfl⟩
    exact (MemLp.locallyIntegrable hf le_top).add (MemLp.locallyIntegrable hg le_rfl)
  simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one]
  refine AESublinearOn.biSup2 h𝓑 ?_ ?_ MemLp.zero MemLp.zero MemLp.add MemLp.add ?_ ?_ ?_
  · intro u hu
    filter_upwards [MB_ae_ne_top' h𝓑 hR (.inl hu)] with x hx
    simpa [MB, maximalFunction] using hx
  · intro u hu
    filter_upwards [MB_ae_ne_top h𝓑 hR hu] with x hx
    simpa [MB, maximalFunction] using hx
  · intro f c hf; exact hf.const_smul _
  · intro f c hf; exact hf.const_smul _
  · intro i _
    refine AESublinearOn.const (T μ c r i) P (fun hf hg ↦ T.add_le i (hP hf))
      (fun f d hf ↦ T.smul i) |>.indicator _

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
irreducible_def CMB (A p : ℝ≥0) : ℝ≥0 := C_realInterpolation ⊤ 1 ⊤ 1 p 1 (A ^ 2) 1 p⁻¹

lemma CMB_eq_of_one_lt_q {b q : ℝ≥0} (hq : 1 < q) :
    CMB b q = 2 * (q / (q - 1) * b ^ 2) ^ (q : ℝ)⁻¹ := by
  suffices ENNReal.toNNReal 2 * q ^ (q : ℝ)⁻¹ *
      (ENNReal.ofReal |q - 1|⁻¹).toNNReal ^ (q : ℝ)⁻¹ *
      (b ^ 2) ^ (q : ℝ)⁻¹ = 2 * (q / (q - 1) * b ^ 2) ^ (q : ℝ)⁻¹ by
    simpa [CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  norm_cast
  have e₁ : (ENNReal.ofReal |q - 1|⁻¹).toNNReal = (q - 1)⁻¹ := by
    rw [ofReal_inv_of_pos]; swap
    · rw [abs_sub_pos, NNReal.coe_ne_one]; exact hq.ne'
    rw [toNNReal_inv, inv_inj, ← NNReal.coe_one, ← NNReal.coe_sub hq.le, NNReal.abs_eq,
      ofReal_coe_nnreal, toNNReal_coe]
  rw [e₁, mul_assoc, ← NNReal.mul_rpow, mul_assoc, ← NNReal.mul_rpow, ← mul_assoc, div_eq_mul_inv]

lemma CMB_defaultA_two_eq {a : ℕ} : CMB (defaultA a) 2 = 2 ^ (a + (3 / 2 : ℝ)) := by
  suffices (2 : ℝ≥0) * 2 ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal |2 - 1|⁻¹).toNNReal ^ (2 : ℝ)⁻¹ *
      ((2 ^ a) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ = 2 ^ (a + 3 / (2 : ℝ)) by
    simpa [CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  rw [← NNReal.rpow_mul, show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
  repeat rw [NNReal.rpow_add two_ne_zero]
  norm_num
  ring

/-- Special case of equation (2.0.44). The proof is given between (9.0.12) and (9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
lemma hasStrongType_MB [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    (h𝓑 : 𝓑.Countable) {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) {p : ℝ≥0} (hp : 1 < p) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) p p μ μ (CMB A p) := by
  have h2p : 0 < p := by positivity
  rw [CMB]
  refine exists_hasStrongType_real_interpolation
    (T := fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x ) (p := p) (q := p) (A := 1) (t := (↑p)⁻¹)
    ⟨ENNReal.zero_lt_top, le_rfl⟩
    ⟨zero_lt_one, le_rfl⟩ (by norm_num) le_rfl ?_
    zero_lt_one (pow_pos (A_pos μ) 2)
    (by simp) (by simp)
    (fun f _ ↦ Measurable.maximalFunction.aestronglyMeasurable)
    ?_ (HasStrongType.MB_top |>.hasWeakType zero_lt_top)
    (HasWeakType.MB_one h𝓑 hR)
  · exact ⟨ENNReal.inv_pos.mpr coe_ne_top, ENNReal.inv_lt_one.mpr <| one_lt_coe_iff.mpr hp⟩
  exact (AESublinearOn.maximalFunction h𝓑 hR).1

lemma hasStrongType_MB_finite [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    (h𝓑 : 𝓑.Finite) {p : ℝ≥0} (hp : 1 < p) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) p p μ μ (CMB A p) :=
  hasStrongType_MB h𝓑.countable (Finite.exists_image_le h𝓑 _).choose_spec hp

/-- The constant factor in the statement that `M_{𝓑, p}` has strong type. -/
irreducible_def C2_0_6 (A p₁ p₂ : ℝ≥0) : ℝ≥0 := CMB A (p₂ / p₁) ^ (p₁⁻¹ : ℝ)

/-- Equation (2.0.44). The proof is given between (9.0.34) and (9.0.36).
This is a special case of `hasStrongType_maximalFunction` below, which doesn't have the assumption
`hR` (but uses this result in its proof). -/
theorem hasStrongType_maximalFunction_aux
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Countable) {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (fun (u : X → E) x ↦ maximalFunction μ 𝓑 c r p₁ u x) p₂ p₂ μ μ
      (C2_0_6 A p₁ p₂) := by
  by_cases h : Nonempty X; swap
  · have := not_nonempty_iff.mp h; intro _ _; simp
  intro v mlpv
  refine ⟨Measurable.maximalFunction.aestronglyMeasurable, ?_⟩; dsimp only
  have cp₁p : 0 < (p₁ : ℝ) := by positivity
  have p₁n : p₁ ≠ 0 := by exact_mod_cast cp₁p.ne'
  conv_lhs =>
    enter [1, x]
    rw [maximalFunction_eq_MB cp₁p, ← enorm_eq_self (MB ..)]
  rw [eLpNorm_enorm_rpow _ (by positivity), ENNReal.ofReal_inv_of_pos cp₁p,
    ENNReal.ofReal_coe_nnreal, ← div_eq_mul_inv, ← ENNReal.coe_div p₁n]
  calc
    _ ≤ (CMB A (p₂ / p₁) * eLpNorm (fun y ↦ ‖v y‖ ^ (p₁ : ℝ)) (p₂ / p₁) μ) ^ p₁.toReal⁻¹ := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      convert (hasStrongType_MB h𝓑 hR (μ := μ) _ (fun x ↦ ‖v x‖ ^ (p₁ : ℝ)) _).2
      · rw [ENNReal.coe_div p₁n]
      · rwa [lt_div_iff₀, one_mul]; exact cp₁p
      · rw [ENNReal.coe_div p₁n]; exact mlpv.norm_rpow_div p₁
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), eLpNorm_norm_rpow _ cp₁p,
        ENNReal.ofReal_coe_nnreal, ENNReal.div_mul_cancel (by positivity) (by simp),
        ENNReal.rpow_rpow_inv (by positivity), ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
        C2_0_6]

variable (𝓑 r) in
def tr (k : ℕ) : Set ι := {i | i ∈ 𝓑 ∧ r i ≤ k}

lemma tr_subset (k : ℕ) : tr 𝓑 r k ⊆ 𝓑 :=
  fun _ hi => hi.left

lemma tr_radius_le (k : ℕ) : ∀ i ∈ tr 𝓑 r k, r i ≤ k :=
  fun _ hi => hi.right

lemma tr_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : tr 𝓑 r k₁ ⊆ tr 𝓑 r k₂ := by
  rintro _ ⟨hi₁, hi₂⟩
  exact ⟨hi₁, hi₂.trans (Nat.cast_le.mpr h)⟩

def maximalFunction_seq (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (q : ℝ) (k : ℕ)
    (u : X → E) (z : X) : ℝ≥0∞ :=
  maximalFunction μ (tr 𝓑 r k) c r q u z

lemma maximalFunction_seq_mono {p : ℝ} {𝓑 : Set ι} :
    Monotone (maximalFunction_seq (E := E) μ 𝓑 c r p) := by
  intro m n hmn u x
  apply iSup_le_iSup_of_subset
  exact tr_mono hmn

lemma maximalFunction_seq_eq (𝓑 : Set ι) (p : ℝ) :
    maximalFunction (E := E) μ 𝓑 c r p = fun u x => ⨆ k : ℕ, maximalFunction_seq μ 𝓑 c r p k u x := by
  ext u x
  simp only [maximalFunction_seq, maximalFunction, ←iSup_iUnion]
  congr!
  apply eq_of_subset_of_subset
  · intro i hi
    rcases exists_nat_ge (r i) with ⟨k, hk⟩
    exact mem_iUnion.mpr ⟨k, hi, hk⟩
  · intro i hi
    exact (mem_iUnion.mp hi).elim (fun _ p => p.left)


/-- Version of `hasWeakType_maximalFunction_equal_exponents` with the additional assumption `hR`.
-/
theorem hasWeakType_maximalFunction_equal_exponents_aux [BorelSpace X]
    {p : ℝ≥0} (h𝓑 : 𝓑.Countable) {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) (hp : 0 < p) :
    HasWeakType (maximalFunction (E := E) μ 𝓑 c r p) p p μ μ (A ^ ((2 / p : ℝ))) := by
  intro v mlpv
  constructor; · exact Measurable.maximalFunction.aestronglyMeasurable
  have cp : 0 < (p : ℝ) := by positivity
  have p₁n : p ≠ 0 := by exact_mod_cast cp.ne'
  conv_lhs =>
    enter [1, x]
    rw [maximalFunction_eq_MB cp]
  have hmb_one : wnorm (MB μ 𝓑 c r fun x ↦ ‖v x‖ ^ (p : ℝ)) 1 μ ≤ ↑A ^ 2 * eLpNorm (fun x ↦ ‖v x‖ ^ (p : ℝ)) 1 μ := by
    apply (HasWeakType.MB_one h𝓑 hR
      (fun x : X ↦ ‖v x‖ ^ (p : ℝ)) _).2
    convert MemLp.norm_rpow_div mlpv p
    exact Eq.symm (ENNReal.div_self (coe_ne_zero.mpr p₁n) coe_ne_top)
  unfold wnorm wnorm' distribution at hmb_one ⊢
  simp only [one_ne_top, ↓reduceIte, enorm_eq_self, toReal_one, inv_one, rpow_one, iSup_le_iff,
    coe_ne_top, coe_toReal] at hmb_one ⊢
  intro t
  by_cases ht : t = 0
  · rw [ht]; simp
  · apply (rpow_le_rpow_iff cp).mp
    rw [ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe]
    convert hmb_one (t ^ (p : ℝ))
    · exact Eq.symm (coe_rpow_of_ne_zero ht ↑p)
    · rw [rpow_inv_rpow (NNReal.coe_ne_zero.mpr p₁n)]
      congr; ext x; rw [coe_rpow_of_ne_zero ht ↑p]; exact (lt_rpow_inv_iff cp)
    · rw [eLpNorm_norm_rpow v cp, ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe,
          div_eq_mul_inv, rpow_mul, rpow_inv_rpow (NNReal.coe_ne_zero.mpr p₁n), rpow_two]; simp

/-- `hasStrongType_maximalFunction` minus the assumption `hR`.
A proof for basically this result is given in Chapter 9, everything following after equation
(9.0.36). -/
theorem hasStrongType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Countable) (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (maximalFunction (E := E) μ 𝓑 c r p₁) p₂ p₂ μ μ
      (C2_0_6 A p₁ p₂) := by
  rw [maximalFunction_seq_eq]
  apply hasStrongType_iSup_of_monotone maximalFunction_seq_mono
  intro n
  exact hasStrongType_maximalFunction_aux (h𝓑.mono (tr_subset n)) (tr_radius_le n) hp₁ hp₁₂

theorem hasWeakType_maximalFunction_equal_exponents
    [BorelSpace X] {p : ℝ≥0} (h𝓑 : 𝓑.Countable) (hp : 0 < p) :
    HasWeakType (maximalFunction (E := E) μ 𝓑 c r p) p p μ μ (A ^ (2 / p : ℝ)) := by
  rw [maximalFunction_seq_eq]
  apply hasWeakType_iSup_of_monotone maximalFunction_seq_mono (by positivity)
  intro n
  exact hasWeakType_maximalFunction_equal_exponents_aux (h𝓑.mono (tr_subset n)) (tr_radius_le n) hp

def C_weakType_maximalFunction (A p₁ p₂ : ℝ≥0) :=
  if p₁ = p₂ then (ofNNReal A) ^ (2 / p₁ : ℝ) else C2_0_6 A p₁ p₂

@[aesop (rule_sets := [finiteness]) safe apply]
lemma C_weakType_maximalFunction_lt_top {A p₁ p₂ : ℝ≥0} :
    C_weakType_maximalFunction A p₁ p₂ < ∞ := by
  unfold C_weakType_maximalFunction
  split_ifs with hps
  · apply rpow_lt_top_of_nonneg (by positivity) (by simp)
  · simp

/-- `hasStrongType_maximalFunction` minus the assumption `hR`, but where `p₁ = p₂` is possible and
we only conclude a weak-type estimate. -/
theorem hasWeakType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Countable) (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂) :
    HasWeakType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x)
      p₂ p₂ μ μ (C_weakType_maximalFunction A p₁ p₂) := by
  unfold C_weakType_maximalFunction
  split_ifs with hps
  · rw [← hps]
    exact hasWeakType_maximalFunction_equal_exponents (A := A) h𝓑 hp₁
  · apply HasStrongType.hasWeakType (coe_lt_coe_of_lt (hp₁.trans_le hp₁₂))
    exact hasStrongType_maximalFunction h𝓑 hp₁ (lt_of_le_of_ne hp₁₂ hps)

section GMF

variable [ProperSpace X]

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6.
`p` is `1` in the blueprint, and `globalMaximalFunction μ p u = (M (u ^ p)) ^ p⁻¹ ` -/
@[nolint unusedArguments]
def globalMaximalFunction [μ.IsDoubling A] (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  A ^ 2 * maximalFunction μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
    (·.1) (fun x ↦ 2 ^ (x.2)) p u x

protected theorem MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    [BorelSpace X] {p : ℝ} {u : X → E} : AEStronglyMeasurable (globalMaximalFunction μ p u) μ :=
  Measurable.maximalFunction.aestronglyMeasurable
    |>.aemeasurable.const_mul _ |>.aestronglyMeasurable

/-- Equation (2.0.45) -/
theorem laverage_le_globalMaximalFunction [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {u : X → E} {z x : X} {r : ℝ} (h : dist x z < r) :
    ⨍⁻ y in ball z r, ‖u y‖ₑ ∂μ ≤ globalMaximalFunction μ 1 u x := by
  rw [globalMaximalFunction, maximalFunction]
  simp only [gt_iff_lt, mem_prod, mem_univ, and_true, ENNReal.rpow_one, inv_one]
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h
  obtain ⟨c, hc, m, h_subset, _, h_subset'⟩ := exists_ball_subset_ball_two z hr
  calc
    _ ≤ (μ (ball z r))⁻¹ * ∫⁻ y in ball c (2 ^ m), ‖u y‖ₑ ∂μ := by
      simp only [laverage, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
        lintegral_smul_measure, smul_eq_mul]
      gcongr
    _ ≤ A ^ 2 * (μ (ball c (2 ^ m)))⁻¹ * ∫⁻ y in ball c (2 ^ m), ‖u y‖ₑ ∂μ := by
      gcongr
      rw [mul_comm,
          ← ENNReal.mul_le_iff_le_inv
            ((measure_ball_pos _ (by positivity) (μ := μ)).ne') (by finiteness),
          ENNReal.mul_inv_le_iff ((measure_ball_pos _ hr (μ := μ)).ne') (by finiteness)]
      exact (μ.mono h_subset').trans <| measure_ball_four_le_same z r
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
      refine (le_iSup₂ (c, m) hc).trans_eq' ?_
      simp [laverage, indicator_of_mem (h_subset h)]

theorem lintegral_ball_le_volume_globalMaximalFunction [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {u : X → E} {z x : X} {r : ℝ} (h : dist x z < r) :
    ∫⁻ y in (ball z r), ‖u y‖ₑ ∂μ  ≤ μ (ball z r) * globalMaximalFunction μ 1 u x := by
  have : IsFiniteMeasure (μ.restrict (ball z r)) := isFiniteMeasure_restrict.mpr (by finiteness)
  rw [← measure_mul_laverage]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  gcongr
  exact laverage_le_globalMaximalFunction h

/-- The constant factor in the statement that `M` has strong type. -/
def C2_0_6' (A p₁ p₂ : ℝ≥0) : ℝ≥0 := A ^ 2 * C2_0_6 A p₁ p₂

lemma C2_0_6'_defaultA_one_two_eq {a : ℕ} : C2_0_6' (defaultA a) 1 2 = 2 ^ (3 * a + 3 / (2 : ℝ)) := by
  simp_rw [C2_0_6', C2_0_6, div_one, CMB_defaultA_two_eq, defaultA, Nat.cast_pow, Nat.cast_ofNat,
    NNReal.coe_one, inv_one, NNReal.rpow_one, ← pow_mul, ← NNReal.rpow_natCast]
  rw [← NNReal.rpow_add (by simp)]
  congr 1
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field

lemma C2_0_6'_defaultA_one_le {a : ℕ} {q : ℝ≥0} (hq : 1 < q) :
    C2_0_6' (defaultA a) 1 q ≤ 2 ^ (4 * a + 1) * (q / (q - 1)) := by
  rw [C2_0_6', C2_0_6, div_one, defaultA, Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_one,
    inv_one, NNReal.rpow_one, CMB_eq_of_one_lt_q hq]
  calc
    _ ≤ (2 ^ a) ^ 2 * (2 * (q / (q - 1) * (2 ^ a) ^ 2)) := by
      conv_rhs => enter [2, 2]; rw [← NNReal.rpow_one (_ * _)]
      gcongr
      · nth_rw 1 [← mul_one 1]; gcongr
        · exact (one_le_div (tsub_pos_of_lt hq)).mpr tsub_le_self
        · norm_cast; rw [← pow_mul]; exact Nat.one_le_two_pow
      · rw [inv_le_one_iff₀]; right; exact_mod_cast hq.le
    _ = _ := by ring

/-- Equation (2.0.46). Easy from `hasStrongType_maximalFunction` -/
theorem hasStrongType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (globalMaximalFunction μ p₁ (E := E))
      p₂ p₂ μ μ (C2_0_6' A p₁ p₂) := by
  apply HasStrongType.const_mul (c := C2_0_6 A p₁ p₂)
  exact hasStrongType_maximalFunction countable_globalMaximalFunction hp₁ hp₁₂

def C_weakType_globalMaximalFunction (A p₁ p₂ : ℝ≥0) :=
  A ^ 2 * C_weakType_maximalFunction A p₁ p₂

lemma C_weakType_globalMaximalFunction_lt_top {A p₁ p₂ : ℝ≥0} :
    C_weakType_globalMaximalFunction A p₁ p₂ < ∞ :=
  mul_lt_top (by simp) (by finiteness)

-- the constant here `A ^ 4` can be improved
theorem hasWeakType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂) :
    HasWeakType (globalMaximalFunction μ p₁ (E := E))
      p₂ p₂ μ μ (C_weakType_globalMaximalFunction A p₁ p₂) := by
  convert HasWeakType.const_mul (c := C_weakType_maximalFunction A p₁ p₂) (e := A ^ 2)
    (coe_ne_zero.mpr (hp₁.trans_le hp₁₂).ne') _
  exact hasWeakType_maximalFunction countable_globalMaximalFunction hp₁ hp₁₂

/-- Use `lowerSemiContinuous_MB` -/
lemma lowerSemiContinuous_globalMaximalFunction :
    LowerSemicontinuous (globalMaximalFunction μ 1 f) := by
  by_cases h : A = 0; · unfold globalMaximalFunction; simp_rw [h]; simp [lowerSemicontinuous_const]
  have : globalMaximalFunction μ 1 f = fun x : X ↦
      ofNNReal A ^ 2 * MB μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
      (fun x ↦ x.1) (fun x ↦ 2 ^ x.2) (fun x ↦ ‖f x‖ ^ (1 : ℝ)) x ^ (1 : ℝ)⁻¹ :=
    funext fun x ↦ congr_arg (HMul.hMul ((A : ℝ≥0∞) ^ 2)) (maximalFunction_eq_MB zero_lt_one)
  rw [this]
  simp only [gt_iff_lt, Real.rpow_one, inv_one, rpow_one]
  refine lowerSemicontinuous_iff_isOpen_preimage.mpr fun y ↦ ?_
  by_cases hy : y = ∞; · rw [hy]; simp
  have : (fun x : X ↦ ofNNReal A ^ 2 * MB μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
      (fun x ↦ x.1) (fun x ↦ 2 ^ x.2) (fun x ↦ ‖f x‖) x)⁻¹' Ioi y =
      (fun x : X ↦ MB μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ)) (fun x ↦ x.1)
      (fun x ↦ 2 ^ x.2) (fun x ↦ ‖f x‖ ) x)⁻¹' Ioi (y / A ^ 2) := by
    ext x
    simp only [gt_iff_lt, mem_preimage, mem_Ioi]
    refine ⟨fun h₀ ↦ div_lt_of_lt_mul' h₀, fun h₀ ↦ ?_⟩; rw [mul_comm]; exact
        (ENNReal.div_lt_iff (Or.inl (ENNReal.pow_ne_zero (coe_ne_zero.mpr h) 2)) (Or.inr hy)).mp h₀
  rw [this]
  exact LowerSemicontinuous.isOpen_preimage lowerSemiContinuous_maximalFunction _

theorem globalMaximalFunction_ae_lt_top [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : MemLp u p₂ μ) :
    ∀ᵐ x ∂μ, globalMaximalFunction μ p₁ u x < ∞ := by
  simp_rw [lt_top_iff_ne_top]
  conv => arg 1; intro x; rw [← enorm_eq_self (x := globalMaximalFunction μ p₁ u x)]
  exact MemWLp.ae_ne_top ((hasWeakType_globalMaximalFunction hp₁ hp₁₂.le).memWLp hu
    C_weakType_globalMaximalFunction_lt_top)

theorem globalMaximalFunction_lt_top {p : ℝ≥0} (hp₁ : 0 < p)
    {u : X → E} (hu : MemLp u ⊤ μ) {x : X} :
    globalMaximalFunction μ p u x < ∞ := by
  unfold globalMaximalFunction
  rw [maximalFunction_eq_MB (by positivity)]
  apply mul_lt_top (by simp) (rpow_lt_top_of_nonneg (by simp) (lt_top_iff_ne_top.mp _))
  have : MemLp (fun x ↦ ‖u x‖ ^ p.toReal) ⊤ μ := by
    have rw1 : p.toReal = (p : ℝ≥0∞).toReal := by simp
    have rw2 : (⊤ : ℝ≥0∞) = ⊤ / p := by simp
    rw [rw1, rw2, memLp_norm_rpow_iff hu.aestronglyMeasurable (by positivity) (by simp)]
    exact hu
  exact lt_of_le_of_lt MB_le_eLpNormEssSup (this.eLpNormEssSup_lt_top)

end GMF


section UnusedContinuity

open scoped Topology in
lemma continuous_integral_ball [OpensMeasurableSpace X]
    (g : X → ℝ≥0∞) (hg : ∀ x : X, ∀ r > (0 : ℝ), ∫⁻ (y : X) in ball x r, g y ∂μ < ⊤)
    (hg2 : AEMeasurable g μ) (hμ : ∀ z : X, ∀ r > (0 : ℝ), μ (sphere z r) = 0 ):
    ContinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, g y ∂μ) (univ ×ˢ Ioi 0) := by
  intro x hx
  have hx_pos : x.2 > 0 := by simp only [mem_prod, mem_univ, mem_Ioi, true_and] at hx; exact hx
  unfold ContinuousWithinAt
  dsimp only
  have : (fun x : X × ℝ ↦ ∫⁻ (y : X) in ball x.1 x.2, g y ∂μ) =
      fun x : X × ℝ ↦ ∫⁻ (y : X), (ball x.1 x.2).indicator g y ∂μ := by
    ext x
    rw [← lintegral_indicator measurableSet_ball]
  rw [this, ← lintegral_indicator measurableSet_ball]
  apply tendsto_of_seq_tendsto
  intro z hz
  have hz' : Tendsto z atTop (𝓝 x) := tendsto_nhds_of_tendsto_nhdsWithin hz
  have := isBounded_range_of_tendsto z hz'
  obtain ⟨r, hr⟩ := Bornology.IsBounded.subset_ball this x
  simp only [range, ball, setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff] at hr
  simp_rw [Prod.dist_eq] at hr
  have hsub (n : ℕ) : ball (z n).1 (z n).2 ⊆ ball x.1 (x.2 + 2 * r) := by
    intro y hy
    simp only [ball, mem_setOf_eq] at hy ⊢
    calc dist y x.1
    _  ≤ dist y (z n).1 + dist (z n).1 x.1 := dist_triangle y (z n).1 x.1
    _ ≤ (z n).2 + dist (z n).1 x.1 := by gcongr
    _ ≤ |(z n).2| + dist (z n).1 x.1 := by gcongr; exact le_abs_self (z n).2
    _ = |(z n).2 - x.2 + x.2| + dist (z n).1 x.1 := by rw [sub_add_cancel]
    _ ≤ |(z n).2 - x.2| + |x.2| + dist (z n).1 x.1 := by gcongr; exact abs_add_le _ _
    _ < r + |x.2| + r := by
      gcongr
      · calc
        _ = dist (z n).2 x.2 := by rw [← Real.dist_eq]
        _ ≤ _ := le_max_right (dist (z n).1 x.1) (dist (z n).2 x.2)
        _ < r := hr _
      · calc
        _ ≤ _ := le_max_left (dist (z n).1 x.1) (dist (z n).2 x.2)
        _ < r := hr _
    _ = r + x.2 + r := by
      congr
      simp only [mem_prod, mem_univ, mem_Ioi, true_and] at hx; rw [abs_of_nonneg hx.le]
    _ = x.2 + 2 * r := by linarith
  let bound := (ball x.1 (x.2 + 2 * r)).indicator g
  apply tendsto_lintegral_of_dominated_convergence' bound
  · exact fun _ ↦ hg2.indicator measurableSet_ball
  · intro n
    filter_upwards with a
    unfold bound indicator
    split_ifs with h₀ h₁
    · simp
    · contrapose! h₁; exact hsub n h₀
    · simp
    · simp
  · unfold bound
    rw [lintegral_indicator measurableSet_ball]
    apply ne_of_lt
    apply hg
    have : 0 < r := by
      calc
      0 ≤ dist (z 0).1 x.1 := dist_nonneg
      _ ≤ max (dist (z 0).1 x.1) (dist (z 0).2 x.2) := le_max_left _ _
      _ < r := hr _
    linarith
  · have : ∀ᵐ z : X ∂μ, dist z x.1 ≠ x.2 := by
      change (μ ({z | ¬ (dist z x.1 ≠ x.2)}) = 0)
      simpa only [ne_eq, Decidable.not_not] using hμ x.1 x.2 hx_pos
    filter_upwards [this] with y hy
    by_cases hy2 : dist y x.1 < x.2
    · simp only [indicator, ball, mem_setOf_eq]
      split_ifs
      apply tendsto_nhds_of_eventually_eq
      have hz2 : ∀ᶠ n : ℕ in atTop, dist y (z n).1 < (z n).2 := by
        let dist_sub (a : X × ℝ) := dist y a.1 - a.2
        have : ContinuousOn dist_sub (univ ×ˢ Ioi 0) := by fun_prop
        have : Tendsto (dist_sub ∘ z) atTop (𝓝 (dist_sub x)) := Tendsto.comp (this x hx) hz
        have : ∀ᶠ (n : ℕ) in atTop, dist y (z n).1 - (z n).2 < 0 := by
          rw [← sub_lt_zero] at hy2; exact Tendsto.eventually_lt_const hy2 this
        filter_upwards [this]; simp
      filter_upwards [hz2]; intro a ha; split_ifs; rfl
    · have hz2 : ∀ᶠ n : ℕ in atTop, dist y (z n).1 > (z n).2 := by
        let dist_sub (a : X × ℝ) := dist y a.1 - a.2
        have : ContinuousOn dist_sub (univ ×ˢ Ioi 0) := by fun_prop
        have hcmp : Tendsto (dist_sub ∘ z) atTop (𝓝 (dist_sub x)) := Tendsto.comp (this x hx) hz
        have hy2 : dist y x.1 > x.2 := by order
        have hy2 : 0 < dist y x.1 - x.2 := sub_pos.mpr hy2
        have : ∀ᶠ (n : ℕ) in atTop, 0 < dist y (z n).1 - (z n).2 := Tendsto.eventually_const_lt hy2 hcmp
        filter_upwards [this]; simp
      simp only [indicator, ball, mem_setOf_eq]
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hz2] with n hn
      have : ¬ (dist y (z n).1 < (z n).2) := by linarith
      split_ifs; rfl

-- unused in Carleson
-- move to separate file (not sure where)
lemma continuous_average_ball [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace X]
    [ProperSpace X] (hf : LocallyIntegrable f μ)
    (hμ : ∀ z : X, ∀ r > (0 : ℝ), μ (sphere z r) = 0) :
    ContinuousOn (fun x : X × ℝ ↦ ⨍⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
  rw [(isOpen_univ.prod isOpen_Ioi).continuousOn_iff]
  intro x hx
  have hx_pos : 0 < x.2 := by simp only [mem_prod, mem_univ, mem_Ioi, true_and] at hx; exact hx
  have : (fun x : X × ℝ ↦ ⨍⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) =
    fun x : X × ℝ ↦ (μ (ball x.1 x.2))⁻¹ * ∫⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ
     := by ext x; simp [laverage]
  rw [this]
  apply ENNReal.Tendsto.mul
  · apply Tendsto.inv
    have : (fun z : X × ℝ ↦ μ (ball z.1 z.2)) =
        (fun z : X × ℝ ↦ ∫⁻ (y : X) in ball z.1 z.2, (1 : ℝ≥0∞) ∂μ) := by simp
    rw [this, (setLIntegral_one (ball x.1 x.2)).symm]
    have : ContinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, (1 : ℝ≥0∞) ∂μ) (univ ×ˢ Ioi 0) := by
      apply continuous_integral_ball _ _ aemeasurable_const hμ
      intro p r hr; rw [setLIntegral_one]; finiteness
    rw [(isOpen_univ.prod isOpen_Ioi).continuousOn_iff] at this
    apply this hx
  · exact Or.inr (hf.integrableOn_ball.right.ne)
  · have : ContinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
      apply continuous_integral_ball _ _ _ hμ
      · exact fun x r hr ↦ hf.integrableOn_ball.right
      · exact hf.aestronglyMeasurable.enorm
    rw [(isOpen_univ.prod isOpen_Ioi).continuousOn_iff] at this
    exact this hx
  · exact Or.inr (inv_ne_top.mpr (measure_ball_pos μ x.1 hx_pos).ne')

open scoped Topology in
-- unused in Carleson
-- move to separate file (not sure where)
lemma lowerSemiContinuousOn_integral_ball [OpensMeasurableSpace X] (hf2 : AEStronglyMeasurable f μ) :
    LowerSemicontinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
  refine lowerSemicontinuousOn_iff_le_liminf.mpr fun x hx ↦ _root_.le_of_forall_pos_le_add ?_
  intro δ hδ
  let M := liminf (fun x ↦ ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ) (𝓝[univ ×ˢ Ioi 0] x) + δ
  by_cases htop : liminf (fun x ↦ ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ) (𝓝[univ ×ˢ Ioi 0] x) = ∞
  · rw [htop]; simp
  have hM : liminf (fun x ↦ ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ)
      (𝓝[univ ×ˢ Ioi 0] x) < M := lt_add_right htop hδ.ne'
  have : ∃ᶠ (z : X × ℝ) in 𝓝[univ ×ˢ Ioi 0] x, ∫⁻ (y : X) in ball z.1 z.2, ‖f y‖ₑ ∂μ < M := by
    refine frequently_lt_of_liminf_lt ?_ hM
    simp only [IsCoboundedUnder, Filter.IsCobounded, ge_iff_le, eventually_map]
    use ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ
    intro a ha; apply Eventually.self_of_nhdsWithin ha hx
  obtain ⟨ns, hns₀, hns₁⟩ :=
    exists_seq_forall_of_frequently (l := 𝓝[univ ×ˢ Ioi 0] x)
        (p := fun z ↦ ∫⁻ (y : X) in ball z.1 z.2, ‖f y‖ₑ ∂μ < M) this
  let g (n : ℕ) := (ball (ns n).1 (ns n).2).indicator (fun y ↦ ‖f y‖ₑ)
  have (z : X) : (ball x.1 x.2).indicator (fun y ↦ ‖f y‖ₑ) z ≤
      liminf (fun n ↦ g n z) atTop := by
    apply le_liminf_of_le (f := atTop)
    unfold g indicator
    split_ifs with hz
    · have hz2 : ∀ᶠ n : ℕ in atTop, z ∈ ball (ns n).1 (ns n).2 := by
        let dist_sub (y : X × ℝ) := dist z y.1 - y.2
        have : ContinuousOn dist_sub (univ ×ˢ Ioi 0) := by fun_prop
        have : Tendsto (dist_sub ∘ ns) atTop (𝓝 (dist_sub x)) := Tendsto.comp (this x hx) hns₀
        have : ∀ᶠ (n : ℕ) in atTop, dist z (ns n).1 - (ns n).2 < 0 := by
          rw [mem_ball, ← sub_lt_zero] at hz; exact Tendsto.eventually_lt_const hz this
        filter_upwards [this]; simp
      filter_upwards [hz2]; intro a ha; split_ifs; rfl
    · simp
  calc
  ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ
    ≤ ∫⁻ y, (ball x.1 x.2).indicator (fun z ↦ ‖f z‖ₑ) y ∂μ := by
    rw [lintegral_indicator]; exact measurableSet_ball
  _ ≤ ∫⁻ y, liminf (fun n ↦ g n y) atTop ∂μ := by gcongr with y; exact this y
  _ ≤ liminf (fun n ↦ ∫⁻ y, g n y ∂μ) atTop := by
    apply lintegral_liminf_le' fun n ↦ by fun_prop (discharger := measurability)
  _ ≤ M := by
    apply liminf_le_of_le (f := atTop)
    intro b hb
    simp only [eventually_atTop, ge_iff_le] at hb
    obtain ⟨a, ha⟩ := hb
    exact le_of_lt <| lt_of_le_of_lt (ha a le_rfl) <|
      by unfold g; rw [lintegral_indicator measurableSet_ball]; exact hns₁ a

end UnusedContinuity
