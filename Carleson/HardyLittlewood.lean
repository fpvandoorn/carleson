import Carleson.DoublingMeasure
import Carleson.RealInterpolation
import Mathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter
open scoped NNReal ENNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

section Prelude

variable (X : Type*) [PseudoMetricSpace X] [SeparableSpace X]

/-- Lemma 9.0.2 -/
lemma covering_separable_space :
    ∃ C : Set X, C.Countable ∧ ∀ r > 0, ⋃ c ∈ C, ball c r = univ := by
  simp_rw [← Metric.dense_iff_iUnion_ball, exists_countable_dense]

lemma countable_globalMaximalFunction :
    (covering_separable_space X).choose ×ˢ (univ : Set ℤ) |>.Countable :=
  (covering_separable_space X).choose_spec.1.prod countable_univ

end Prelude

variable {X E : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsDoubling A] [NormedAddCommGroup E]
  {f : X → E} {x : X} {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ}
  -- feel free to assume `A ≥ 16` or similar

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑.
M_{𝓑, p} in the blueprint. -/
def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ)
    (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖u y‖₊ ^ p ∂μ) ^ p⁻¹

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑 with exponent 1.
M_𝓑 in the blueprint. -/
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ 𝓑 c r 1 u x

lemma maximalFunction_eq_MB
    {μ : Measure X} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ} {p : ℝ} {u : X → E} {x : X} (hp : 0 ≤ p) :
    maximalFunction μ 𝓑 c r p u x = (MB μ 𝓑 c r (‖u ·‖ ^ p) x) ^ p⁻¹ := by
  unfold MB maximalFunction; rw [← ENNReal.rpow_mul, inv_one, one_mul]; congr! 8
  rw [ENNReal.rpow_one, ← ENNReal.coe_rpow_of_nonneg _ hp, ENNReal.coe_inj,
    Real.nnnorm_rpow_of_nonneg (by simp), nnnorm_norm]

-- We will replace the criterion `P` used in `MeasureTheory.AESublinearOn.maximalFunction` with the
-- weaker criterion `LocallyIntegrable` that is closed under addition and scalar multiplication.

variable (μ) in
private def P (f : X → E) : Prop := Memℒp f ∞ μ ∨ Memℒp f 1 μ

private lemma LocallyIntegrable_of_P [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ]
    {u : X → E} (hu : P μ u) : LocallyIntegrable u μ := by
  refine hu.elim (Memℒp.locallyIntegrable · le_top) (Memℒp.locallyIntegrable · le_rfl)

-- The average that appears in the definition of `MB`
variable (μ c r) in
private def T (i : ι) (u : X → E) := (⨍⁻ (y : X) in ball (c i) (r i), ‖u y‖₊ ∂μ).toReal

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_of_isBounded [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : IsBounded s) : IntegrableOn f s μ :=
  hf.integrableOn_isCompact hs.isCompact_closure |>.mono_set subset_closure

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_ball [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {x : X} {r : ℝ} : IntegrableOn f (ball x r) μ :=
  hf.integrableOn_of_isBounded isBounded_ball

-- move
lemma MeasureTheory.LocallyIntegrable.laverage_ball_lt_top
    [MeasurableSpace E] [BorelSpace E] [BorelSpace X] [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ)
    {x₀ : X} {r : ℝ} :
    ⨍⁻ x in ball x₀ r, ‖f x‖₊ ∂μ < ⊤ :=
  laverage_lt_top hf.integrableOn_ball.2.ne

private lemma T.add_le [MeasurableSpace E] [BorelSpace E] [BorelSpace X] [ProperSpace X]
    (i : ι) {f g : X → E} (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) :
    ‖T μ c r i (f + g)‖ ≤ ‖T μ c r i f‖ + ‖T μ c r i g‖ := by
  simp only [T, Pi.add_apply, Real.norm_eq_abs, ENNReal.abs_toReal]
  rw [← ENNReal.toReal_add hf.laverage_ball_lt_top.ne hg.laverage_ball_lt_top.ne, ENNReal.toReal_le_toReal]
  · rw [← laverage_add_left hf.integrableOn_ball.aemeasurable.ennnorm]
    exact laverage_mono (fun x ↦ ENNNorm_add_le (f x) (g x))
  · exact (hf.add hg).laverage_ball_lt_top.ne
  · exact (ENNReal.add_lt_top.2 ⟨hf.laverage_ball_lt_top, hg.laverage_ball_lt_top⟩).ne

private lemma T.smul [NormedSpace ℝ E] (i : ι) : ∀ {f : X → E} {d : ℝ}, LocallyIntegrable f μ →
    d ≥ 0 → T μ c r i (d • f) = d • T μ c r i f := by
  intro f d _ hd
  simp_rw [T, Pi.smul_apply, smul_eq_mul]
  nth_rewrite 2 [← (ENNReal.toReal_ofReal hd)]
  rw [← ENNReal.toReal_mul]
  congr
  rw [laverage_const_mul ENNReal.ofReal_ne_top]
  congr
  ext x
  simp only [nnnorm_smul, ENNReal.coe_mul, ← Real.toNNReal_eq_nnnorm_of_nonneg hd]
  congr

-- todo: move
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
  by_cases ht : ∀ a ∈ t, r a < 0
  · refine ⟨t, .rfl, fun a ha b _ _ ↦ by
      simp only [Function.onFun, closedBall_eq_empty.2 (ht a ha), empty_disjoint],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset],
      fun u hut hu ↦ (ht u hut).not_le hu |>.elim⟩⟩
  push_neg at ht
  let t' := { a ∈ t | 0 ≤ r a }
  have h2τ : 1 < (τ - 1) / 2 := by linarith
  rcases exists_disjoint_subfamily_covering_enlargment (fun a => closedBall (x a) (r a)) t' r
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
  rcases le_or_lt 0 (r a) with (h'a | h'a)
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
  obtain h2a|h2a := le_or_lt (r a) 0
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

/- NOTE: This was changed to use `ℝ≥0∞` rather than `ℝ≥0` because that was more convenient for the
proof of `first_exception'` in ExceptionalSet.lean. But everything involved there is finite, so
you can prove this with `ℝ≥0` and deal with casting between `ℝ≥0` and `ℝ≥0∞` there, if that turns
out to be easier. -/
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
          refine l.mul_left_mono (μ.mono fun x hx ↦ ?_)
          simp only [mem_iUnion, mem_ball, exists_prop] at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑
          refine mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) :=
          l.mul_left_mono <| measure_biUnion_le μ (h𝓑.mono hB𝓑) fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
          refine l.mul_left_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
          rw [sq, sq, mul_assoc, mul_assoc]
          apply (measure_ball_two_le_same (c i) (2 * r i)).trans
          exact ENNReal.mul_left_mono (measure_ball_two_le_same (c i) (r i))
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc, mul_comm l]
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := by
          gcongr; exact h2u _ (hB𝓑 (Subtype.coe_prop _))
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := by
          congr; simpa using (lintegral_iUnion (fun i ↦ measurableSet_ball) disj u).symm
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := by
          gcongr; exact setLIntegral_le_lintegral (⋃ i ∈ B, ball (c i) (r i)) u

protected theorem Finset.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (𝓑 : Finset ι)
    (l : ℝ≥0∞) (u : X → ℝ≥0∞)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  :=
  let ⟨c, hc⟩ := 𝓑.exists_image_le r
  𝓑.countable_toSet.measure_biUnion_le_lintegral l u c hc h2u

protected theorem MeasureTheory.AEStronglyMeasurable.maximalFunction [BorelSpace X] {p : ℝ}
    {u : X → E} (h𝓑 : 𝓑.Countable) : AEStronglyMeasurable (maximalFunction μ 𝓑 c r p u) μ :=
  (AEMeasurable.biSup 𝓑 h𝓑 fun _ _ ↦ aemeasurable_const.indicator measurableSet_ball).pow
    aemeasurable_const |>.aestronglyMeasurable

theorem MeasureTheory.AEStronglyMeasurable.maximalFunction_toReal [BorelSpace X]
    {p : ℝ} {u : X → E} (h𝓑 : 𝓑.Countable) :
    AEStronglyMeasurable (fun x ↦ maximalFunction μ 𝓑 c r p u x |>.toReal) μ :=
  AEStronglyMeasurable.maximalFunction h𝓑 |>.ennreal_toReal

theorem MB_le_eLpNormEssSup {u : X → E} {x : X} : MB μ 𝓑 c r u x ≤ eLpNormEssSup u μ :=
  calc MB μ 𝓑 c r u x ≤
    ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
        fun _x ↦ ⨍⁻ _y in ball (c i) (r i), eLpNormEssSup u μ ∂μ := by
        simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one]
        gcongr
        exact setLAverage_mono_ae <| coe_nnnorm_ae_le_eLpNormEssSup u μ
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x) fun _x ↦ eLpNormEssSup u μ := by
      gcongr; apply setLaverage_const_le
    _ ≤ ⨆ i ∈ 𝓑, eLpNormEssSup u μ := by gcongr; apply indicator_le_self
    _ ≤ eLpNormEssSup u μ := by
      simp_rw [iSup_le_iff, le_refl, implies_true]

protected theorem HasStrongType.MB_top [BorelSpace X] (h𝓑 : 𝓑.Countable) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) ⊤ ⊤ μ μ 1 := by
  intro f _
  use AEStronglyMeasurable.maximalFunction_toReal h𝓑
  simp only [ENNReal.coe_one, one_mul, eLpNorm_exponent_top]
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun x ↦ ?_)
  simp_rw [ENNReal.nnorm_toReal]
  exact ENNReal.coe_toNNReal_le_self |>.trans MB_le_eLpNormEssSup

protected theorem MeasureTheory.AESublinearOn.maximalFunction
    [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] (h𝓑 : 𝓑.Finite) :
    AESublinearOn (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
    (fun f ↦ Memℒp f ∞ μ ∨ Memℒp f 1 μ) 1 μ := by
  apply AESublinearOn.antitone LocallyIntegrable_of_P
  simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one]
  apply AESublinearOn.biSup (P := (LocallyIntegrable · μ)) 𝓑 h𝓑.countable _ _
    LocallyIntegrable.add (fun hf _ ↦ hf.smul _)
  · intro i _
    let B := ball (c i) (r i)
    have (u : X → E) (x : X) : (B.indicator (fun _ ↦ ⨍⁻ y in B, ‖u y‖₊ ∂μ) x).toReal =
        (B.indicator (fun _ ↦ (⨍⁻ y in B, ‖u y‖₊ ∂μ).toReal) x) := by
      by_cases hx : x ∈ B <;> simp [hx]
    simp_rw [this]
    apply (AESublinearOn.const (T μ c r i) (LocallyIntegrable · μ) (T.add_le i)
      (fun f d ↦ T.smul i)).indicator
  · refine fun f hf ↦ ae_of_all _ (fun x ↦ ?_)
    by_cases h𝓑' : 𝓑.Nonempty; swap
    · simp [not_nonempty_iff_eq_empty.mp h𝓑']
    have ⟨i, _, hi⟩ := h𝓑.biSup_eq h𝓑' (fun i ↦ (ball (c i) (r i)).indicator
      (fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖f y‖₊ ∂μ) x)
    rw [hi]
    by_cases hx : x ∈ ball (c i) (r i)
    · simpa [hx] using hf.laverage_ball_lt_top.ne
    · simp [hx]

/- The proof is roughly between (9.0.12)-(9.0.22). -/
open ENNReal in
variable (μ) in
protected theorem HasWeakType.MB_one [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    HasWeakType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) 1 1 μ μ (A ^ 2) := by
  intro f _
  use AEStronglyMeasurable.maximalFunction_toReal h𝓑
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖₊ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, reduceIte, wnorm', one_toReal, inv_one, rpow_one, coe_pow, eLpNorm,
    one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self, iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hBₗ : (Bₗ t).Countable := h𝓑.mono (fun i hi ↦ mem_of_mem_inter_left hi)
  refine le_trans ?_ (hBₗ.measure_biUnion_le_lintegral (c := c) (r := r) (l := t)
    (u := fun x ↦ ‖f x‖₊) (R := R) ?_ ?_)
  · refine mul_left_mono <| μ.mono (fun x hx ↦ mem_iUnion₂.mpr ?_)
    -- We need a ball in `Bₗ t` containing `x`. Since `MB μ 𝓑 c r f x` is large, such a ball exists
    simp only [nnorm_toReal, mem_setOf_eq] at hx
    replace hx := lt_of_lt_of_le hx coe_toNNReal_le_self
    simp only [MB, maximalFunction, rpow_one, inv_one] at hx
    obtain ⟨i, ht⟩ := lt_iSup_iff.mp hx
    replace hx : x ∈ ball (c i) (r i) :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (coe_lt_coe.mp <| by simp [h] at ht)
    refine ⟨i, ?_, hx⟩
    -- It remains only to confirm that the chosen ball is actually in `Bₗ t`
    simp only [ge_iff_le, mem_setOf_eq, Bₗ]
    have hi : i ∈ 𝓑 :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (coe_lt_coe.mp <| by simp [h] at ht)
    exact ⟨hi, mul_le_of_le_div <| le_of_lt (by simpa [setLaverage_eq, hi, hx] using ht)⟩
  · exact fun i hi ↦ hR i (mem_of_mem_inter_left hi)
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
irreducible_def CMB (A p : ℝ≥0) : ℝ≥0 := C_realInterpolation ⊤ 1 ⊤ 1 p 1 (A ^ 2) 1 p⁻¹

/-- Special case of equation (2.0.44). The proof is given between (9.0.12) and (9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
lemma hasStrongType_MB [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    (h𝓑 : 𝓑.Finite) {p : ℝ≥0} (hp : 1 < p) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
      p p μ μ (CMB A p) := by
  have h2p : 0 < p := by positivity
  rw [CMB]
  apply exists_hasStrongType_real_interpolation
    (T := fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) (p := p) (q := p) (A := 1) ⟨ENNReal.zero_lt_top, le_rfl⟩
    ⟨zero_lt_one, le_rfl⟩ (by norm_num) zero_lt_one (by simp [inv_lt_one_iff₀, hp, h2p] : p⁻¹ ∈ _) zero_lt_one (pow_pos (A_pos μ) 2)
    (by simp [ENNReal.coe_inv h2p.ne']) (by simp [ENNReal.coe_inv h2p.ne'])
    (fun f _ ↦ AEStronglyMeasurable.maximalFunction_toReal h𝓑.countable)
    (AESublinearOn.maximalFunction h𝓑).1 (HasStrongType.MB_top h𝓑.countable |>.hasWeakType le_top)
    (HasWeakType.MB_one μ h𝓑.countable (h𝓑.exists_image_le r).choose_spec)

/-- The constant factor in the statement that `M_{𝓑, p}` has strong type. -/
irreducible_def C2_0_6 (A p₁ p₂ : ℝ≥0) : ℝ≥0 := CMB A (p₂ / p₁) ^ (p₁⁻¹ : ℝ)

/-- Equation (2.0.44). The proof is given between (9.0.34) and (9.0.36). -/
theorem hasStrongType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Finite) (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x |>.toReal)
      p₂ p₂ μ μ (C2_0_6 A p₁ p₂) := fun v mlpv ↦ by
  dsimp only
  constructor; · exact AEStronglyMeasurable.maximalFunction_toReal h𝓑.countable
  have cp₁p : 0 < (p₁ : ℝ) := by positivity
  have p₁n : p₁ ≠ 0 := by exact_mod_cast cp₁p.ne'
  conv_lhs =>
    enter [1, x]
    rw [maximalFunction_eq_MB (by exact zero_le_one.trans hp₁), ← ENNReal.toReal_rpow,
      ← ENNReal.abs_toReal, ← Real.norm_eq_abs]
  rw [eLpNorm_norm_rpow _ (by positivity), ENNReal.ofReal_inv_of_pos cp₁p,
    ENNReal.ofReal_coe_nnreal, ← div_eq_mul_inv, ← ENNReal.coe_div p₁n]
  calc
    _ ≤ (CMB A (p₂ / p₁) * eLpNorm (fun y ↦ ‖v y‖ ^ (p₁ : ℝ)) (p₂ / p₁) μ) ^ p₁.toReal⁻¹ := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      convert (hasStrongType_MB h𝓑 (μ := μ) _ (fun x ↦ ‖v x‖ ^ (p₁ : ℝ)) _).2
      · exact (ENNReal.coe_div p₁n).symm
      · rwa [lt_div_iff₀, one_mul]; exact cp₁p
      · rw [ENNReal.coe_div p₁n]; exact Memℒp.norm_rpow_div mlpv p₁
    _ ≤ _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), eLpNorm_norm_rpow _ cp₁p,
        ENNReal.ofReal_coe_nnreal, ENNReal.div_mul_cancel (by positivity) (by simp),
        ENNReal.rpow_rpow_inv (by positivity), ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
        C2_0_6]

section GMF

variable [ProperSpace X]

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6.
`p` is `1` in the blueprint, and `globalMaximalFunction μ p u = (M (u ^ p)) ^ p⁻¹ ` -/
@[nolint unusedArguments]
def globalMaximalFunction [μ.IsDoubling A] (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  A ^ 2 * maximalFunction μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
    (·.1) (2 ^ ·.2) p u x

-- prove only if needed. Use `MB_le_eLpNormEssSup`
theorem globalMaximalFunction_lt_top {p : ℝ≥0} (hp₁ : 1 ≤ p)
    {u : X → E} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u)) {x : X} :
    globalMaximalFunction μ p u x < ∞ := by
  sorry

protected theorem MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    [BorelSpace X] {p : ℝ} {u : X → E} : AEStronglyMeasurable (globalMaximalFunction μ p u) μ :=
  AEStronglyMeasurable.maximalFunction (countable_globalMaximalFunction X)
    |>.aemeasurable.const_mul _ |>.aestronglyMeasurable

/-- Equation (2.0.45). -/
theorem laverage_le_globalMaximalFunction {u : X → E} (hu : AEStronglyMeasurable u μ)
    (hu : IsBounded (range u)) {z x : X} {r : ℝ} (h : dist x z < r) :
    ⨍⁻ y, ‖u y‖₊ ∂μ.restrict (ball z r) ≤ globalMaximalFunction μ 1 u x := by
  sorry

/-- The constant factor in the statement that `M` has strong type. -/
def C2_0_6' (A p₁ p₂ : ℝ≥0) : ℝ≥0 := A ^ 2 * C2_0_6 A p₁ p₂

/-- Equation (2.0.46).
Easy from `hasStrongType_maximalFunction`. Ideally prove separately
`HasStrongType.const_smul` and `HasStrongType.const_mul`. -/
theorem hasStrongType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [Nonempty X] [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (fun (u : X → E) (x : X) ↦ globalMaximalFunction μ p₁ u x |>.toReal)
      p₂ p₂ μ μ (C2_0_6' A p₁ p₂) := by
  unfold globalMaximalFunction
  simp_rw [ENNReal.toReal_mul]
  -- apply HasStrongType.const_mul -- this needs to be adapted
  -- refine hasStrongType_maximalFunction ?_ hp₁ hp₁₂
  /- `hasStrongType_maximalFunction` currently requires the collection of balls `𝓑`
  to be finite, but its generalization to countable collectinos is already planned (see https://leanprover.zulipchat.com/#narrow/channel/442935-Carleson/topic/Hardy-Littlewood.20maximal.20principle.20for.20countable.20many.20balls/near/478069896).
  -/
  sorry


end GMF
