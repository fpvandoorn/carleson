import Carleson.ToMathlib.DoublingMeasure
import Carleson.ToMathlib.RealInterpolation
import Mathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter ENNReal Pointwise
open scoped NNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

section Prelude

variable {X : Type*} [PseudoMetricSpace X] [SeparableSpace X]

variable (X) in
/-- Lemma 9.0.2 -/
lemma covering_separable_space :
    ∃ C : Set X, C.Countable ∧ ∀ r > 0, ⋃ c ∈ C, ball c r = univ := by
  simp_rw [← Metric.dense_iff_iUnion_ball, exists_countable_dense]

lemma countable_globalMaximalFunction :
    (covering_separable_space X).choose ×ˢ (univ : Set ℤ) |>.Countable :=
  (covering_separable_space X).choose_spec.1.prod countable_univ

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

/-- Use the dominated convergence theorem
e.g. [Folland, Real Analysis. Modern Techniques and Their Applications, Lemma 3.16] -/
lemma continuous_average_ball (hf : LocallyIntegrable f μ) :
    ContinuousOn (fun x : X × ℝ ↦ ⨍⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
  sorry


/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑.
M_{𝓑, p} in the blueprint. -/
def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ)
    (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖u y‖ₑ ^ p ∂μ) ^ p⁻¹

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑 with exponent 1.
M_𝓑 in the blueprint. -/
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ 𝓑 c r 1 u x

lemma MB_def : MB μ 𝓑 c r f x = (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖f y‖ₑ ∂μ) := by
  unfold MB maximalFunction; simp_rw [inv_one, rpow_one]

lemma maximalFunction_eq_MB
    {μ : Measure X} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ} {p : ℝ} {u : X → E} {x : X} (hp : 0 ≤ p) :
    maximalFunction μ 𝓑 c r p u x = (MB μ 𝓑 c r (‖u ·‖ ^ p) x) ^ p⁻¹ := by
  rw [maximalFunction, MB_def]
  congr! 8
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ hp, ENNReal.coe_inj,
    Real.nnnorm_rpow_of_nonneg (by simp), nnnorm_norm]

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

-- move
lemma MeasureTheory.LocallyIntegrable.laverage_ball_lt_top [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ)
    {x₀ : X} {r : ℝ} :
    ⨍⁻ x in ball x₀ r, ‖f x‖ₑ ∂μ < ⊤ :=
  laverage_lt_top hf.integrableOn_ball.2.ne

private lemma T.add_le [MeasurableSpace E] [BorelSpace E] [BorelSpace X] [ProperSpace X]
    (i : ι) {f g : X → E} (hf : LocallyIntegrable f μ) :
    ‖T μ c r i (f + g)‖ₑ ≤ ‖T μ c r i f‖ₑ + ‖T μ c r i g‖ₑ := by
  simp only [T, Pi.add_apply, enorm_eq_self, ← enorm_eq_nnnorm]
  rw [← laverage_add_left hf.integrableOn_ball.aemeasurable.enorm]
  exact laverage_mono (fun x ↦ ENNNorm_add_le (f x) (g x))

-- move
lemma NNReal.smul_ennreal_eq_mul (x : ℝ≥0) (y : ℝ≥0∞) : x • y = x * y := rfl

private lemma T.smul [NormedSpace ℝ E] (i : ι) {f : X → E} {d : ℝ≥0} :
    T μ c r i (d • f) = d • T μ c r i f := by
  simp_rw [T, Pi.smul_apply, NNReal.smul_def, NNReal.smul_ennreal_eq_mul,
    laverage_const_mul ENNReal.coe_ne_top]
  simp [_root_.enorm_smul]

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
          refine mul_left_mono (μ.mono fun x hx ↦ ?_)
          simp only [mem_iUnion, mem_ball, exists_prop] at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑
          refine mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) :=
          mul_left_mono <| measure_biUnion_le μ (h𝓑.mono hB𝓑) fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
          refine mul_left_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
          rw [sq, sq, mul_assoc, mul_assoc]
          apply (measure_ball_two_le_same (c i) (2 * r i)).trans
          exact mul_left_mono (measure_ball_two_le_same (c i) (r i))
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
        exact MeasureTheory.enorm_ae_le_eLpNormEssSup u μ
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x) fun _x ↦ eLpNormEssSup u μ := by
      gcongr; apply setLaverage_const_le
    _ ≤ ⨆ i ∈ 𝓑, eLpNormEssSup u μ := by gcongr; apply indicator_le_self
    _ ≤ eLpNormEssSup u μ := by
      simp_rw [iSup_le_iff, le_refl, implies_true]

protected theorem HasStrongType.MB_top [BorelSpace X] (h𝓑 : 𝓑.Countable) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) ⊤ ⊤ μ μ 1 := by
  intro f _
  use AEStronglyMeasurable.maximalFunction h𝓑
  simp only [ENNReal.coe_one, one_mul, eLpNorm_exponent_top]
  exact essSup_le_of_ae_le _ (Eventually.of_forall fun x ↦ MB_le_eLpNormEssSup)

/- The proof is roughly between (9.0.12)-(9.0.22). -/
protected theorem HasWeakType.MB_one [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    HasWeakType (MB (E := E) μ 𝓑 c r) 1 1 μ μ (A ^ 2) := by
  intro f _
  use AEStronglyMeasurable.maximalFunction h𝓑
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖ₑ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, wnorm', toReal_one, inv_one, ENNReal.rpow_one, reduceIte,
    ENNReal.coe_pow, eLpNorm, one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self,
    iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hBₗ : (Bₗ t).Countable := h𝓑.mono (fun i hi ↦ mem_of_mem_inter_left hi)
  refine le_trans ?_ (hBₗ.measure_biUnion_le_lintegral (c := c) (r := r) (l := t)
    (u := fun x ↦ ‖f x‖ₑ) (R := R) ?_ ?_)
  · refine mul_left_mono <| μ.mono (fun x hx ↦ mem_iUnion₂.mpr ?_)
    -- We need a ball in `Bₗ t` containing `x`. Since `MB μ 𝓑 c r f x` is large, such a ball exists
    simp only [mem_setOf_eq] at hx
    -- replace hx := lt_of_lt_of_le hx coe_toNNReal_le_self
    simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one] at hx
    obtain ⟨i, ht⟩ := lt_iSup_iff.mp hx
    replace hx : x ∈ ball (c i) (r i) :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    refine ⟨i, ?_, hx⟩
    -- It remains only to confirm that the chosen ball is actually in `Bₗ t`
    simp only [ge_iff_le, mem_setOf_eq, Bₗ]
    have hi : i ∈ 𝓑 :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    exact ⟨hi, mul_le_of_le_div <| le_of_lt (by simpa [setLaverage_eq, hi, hx] using ht)⟩
  · exact fun i hi ↦ hR i (mem_of_mem_inter_left hi)
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

include A in
theorem MB_ae_ne_top [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R)
    {u : X → E} (hu : MemLp u 1 μ) : ∀ᵐ x : X ∂μ, MB μ 𝓑 c r u x ≠ ∞ := by
  simpa only [enorm_eq_self] using HasWeakType.MB_one h𝓑 hR |>.memWℒp hu coe_lt_top |>.ae_ne_top

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
  · intro f c hf; rw [NNReal.smul_def]; exact hf.const_smul _
  · intro f c hf; rw [NNReal.smul_def]; exact hf.const_smul _
  · intro i _
    refine AESublinearOn.const (T μ c r i) P (fun hf hg ↦ T.add_le i (hP hf))
      (fun f d hf ↦ T.smul i) |>.indicator _

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
irreducible_def CMB (A p : ℝ≥0) : ℝ≥0 := C_realInterpolation ⊤ 1 ⊤ 1 p 1 (A ^ 2) 1 p⁻¹

/-- Special case of equation (2.0.44). The proof is given between (9.0.12) and (9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
lemma hasStrongType_MB [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    (h𝓑 : 𝓑.Countable) {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) {p : ℝ≥0} (hp : 1 < p) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) p p μ μ (CMB A p) := by
  rw [← hasStrongType_toReal_iff sorry /- cleanup after RealInterpolation works for ENorm. -/]
  have h2p : 0 < p := by positivity
  rw [CMB]
  apply exists_hasStrongType_real_interpolation
    (T := fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) (p := p) (q := p) (A := 1)
    ⟨ENNReal.zero_lt_top, le_rfl⟩
    ⟨zero_lt_one, le_rfl⟩ (by norm_num) zero_lt_one (by simp [inv_lt_one_iff₀, hp, h2p] : p⁻¹ ∈ _)
    zero_lt_one (pow_pos (A_pos μ) 2)
    (by simp [ENNReal.coe_inv h2p.ne']) (by simp [ENNReal.coe_inv h2p.ne'])
    (fun f _ ↦ AEStronglyMeasurable.maximalFunction_toReal h𝓑)
    _ (HasStrongType.MB_top h𝓑 |>.toReal.hasWeakType le_top)
    (HasWeakType.MB_one h𝓑 hR).toReal
  exact ((AESublinearOn.maximalFunction h𝓑 hR).toReal <| MB_ae_ne_top' h𝓑 hR).1

lemma hasStrongType_MB_finite [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    (h𝓑 : 𝓑.Finite) {p : ℝ≥0} (hp : 1 < p) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x) p p μ μ (CMB A p) :=
  hasStrongType_MB h𝓑.countable (Finite.exists_image_le h𝓑 _).choose_spec hp

/-- The constant factor in the statement that `M_{𝓑, p}` has strong type. -/
irreducible_def C2_0_6 (A p₁ p₂ : ℝ≥0) : ℝ≥0 := CMB A (p₂ / p₁) ^ (p₁⁻¹ : ℝ)

/-- Equation (2.0.44). The proof is given between (9.0.34) and (9.0.36). -/
theorem hasStrongType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Countable) {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x)
      p₂ p₂ μ μ (C2_0_6 A p₁ p₂) := by
  rw [← hasStrongType_toReal_iff sorry /- cleanup (task 117) -/]
  intro v mlpv
  dsimp only
  constructor; · exact AEStronglyMeasurable.maximalFunction_toReal h𝓑
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
      convert (hasStrongType_MB h𝓑 hR (μ := μ) _ |>.toReal (fun x ↦ ‖v x‖ ^ (p₁ : ℝ)) _).2
      · exact (ENNReal.coe_div p₁n).symm
      · rwa [lt_div_iff₀, one_mul]; exact cp₁p
      · rw [ENNReal.coe_div p₁n]; exact MemLp.norm_rpow_div mlpv p₁
    _ ≤ _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), eLpNorm_norm_rpow _ cp₁p,
        ENNReal.ofReal_coe_nnreal, ENNReal.div_mul_cancel (by positivity) (by simp),
        ENNReal.rpow_rpow_inv (by positivity), ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
        C2_0_6]

/-- `hasStrongType_maximalFunction` minus the assumption `hR`.
A proof for basically this result is given in Chapter 9, everything following after equation
(9.0.36). -/
theorem hasStrongType_maximalFunction_todo
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Countable) (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x)
      p₂ p₂ μ μ (C2_0_6 A p₁ p₂) := fun v mlpv ↦ by
  sorry

/-- Use `lowerSemicontinuous_iff_isOpen_preimage` and `continuous_average_ball` -/
lemma lowerSemiContinuous_MB (hf : LocallyIntegrable f μ) :
    LowerSemicontinuous (MB μ 𝓑 c r f) := by
  sorry

/-- `hasStrongType_maximalFunction` minus the assumption `hR`, but where `p₁ = p₂` is possible and
we only conclude a weak-type estimate.
The proof of this should be basically the same as that of `hasStrongType_maximalFunction` +
`hasStrongType_maximalFunction_todo`, but starting with `HasWeakType.MB_one` instead of
`hasStrongType_MB`. (For `p₂ > p₁` you can also derive this from
`hasStrongType_maximalFunction_todo`) -/
theorem hasWeakType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (h𝓑 : 𝓑.Countable) (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) :
    HasWeakType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x)
      p₂ p₂ μ μ (A ^ 2) := fun v mlpv ↦ by
  sorry

section GMF

variable [ProperSpace X]

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6.
`p` is `1` in the blueprint, and `globalMaximalFunction μ p u = (M (u ^ p)) ^ p⁻¹ ` -/
@[nolint unusedArguments]
def globalMaximalFunction [μ.IsDoubling A] (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  A ^ 2 * maximalFunction μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
    (·.1) (fun x ↦ 2 ^ (x.2)) p u x

-- prove only if needed. Use `MB_le_eLpNormEssSup`
-- theorem globalMaximalFunction_lt_top {p : ℝ≥0} (hp₁ : 1 ≤ p)
--     {u : X → E} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u)) {x : X} :
--     globalMaximalFunction μ p u x < ∞ := by
--   sorry

protected theorem MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    [BorelSpace X] {p : ℝ} {u : X → E} : AEStronglyMeasurable (globalMaximalFunction μ p u) μ :=
  AEStronglyMeasurable.maximalFunction countable_globalMaximalFunction
    |>.aemeasurable.const_mul _ |>.aestronglyMeasurable

/-- Equation (2.0.45).-/
theorem laverage_le_globalMaximalFunction [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {u : X → E} {z x : X} {r : ℝ} (h : dist x z < r) :
    ⨍⁻ y, ‖u y‖ₑ ∂μ.restrict (ball z r) ≤ globalMaximalFunction μ 1 u x := by
  rw [globalMaximalFunction, maximalFunction]
  simp only [gt_iff_lt, mem_prod, mem_univ, and_true, ENNReal.rpow_one, inv_one]
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h
  obtain ⟨c, hc, m, h_subset, _, h_subset'⟩ := exists_ball_subset_ball_two z hr
  calc
    _ ≤ (μ (ball z r))⁻¹ * ∫⁻ y in ball c (2 ^ m), ‖u y‖ₑ ∂μ := by
      simp only [laverage, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
        lintegral_smul_measure, smul_eq_mul]
      gcongr
      exact lintegral_mono_set h_subset
    _ ≤ A ^ 2 * (μ (ball c (2 ^ m)))⁻¹ * ∫⁻ y in ball c (2 ^ m), ‖u y‖ₑ ∂μ := by
      gcongr
      rw [mul_comm, ← ENNReal.mul_le_iff_le_inv
        ((measure_ball_pos _ (zpow_pos zero_lt_two _) (μ := μ)).ne')
          (measure_ball_ne_top c _), ENNReal.mul_inv_le_iff
            ((measure_ball_pos _ hr (μ := μ)).ne') (measure_ball_ne_top z r)]
      exact (μ.mono h_subset').trans <| measure_ball_four_le_same' z r
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
      refine (le_iSup₂ (c, m) hc).trans_eq' ?_
      simp [laverage, indicator_of_mem (h_subset h)]

/-- The constant factor in the statement that `M` has strong type. -/
def C2_0_6' (A p₁ p₂ : ℝ≥0) : ℝ≥0 := A ^ 2 * C2_0_6 A p₁ p₂

/-- Equation (2.0.46). Easy from `hasStrongType_maximalFunction` -/
theorem hasStrongType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [Nonempty X] [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (fun (u : X → E) (x : X) ↦ globalMaximalFunction μ p₁ u x)
      p₂ p₂ μ μ (C2_0_6' A p₁ p₂) := by
  convert HasStrongType.const_mul (c := C2_0_6 A p₁ p₂) _ _
  · sorry -- how to prevent this diamond?
  · sorry -- missing instance, right?
  convert hasStrongType_maximalFunction_todo countable_globalMaximalFunction hp₁ hp₁₂
  -- TODO: all these goals are "obvious", there is always a matching instance in context
  -- figure out what's going wrong here!
  all_goals sorry

theorem hasWeakType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [Nonempty X] [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 1 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) :
    HasWeakType (fun (u : X → E) (x : X) ↦ globalMaximalFunction μ p₁ u x)
      p₂ p₂ μ μ (A ^ 4) := by
  -- rw [← hasWeakType_toReal_iff sorry /- todo: cleanup (task 117). -/]
  -- unfold globalMaximalFunction
  -- simp_rw [ENNReal.toReal_mul]
  have : ofNNReal p₂ ≠ 0 := by -- surely, there is a simpler proof
    refine coe_ne_zero.mpr ?_
    have : 1 ≤ p₂ := by
      trans p₁
      exacts [hp₁, hp₁₂]
    positivity
  sorry
  /- TODO: fix this proof (currently times out), was:
  apply HasWeakType.const_mul (c := A ^ 2) (e := A ^ 2) (p' := p₂) (μ := μ) (ν := μ) (p := p₂) this _
  -- perhaps specify (ε := E) also
  · simp; ring
  exact hasWeakType_maximalFunction countable_globalMaximalFunction hp₁ hp₁₂ -/

/-- Use `lowerSemiContinuous_MB` -/
lemma lowerSemiContinuous_globalMaximalFunction (hf : LocallyIntegrable f μ) :
    LowerSemicontinuous (globalMaximalFunction μ 1 f) := by
  sorry


end GMF
