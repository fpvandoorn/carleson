module

public import Carleson.Defs
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Indexed
public import Carleson.ToMathlib.RealInterpolation.Main
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Average
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.Field
import Carleson.ToMathlib.MeasureTheory.Covering.Vitali

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

variable {X E : Type*} {A : ℝ≥0} [PseudoMetricSpace X] [MeasurableSpace X]
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

theorem measure_biUnion_le_lintegral_aux [OpensMeasurableSpace X] [SeparableSpace X]
    (𝓑 : Set ι) (l : ℝ≥0∞) (u : X → ℝ≥0∞) (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  let 𝓑' := { a ∈ 𝓑 | 0 < r a }
  obtain ⟨B, hB𝓑, hB, h2B⟩ := exists_disjoint_subfamily_covering_enlargement_ball
    𝓑' c r R (fun a ha => hR a ha.1) (2 ^ 2) (by norm_num)
  have : Countable B := hB.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a ha => nonempty_ball.mpr (hB𝓑 ha).right)
  have disj := fun i j hij ↦
    hB (Subtype.coe_prop i) (Subtype.coe_prop j) (Subtype.coe_ne_coe.mpr hij)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
          refine mul_right_mono (μ.mono fun x hx ↦ ?_)
          push _ ∈ _ at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          have i𝓑' : i ∈ 𝓑' := .intro i𝓑 (nonempty_ball.mp (nonempty_of_mem hi))
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑'
          exact mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) :=
          mul_right_mono <| measure_biUnion_le μ this fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
          refine mul_right_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
          rw [sq, sq, mul_assoc, mul_assoc]
          apply (measure_ball_two_le_same (c i) (2 * r i)).trans
          gcongr; exact measure_ball_two_le_same (c i) (r i)
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc, mul_comm l]
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := by
          gcongr; exact h2u _ (hB𝓑 (Subtype.coe_prop _)).left
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := by
          congr; simpa using (lintegral_iUnion (fun i ↦ measurableSet_ball) disj u).symm
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := by
          gcongr; exact Measure.restrict_le_self

variable (𝓑 r) in
def tr (k : ℕ) : Set ι := {i | i ∈ 𝓑 ∧ r i ≤ k}

lemma tr_subset (k : ℕ) : tr 𝓑 r k ⊆ 𝓑 :=
  fun _ hi => hi.left

lemma tr_radius_le (k : ℕ) : ∀ i ∈ tr 𝓑 r k, r i ≤ k :=
  fun _ hi => hi.right

lemma tr_mono : Monotone (tr 𝓑 r) := by
  intro i j hij
  rintro k ⟨hi₁, hi₂⟩
  exact ⟨hi₁, hi₂.trans (Nat.cast_le.mpr hij)⟩

lemma tr_union (𝓑) (r : ι → ℝ) : 𝓑 = ⋃ k, tr 𝓑 r k := by
  apply eq_of_subset_of_subset
  · intro i hi
    rcases exists_nat_ge (r i) with ⟨k, hk⟩
    exact mem_iUnion.mpr ⟨k, hi, hk⟩
  · intro i hi
    exact (mem_iUnion.mp hi).elim (fun _ p => p.left)

theorem measure_biUnion_le_lintegral [OpensMeasurableSpace X] [SeparableSpace X]
    (𝓑 : Set ι) (l : ℝ≥0∞) (u : X → ℝ≥0∞)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  have : μ (⋃ i ∈ 𝓑, ball (c i) (r i)) = ⨆ k, μ (⋃ i ∈ tr 𝓑 r k, ball (c i) (r i)) := by
    conv_lhs => rw [tr_union 𝓑 r, biUnion_iUnion]
    have : Monotone (⋃ x ∈ tr 𝓑 r ·, ball (c x) (r x)) :=
      fun i j hij ↦ biUnion_mono (tr_mono hij) (fun _ _ ↦ by rfl)
    rw [this.measure_iUnion]
  rw [this, mul_iSup]
  exact iSup_le fun R ↦
    measure_biUnion_le_lintegral_aux (tr 𝓑 r R) l u R (fun i hi ↦ hi.2) (fun i hi ↦ h2u i hi.1)

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
protected theorem HasWeakType.MB_one [BorelSpace X] [SeparableSpace X] :
    HasWeakType (MB (E := E) μ 𝓑 c r) 1 1 μ μ (A ^ 2) := by
  intro f _
  use Measurable.maximalFunction.aestronglyMeasurable
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖ₑ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, wnorm', toReal_one, inv_one, ENNReal.rpow_one, reduceIte, eLpNorm,
    one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self, iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  refine le_trans ?_ (measure_biUnion_le_lintegral (𝓑 := Bₗ t) (c := c) (r := r) (l := t)
    (u := fun x ↦ ‖f x‖ₑ) ?_)
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
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

include A in
theorem MB_ae_ne_top [BorelSpace X] [SeparableSpace X]
    {u : X → E} (hu : MemLp u 1 μ) : ∀ᵐ x : X ∂μ, MB μ 𝓑 c r u x ≠ ∞ := by
  simpa only [enorm_eq_self] using HasWeakType.MB_one |>.memWLp hu coe_lt_top |>.ae_ne_top

-- move
lemma MeasureTheory.MemLp.eLpNormEssSup_lt_top {α} [MeasurableSpace α] {μ : Measure α}
    {u : α → E} (hu : MemLp u ⊤ μ) : eLpNormEssSup u μ < ⊤ := by
  simp_rw [MemLp, eLpNorm_exponent_top] at hu
  exact hu.2

include A in
theorem MB_ae_ne_top' [BorelSpace X] [SeparableSpace X]
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
  · exact MB_ae_ne_top hu

protected theorem MeasureTheory.SublinearOn.maximalFunction
    [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] :
    SublinearOn (MB (E := E) μ 𝓑 c r) (fun f ↦ MemLp f ∞ μ ∨ MemLp f 1 μ) 1 := by
  let P := fun (f : X → E) ↦ MemLp f ∞ μ ∨ MemLp f 1 μ
  have hP {g} : P g → LocallyIntegrable g μ
    | .inl hl => hl.locallyIntegrable le_top
    | .inr hr => hr.locallyIntegrable le_rfl
  refine .biSup fun i hi => .indicator _ ?_
  simp_rw [inv_one, ENNReal.rpow_one]
  exact SublinearOn.const (T μ c r i) P (fun hf hg ↦ by exact T.add_le i (hP hf))
    (fun f d hf ↦ T.smul i)

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
    {p : ℝ≥0} (hp : 1 < p) :
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
    HasWeakType.MB_one
  · exact ⟨ENNReal.inv_pos.mpr coe_ne_top, ENNReal.inv_lt_one.mpr <| one_lt_coe_iff.mpr hp⟩
  exact SublinearOn.maximalFunction.aeSublinearOn.1

/-- The constant factor in the statement that `M_{𝓑, p}` has strong type. -/
irreducible_def C2_0_6 (A p₁ p₂ : ℝ≥0) : ℝ≥0 := CMB A (p₂ / p₁) ^ (p₁⁻¹ : ℝ)

/-- The `maximalFunction` has strong type when `p₁ < p₂`. -/
theorem hasStrongType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
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
      convert (hasStrongType_MB (μ := μ) _ (fun x ↦ ‖v x‖ ^ (p₁ : ℝ)) _).2
      · rw [ENNReal.coe_div p₁n]
      · rwa [lt_div_iff₀, one_mul]; exact cp₁p
      · rw [ENNReal.coe_div p₁n]; exact mlpv.norm_rpow_div p₁
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), eLpNorm_norm_rpow _ cp₁p,
        ENNReal.ofReal_coe_nnreal, ENNReal.div_mul_cancel (by positivity) (by simp),
        ENNReal.rpow_rpow_inv (by positivity), ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
        C2_0_6]

/-- Version of `hasWeakType_maximalFunction_equal_exponents` with the additional assumption `hR`.
-/
theorem hasWeakType_maximalFunction_equal_exponents [BorelSpace X] [SeparableSpace X]
    {p : ℝ≥0} (hp : 0 < p) :
    HasWeakType (maximalFunction (E := E) μ 𝓑 c r p) p p μ μ (A ^ ((2 / p : ℝ))) := by
  intro v mlpv
  constructor; · exact Measurable.maximalFunction.aestronglyMeasurable
  have cp : 0 < (p : ℝ) := by positivity
  have p₁n : p ≠ 0 := by exact_mod_cast cp.ne'
  conv_lhs =>
    enter [1, x]
    rw [maximalFunction_eq_MB cp]
  have hmb_one : wnorm (MB μ 𝓑 c r fun x ↦ ‖v x‖ ^ (p : ℝ)) 1 μ ≤ ↑A ^ 2 * eLpNorm (fun x ↦ ‖v x‖ ^ (p : ℝ)) 1 μ := by
    apply (HasWeakType.MB_one (fun x : X ↦ ‖v x‖ ^ (p : ℝ)) _).2
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
    {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂) :
    HasWeakType (fun (u : X → E) (x : X) ↦ maximalFunction μ 𝓑 c r p₁ u x)
      p₂ p₂ μ μ (C_weakType_maximalFunction A p₁ p₂) := by
  unfold C_weakType_maximalFunction
  split_ifs with hps
  · rw [← hps]
    exact hasWeakType_maximalFunction_equal_exponents (A := A) hp₁
  · apply HasStrongType.hasWeakType (coe_lt_coe_of_lt (hp₁.trans_le hp₁₂))
    exact hasStrongType_maximalFunction hp₁ (lt_of_le_of_ne hp₁₂ hps)

section GMF

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6.
`p` is `1` in the blueprint, and `globalMaximalFunction μ p u = (M (u ^ p)) ^ p⁻¹ ` -/
def globalMaximalFunction (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ (univ : Set (X × ℝ)) (·.1) (·.2) p u x

protected theorem MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    [BorelSpace X] {p : ℝ} {u : X → E} : AEStronglyMeasurable (globalMaximalFunction μ p u) μ :=
  Measurable.maximalFunction.aestronglyMeasurable

/-- Equation (2.0.45) -/
theorem laverage_le_globalMaximalFunction [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {u : X → E} {z x : X} {r : ℝ} (h : dist x z < r) :
    ⨍⁻ y in ball z r, ‖u y‖ₑ ∂μ ≤ globalMaximalFunction μ 1 u x := by
  rw [globalMaximalFunction, maximalFunction]
  simp only [mem_univ, ENNReal.rpow_one, inv_one]
  apply le_iSup₂_of_le (z, r) trivial
  rw [indicator_of_mem (mem_ball.mpr h)]

lemma lowerSemiContinuous_globalMaximalFunction :
    LowerSemicontinuous (globalMaximalFunction μ 1 f) :=
  lowerSemiContinuous_maximalFunction

theorem globalMaximalFunction_lt_top {p : ℝ≥0} (hp₁ : 0 < p)
    {u : X → E} (hu : MemLp u ⊤ μ) {x : X} :
    globalMaximalFunction μ p u x < ∞ := by
  unfold globalMaximalFunction
  rw [maximalFunction_eq_MB (by positivity)]
  apply rpow_lt_top_of_nonneg (by simp) (lt_top_iff_ne_top.mp _)
  have : MemLp (fun x ↦ ‖u x‖ ^ p.toReal) ⊤ μ := by
    have rw1 : p.toReal = (p : ℝ≥0∞).toReal := by simp
    have rw2 : (⊤ : ℝ≥0∞) = ⊤ / p := by simp
    rw [rw1, rw2, memLp_norm_rpow_iff hu.aestronglyMeasurable (by positivity) (by simp)]
    exact hu
  refine lt_of_le_of_lt MB_le_eLpNormEssSup this.eLpNormEssSup_lt_top

variable [ProperSpace X]

theorem lintegral_ball_le_volume_globalMaximalFunction [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {u : X → E} {z x : X} {r : ℝ} (h : dist x z < r) :
    ∫⁻ y in (ball z r), ‖u y‖ₑ ∂μ  ≤ μ (ball z r) * globalMaximalFunction μ 1 u x := by
  have : IsFiniteMeasure (μ.restrict (ball z r)) := isFiniteMeasure_restrict.mpr (by finiteness)
  rw [← measure_mul_laverage]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  gcongr
  exact laverage_le_globalMaximalFunction h

/-- The constant factor in the statement that `M` has strong type. -/
def C2_0_6' (A p₁ p₂ : ℝ≥0) : ℝ≥0 := C2_0_6 A p₁ p₂

lemma C2_0_6'_defaultA_one_two_eq {a : ℕ} : C2_0_6' (defaultA a) 1 2 = 2 ^ (a + 3 / (2 : ℝ)) := by
  simp_rw [C2_0_6', C2_0_6, div_one, CMB_defaultA_two_eq,
    NNReal.coe_one, inv_one, NNReal.rpow_one]

lemma C2_0_6'_defaultA_one_le {a : ℕ} {q : ℝ≥0} (hq : 1 < q) :
    C2_0_6' (defaultA a) 1 q ≤ 2 ^ (2 * a + 1) * (q / (q - 1)) := by
  rw [C2_0_6', C2_0_6, div_one, defaultA, Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_one,
    inv_one, NNReal.rpow_one, CMB_eq_of_one_lt_q hq]
  ring_nf
  gcongr
  apply Real.rpow_le_self_of_one_le _ (inv_le_one_of_one_le₀ hq.le)
  norm_cast
  apply one_le_mul
  · field_simp
    apply one_le_div _ |>.mpr <;> simp [hq]
  · norm_cast
    grind

/-- Equation (2.0.46). Easy from `hasStrongType_maximalFunction` -/
theorem hasStrongType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (globalMaximalFunction μ p₁ (E := E))
      p₂ p₂ μ μ (C2_0_6 A p₁ p₂) :=
  hasStrongType_maximalFunction hp₁ hp₁₂

def C_weakType_globalMaximalFunction (A p₁ p₂ : ℝ≥0) :=
  A ^ 2 * C_weakType_maximalFunction A p₁ p₂

lemma C_weakType_globalMaximalFunction_lt_top {A p₁ p₂ : ℝ≥0} :
    C_weakType_globalMaximalFunction A p₁ p₂ < ∞ :=
  mul_lt_top (by simp) (by finiteness)

-- the constant here `A ^ 4` can be improved
theorem hasWeakType_globalMaximalFunction [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂) :
    HasWeakType (globalMaximalFunction μ p₁ (E := E))
      p₂ p₂ μ μ (C_weakType_maximalFunction A p₁ p₂) :=
  hasWeakType_maximalFunction hp₁ hp₁₂

include A in
theorem globalMaximalFunction_ae_lt_top [BorelSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂)
    {u : X → E} (hu : MemLp u p₂ μ) :
    ∀ᵐ x ∂μ, globalMaximalFunction μ p₁ u x < ∞ := by
  simp_rw [lt_top_iff_ne_top]
  conv =>
    enter [1, x, 1]
    rw [← enorm_eq_self (x := globalMaximalFunction μ p₁ u x)]
  exact (hasWeakType_globalMaximalFunction hp₁ hp₁₂.le).memWLp hu |>.ae_ne_top

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
