module

public import Carleson.ToMathlib.MeasureTheory.Measure.IsDoubling
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Indexed
public import Carleson.ToMathlib.RealInterpolation.Main
public import Mathlib.MeasureTheory.Covering.Vitali

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

variable {X E : Type*} {A : ℝ≥0} [PseudoMetricSpace X] [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} [μ.IsDoubling A]
  {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ} {p : ℝ} {u : X → E} {x : X}

/-- The uncentered Hardy-Littlewood maximal function, for a family of balls. -/
@[expose] public def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (p : ℝ)
    (u : X → E) (x : X) : ℝ≥0∞ :=
  ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ (⨍⁻ y in ball (c i) (r i), ‖u y‖ₑ ^ p ∂μ) ^ p⁻¹

/-- The uncentered Hardy-Littlewood maximal function. -/
@[expose] public def globalMaximalFunction (μ : Measure X) (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ (univ (α := X × ℝ)) (·.fst) (·.snd) p u x

/-- The average of the norm of a function over a particular ball is smaller than the value of the
`globalMaximalFuntion` at a point inside that ball. -/
public theorem laverage_le_globalMaximalFunction {z : X} {r : ℝ} (h : dist x z < r) :
    ⨍⁻ y in ball z r, ‖u y‖ₑ ∂μ ≤ globalMaximalFunction μ 1 u x := by
  apply le_iSup₂_of_le (z, r) trivial
  simp only [ENNReal.rpow_one, inv_one, indicator_of_mem (mem_ball.mpr h)]
  rfl

/-- The integral of the norm of a function over a particular ball is smaller than the volume of the
ball times the value of the `globalMaximalFuntion` at a point inside that ball. -/
public theorem lintegral_ball_le_volume_mul_globalMaximalFunction
    [ProperSpace X] [IsFiniteMeasureOnCompacts μ] {z : X} {r : ℝ}
    (h : dist x z < r) :
    ∫⁻ y in ball z r, ‖u y‖ₑ ∂μ ≤ μ (ball z r) * globalMaximalFunction μ 1 u x := by
  have : IsFiniteMeasure (μ.restrict (ball z r)) := isFiniteMeasure_restrict.mpr (by finiteness)
  rw [← measure_mul_laverage]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  gcongr
  exact laverage_le_globalMaximalFunction h

lemma indicator_rpow {α : Type*} {p : ℝ} (hp : 0 < p) {s : Set α} {f : α → ℝ≥0∞} :
    s.indicator (fun y ↦ f y ^ p) = (s.indicator f) ^ p :=
  indicator_comp_of_zero (g := fun a => a ^ p) (ENNReal.zero_rpow_of_pos hp)

lemma maximalFunction_eq_maximalFunction_one_rpow (hp : 0 < p) :
    maximalFunction μ 𝓑 c r p u x = (maximalFunction μ 𝓑 c r 1 (‖u ·‖ ^ p) x) ^ p⁻¹ := by
  simp only [maximalFunction, indicator_rpow (inv_pos_of_pos hp),
    Pi.pow_apply, rpow_one, inv_one, iSup_rpow (inv_pos_of_pos hp)]
  congr! 8
  rw [Real.enorm_rpow_of_nonneg (by positivity) hp.le, enorm_norm]

-- The average that appears in the definition of `MB`
variable (μ c r) in
private def T (i : ι) (u : X → E) := ⨍⁻ (y : X) in ball (c i) (r i), ‖u y‖ₑ ∂μ

-- We replace the criterion `P` used in `MeasureTheory.AESublinearOn.maximalFunction` with the
-- weaker criterion `AEMeasurable` that is closed under addition and scalar multiplication.

private lemma T.add_le [MeasurableSpace E] [BorelSpace E]
    {i} {f g : X → E} (hf : AEMeasurable f μ) :
    ‖T μ c r i (f + g)‖ₑ ≤ ‖T μ c r i f‖ₑ + ‖T μ c r i g‖ₑ := by
  simp only [T, Pi.add_apply, enorm_eq_self]
  rw [← laverage_add_left hf.restrict.enorm]
  exact laverage_mono (fun x ↦ enorm_add_le (f x) (g x))

-- move to `ENNReal.Basic` or similar
lemma NNReal.smul_ennreal_eq_mul (x : ℝ≥0) (y : ℝ≥0∞) : x • y = x * y := rfl

private lemma T.smul [NormedSpace ℝ E] {c r} {i : ι} {d : ℝ≥0} :
    T μ c r i (d • u) = d • T μ c r i u := by
  simp [T, NNReal.smul_def, NNReal.smul_ennreal_eq_mul,
    laverage_const_mul (by finiteness), enorm_smul]

section MeasureBiUnionBall

variable {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ}

theorem measure_biUnion_le_lintegral_aux [OpensMeasurableSpace X] [SeparableSpace X]
    (l : ℝ≥0∞) (u : X → ℝ≥0∞) (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
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

public theorem measure_biUnion_le_lintegral [OpensMeasurableSpace X] [SeparableSpace X]
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
    measure_biUnion_le_lintegral_aux l u R (fun i hi ↦ hi.2) (fun i hi ↦ h2u i hi.1)

end MeasureBiUnionBall

public lemma lowerSemiContinuous_maximalFunction :
    LowerSemicontinuous (maximalFunction μ 𝓑 c r p u) := by
  intro x s hxr
  have ⟨i, hi, h⟩ := exists_lt_of_lt_ciSup₂' hxr
  have hx : x ∈ ball (c i) (r i) :=
    mem_of_indicator_ne_zero (h.trans_le' bot_le |>.ne.symm)
  rw [indicator_of_mem hx] at h
  apply eventually_of_mem
  · exact isOpen_ball.mem_nhds hx
  · intro y hy
    apply LT.lt.trans_le _ (le_iSup₂ i hi)
    rwa [indicator_of_mem hy]

public theorem measurable_maximalFunction [BorelSpace X] :
    Measurable (maximalFunction μ 𝓑 c r p u) :=
  lowerSemiContinuous_maximalFunction.measurable

public theorem maximalFunction_one_le_eLpNormEssSup :
    maximalFunction μ 𝓑 c r 1 u x ≤ eLpNormEssSup u μ :=
  calc
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
      fun _x ↦ ⨍⁻ _ in ball (c i) (r i), eLpNormEssSup u μ ∂μ := by
      simp_rw [maximalFunction, inv_one, ENNReal.rpow_one]
      gcongr
      exact MeasureTheory.enorm_ae_le_eLpNormEssSup u μ
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x) fun _ ↦ eLpNormEssSup u μ := by
      gcongr; apply setLaverage_const_le
    _ ≤ ⨆ i ∈ 𝓑, eLpNormEssSup u μ := by gcongr; apply indicator_le_self
    _ ≤ eLpNormEssSup u μ := by
      simp_rw [iSup_le_iff, le_refl, implies_true]

theorem MeasureTheory.MemLp.maximalFunction_lt_top (hp₁ : 0 < p) (hu : MemLp u ⊤ μ) :
    maximalFunction μ 𝓑 c r p u x < ∞ := by
  rw [maximalFunction_eq_maximalFunction_one_rpow (by positivity)]
  apply rpow_lt_top_of_nonneg (by positivity) (lt_top_iff_ne_top.mp _)
  have : MemLp (fun x ↦ ‖u x‖ ^ p) ⊤ μ := by
    rw [← toReal_ofReal hp₁.le,
      show ∞ = ∞ / (ENNReal.ofReal p) from ENNReal.top_div_of_ne_top (by finiteness) |>.symm]
    exact hu.norm_rpow_div _
  refine lt_of_le_of_lt maximalFunction_one_le_eLpNormEssSup this.eLpNormEssSup_lt_top

theorem hasStrongType_maximalFunction_top [BorelSpace X] :
    HasStrongType (maximalFunction (E := E) μ 𝓑 c r 1) ⊤ ⊤ μ μ 1 := by
  intro f _
  use measurable_maximalFunction.aestronglyMeasurable
  simp only [one_mul, eLpNorm_exponent_top]
  exact essSup_le_of_ae_le _ (Eventually.of_forall fun x ↦ maximalFunction_one_le_eLpNormEssSup)

/- The proof is roughly between (9.0.12)-(9.0.22). -/
theorem hasWeakType_maximalFunction_one [BorelSpace X] [SeparableSpace X] :
    HasWeakType (maximalFunction (E := E) μ 𝓑 c r 1) 1 1 μ μ (A ^ 2) := by
  intro f _
  use measurable_maximalFunction.aestronglyMeasurable
  let Bₗ (ℓ : ℝ≥0∞) := { (c, r) | ∫⁻ y in (ball c r), ‖f y‖ₑ ∂μ ≥ ℓ * μ (ball c r) }
  simp only [wnorm, one_ne_top, wnorm', toReal_one, inv_one, ENNReal.rpow_one, reduceIte, eLpNorm,
    one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self, iSup_le_iff]
  intro t
  refine le_trans ?_ (measure_biUnion_le_lintegral (𝓑 := Bₗ t) (c := (·.1)) (r := (·.2)) (l := t)
    (u := fun x ↦ ‖f x‖ₑ) ?_)
  · refine mul_right_mono <| μ.mono (fun x hx ↦ mem_iUnion₂.mpr ?_)
    -- We need a ball in `Bₗ t` containing `x`. Since `MB μ 𝓑 c r f x` is large, such a ball exists
    simp only [mem_setOf_eq, maximalFunction, ENNReal.rpow_one, inv_one] at hx
    obtain ⟨i, ht⟩ := lt_iSup_iff.mp hx
    obtain ⟨hi, ht⟩ := lt_iSup_iff.mp ht
    replace hx : x ∈ ball (c i) (r i) := by
      by_contra h
      exact not_lt_of_ge (zero_le (a := t)) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    refine ⟨(c i, r i), ?_, hx⟩
    simp only [ge_iff_le, mem_setOf_eq, Bₗ]
    exact mul_le_of_le_div <| le_of_lt (by simpa [setLAverage_eq, hx] using ht)
  · exact fun (c, r) h ↦ h.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

theorem sublinearOn_maximalFunction_one
    [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] :
    SublinearOn (maximalFunction (E := E) μ 𝓑 c r 1) (fun f ↦ AEMeasurable f μ) 1 := by
  refine .iSup₂ fun i hi => .indicator _ ?_
  simp_rw [inv_one, ENNReal.rpow_one]
  exact SublinearOn.const (T μ c r i) _ (fun hf hg ↦ by exact T.add_le hf) (fun f d hf ↦ T.smul)

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
public def CMB (A p : ℝ≥0) : ℝ≥0 := C_realInterpolation ⊤ 1 ⊤ 1 p 1 (A ^ 2) 1 p⁻¹

public lemma CMB_def {A p : ℝ≥0} : CMB A p = C_realInterpolation ⊤ 1 ⊤ 1 p 1 (A ^ 2) 1 p⁻¹ := (rfl)

public lemma CMB_eq_of_one_lt_q {b q : ℝ≥0} (hq : 1 < q) :
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

public lemma CMB_defaultA_two_eq {a : ℕ} : CMB (defaultA a) 2 = 2 ^ (a + (3 / 2 : ℝ)) := by
  suffices (2 : ℝ≥0) * 2 ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal |2 - 1|⁻¹).toNNReal ^ (2 : ℝ)⁻¹ *
      ((2 ^ a) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ = 2 ^ (a + 3 / (2 : ℝ)) by
    simpa [CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  rw [← NNReal.rpow_mul, show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
  repeat rw [NNReal.rpow_add two_ne_zero]
  norm_num
  ring

/-- Special case of equation (2.0.44). The proof is given between (9.0.12) and (9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
public lemma hasStrongType_maximalFunction_one [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [μ.IsOpenPosMeasure]
    {p : ℝ≥0} (hp : 1 < p) :
    HasStrongType (maximalFunction (E := E) μ 𝓑 c r 1) p p μ μ (CMB A p) := by
  by_cases h : Nonempty X; swap
  · have := not_nonempty_iff.mp h; intro _ _; simp
  rw [CMB]
  refine exists_hasStrongType_real_interpolation
    (T := maximalFunction (E := E) μ 𝓑 c r 1) (p := p) (q := p) (A := 1) (t := (↑p)⁻¹)
    ⟨ENNReal.zero_lt_top, le_rfl⟩
    ⟨zero_lt_one, le_rfl⟩ (by norm_num) le_rfl ?_
    zero_lt_one (pow_pos (A_pos μ) 2)
    (by simp) (by simp)
    (fun f _ ↦ measurable_maximalFunction.aestronglyMeasurable)
    ?_ (hasStrongType_maximalFunction_top |>.hasWeakType zero_lt_top)
    hasWeakType_maximalFunction_one
  · exact ⟨ENNReal.inv_pos.mpr coe_ne_top, ENNReal.inv_lt_one.mpr <| one_lt_coe_iff.mpr hp⟩
  exact sublinearOn_maximalFunction_one.imp (·.elim (·.aemeasurable) (·.aemeasurable))
    |>.aeSublinearOn.1

/-- The constant factor in the statement that `M_{𝓑, p}` has strong type. -/
@[expose] public def C2_0_6 (A p₁ p₂ : ℝ≥0) : ℝ≥0 := CMB A (p₂ / p₁) ^ (p₁⁻¹ : ℝ)

/-- The `maximalFunction` has strong type when `p₁ < p₂`. -/
public theorem hasStrongType_maximalFunction
    [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (maximalFunction (E := E) μ 𝓑 c r p₁) p₂ p₂ μ μ (C2_0_6 A p₁ p₂) := by
  by_cases h : Nonempty X; swap
  · have := not_nonempty_iff.mp h; intro _ _; simp
  intro v mlpv
  refine ⟨measurable_maximalFunction.aestronglyMeasurable, ?_⟩
  have cp₁p : 0 < (p₁ : ℝ) := by positivity
  have p₁n : p₁ ≠ 0 := by exact_mod_cast cp₁p.ne'
  conv_lhs =>
    enter [1, x]
    rw [maximalFunction_eq_maximalFunction_one_rpow cp₁p, ← enorm_eq_self (maximalFunction ..)]
  rw [eLpNorm_enorm_rpow _ (by positivity), ENNReal.ofReal_inv_of_pos cp₁p,
    ENNReal.ofReal_coe_nnreal, ← div_eq_mul_inv, ← ENNReal.coe_div p₁n]
  calc
    _ ≤ (CMB A (p₂ / p₁) * eLpNorm (fun y ↦ ‖v y‖ ^ (p₁ : ℝ)) (p₂ / p₁) μ) ^ p₁.toReal⁻¹ := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      convert (hasStrongType_maximalFunction_one (μ := μ) _ (fun x ↦ ‖v x‖ ^ (p₁ : ℝ)) _).2
      · rw [ENNReal.coe_div p₁n]
      · rwa [lt_div_iff₀, one_mul]; exact cp₁p
      · rw [ENNReal.coe_div p₁n]; exact mlpv.norm_rpow_div p₁
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), eLpNorm_norm_rpow _ cp₁p,
        ENNReal.ofReal_coe_nnreal, ENNReal.div_mul_cancel (by positivity) (by simp),
        ENNReal.rpow_rpow_inv (by positivity), ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
        C2_0_6]

theorem hasWeakType_maximalFunction_equal_exponents [BorelSpace X] [SeparableSpace X]
    {p : ℝ≥0} (hp : 0 < p) :
    HasWeakType (maximalFunction (E := E) μ 𝓑 c r p) p p μ μ (A ^ ((2 / p : ℝ))) := by
  intro v mlpv
  constructor; · exact measurable_maximalFunction.aestronglyMeasurable
  have cp : 0 < (p : ℝ) := by positivity
  have p₁n : p ≠ 0 := by exact_mod_cast cp.ne'
  conv_lhs =>
    enter [1, x]
    rw [maximalFunction_eq_maximalFunction_one_rpow cp]
  have hmb_one : wnorm (maximalFunction μ 𝓑 c r 1 (‖v ·‖ ^ (p : ℝ))) 1 μ
      ≤ ↑A ^ 2 * eLpNorm (fun x ↦ ‖v x‖ ^ (p : ℝ)) 1 μ := by
    apply (hasWeakType_maximalFunction_one (fun x : X ↦ ‖v x‖ ^ (p : ℝ)) _).2
    convert! MemLp.norm_rpow_div mlpv p
    exact (ENNReal.div_self (coe_ne_zero.mpr p₁n) coe_ne_top).symm
  unfold wnorm wnorm' distribution at hmb_one ⊢
  simp only [one_ne_top, ↓reduceIte, enorm_eq_self, toReal_one, inv_one, rpow_one, iSup_le_iff,
    coe_ne_top, coe_toReal] at hmb_one ⊢
  intro t
  by_cases ht : t = 0
  · rw [ht]; simp
  · apply (rpow_le_rpow_iff cp).mp
    rw [ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe]
    convert! hmb_one (t ^ (p : ℝ))
    · exact (coe_rpow_of_ne_zero ht p).symm
    · rw [rpow_inv_rpow (NNReal.coe_ne_zero.mpr p₁n)]
      congr; ext x; rw [coe_rpow_of_ne_zero ht ↑p]; exact (lt_rpow_inv_iff cp)
    · rw [eLpNorm_norm_rpow v cp, ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe,
        div_eq_mul_inv, rpow_mul, rpow_inv_rpow (NNReal.coe_ne_zero.mpr p₁n), rpow_two]; simp

@[expose]
public def C_weakType_maximalFunction (A p₁ p₂ : ℝ≥0) :=
  if p₁ = p₂ then (ofNNReal A) ^ (2 / p₁ : ℝ) else C2_0_6 A p₁ p₂

@[aesop (rule_sets := [finiteness]) safe apply]
public lemma C_weakType_maximalFunction_lt_top {A p₁ p₂ : ℝ≥0} :
    C_weakType_maximalFunction A p₁ p₂ < ∞ := by
  unfold C_weakType_maximalFunction
  split_ifs with hps
  · apply rpow_lt_top_of_nonneg (by positivity) (by simp)
  · simp

/-- `hasStrongType_maximalFunction` minus the assumption `hR`, but where `p₁ = p₂` is possible and
we only conclude a weak-type estimate. -/
public theorem hasWeakType_maximalFunction
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

include A in
theorem maximalFunction_ae_lt_top [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ ≤ p₂)
    {u : X → E} (hu : MemLp u p₂ μ) :
    ∀ᵐ x ∂μ, maximalFunction μ 𝓑 c r p₁ u x < ∞ := by
  simpa only [lt_top_iff_ne_top, enorm_eq_self] using
    hasWeakType_maximalFunction hp₁ hp₁₂ |>.memWLp hu C_weakType_maximalFunction_lt_top |>.ae_ne_top

public lemma C2_0_6_defaultA_one_two_eq {a : ℕ} :
    C2_0_6 (defaultA a) 1 2 = 2 ^ (a + 3 / (2 : ℝ)) := by
  simp_rw [C2_0_6, div_one, CMB_defaultA_two_eq,
    NNReal.coe_one, inv_one, NNReal.rpow_one]

public lemma C2_0_6_defaultA_one_le {a : ℕ} {q : ℝ≥0} (hq : 1 < q) :
    C2_0_6 (defaultA a) 1 q ≤ 2 ^ (2 * a + 1) * (q / (q - 1)) := by
  rw [C2_0_6, div_one, defaultA, Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_one,
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
