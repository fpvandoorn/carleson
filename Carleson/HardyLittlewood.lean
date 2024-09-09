import Carleson.DoublingMeasure
import Carleson.RealInterpolation
import Mathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter
open scoped NNReal ENNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

-- #check VitaliFamily
-- Note: Lemma 9.0.2 is roughly Vitali.exists_disjoint_covering_ae

section Prelude

variable (X : Type*) [PseudoMetricSpace X] [SeparableSpace X]

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
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) :=
  maximalFunction μ 𝓑 c r 1 u x

-- We will replace the criterion `P` used in `MeasureTheory.SublinearOn.maximalFunction` with a
-- weaker criterion `P'` that is closed under addition and scalar multiplication.

variable (μ) in
private def P (f : X → E) : Prop := Memℒp f ∞ μ ∨ Memℒp f 1 μ

variable (μ) in
private def P' (f : X → E) : Prop :=
  AEStronglyMeasurable f μ ∧ ∀ (c : X) (r : ℝ), ∫⁻ (y : X) in ball c r, ‖f y‖₊ ∂μ < ⊤

private lemma P'_of_P [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ]
    {u : X → E} (hu : P μ u) : P' μ u := by
  refine ⟨hu.elim Memℒp.aestronglyMeasurable Memℒp.aestronglyMeasurable, fun c r ↦ ?_⟩
  refine hu.elim (fun hu ↦ ?_) (fun hu ↦ ?_)
  · have hfg : ∀ᵐ (x : X) ∂μ, x ∈ ball c r → ‖u x‖₊ ≤ eLpNormEssSup u μ :=
      (coe_nnnorm_ae_le_eLpNormEssSup u μ).mono (by tauto)
    apply lt_of_le_of_lt (MeasureTheory.setLIntegral_mono_ae' measurableSet_ball hfg)
    rw [MeasureTheory.setLIntegral_const (ball c r) (eLpNormEssSup u μ)]
    refine ENNReal.mul_lt_top ?_ measure_ball_lt_top
    exact eLpNorm_exponent_top (f := u) ▸ hu.eLpNorm_lt_top
  · have := hu.eLpNorm_lt_top
    simp [eLpNorm, one_ne_zero, reduceIte, ENNReal.one_ne_top, eLpNorm', ENNReal.one_toReal,
      ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self] at this
    exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) this

private lemma P'.add [MeasurableSpace E] [BorelSpace E]
    {f : X → E} {g : X → E} (hf : P' μ f) (hg : P' μ g) : P' μ (f + g) := by
  constructor
  · exact AEStronglyMeasurable.add hf.1 hg.1
  · intro c r
    apply lt_of_le_of_lt (lintegral_mono_nnreal fun y ↦ Pi.add_apply f g y ▸ nnnorm_add_le _ _)
    simp_rw [ENNReal.coe_add, lintegral_add_left' <| aemeasurable_coe_nnreal_ennreal_iff.mpr
      hf.1.aemeasurable.nnnorm.restrict]
    exact ENNReal.add_lt_top.mpr ⟨hf.2 c r, hg.2 c r⟩

private lemma P'.smul [NormedSpace ℝ E] {f : X → E} (hf : P' μ f) (s : ℝ) : P' μ (s • f) := by
  refine ⟨AEStronglyMeasurable.const_smul hf.1 s, fun c r ↦ ?_⟩
  simp_rw [Pi.smul_apply, nnnorm_smul, ENNReal.coe_mul, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hf.2 c r)

-- The average that appears in the definition of `MB`
variable (μ c r) in
private def T (i : ι) (u : X → E) := (⨍⁻ (y : X) in ball (c i) (r i), ‖u y‖₊ ∂μ).toReal

private lemma T.add_le [MeasurableSpace E] [BorelSpace E] [BorelSpace X]
    (i : ι) {f g : X → E} (hf : P' μ f) (hg : P' μ g) :
    ‖T μ c r i (f + g)‖ ≤ ‖T μ c r i f‖ + ‖T μ c r i g‖ := by
  simp only [T, Pi.add_apply, Real.norm_eq_abs, ENNReal.abs_toReal]
  rw [← ENNReal.toReal_add (laverage_lt_top (hf.2 _ _).ne).ne (laverage_lt_top (hg.2 _ _).ne).ne]
  rw [ENNReal.toReal_le_toReal]
  · rw [← setLaverage_add_left' hf.1.ennnorm]
    exact setLaverage_mono' measurableSet_ball (fun x _ ↦ ENNNorm_add_le (f x) (g x))
  · exact (laverage_lt_top ((P'.add hf hg).2 _ _).ne).ne
  · exact (ENNReal.add_lt_top.2 ⟨laverage_lt_top (hf.2 _ _).ne, (laverage_lt_top (hg.2 _ _).ne)⟩).ne

private lemma T.smul [NormedSpace ℝ E] (i : ι) : ∀ {f : X → E} {d : ℝ}, P' μ f → d ≥ 0 →
    T μ c r i (d • f) = d • T μ c r i f := by
  intro f d _ hd
  simp_rw [T, Pi.smul_apply, smul_eq_mul]
  nth_rewrite 2 [← (ENNReal.toReal_ofReal hd)]
  rw [← ENNReal.toReal_mul]
  congr
  rw [setLaverage_const_mul' ENNReal.ofReal_ne_top]
  congr
  ext x
  simp only [nnnorm_smul, ENNReal.coe_mul, ← Real.toNNReal_eq_nnnorm_of_nonneg hd]
  congr

/- NOTE: This was changed to use `ℝ≥0∞` rather than `ℝ≥0` because that was more convenient for the
proof of `first_exception'` in ExceptionalSet.lean. But everything involved there is finite, so
you can prove this with `ℝ≥0` and deal with casting between `ℝ≥0` and `ℝ≥0∞` there, if that turns
out to be easier. -/
theorem Set.Countable.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (h𝓑 : 𝓑.Countable)
    {l : ℝ≥0∞} (hl : 0 < l) {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  obtain ⟨B, hB𝓑, hB, h2B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall
    𝓑 c r R hR (2 ^ 2) (by norm_num)
  have : Countable B := h𝓑.mono hB𝓑
  have disj := fun i j hij ↦ Disjoint.mono ball_subset_closedBall ball_subset_closedBall <|
    hB (Subtype.coe_prop i) (Subtype.coe_prop j) (Subtype.coe_ne_coe.mpr hij)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
          refine l.mul_left_mono (μ.mono fun x hx ↦ ?_)
          simp only [mem_iUnion, mem_ball, exists_prop] at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑
          refine mem_iUnion₂.mpr ⟨b, bB, ?_⟩
          have := interior_mono hb (Metric.ball_subset_interior_closedBall hi)
          -- We would be done if `interior (closedBall (c b) (2 ^ 2 * r b))` was known to be a
          -- subset of `ball (c b) (2 ^ 2 * r b)`.
          sorry
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
    {l : ℝ≥0∞} (hl : 0 < l) {u : X → ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  :=
  let ⟨c, hc⟩ := (𝓑.image r).exists_le
  𝓑.countable_toSet.measure_biUnion_le_lintegral hl hu c (by simpa using hc) h2u

protected theorem MeasureTheory.AEStronglyMeasurable.maximalFunction [BorelSpace X] {p : ℝ}
    {u : X → E} (h𝓑 : 𝓑.Countable) : AEStronglyMeasurable (maximalFunction μ 𝓑 c r p u) μ :=
  (aemeasurable_biSup 𝓑 h𝓑 fun _ _ ↦ aemeasurable_const.indicator measurableSet_ball).pow
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
  refine ENNReal.coe_toNNReal_le_self |>.trans ?_
  apply MB_le_eLpNormEssSup

protected theorem MeasureTheory.SublinearOn.maximalFunction
    [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] (h𝓑 : 𝓑.Finite) :
    SublinearOn (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
    (fun f ↦ Memℒp f ∞ μ ∨ Memℒp f 1 μ) 1 := by
  apply SublinearOn.antitone P'_of_P
  simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one]
  apply SublinearOn.biSup 𝓑 _ _ P'.add (fun hf _ ↦ P'.smul hf _)
  · intro i _
    let B := ball (c i) (r i)
    have (u : X → E) (x : X) : (B.indicator (fun _ ↦ ⨍⁻ y in B, ‖u y‖₊ ∂μ) x).toReal =
        (B.indicator (fun _ ↦ (⨍⁻ y in B, ‖u y‖₊ ∂μ).toReal) x) := by
      by_cases hx : x ∈ B <;> simp [hx]
    simp_rw [this]
    apply (SublinearOn.const (T μ c r i) (P' μ) (T.add_le i) (fun f d ↦ T.smul i)).indicator
  · intro f x hf
    by_cases h𝓑' : 𝓑.Nonempty; swap
    · simp [not_nonempty_iff_eq_empty.mp h𝓑']
    have ⟨i, _, hi⟩ := h𝓑.biSup_eq h𝓑' (fun i ↦ (ball (c i) (r i)).indicator
      (fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖f y‖₊ ∂μ) x)
    rw [hi]
    by_cases hx : x ∈ ball (c i) (r i)
    · simpa [hx] using (laverage_lt_top (hf.2 (c i) (r i)).ne).ne
    · simp [hx]

/- The proof is roughly between (9.0.12)-(9.0.22). -/
open ENNReal in
variable (μ) in
protected theorem HasWeakType.MB_one [BorelSpace X] (h𝓑 : 𝓑.Countable) :
    HasWeakType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) 1 1 μ μ (A ^ 2) := by
  intro f hf
  use AEStronglyMeasurable.maximalFunction_toReal h𝓑
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖₊ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, reduceIte, wnorm', one_toReal, inv_one, rpow_one, coe_pow, eLpNorm,
    one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self, iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hBₗ : (Bₗ t).Countable := h𝓑.mono (fun i hi ↦ mem_of_mem_inter_left hi)
  refine le_trans ?_ (hBₗ.measure_biUnion_le_lintegral (c := c) (r := r) (l := t) ?_ ?_ ?_ ?_ ?_)
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
  · exact coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  · exact continuous_coe.comp_aestronglyMeasurable hf.aestronglyMeasurable.nnnorm
  · sorry -- Removing these two sorries is trivial if `𝓑` is finite.
  · sorry
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x hx ↦ by simp)

/-- The constant factor in the statement that `M_𝓑` has strong type. -/
irreducible_def CMB (A p : ℝ≥0) : ℝ≥0 := sorry

/- The proof is given between (9.0.12)-(9.0.34).
Use the real interpolation theorem instead of following the blueprint. -/
lemma hasStrongType_MB [BorelSpace X] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts μ] [ProperSpace X] [Nonempty X] [μ.IsOpenPosMeasure]
    (h𝓑 : 𝓑.Finite) {p : ℝ≥0} (hp : 1 < p) {u : X → E} (hu : AEStronglyMeasurable u μ) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal)
      p p μ μ (CMB A p) := by
  have h2p : 0 < p := zero_lt_one.trans hp
  have := exists_hasStrongType_real_interpolation
    (T := fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) (p := p) (q := p) (A := 1) ⟨ENNReal.zero_lt_top, le_rfl⟩
    ⟨zero_lt_one, le_rfl⟩ (by norm_num) zero_lt_one (by simp [inv_lt_one_iff, hp, h2p] : p⁻¹ ∈ _) zero_lt_one (pow_pos (A_pos μ) 2)
    (by simp [ENNReal.coe_inv h2p.ne']) (by simp [ENNReal.coe_inv h2p.ne'])
    (fun f hf ↦ AEStronglyMeasurable.maximalFunction_toReal h𝓑.countable)
    (SublinearOn.maximalFunction h𝓑).1 (HasStrongType.MB_top h𝓑.countable |>.hasWeakType le_top)
    (HasWeakType.MB_one μ h𝓑.countable)
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

section GMF

variable [ProperSpace X]

variable (μ) in
/-- The transformation `M` characterized in Proposition 2.0.6.
`p` is `1` in the blueprint, and `globalMaximalFunction μ p u = (M (u ^ p)) ^ p⁻¹ ` -/
@[nolint unusedArguments]
def globalMaximalFunction [μ.IsDoubling A] (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  A ^ 2 * maximalFunction μ ((covering_separable_space X).choose ×ˢ (univ : Set ℤ))
    (fun z ↦ z.1) (fun z ↦ 2 ^ z.2) p u x

-- prove only if needed. Use `MB_le_eLpNormEssSup`
theorem globalMaximalFunction_lt_top {p : ℝ≥0} (hp₁ : 1 ≤ p)
    {u : X → E} (hu : AEStronglyMeasurable u μ) (hu : IsBounded (range u)) {x : X} :
    globalMaximalFunction μ p u  x < ∞ := by
  sorry

protected theorem MeasureTheory.AEStronglyMeasurable.globalMaximalFunction
    [BorelSpace X] {p : ℝ} {u : X → E} : AEStronglyMeasurable (globalMaximalFunction μ p u) μ :=
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

end GMF
