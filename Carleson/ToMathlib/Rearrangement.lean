import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.WeakType

noncomputable section

-- Upstreaming status: NOT READY; this file is being actively worked on.
-- Needs significant clean-up (refactoring, code style, extracting lemmas etc.) first.
-- Warning: Lemmas might have missing assumptions.
open scoped NNReal ENNReal

variable {α ε ε' : Type*} {m : MeasurableSpace α}

namespace MeasureTheory


section rearrangement
variable [ENorm ε] [ENorm ε']


/-! # Decreasing rearrangements `f^#` -/
/- many lemma statements were initially taken from
https://github.com/fpvandoorn/BonnAnalysis/blob/master/BonnAnalysis/LorentzSpace.lean -/

/-- The decreasing rearrangement function `f^#`. It equals `μ univ` for `t = 0`.
Note that unlike the notes, we also define this for `t = ∞`. -/
def rearrangement (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  sInf {σ | distribution f σ μ ≤ t}


variable {f : α → ε} {g : α → ε'} {μ : Measure α} {x y : ℝ≥0∞}

@[gcongr] lemma rearrangement_mono_right (h : x ≤ y) :
    rearrangement f y μ ≤ rearrangement f x μ := by
  apply csInf_le_csInf
  · use 0
    intro σ hσ
    exact zero_le
  · use ⊤
    simp
  · intro x hx
    exact hx.out.trans h

lemma rearrangement_mono_right' : (Antitone (fun t ↦ rearrangement f t μ)) :=
  fun _ _ h ↦ rearrangement_mono_right h

@[gcongr] lemma rearrangement_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    rearrangement f x μ ≤ rearrangement g x μ := by
  apply csInf_le_csInf
  · exact ⟨0, fun σ hσ ↦ zero_le⟩
  · exact ⟨⊤, by simp⟩
  · exact fun σ hσ => le_trans (distribution_mono_left h) hσ

/-
lemma rearrangement_antitone {f : α → ε} {μ : Measure α} :
  Antitone (rearrangement f · μ) := sorry
-/

@[gcongr] lemma rearrangement_mono (h1 : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h2 : x ≤ y) :
    rearrangement f y μ ≤ rearrangement g x μ :=
  le_trans (rearrangement_mono_right h2) (rearrangement_mono_left h1)

@[measurability, fun_prop]
lemma rearrangement_measurable₀ : Measurable (fun t ↦ rearrangement f t μ) :=
  Antitone.measurable (rearrangement_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma rearrangement_measurable {α' : Type*} {m : MeasurableSpace α'} {g : α' → ℝ≥0∞}
  (hg : Measurable g) :
    Measurable (fun y : α' ↦ rearrangement f (g y) μ) := by fun_prop

/-
lemma rearrangement_smul_left (c : 𝕜) :
  rearrangement (c • f) x μ = ‖c‖ₑ * rearrangement f x μ := sorry
-/

lemma rearrangement_distribution_le : rearrangement f (distribution f x μ) μ ≤ x :=
  csInf_le ⟨0, fun y hy ↦ zero_le⟩ (by simp)

lemma distribution_rearrangement_le : distribution f (rearrangement f x μ) μ ≤ x := by
  by_cases hx : rearrangement f x μ = ⊤;
  · aesop
  · -- By definition of `rearrangement`, we know that for any ε > 0, `distribution f (rearrangement f x μ + ε) μ ≤ x`.
    have h_eps : ∀ ε > 0, distribution f (rearrangement f x μ + ε) μ ≤ x := by
      intro ε ε_pos;
      have := exists_lt_of_csInf_lt (by contrapose! hx; simp_all [rearrangement]) (ENNReal.lt_add_right hx ε_pos.ne')
      rcases this with  ⟨σ, hσ₁, hσ₂⟩
      exact le_trans ( distribution_mono_right hσ₂.le ) hσ₁;
    have h_lim : Filter.Tendsto (fun ε => distribution f (rearrangement f x μ + ε) μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (distribution f (rearrangement f x μ) μ)) := by
      have h_lim : ContinuousWithinAt (fun ε => distribution f (rearrangement f x μ + ε) μ) (Set.Ioi 0) 0 := by
        have h_lim : ContinuousWithinAt (fun ε => distribution f ε μ) (Set.Ioi (rearrangement f x μ)) (rearrangement f x μ) :=
          continuousWithinAt_distribution (rearrangement f x μ);
        rw [ ContinuousWithinAt ] at *;
        convert h_lim.comp ( show Filter.Tendsto ( fun ε : ℝ≥0∞ => rearrangement f x μ + ε ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhdsWithin ( rearrangement f x μ ) ( Set.Ioi ( MeasureTheory.rearrangement f x μ ) ) ) from ?_ ) using 2;
        · rw [ add_zero ];
        · rw [ tendsto_nhdsWithin_iff ];
          simp_all only [gt_iff_lt, Set.mem_Ioi]
          constructor
          · exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' (by continuity) _ _ (by simp) );
          · filter_upwards [ self_mem_nhdsWithin ] with n hn using ENNReal.lt_add_right hx hn.ne';
      simpa using h_lim.tendsto
    exact le_of_tendsto h_lim ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_eps ε hε )

-- Lemma 1.1.22 of [Ian Tice]
lemma lt_rearrangement_iff {f : α → ε} {μ : Measure α} {t : ℝ≥0∞} {y : ℝ≥0∞} :
    y < rearrangement f t μ ↔ t < distribution f y μ := by
  constructor
  · unfold rearrangement
    intro h
    contrapose! h
    apply sInf_le
    simpa
  · intro h
    contrapose! h
    calc _
      _ ≤ distribution f (rearrangement f t μ) μ := distribution_mono_right h
      _ ≤ t := distribution_rearrangement_le

lemma distribution_rearrangement {f : α → ε} {μ : Measure α} {t : ℝ≥0} :
    distribution f t μ = distribution (rearrangement f · μ) t volume := by
  unfold distribution
  simp only [enorm_eq_self]
  have : {x | t < rearrangement f x μ} = Set.Iio (distribution f t μ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    exact lt_rearrangement_iff
  rw [this, ENNReal.volume_Iio]
  rfl

lemma rearrangement_add_le {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f g : α → ε} :
    rearrangement (f + g) (x + y) μ ≤ rearrangement f x μ + rearrangement g y μ := by
  apply csInf_le'
  apply le_trans distribution_add_le
  exact add_le_add distribution_rearrangement_le distribution_rearrangement_le

/-
lemma _root_.ContinuousLinearMap.rearrangement_le {f : α → E₁} {g : α → E₂} :
    rearrangement (fun x ↦ L (f x) (g x)) (‖L‖₊ * x * y) μ ≤
    rearrangement f x μ + rearrangement g y μ := sorry
-/

-- Lemma 1.1.22 of [Ian Tice]
lemma continuousWithinAt_rearrangement
  (x : ℝ≥0∞) :
    ContinuousWithinAt (rearrangement f · μ) (Set.Ici x) x := by
  apply tendsto_order.2 ⟨ fun y hy => _, fun y hy => _ ⟩
  · intro y hy
    have := lt_rearrangement_iff.mp hy;
    rw [eventually_nhdsWithin_iff]
    filter_upwards [gt_mem_nhds this] with b hb hb' using by simpa using lt_rearrangement_iff.mpr hb
  · intro y hy
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro b hb
    exact lt_of_le_of_lt (rearrangement_mono_right hb) hy

-- Lemma 1.1.22 of [Ian Tice]
lemma volume_lt_rearrangement [TopologicalSpace ε] (hf : AEStronglyMeasurable f μ) (s : ℝ≥0∞) :
  volume { x | s < rearrangement f (.ofReal x) μ } = distribution f s μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma lintegral_rearrangement_pow [TopologicalSpace ε] (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
  ∫⁻ t, (rearrangement f (.ofReal t) μ) ^ p = ∫⁻ x, ‖f x‖ₑ ∂μ := sorry

-- Lemma 1.1.22 of [Ian Tice]
lemma sSup_rearrangement :
    ⨆ t > 0, rearrangement f t μ = rearrangement f 0 μ := by
  have h := continuousWithinAt_rearrangement 0 (f := f) (μ := μ)
  rw [← continuousWithinAt_Ioi_iff_Ici] at h
  rw [iSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · intro i
    simp only [gt_iff_lt, iSup_le_iff]
    intro hi
    exact rearrangement_mono_right hi.le
  · intro w hw
    have := (h.eventually (lt_mem_nhds hw)).and self_mem_nhdsWithin
    obtain ⟨t, ht₁, ht₂⟩ := this.exists
    use t
    aesop

-- Lemma 1.1.22 of [Ian Tice]
lemma essSup_nnnorm_eq_rearrangement_zero :
    essSup (‖f ·‖ₑ) μ = rearrangement f 0 μ  := by
  unfold essSup rearrangement distribution
  simp [Filter.limsup_eq, ae_iff]

@[simp]
lemma rearrangement_indicator_const {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {s : Set α} {a : ε} :
  rearrangement (s.indicator (Function.const _ a)) x μ
    = ((Set.Ico 0 (μ s)).indicator (Function.const _ ‖a‖ₑ) x) := by
  unfold rearrangement
  simp_rw [distribution_indicator_const]
  unfold Set.indicator
  simp only [Set.mem_Iio, Set.mem_Ico, zero_le, true_and, Function.const_apply]
  split_ifs with h
  · apply le_antisymm
    · apply sInf_le
      simp
    · apply le_sInf
      simp only [Set.mem_setOf_eq]
      intro b hb
      contrapose! hb
      rwa [ite_cond_eq_true]
      simpa
  · rw [← ENNReal.bot_eq_zero, eq_bot_iff]
    apply sInf_le
    simp only [not_lt, bot_eq_zero', Set.mem_setOf_eq] at *
    split_ifs
    · assumption
    · simp

/-
lemma ae_eq_zero_of_rearrangement_eq_zero [TopologicalSpace ε] [ENormedAddMonoid ε]
  (h : (fun t ↦ rearrangement f t μ) =ᵐ[volume] 0) :
    f =ᵐ[μ] 0 := by
  unfold rearrangement at h
-/

open Filter Topology

-- Lemma 1.1.23 of [Ian Tice]
lemma tendsto_rearrangement [TopologicalSpace ε] {s : ℕ → α → ε}
  (hs : ∀ᶠ i in atTop, AEStronglyMeasurable (s i) μ) (hf : AEStronglyMeasurable f μ)
    (h2s : ∀ᵐ x ∂μ, Monotone (fun n ↦ ‖s n x‖ₑ))
      (h : ∀ᵐ x ∂μ, Tendsto (‖s · x‖ₑ) atTop (𝓝 ‖f x‖ₑ)) :
        Tendsto s atTop (𝓝 f) := sorry

-- Lemma 1.1.23 of [Ian Tice]
lemma liminf_rearrangement [TopologicalSpace ε] {s : ℕ → α → ε}
  (hs : ∀ᶠ i in atTop, AEStronglyMeasurable (s i) μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ liminf (‖s · x‖ₑ) atTop) :
      rearrangement f x μ ≤ liminf (fun i ↦ rearrangement (s i) x μ) atTop := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_distribution [TopologicalSpace ε] [Zero ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ distribution f t μ := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_measure [TopologicalSpace ε] [Zero ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ μ X := sorry

-- Lemma 1.1.24 of [Ian Tice]
/-- Version of `rearrangement_indicator_le` for `t : ℝ≥0∞` -/
lemma rearrangement_indicator_le' [TopologicalSpace ε] [Zero ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    rearrangement (X.indicator f) t μ ≤
      Set.indicator (Set.Iio (μ X)) (rearrangement f · μ) t := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma integral_norm_le_integral_rearrangement [TopologicalSpace ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤
      ∫⁻ t in (Set.Iio (μ X)), rearrangement f t μ := sorry

--Theorem 4.17 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_eq [TopologicalSpace ε] [NoAtoms μ] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0} :
    ∫⁻ (s : ℝ≥0) in Set.Iio t, rearrangement f s μ = ⨆ (E : Set α) (_ : μ E ≤ t), ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
  sorry

--Remark 4.18 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_add_rearrangement_le_add_lintegral
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [NoAtoms μ] {f g : α → ε}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {t : ℝ≥0} :
      ∫⁻ (s : ℝ≥0) in Set.Iio t, rearrangement (f + g) s μ
        ≤ (∫⁻ (s : ℝ≥0) in Set.Iio t, rearrangement f s μ)
          + ∫⁻ (s : ℝ≥0) in Set.Iio t, rearrangement g s μ := by
  sorry --use: lintegral_rearrangement_eq

/-

-- todo: Hardy-Littlewood rearrangement inequality for functions into `ℝ≥0∞`.

/-- The Hardy-Littlewood rearrangement inequality, for functions into `𝕜` -/
theorem lintegral_norm_mul_le_lintegral_rearrangement_mul {f g : α → 𝕜} :
    ∫⁻ x, ‖f x * g x‖₊ ∂μ ≤
    ∫⁻ t, rearrangement f (.ofReal t) μ * rearrangement g (.ofReal t) μ := by
  sorry

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q < ∞`. -/
def lnorm' (f : α → E) (p : ℝ≥0∞) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, (ENNReal.ofReal (t ^ (p⁻¹).toReal) *
  rearrangement f (.ofReal t) μ) ^ q⁻¹ / (ENNReal.ofReal t)

/- to do: state and prove lemmas about `lnorm'`. -/

/-- The norm corresponding to the Lorentz space `L^{p,q}` for `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`. -/
def lnorm (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if q = ∞ then
    ⨆ t > 0, ENNReal.ofReal (t ^ (p⁻¹).toReal) * rearrangement f (.ofReal t) μ
  else
    lnorm' f p q.toReal μ

/- to do: double check definition for `p = ∞`
to do: state and prove lemmas about `lnorm`. -/

/-- the Lorentz space `L^{p,q}` -/
def Lorentz {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p q : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | lnorm f p q μ < ∞ }
  zero_mem' := by sorry
  add_mem' {f g} hf hg := by sorry
  neg_mem' {f} hf := by sorry

-/


end rearrangement

end MeasureTheory
