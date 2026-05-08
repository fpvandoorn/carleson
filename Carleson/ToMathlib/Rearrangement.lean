module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
public import Carleson.ToMathlib.MeasureTheory.Integral.Layercake
public import Carleson.ToMathlib.Distribution
public import Carleson.ToMathlib.NoAtoms

@[expose] public section

noncomputable section

-- Upstreaming status: NOT READY; this file is being actively worked on.
-- Needs significant clean-up (refactoring, code style, extracting lemmas etc.) first.
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

@[simp] lemma rearrangement_top : rearrangement f ⊤ μ = 0 := by
  unfold rearrangement
  simp

lemma rearrangement_eq_zero_of_ae_zero_enorm (h : enorm ∘ f =ᵐ[μ] 0) :
    rearrangement f x μ = 0 := by
  unfold rearrangement
  simp_rw [distribution_eq_zero_of_ae_zero_enorm h]
  simp

lemma rearrangement_eq_zero_of_ae_zero {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε}
  (h : f =ᵐ[μ] 0) :
    rearrangement f x μ = 0 := by
  apply rearrangement_eq_zero_of_ae_zero_enorm
  filter_upwards [h] with x hx using (by simp [hx])

@[simp] lemma rearrangement_zero {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] :
    rearrangement (0 : α → ε) x μ = 0 := by
  apply rearrangement_eq_zero_of_ae_zero ae_eq_rfl

@[gcongr] lemma rearrangement_antitone' (h : x ≤ y) :
    rearrangement f y μ ≤ rearrangement f x μ := by
  apply sInf_le_sInf
  intro σ hσ
  exact hσ.out.trans h

lemma rearrangement_antitone : (Antitone (fun t ↦ rearrangement f t μ)) :=
  fun _ _ h ↦ rearrangement_antitone' h

@[gcongr] lemma rearrangement_mono_fun (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    rearrangement f x μ ≤ rearrangement g x μ := by
  apply sInf_le_sInf
  exact fun σ hσ => (distribution_mono_left h).trans hσ

@[gcongr] lemma rearrangement_le_rearrangement (h1 : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h2 : x ≤ y) :
    rearrangement f y μ ≤ rearrangement g x μ :=
  le_trans (rearrangement_antitone' h2) (rearrangement_mono_fun h1)

lemma rearrangment_eq_rearrangement_of_distribution_eq_distribution {β : Type*}
  {m' : MeasurableSpace β} {ν : Measure β} {g : β → ε'} {t : ℝ≥0∞}
  (h : ∀ ⦃s⦄, distribution f s μ = distribution g s ν) :
    rearrangement f t μ = rearrangement g t ν := by
  unfold rearrangement
  simp_rw [h]

@[measurability, fun_prop]
lemma rearrangement_measurable₀ : Measurable (fun t ↦ rearrangement f t μ) :=
  Antitone.measurable (rearrangement_antitone (f := f) (μ := μ))

@[measurability, fun_prop]
lemma rearrangement_measurable {α' : Type*} {m : MeasurableSpace α'} {g : α' → ℝ≥0∞}
  (hg : Measurable g) :
    Measurable (fun y : α' ↦ rearrangement f (g y) μ) := by fun_prop

lemma rearrangement_distribution_le : rearrangement f (distribution f x μ) μ ≤ x :=
  sInf_le (by simp)

lemma distribution_rearrangement_le : distribution f (rearrangement f x μ) μ ≤ x := by
  by_cases hx : rearrangement f x μ = ⊤;
  · aesop
  · -- By definition of `rearrangement`, we know that for any ε > 0, `distribution f (rearrangement f x μ + ε) μ ≤ x`.
    have h_eps : ∀ ε > 0, distribution f (rearrangement f x μ + ε) μ ≤ x := by
      intro ε ε_pos
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
lemma lt_rearrangement_iff_lt_distribution {f : α → ε} {μ : Measure α} {t : ℝ≥0∞} {y : ℝ≥0∞} :
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

lemma rearrangement_le_iff_distribution_le {f : α → ε} {μ : Measure α} {t : ℝ≥0∞} {y : ℝ≥0∞} :
    rearrangement f t μ ≤ y ↔ distribution f y μ ≤ t := by
  contrapose!
  apply lt_rearrangement_iff_lt_distribution

@[simp]
lemma distribution_rearrangement_eq_distribution {f : α → ε} {μ : Measure α} {t : ℝ≥0∞} :
    distribution (rearrangement f · μ) t volume = distribution f t μ := by
  unfold distribution
  simp only [enorm_eq_self]
  have : {x | t < rearrangement f x μ} = Set.Iio (distribution f t μ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    exact lt_rearrangement_iff_lt_distribution
  rw [this, ENNReal.volume_Iio]
  rfl

@[simp]
lemma support_rearrangement_eq {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε} :
    (rearrangement f · μ).support = Set.Iio (μ f.support) := by
  ext x
  simp only [Function.mem_support, ne_eq, Set.mem_Iio]
  rw [← distribution_zero_eq_measure_support, ← lt_rearrangement_iff_lt_distribution]
  simp

lemma ae_eq_zero_of_rearrangement_ae_eq_zero {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (h : (fun t ↦ rearrangement f t μ) =ᵐ[volume] 0) :
    f =ᵐ[μ] 0 := by
  change volume (rearrangement f · μ).support = 0 at h
  rw [support_rearrangement_eq, ENNReal.volume_Iio] at h
  exact h

-- Lemma 1.1.22 of [Ian Tice]
lemma continuousWithinAt_rearrangement :
    ContinuousWithinAt (rearrangement f · μ) (Set.Ici x) x := by
  apply tendsto_order.2 ⟨ fun y hy => _, fun y hy => _ ⟩
  · intro y hy
    have := lt_rearrangement_iff_lt_distribution.mp hy;
    rw [eventually_nhdsWithin_iff]
    filter_upwards [gt_mem_nhds this] with b hb hb' using by simpa using lt_rearrangement_iff_lt_distribution.mpr hb
  · intro y hy
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro b hb
    exact lt_of_le_of_lt (rearrangement_antitone' hb) hy

lemma rearrangement_eq_rearrangement_prod {ε}
  [ENorm ε] {f : α → ε} {t : ℝ≥0∞}
  {β : Type*} {m' : MeasurableSpace β} {ν : Measure β} [IsProbabilityMeasure ν] :
    rearrangement f t μ = rearrangement (fun x : α × β ↦ f x.1) t (μ.prod ν) := by
  apply rearrangment_eq_rearrangement_of_distribution_eq_distribution
  intro s
  exact distribution_eq_distribution_prod

-- Lemma 1.1.24 of [Ian Tice]
lemma rearrangement_indicator_le {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε}
  {X : Set α} :
    rearrangement (X.indicator f) x μ ≤
      Set.indicator (Set.Iio (μ X)) (rearrangement f · μ) x := by
  rw [rearrangement_le_iff_distribution_le]
  rw [Set.indicator_apply]
  split_ifs with hx
  · apply (distribution_mono_left _).trans distribution_rearrangement_le
    filter_upwards
    intro a
    unfold Set.indicator
    split_ifs <;> simp
  · simp only [Set.mem_Iio, not_lt] at hx
    exact distribution_indicator_le_measure.trans hx

@[simp]
lemma rearrangement_indicator_const {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {s : Set α} {a : ε} :
  rearrangement (s.indicator (Function.const _ a)) x μ
    = ((Set.Iio (μ s)).indicator (Function.const _ ‖a‖ₑ) x) := by
  unfold rearrangement
  simp_rw [distribution_indicator_const]
  unfold Set.indicator
  simp only [Set.mem_Iio, Function.const_apply]
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

lemma rearrangement_const_smul {f : α → ℝ≥0∞} {a : ℝ≥0∞} :
    rearrangement (a • f) x μ = a * rearrangement f x μ := by
  by_cases a_zero : a = 0
  · rw [a_zero]
    simp
  by_cases a_top : a = ⊤
  · have : ∞ • f = f.support.indicator (Function.const _ ∞) := by
      ext x
      unfold Set.indicator Function.support
      split_ifs with h
      · simp [ENNReal.top_mul h]
      · simp_all
    rw [a_top, this, rearrangement_indicator_const, ← distribution_zero_eq_measure_support]
    unfold Set.indicator
    simp only [Set.mem_Iio, enorm_eq_self, Function.const_apply]
    split_ifs with hx
    · rw [ENNReal.top_mul]
      rw [← lt_rearrangement_iff_lt_distribution] at hx
      exact hx.ne'
    · push Not at hx
      rw [← rearrangement_le_iff_distribution_le, nonpos_iff_eq_zero] at hx
      rw [hx, mul_zero]
  apply le_antisymm
  · apply sInf_le
    simp only [Set.mem_setOf_eq]
    rw [distribution_const_smul (Or.inl a_zero) (Or.inl a_top),
      mul_div_assoc, ENNReal.mul_div_cancel a_zero a_top]
    apply distribution_rearrangement_le
  · apply le_sInf
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    rw [distribution_const_smul (Or.inl a_zero) (Or.inl a_top)] at hs
    calc _
      _ ≤ a * rearrangement f (distribution f (s / a) μ) μ := by gcongr
      _ ≤ a * (s / a) := by
        gcongr
        apply rearrangement_distribution_le
      _ = s := ENNReal.mul_div_cancel a_zero a_top

section superlevelSet

lemma rearrangement_indicator_superlevelSet {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} {t : ℝ≥0∞} :
    rearrangement ((superlevelSet f t).indicator f) x μ
      = (superlevelSet (rearrangement f · μ) t).indicator (rearrangement f · μ) x := by
  rw [rearrangement]
  simp_rw [distribution_indicator_superlevelSet]
  simp only [inf_le_iff]
  unfold Set.indicator superlevelSet
  simp only [enorm_eq_self, Set.mem_setOf_eq]
  split_ifs with h
  · rw [lt_rearrangement_iff_lt_distribution] at h
    unfold rearrangement
    congr with σ
    simp [h]
  · push Not at h
    rw [rearrangement_le_iff_distribution_le] at h
    simp [h]

lemma rearrangement_indicator_superlevelSet_compl {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} (ht : distribution f t μ ≠ ∞) :
    rearrangement ((superlevelSet f t)ᶜ.indicator f) x μ
      = rearrangement f (x + distribution f t μ) μ := by
  rw [rearrangement]
  simp_rw [distribution_indicator_superlevelSet_compl hf ht, tsub_le_iff_right]
  rfl

end superlevelSet

section comp

lemma measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite' {ε} [TopologicalSpace ε]
  [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) (hf' : μ f.support < ∞) {s : Set ℝ≥0∞}
  (hs : MeasurableSet s) :
    μ {x | ‖f x‖ₑ ∈ s \ {0}} = volume {x | rearrangement f x μ ∈ s \ {0}} := by
  apply MeasurableSpace.induction_on_inter
    (C := fun s hs ↦ μ {x | ‖f x‖ₑ ∈ s \ {0}} = volume {x | ‖rearrangement f x μ‖ₑ ∈ s \ {0}})
    (borel_eq_generateFrom_Ioi ℝ≥0∞) isPiSystem_Ioi _ _ _ _ _ hs
  · simp
  · intro s hs
    rcases hs with ⟨t, ht⟩
    rw [← ht]
    simp only [Set.mem_Ioi, not_lt_zero, not_false_eq_true, Set.diff_singleton_eq_self]
    rw [← distribution, ← distribution, distribution_rearrangement_eq_distribution]
  · intro s hs h
    calc _
      _ = μ {x | ‖f x‖ₑ ≠ 0} - μ {x | ‖f x‖ₑ ∈ s \ {0}} := by
        rw [← measure_diff]
        · nth_rw 2 [Set.diff_eq]
          rw [Set.compl_setOf, ← Set.setOf_and]
          congr with x
          grind
        · simp
        · exact AEMeasurable.nullMeasurableSet_preimage hf.enorm (by aesop)
        · rw [← lt_top_iff_ne_top]
          apply hf'.trans_le'
          gcongr
          unfold Function.support
          aesop
      _ = volume {x | rearrangement f x μ ≠ 0} - volume {x | rearrangement f x μ ∈ s \ {0}} := by
        congr
        rw [← ENNReal.bot_eq_zero]
        simp_rw [← bot_lt_iff_ne_bot]
        rw [ENNReal.bot_eq_zero, ← distribution, ← distribution_rearrangement_eq_distribution]
        rfl
      _ = volume {x | rearrangement f x μ ∈ sᶜ \ {0}} := by
        rw [← measure_diff]
        · nth_rw 1 [Set.diff_eq]
          rw [Set.compl_setOf, ← Set.setOf_and]
          congr with x
          grind
        · simp
        · exact AEMeasurable.nullMeasurableSet_preimage rearrangement_measurable₀.aemeasurable (by aesop)
        · rw [← lt_top_iff_ne_top]
          apply hf'.trans_le'
          rw [← distribution_zero_eq_measure_support, ← distribution_rearrangement_eq_distribution]
          unfold distribution
          rw [← ENNReal.bot_eq_zero]
          simp_rw [bot_lt_iff_ne_bot]
          rw [ENNReal.bot_eq_zero]
          gcongr
          aesop
  · intro S hSd hSm hS
    calc _
      _ = μ (⋃ i, {x | ‖f x‖ₑ ∈ S i \ {0}}) := by
        rw [Set.iUnion_setOf]
        congr with x
        simp
      _ = ∑' i, μ ({x | ‖f x‖ₑ ∈ S i \ {0}}) := by
        apply measure_iUnion₀
        · intro i j hij
          unfold Function.onFun
          apply Disjoint.aedisjoint
          rw [Set.disjoint_iff]
          intro x
          simp only [Set.mem_diff, Set.mem_singleton_iff, enorm_eq_zero, Set.mem_inter_iff,
            Set.mem_setOf_eq, Set.mem_empty_iff_false, imp_false, not_and, not_not, and_imp]
          intro hi _ hj
          exfalso
          have := hSd hij
          contrapose this
          rw [Set.not_disjoint_iff]
          use ‖f x‖ₑ, hi, hj
        · exact fun i ↦ AEMeasurable.nullMeasurableSet_preimage hf.enorm (by aesop)
      _ = ∑' i,  volume {x | rearrangement f x μ ∈ S i \ {0}} := by
        congr with i
        exact hS i
      _ = volume (⋃ i, {x | rearrangement f x μ ∈ S i \ {0}}) := by
        symm
        apply measure_iUnion₀
        · intro i j hij
          unfold Function.onFun
          apply Disjoint.aedisjoint
          rw [Set.disjoint_iff]
          intro x
          simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_inter_iff,
            Set.mem_setOf_eq, Set.mem_empty_iff_false, imp_false, not_and, not_not, and_imp]
          intro hi _ hj
          exfalso
          have := hSd hij
          contrapose this
          rw [Set.not_disjoint_iff]
          use ‖rearrangement f x μ‖ₑ, hi, hj
        · exact fun i ↦ AEMeasurable.nullMeasurableSet_preimage rearrangement_measurable₀.aemeasurable (by aesop)
      _ = volume {x | rearrangement f x μ ∈ (⋃ i, S i) \ {0}} := by
        rw [Set.iUnion_setOf]
        congr with x
        simp

lemma measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite {ε} [TopologicalSpace ε]
  [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) (hf' : μ f.support < ∞) {s : Set ℝ≥0∞}
  (hs : MeasurableSet s) (zero_notin_s : 0 ∉ s) :
    μ {x | ‖f x‖ₑ ∈ s} = volume {x | rearrangement f x μ ∈ s} := by
  have : s = s \ {0} := by aesop
  rw [this]
  exact measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite' hf hf' hs

lemma measure_enorm_mem_eq_volume_rearrangement_mem' {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {s : Set ℝ≥0∞}
  (hs : MeasurableSet s) (zero_notin_s : 0 ∉ s) (h : ∃ T, (∀ t ∈ s, T < t) ∧ distribution f T μ < ∞) :
    μ {x | ‖f x‖ₑ ∈ s} = volume {x | rearrangement f x μ ∈ s} := by
  rcases h with ⟨T, hT, hT'⟩
  have hμ : {x | ‖f x‖ₑ ∈ s} = {x | ‖(superlevelSet f T).indicator f x‖ₑ ∈ s} := by
    ext x
    unfold superlevelSet Set.indicator
    aesop
  have hvolume : {x | rearrangement f x μ ∈ s}
      = {x | (superlevelSet (rearrangement f · μ) T).indicator (rearrangement f · μ) x ∈ s} := by
    ext x
    unfold superlevelSet Set.indicator
    aesop
  rw [hμ, hvolume]
  rw [measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite (μ := μ) _ _ hs zero_notin_s]
  · congr with x
    rw [rearrangement_indicator_superlevelSet]
  · exact hf.indicator₀ (nullMeasurableSet_superlevelSet hf)
  · rw [← distribution_zero_eq_measure_support, distribution_indicator_superlevelSet]
    exact min_lt_of_left_lt hT'

lemma measure_enorm_eq_eq_volume_rearrangement_eq {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {a : ℝ≥0∞}
  (ha : distribution f a μ ≠ ∞) (h : μ {x | ‖f x‖ₑ = a} = ⊤) :
    volume {x | rearrangement f x μ = a} = ⊤ := by
  rw [← top_le_iff]
  calc _
    _ ≤ volume {x | rearrangement f (x + distribution f a μ) μ = a} := by
      simp_rw [← rearrangement_indicator_superlevelSet_compl hf ha]
      rw [← ENNReal.volume_Iio (a := ∞)]
      gcongr
      intro x hx
      simp only [Set.mem_Iio, Set.mem_setOf_eq] at *
      apply le_antisymm
      · rw [rearrangement_le_iff_distribution_le]
        have :  distribution ((superlevelSet f a)ᶜ.indicator f) a μ = 0 := by
          unfold distribution superlevelSet Set.indicator
          rw [← measure_empty (μ := μ)]
          congr 1
          ext x
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Set.mem_empty_iff_false,
            iff_false]
          split_ifs
          · assumption
          · simp
        rw [this]
        simp
      · unfold rearrangement
        apply le_sInf
        intro b
        simp only [Set.mem_setOf_eq]
        contrapose!
        intro hb
        unfold distribution
        apply hx.trans_le
        rw [← h]
        gcongr with x
        intro hfa
        unfold Set.indicator superlevelSet
        split_ifs with h
        · rwa [hfa]
        · simp at h
          order
    _ = Measure.map (· + distribution f a μ) volume {x | rearrangement f x μ = a} := by
      rw [Measure.map_apply (by measurability) (by measurability)]
      congr
    _ ≤ volume {x | rearrangement f x μ = a} := by
      apply ENNReal.volume_map_add_right_le_self ha (by measurability)

lemma measure_enorm_mem_eq_volume_rearrangement_mem {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {s : Set ℝ≥0∞}
  (hs : MeasurableSet s) (zero_notin_s : 0 ∉ s) (inf_not_mem : sInf s ∉ s)
  (hs' : ∀ t ∈ s, distribution f t μ < ∞) :
    μ {x | ‖f x‖ₑ ∈ s} = volume {x | rearrangement f x μ ∈ s} := by
  by_cases s_nonempty : s = ∅
  · rw [s_nonempty]
    simp
  simp_rw [← Set.nonempty_iff_ne_empty] at s_nonempty
  have s_bddBelow : BddBelow s := by simp
  rcases exists_seq_tendsto_sInf s_nonempty s_bddBelow with ⟨u, antitone_u, tendsto_u, hus⟩
  have hμ : {x | ‖f x‖ₑ ∈ s} = ⋃ n, {x | ‖(superlevelSet f (u n)).indicator f x‖ₑ ∈ s} := by
    ext x
    unfold superlevelSet Set.indicator
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hfs
      have : ∃ i, u i < ‖f x‖ₑ := by
        refine iInf_lt_iff.mp ?_
        rw [iInf_eq_of_tendsto antitone_u tendsto_u]
        apply lt_of_le_of_ne (sInf_le hfs)
        grind
      rcases this with ⟨i, hi⟩
      use i
      split_ifs
      use hfs
    · aesop
  have hvolume : {x | rearrangement f x μ ∈ s}
      = ⋃ n, {x | (superlevelSet (rearrangement f · μ) (u n)).indicator (rearrangement f · μ) x ∈ s} := by
    ext x
    unfold superlevelSet Set.indicator
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hfs
      have : ∃ i, u i < rearrangement f x μ := by
        refine iInf_lt_iff.mp ?_
        rw [iInf_eq_of_tendsto antitone_u tendsto_u]
        apply lt_of_le_of_ne (sInf_le hfs)
        grind
      rcases this with ⟨i, hi⟩
      use i
      simp only [enorm_eq_self]
      split_ifs
      use hfs
    · aesop
  rw [hμ, hvolume, Monotone.measure_iUnion, Monotone.measure_iUnion]
  · congr with i
    rw [measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite (μ := μ) _ _ hs zero_notin_s]
    · congr with x
      rw [rearrangement_indicator_superlevelSet]
    · exact hf.indicator₀ (nullMeasurableSet_superlevelSet hf)
    · rw [← distribution_zero_eq_measure_support, distribution_indicator_superlevelSet]
      exact min_lt_of_left_lt (hs' (u i) (hus i))
  · intro n m hmn
    simp only
    unfold Set.indicator
    intro x
    simp only [Set.mem_setOf_eq]
    split_ifs with hn hm
    · exact id
    · exfalso
      unfold superlevelSet at hn hm
      simp only [enorm_eq_self, Set.mem_setOf_eq, not_lt] at hn hm
      have := antitone_u hmn
      order
    · simp [zero_notin_s]
    · exact id
  · intro n m hmn
    simp only
    unfold Set.indicator
    intro x
    simp only [Set.mem_setOf_eq]
    split_ifs with hn hm
    · exact id
    · exfalso
      unfold superlevelSet at hn hm
      simp only [Set.mem_setOf_eq, not_lt] at hn hm
      have := antitone_u hmn
      order
    · simp [zero_notin_s]
    · exact id

lemma distribution_comp_eq_distribution_comp_rearrangement' {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) (g_zero : g 0 = 0)
  {t : ℝ≥0∞} (h : ∃ T, (∀ s ≤ T, g s ≤ t) ∧ distribution f T μ < ∞) :
    distribution (fun x ↦ g ‖f x‖ₑ) t μ = distribution (g ∘ (rearrangement f · μ)) t volume := by
  unfold distribution
  simp only [enorm_eq_self]
  calc _
    _ = μ {x | ‖f x‖ₑ ∈ g ⁻¹' Set.Ioi t} := by rfl
    _ = volume {s | rearrangement f s μ ∈ g ⁻¹' Set.Ioi t} := by
      apply measure_enorm_mem_eq_volume_rearrangement_mem' hf (by measurability) (by aesop)
      rcases h with ⟨T, hT, hT'⟩
      use T
      simp only [Set.mem_preimage, Set.mem_Ioi, hT', and_true]
      intro s hs
      contrapose! hs
      exact hT s hs

lemma distribution_comp_eq_distribution_comp_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) (hf' : ∀ σ > 0, distribution f σ μ < ∞) {g : ℝ≥0∞ → ℝ≥0∞} {t : ℝ≥0∞}
  (hg : Measurable g) (g_zero : g 0 = 0) :
    distribution (fun x ↦ g ‖f x‖ₑ) t μ = distribution (g ∘ (rearrangement f · μ)) t volume := by
  by_cases! h : sInf (g ⁻¹' Set.Ioi t) ≠ 0
  · rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot, ENNReal.bot_eq_zero] at h
    apply distribution_comp_eq_distribution_comp_rearrangement' hf hg g_zero
    rcases exists_between h with ⟨T, hT, hT'⟩
    use T
    simp only [hf' _ hT, and_true]
    intro s hs
    by_contra!
    have : sInf (g ⁻¹' Set.Ioi t) ≤ s := by
      apply sInf_le
      exact this
    order
  unfold distribution
  simp only [enorm_eq_self]
  calc _
    _ = μ {x | ‖f x‖ₑ ∈ g ⁻¹' Set.Ioi t} := by rfl
    _ = volume {s | rearrangement f s μ ∈ g ⁻¹' Set.Ioi t} := by
      apply measure_enorm_mem_eq_volume_rearrangement_mem hf (by measurability) (by aesop)
      · rw [h]
        aesop
      intro σ hσ
      apply hf'
      contrapose! hσ
      aesop

lemma lintegral_comp_rearrangement' {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) (g_zero : g 0 = 0)
  (hg' : ∀ t > 0, distribution f t μ = ∞ → ∃ S > 0, ∀ y > t, S < g y) :
    ∫⁻ x, g ‖f x‖ₑ ∂μ = ∫⁻ t, g (rearrangement f t μ) := by
  set T := sInf {σ | distribution f σ μ < ∞}
  rw [lintegral_eq_lintegral_distribution _ (by fun_prop)]
  symm
  rw [lintegral_eq_lintegral_distribution _ (by fun_prop)]
  symm
  by_cases hT : T = 0
  · congr with t
    apply distribution_comp_eq_distribution_comp_rearrangement hf _ hg g_zero
    unfold T at hT
    rw [← ENNReal.bot_eq_zero, sInf_eq_bot] at hT
    intro σ hσ
    rcases hT σ hσ with ⟨s, hs, hsσ⟩
    exact hs.trans_le' (distribution_mono_right hsσ.le)
  unfold T at hT
  rw [← ENNReal.bot_eq_zero, sInf_eq_bot] at hT
  simp only [bot_eq_zero', Set.mem_setOf_eq, not_forall, not_exists,
    not_and, not_lt] at hT
  simp_rw [← not_lt, imp_not_comm, not_lt, top_le_iff] at hT
  rcases hT with ⟨u, u_pos, hu⟩
  rcases exists_between u_pos with ⟨t, t_pos, ht⟩
  have ht := hu t ht
  have hS : ∃ S > 0, distribution (fun x ↦ g ‖f x‖ₑ) S μ = ∞ := by
    rcases hg' t t_pos ht with ⟨S, S_pos, hS⟩
    use S, S_pos
    rw [← top_le_iff, ← ht]
    unfold distribution
    gcongr 2 with x
    intro h
    simp only [enorm_eq_self]
    exact hS _ h
  have hS' : ∃ S > 0, distribution (fun t ↦ g (rearrangement f t μ)) S volume = ∞ := by
    rcases hg' t t_pos ht with ⟨S, S_pos, hS⟩
    use S, S_pos
    rw [← top_le_iff, ← ht, ← distribution_rearrangement_eq_distribution]
    unfold distribution
    gcongr 2 with x
    intro h
    simp only [enorm_eq_self]
    exact hS _ h
  convert (Eq.refl ∞)
  · rw [eq_top_iff]
    rcases hS with ⟨S, S_pos, hS⟩
    calc _
      _ = ∫⁻ t in Set.Iio S, ⊤ := by
        rw [lintegral_const]
        simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
        rw [ENNReal.volume_Iio, ENNReal.top_mul S_pos.ne']
      _ = ∫⁻ t in Set.Iio S, distribution (fun x ↦ g ‖f x‖ₑ) t μ := by
        apply setLIntegral_congr_fun measurableSet_Iio
        intro x hx
        simp only
        symm
        rw [eq_top_iff, ← hS]
        apply distribution_mono_right hx.le
      _ ≤ ∫⁻ t, distribution (fun x ↦ g ‖f x‖ₑ) t μ := by
        apply setLIntegral_le_lintegral
  · rw [eq_top_iff]
    rcases hS' with ⟨S, S_pos, hS⟩
    calc _
      _ = ∫⁻ t in Set.Iio S, ⊤ := by
        rw [lintegral_const]
        simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
        rw [ENNReal.volume_Iio, ENNReal.top_mul S_pos.ne']
      _ = ∫⁻ t in Set.Iio S, distribution (fun t ↦ g (rearrangement f t μ)) t volume := by
        apply setLIntegral_congr_fun measurableSet_Iio
        intro x hx
        simp only
        symm
        rw [eq_top_iff, ← hS]
        apply distribution_mono_right hx.le
      _ ≤ ∫⁻ t, distribution (fun t ↦ g (rearrangement f t μ)) t volume := by
        apply setLIntegral_le_lintegral

lemma lintegral_comp_rearrangement_of_distribution_finite {ε} [TopologicalSpace ε]
  [ENormedAddMonoid ε] {f : α → ε} (hf : AEStronglyMeasurable f μ)
  (hf' : ∀ t > 0, distribution f t μ ≠ ⊤) {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) (g_zero : g 0 = 0) :
    ∫⁻ x, g ‖f x‖ₑ ∂μ = ∫⁻ t, g (rearrangement f t μ) := by
  apply lintegral_comp_rearrangement' hf hg g_zero
  intro t t_pos h
  exfalso
  exact hf' t t_pos h

lemma lintegral_comp_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) (g_zero : g 0 = 0)
  (hg' : ∀ t > 0, ∃ S > 0, ∀ y > t, S < g y) :
    ∫⁻ x, g ‖f x‖ₑ ∂μ = ∫⁻ t, g (rearrangement f t μ) := by
  apply lintegral_comp_rearrangement' hf hg g_zero
  intro t t_pos _
  exact hg' t t_pos

lemma lintegral_comp_rearrangement_of_strictmono {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) (g_zero : g 0 = 0)
  (hg' : StrictMono g) :
    ∫⁻ x, g ‖f x‖ₑ ∂μ = ∫⁻ t, g (rearrangement f t μ) := by
  apply lintegral_comp_rearrangement hf hg g_zero
  intro t t_pos
  use g t
  rw [← g_zero]
  use hg' t_pos, fun y hy ↦ hg' hy

--TODO: more versions with more general assumptions on g

-- Lemma 1.1.22 of [Ian Tice]
lemma lintegral_rearrangement_pow {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ t, (rearrangement f t μ) ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  symm
  apply lintegral_comp_rearrangement_of_strictmono (g := fun t ↦ t ^ p) hf (by fun_prop) (by simpa)
  exact ENNReal.strictMono_rpow_of_pos hp

lemma lintegral_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) :
    ∫⁻ t, (rearrangement f t μ) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have := lintegral_rearrangement_pow hf zero_lt_one
  simp at this
  assumption

end comp

lemma rearrangement_add_le {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f g : α → ε} :
    rearrangement (f + g) (x + y) μ ≤ rearrangement f x μ + rearrangement g y μ := by
  apply csInf_le'
  apply le_trans distribution_add_le
  exact add_le_add distribution_rearrangement_le distribution_rearrangement_le

-- Lemma 1.1.22 of [Ian Tice]
lemma sSup_rearrangement :
    ⨆ t > 0, rearrangement f t μ = rearrangement f 0 μ := by
  have h := continuousWithinAt_rearrangement (x := 0) (f := f) (μ := μ)
  rw [← continuousWithinAt_Ioi_iff_Ici] at h
  rw [iSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · intro i
    simp only [gt_iff_lt, iSup_le_iff]
    intro hi
    exact rearrangement_antitone' hi.le
  · intro w hw
    have := (h.eventually (lt_mem_nhds hw)).and self_mem_nhdsWithin
    obtain ⟨t, ht₁, ht₂⟩ := this.exists
    use t
    aesop

section eLpNorm

-- Lemma 1.1.22 of [Ian Tice]
lemma rearrangement_zero_eq_eLpNormEssSup :
    rearrangement f 0 μ = eLpNormEssSup f μ  := by
  unfold eLpNormEssSup essSup rearrangement distribution
  simp [Filter.limsup_eq, ae_iff]

--TODO: do we need these lemmas?
/-
lemma eLpNormEssSup_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε} :
    eLpNormEssSup (rearrangement f · μ) volume = eLpNormEssSup f μ := by
  /-
  rw [eLpNorm, ENNReal.rpow_zero, one_mul]
  exact rearrangement_zero_eq_eLpNormEssSup
  -/
  --distribution_eLpNormEssSup
  sorry
-/

lemma eLpNorm'_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm' (rearrangement f · μ) p volume = eLpNorm' f p μ := by
  unfold eLpNorm'
  simp only [enorm_eq_self, one_div]
  rw [lintegral_rearrangement_pow hf hp]

--TODO: do we need these lemmas?
/-
lemma eLpNorm_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} :
    eLpNorm (rearrangement f · μ) p volume = eLpNorm f p μ := by
  unfold eLpNorm
  split_ifs with p_zero p_top
  · rfl
  · exact eLpNormEssSup_rearrangement
  · exact eLpNorm'_rearrangement hf (ENNReal.toReal_pos p_zero p_top)
-/

end eLpNorm

section lintegral

--TODO: prove these lemmas when needed
/-
--Theorem 4.15 in https://doi.org/10.1007/978-3-319-30034-4
/-- Hardy-Littlewood rearrangement inequality -/
lemma lintegral_mul_le_lintegral_rearrangement_mul_rearrangement {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f g : α → ε}
  (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ ≤ ∫⁻ t, rearrangement f t μ * rearrangement g t μ := by
  sorry

lemma lintegral_withDensity_le_lintegral_rearrangement_withDensity {ε} [TopologicalSpace ε]
  [ContinuousENorm ε] {f : α → ε} {d : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
  (hd : AEMeasurable d μ) :
    ∫⁻ x, ‖f x‖ₑ ∂μ.withDensity d ≤ ∫⁻ t, rearrangement f t μ ∂volume.withDensity (rearrangement d · μ) := by
    rw [lintegral_withDensity_eq_lintegral_mul₀' hd (by fun_prop)]
    dsimp only [Pi.mul_apply]
    conv in (d _) => rw [← enorm_eq_self (d _)]
    calc _
      _ ≤ ∫⁻ s, rearrangement d s μ * rearrangement f s μ := by
        apply lintegral_mul_le_lintegral_rearrangement_mul_rearrangement hd.aestronglyMeasurable hf.enorm.aestronglyMeasurable
      _ = ∫⁻ t, rearrangement f t μ ∂volume.withDensity (rearrangement d · μ) := by
        rw [lintegral_withDensity_eq_lintegral_mul₀' (by fun_prop) (by fun_prop)]
        simp
-/

-- Lemma 1.1.24 of [Ian Tice]
lemma setLIntegral_enorm_le_lintegral_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) :
    ∫⁻ x in X, ‖f x‖ₑ ∂μ ≤
      ∫⁻ t in (Set.Iio (μ X)), rearrangement f t μ := by
  rw [← lintegral_indicator hX, ← lintegral_indicator measurableSet_Iio]
  have : (fun x ↦ ‖f x‖ₑ) = enorm ∘ f := by
    ext x
    simp only [Function.comp_apply]
  rw [this, Set.indicator_comp_of_zero enorm_zero]
  simp only [Function.comp_apply]
  rw [← lintegral_rearrangement (by measurability)]
  gcongr with t
  exact rearrangement_indicator_le

lemma setLIntegral_enorm_eq {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : NullMeasurableSet X μ) :
    ∫⁻ x in X, ‖f x‖ₑ ∂μ =
      ∫⁻ t, μ (X ∩ {x | t < ‖f x‖ₑ}) := by
  rw [← lintegral_indicator₀ hX, lintegral_eq_lintegral_distribution _ (by measurability)]
  congr with t
  unfold distribution
  congr with x
  unfold Set.indicator
  simp only [enorm_eq_self]
  have : (X ∩ {x | t < ‖f x‖ₑ}) x = (x ∈ X ∧ t < ‖f x‖ₑ) := rfl
  rw [this]
  split_ifs with hx <;> simp [hx]

lemma setLIntegral_eq {f : α → ℝ≥0∞}
  (hf : AEMeasurable f μ) {X : Set α} (hX : NullMeasurableSet X μ) :
    ∫⁻ x in X, f x ∂μ =
      ∫⁻ t, μ (X ∩ {x | t < f x}) := by
  conv => pattern f _; rw [← enorm_eq_self (f _)]
  rw [setLIntegral_enorm_eq hf.aestronglyMeasurable hX]
  simp

lemma lintegral_rearrangement_eq' {f : α → ε} {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ = ∫⁻ s, min (distribution f s μ) t := by
  rw [lintegral_eq_lintegral_distribution _ (by fun_prop)]
  congr with s
  unfold distribution
  simp only [enorm_eq_self, measurableSet_Iio, Measure.restrict_apply']
  simp_rw [lt_rearrangement_iff_lt_distribution, Set.Iio_def, Set.Iio_inter_Iio]
  rw [ENNReal.volume_Iio]
  rfl

lemma lintegral_rearrangement_eq'' {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio (distribution f t μ), rearrangement f s μ = ∫⁻ x in {y | t < ‖f y‖ₑ}, ‖f x‖ₑ ∂μ := by
  rw [lintegral_rearrangement_eq',
    setLIntegral_eq hf.enorm (nullMeasurableSet_lt measurable_const.aemeasurable hf.enorm)]
  congr with s
  rw [← distribution_mono_right'.map_max]
  unfold distribution
  congr 1
  ext x
  aesop

--Theorem 4.17 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_eq {ε} [TopologicalSpace ε] [ContinuousENorm ε] [NoAtoms' μ] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ
      = ⨆ (E : Set α) (_ : NullMeasurableSet E μ) (_ : μ E ≤ t), ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
  rw [lintegral_rearrangement_eq']
  apply le_antisymm
  · by_cases h_zero : rearrangement f t μ = 0
    · rw [← ENNReal.bot_eq_zero, ← le_bot_iff, rearrangement_le_iff_distribution_le, ENNReal.bot_eq_zero] at h_zero
      apply le_iSup_of_le (superlevelSet f 0)
      apply le_iSup_of_le (nullMeasurableSet_superlevelSet hf)
      apply le_iSup_of_le h_zero
      rw [setLIntegral_enorm_eq hf (nullMeasurableSet_superlevelSet hf), superlevelSet]
      gcongr with s
      apply min_le_of_left_le
      unfold distribution
      gcongr
      intro x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      intro hs
      simp only [hs, and_true]
      apply hs.trans_le'
      simp
    rw [← ENNReal.bot_eq_zero, ← le_bot_iff, not_le, ENNReal.bot_eq_zero] at h_zero
    have : ∀ a < rearrangement f t μ,
      ∫⁻ s in (Set.Ioo a (rearrangement f t μ))ᶜ, min (distribution f s μ) t
        ≤ ⨆ E, ⨆ (_ : NullMeasurableSet E μ), ⨆ (_ : μ E ≤ t), ∫⁻ (x : α) in E, ‖f x‖ₑ ∂μ := by
      intro a ha
      have : ∃ E, NullMeasurableSet E μ∧ superlevelSet f (rearrangement f t μ) ⊆ E ∧ E ⊆ superlevelSet f a ∧ μ E = t := by
        have lb := distribution_rearrangement_le (f := f) (μ := μ) (x := t)
        rw [distribution_eq_measure_superlevelSet] at lb
        have ub : t ≤ μ (superlevelSet f a) := by
          rw [lt_rearrangement_iff_lt_distribution] at ha
          exact ha.le
        apply NoAtoms'.exists_nullmeasurable_between_measure_eq (nullMeasurableSet_superlevelSet hf)
          (nullMeasurableSet_superlevelSet hf) (superlevelSet_antitone ha.le) lb ub
      rcases this with ⟨E, measE, hE, hE', hμE⟩
      apply le_iSup_of_le E
      apply le_iSup_of_le measE
      apply le_iSup_of_le hμE.le
      rw [setLIntegral_enorm_eq hf measE, ← lintegral_indicator measurableSet_Ioo.compl]
      gcongr with s
      unfold Set.indicator
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt]
      split_ifs with h
      rotate_left
      · simp
      by_cases! h' : distribution f s μ ≤ t
      · rw [min_eq_left h']
        rw [← rearrangement_le_iff_distribution_le] at h'
        unfold distribution
        gcongr
        rw [Set.inter_eq_right.mpr]
        apply hE.trans'
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        exact hx.trans_le' h'
      · have has : s ≤ a := by
          rw [rearrangement_le_iff_distribution_le] at h
          contrapose! h
          exact ⟨h, h'⟩
        rw [min_eq_right h'.le, ← hμE]
        gcongr
        rw [Set.inter_eq_left.mpr]
        apply hE'.trans
        simp only [Set.setOf_subset_setOf, superlevelSet]
        exact fun a_2 a_3 ↦ Std.lt_of_le_of_lt has a_3
    rcases exists_seq_strictMono_tendsto' h_zero with ⟨a, mono_a, ha, a_tendsto⟩
    calc _
      _ = ⨆ n, ∫⁻ (s : ℝ≥0∞), (Set.Ioo (a n) (rearrangement f t μ))ᶜ.indicator (fun s ↦ min (distribution f s μ) t) s := by
        rw [← lintegral_iSup]
        rotate_left
        · intro n
          measurability
        · intro n m hmn
          simp only
          gcongr
          exact mono_a.monotone hmn
        congr with s
        rw [← iSup_apply, Set.iSup_indicator ENNReal.bot_eq_zero monotone_const]
        rotate_left
        · intro n m hmn
          simp only [compl_le_compl_iff_le, Set.le_eq_subset]
          gcongr
          exact mono_a.monotone hmn
        have : Set.univ = ⋃ n, (Set.Ioo (a n) (rearrangement f t μ))ᶜ := by
          ext x
          simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt,
            true_iff]
          rw [tendsto_order] at a_tendsto
          have a_tendsto := a_tendsto.1
          contrapose! a_tendsto
          use x, (a_tendsto 0).2
          apply Filter.Frequently.of_forall
          exact fun n ↦ (a_tendsto n).1.le
        rw [← this]
        simp
      _ ≤ _ := by
        apply iSup_le
        intro n
        rw [lintegral_indicator measurableSet_Ioo.compl]
        exact this (a n) (ha n).2
  · simp only [iSup_le_iff]
    intro E measE hμE
    rw [setLIntegral_enorm_eq hf measE]
    gcongr with s
    apply le_min
    · unfold distribution
      gcongr
      exact Set.inter_subset_right
    · apply hμE.trans'
      gcongr
      exact Set.inter_subset_left

lemma lintegral_rearrangement_eq_and {ε} [TopologicalSpace ε] [ContinuousENorm ε] [NoAtoms' μ] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ = ⨆ (E : Set α) (_ : NullMeasurableSet E μ ∧ μ E ≤ t), ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
  rw [lintegral_rearrangement_eq hf]
  congr with E
  rw [iSup_and']

lemma Antitone.lintegral_withDensity_le {f d : ℝ≥0∞ → ℝ≥0∞} (hf : Antitone f)
  (hf' : AEMeasurable f) (hd : d ≤ 1) (hd' : AEMeasurable d) :
    ∫⁻ t, f t ∂volume.withDensity d ≤ ∫⁻ t in Set.Iio (∫⁻ t, d t), f t := by
  set T := ∫⁻ t, d t with T_def
  by_cases d_int : T = ⊤
  · rw [d_int, lintegral_withDensity_eq_lintegral_mul₀' hd' (by fun_prop)]
    simp only [Pi.mul_apply]
    calc _
      _ = ∫⁻ t in Set.univ, d t * f t := by simp
      _ = (∫⁻ t in Set.Iio ⊤, d t * f t) + ∫⁻ t in {⊤}, d t * f t := by
        rw [← lintegral_union (measurableSet_singleton _) (by simp)]
        simp
      _ ≤ ∫⁻ (t : ℝ≥0∞) in Set.Iio ⊤, f t := by
        simp only [Measure.restrict_singleton, measure_singleton, zero_smul, lintegral_zero_measure,
          add_zero]
        apply setLIntegral_mono' measurableSet_Iio
        intro x _
        nth_rw 2 [← one_mul (f x)]
        gcongr
        exact hd x
  have d_int' : ∫⁻ (s : ℝ≥0∞) in Set.Iio T, d s ≠ ⊤ := by
    rw [← ne_eq] at d_int
    rw [← lt_top_iff_ne_top] at *
    apply d_int.trans_le'
    nth_rw 2 [T_def]
    apply setLIntegral_le_lintegral
  by_cases f_int : ∫⁻ (s : ℝ≥0∞) in Set.Iio T, f s = ⊤
  · rw [f_int]
    simp
  have f_int' : ∫⁻ (s : ℝ≥0∞) in Set.Iio T, (1 - d s) * f s ≠ ⊤ := by
    rw [← ne_eq] at f_int
    rw [← lt_top_iff_ne_top] at *
    apply f_int.trans_le'
    apply setLIntegral_mono' measurableSet_Iio
    intro x hx
    nth_rw 2 [← one_mul (f x)]
    gcongr
    simp
  calc _
    _ = ∫⁻ t in Set.Iio T, f t ∂volume.withDensity d + ∫⁻ t in Set.Ici T, f t ∂volume.withDensity d := by
      rw [← lintegral_union measurableSet_Ici (Set.Iio_disjoint_Ici le_rfl)]
      simp
    _ = ((∫⁻ t in Set.Iio T, f t) - ∫⁻ t in Set.Iio T, (1 - d t) * f t)
        + ∫⁻ t in Set.Ici T, f t ∂volume.withDensity d := by
      congr 1
      rw [setLIntegral_withDensity_eq_lintegral_mul₀' hd' (by fun_prop) measurableSet_Iio]
      simp only [Pi.mul_apply]
      calc _
        _ = ∫⁻ t in Set.Iio T, (1 - (1 - d t)) * f t := by
          congr with s
          congr
          symm
          apply ENNReal.sub_sub_cancel ENNReal.one_ne_top (hd s)
        _ = (∫⁻ t in Set.Iio T, f t) - ∫⁻ t in Set.Iio T, (1 - d t) * f t := by
          rw [← lintegral_sub' (by fun_prop) f_int']
          · apply setLIntegral_congr_fun_ae measurableSet_Iio
            have : ∀ᵐ (s : ℝ≥0∞), s ≠ 0 := Measure.ae_ne volume 0
            filter_upwards [this] with t t_ne_zero ht
            rw [ENNReal.sub_mul, one_mul]
            intros
            contrapose! f_int
            rw [eq_top_iff]
            calc ⊤
              _ = ∫⁻ (s : ℝ≥0∞) in Set.Iio t, ⊤ := by
                simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
                  Set.univ_inter]
                rw [ENNReal.volume_Iio, ENNReal.top_mul t_ne_zero]
              _ = ∫⁻ (s : ℝ≥0∞) in Set.Iio t, f s := by
                apply setLIntegral_congr_fun measurableSet_Iio
                intro s hs
                simp only
                symm
                rw [eq_top_iff, ← f_int]
                apply hf hs.le
              _ ≤ ∫⁻ (s : ℝ≥0∞) in Set.Iio T, f s := by
                gcongr
                exact ht.le
          · filter_upwards []
            intro s
            nth_rw 2 [← one_mul (f s)]
            apply mul_le_mul_left
            simp
    _ ≤ (∫⁻ t in Set.Iio T, f t)
        + ((∫⁻ t in Set.Ici T, f t ∂volume.withDensity d)
            - ∫⁻ t in Set.Iio T, (1 - d t) * f t) := by
      rw [ENNReal.sub_add_eq_add_sub _ f_int']
      · apply add_tsub_le_assoc
      · apply setLIntegral_mono' measurableSet_Iio
        intro x hx
        nth_rw 2 [← one_mul (f x)]
        gcongr
        simp
    _ ≤ (∫⁻ t in Set.Iio T, f t)
        + ((∫⁻ t in Set.Ici T, f T ∂volume.withDensity d)
            - ∫⁻ t in Set.Iio T, (1 - d t) * f T) := by
      gcongr 2
      · apply setLIntegral_mono' measurableSet_Ici
        intro s hs
        exact hf hs
      · apply setLIntegral_mono' measurableSet_Iio
        intro s hs
        gcongr
        exact hf hs.le
    _ = (∫⁻ t in Set.Iio T, f t)
        + ((∫⁻ t in Set.Ici T, 1 ∂volume.withDensity d) * f T
            - ((∫⁻ t in Set.Iio T, 1) - ∫⁻ t in Set.Iio T, d t) * f T) := by
      congr 2
      · rw [← lintegral_mul_const'' _ (by fun_prop), one_mul]
      · rw [lintegral_mul_const'' _ (by fun_prop), lintegral_sub' (by fun_prop) d_int']
        filter_upwards []
        exact hd
    _ = (∫⁻ t in Set.Iio T, f t)
        + ((∫⁻ t in Set.Ici T, d t) * f T
            - (∫⁻ t in Set.Ici T, d t) * f T) := by
      congr 2
      · rw [setLIntegral_withDensity_eq_lintegral_mul₀' hd' (by fun_prop) measurableSet_Ici]
        simp
      · congr
        rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            ENNReal.volume_Iio]
        nth_rw 1 [T_def]
        have : ∫⁻ t, d t = (∫⁻ t in Set.Iio T, d t) + ∫⁻ t in Set.Ici T, d t := by
          rw [← lintegral_union measurableSet_Ici] <;> simp
        rw [this, ENNReal.add_sub_cancel_left d_int']
    _ = ∫⁻ t in Set.Iio T, f t := by
      simp

/-
--Upgrade of Theorem 4.17 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_eq''' {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ =
      ⨆ (d : α → ℝ≥0∞) (_ : ∀ x, d x ≤ 1) (_ : ∫⁻ x, d x ∂μ = t), (∫⁻ x, ‖f x‖ₑ ∂μ.withDensity d) := by
  --TODO: might need to require some measurability of d
  apply le_antisymm
  · sorry --TODO: get this from lintegral_rearrangement_eq by taking product with the unit interval
  · simp only [iSup_le_iff]
    intro d d_le_one d_int
    apply (lintegral_withDensity_le_lintegral_rearrangement_withDensity hf sorry).trans --TODO: assume measurability for d?
    apply (Antitone.lintegral_withDensity_le rearrangement_antitone (by fun_prop) _ (by fun_prop)).trans_eq
    · congr
      rw [← d_int, lintegral_rearrangement sorry] --TODO: assume measurability for d?
      simp
    · intro x
      rw [rearrangement_le_iff_distribution_le]
      simp only [Pi.one_apply]
      unfold distribution
      convert zero_le'
      convert OuterMeasureClass.measure_empty μ
      aesop
-/

--Remark 4.18 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_add_rearrangement_le_add_lintegral {ε}
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [ContinuousAdd ε] {f g : α → ε}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {t : ℝ≥0∞} :
      ∫⁻ (s : ℝ≥0∞) in Set.Iio t, rearrangement (f + g) s μ
        ≤ (∫⁻ (s : ℝ≥0∞) in Set.Iio t, rearrangement f s μ)
          + ∫⁻ (s : ℝ≥0∞) in Set.Iio t, rearrangement g s μ := by
  wlog na : NoAtoms' μ
  · -- This is a nice trick to get rid of the `NoAtoms` assumption
    let ν := @volume unitInterval
    simp_rw [rearrangement_eq_rearrangement_prod (ν := ν) (f := f),
            rearrangement_eq_rearrangement_prod (ν := ν) (f := g),
            rearrangement_eq_rearrangement_prod (ν := ν) (f := f + g)]
    have h : (fun (x : α × unitInterval) ↦ (f + g) x.1)
        = (fun (x : α × unitInterval) ↦ f x.1) + (fun (x : α × unitInterval) ↦ g x.1) := by
      ext x
      simp
    rw [h]
    --TODO: prove something along these lines :
    --https://math.stackexchange.com/questions/3881683/does-mu-x-0-imply-non-atomic-for-radon-measure
    --#check MeasureTheory.Measure.IsAddHaarMeasure.noAtoms
    --#check MeasureTheory.Measure.prod.instNoAtoms_snd
    have na : NoAtoms' (μ.prod ν) := by sorry
    exact this hf.comp_fst hg.comp_fst na
  rw [lintegral_rearrangement_eq_and (hf.add hg), lintegral_rearrangement_eq_and hf, lintegral_rearrangement_eq_and hg]
  calc _
    _ ≤ ⨆ E, ⨆ (_ : NullMeasurableSet E μ ∧ μ E ≤ t), ∫⁻ (x : α) in E, ‖f x‖ₑ + ‖g x‖ₑ ∂μ := by
      gcongr
      apply enorm_add_le
    _ = ⨆ E, ⨆ (_ : NullMeasurableSet E μ ∧ μ E ≤ t), (∫⁻ (x : α) in E, ‖f x‖ₑ ∂μ) + ∫⁻ (x : α) in E, ‖g x‖ₑ ∂μ := by
      congr with E
      congr with hE
      apply lintegral_add_left'
      fun_prop
    _ ≤ (⨆ E, ⨆ (_ : NullMeasurableSet E μ ∧ μ E ≤ t), ∫⁻ (x : α) in E, ‖f x‖ₑ ∂μ)
        + (⨆ E, ⨆ (_ : NullMeasurableSet E μ ∧ μ E ≤ t), ∫⁻ (x : α) in E, ‖g x‖ₑ ∂μ) := by
      apply ENNReal.biSup_add_le_add_biSup

end lintegral

--TODO: do we need these lemmas?
/-
section Filter

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

end Filter
-/

--TODO: do we need a lemma like this?
/-
lemma _root_.ContinuousLinearMap.rearrangement_le {f : α → E₁} {g : α → E₂} :
    rearrangement (fun x ↦ L (f x) (g x)) (‖L‖₊ * x * y) μ ≤
    rearrangement f x μ + rearrangement g y μ := sorry
-/

end rearrangement

end MeasureTheory
