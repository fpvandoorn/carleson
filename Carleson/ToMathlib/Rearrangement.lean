import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.MeasureTheory.Integral.Layercake
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
    exact zero_le _
  · use ⊤
    simp
  · intro x hx
    exact hx.out.trans h

lemma rearrangement_mono_right' : (Antitone (fun t ↦ rearrangement f t μ)) :=
  fun _ _ h ↦ rearrangement_mono_right h

@[gcongr] lemma rearrangement_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    rearrangement f x μ ≤ rearrangement g x μ := by
  apply csInf_le_csInf
  · exact ⟨0, fun σ hσ => zero_le _⟩
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
  csInf_le ⟨0, fun y hy => zero_le _⟩ (by simp)

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

lemma rearrangement_le_iff {f : α → ε} {μ : Measure α} {t : ℝ≥0∞} {y : ℝ≥0∞} :
    rearrangement f t μ ≤ y ↔ distribution f y μ ≤ t := by
  contrapose!
  apply lt_rearrangement_iff

--TODO: is this even true?
lemma distribution'_rearrangement_ge {t : ℝ≥0∞} : t ≤ μ {y | rearrangement f t μ ≤ ‖f y‖ₑ} := by
  --unfold rearrangement
  simp_rw [rearrangement_le_iff]
  unfold distribution
  sorry

lemma distribution_rearrangement {f : α → ε} {μ : Measure α} {t : ℝ≥0∞} :
    distribution f t μ = distribution (rearrangement f · μ) t volume := by
  unfold distribution
  simp only [enorm_eq_self]
  have : {x | t < rearrangement f x μ} = Set.Iio (distribution f t μ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    exact lt_rearrangement_iff
  rw [this, ENNReal.volume_Iio]
  rfl

lemma distribution_indicator_superlevelSet {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} {t : ℝ≥0∞} :
    distribution ((superlevelSet f t).indicator f) x μ
      = min (distribution f t μ) (distribution f x μ) := by
    by_cases h : t ≤ x
    · rw [min_eq_right (distribution_mono_right h)]
      unfold distribution superlevelSet Set.indicator
      congr with y
      split_ifs with h
      · rfl
      · simp only [enorm_zero, not_lt_zero, false_iff, not_lt]
        simp only [Set.mem_setOf_eq, not_lt] at h
        order
    · push_neg at h
      rw [min_eq_left (distribution_mono_right h.le)]
      unfold distribution superlevelSet Set.indicator
      congr with y
      split_ifs with h
      · simp only [Set.mem_setOf_eq] at h
        simp only [h, iff_true]
        order
      · simp only [Set.mem_setOf_eq] at h
        simp [h]

lemma distribution_indicator_superlevelSet_compl {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} (ht : distribution f t μ ≠ ∞) :
    distribution ((superlevelSet f t)ᶜ.indicator f) x μ
      = distribution f x μ - distribution f t μ := by
    by_cases h : t ≤ x
    · rw [tsub_eq_zero_of_le (distribution_mono_right h), ← measure_empty (μ := μ)]
      unfold distribution superlevelSet Set.indicator
      congr 1
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Set.mem_empty_iff_false, iff_false]
      split_ifs with h
      · order
      · simp
    · push_neg at h
      unfold distribution superlevelSet Set.indicator
      rw [← measure_diff _ _ ht]
      rotate_left
      · intro y
        simp only [Set.mem_setOf_eq]
        exact h.trans
      · exact (nullMeasurableSet_superlevelSet hf)
      congr 1
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Set.mem_diff]
      split_ifs with h <;> simp [h]

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
  · rw [lt_rearrangement_iff] at h
    unfold rearrangement
    congr with σ
    simp [h]
  · push_neg at h
    rw [rearrangement_le_iff] at h
    simp [h]

lemma rearrangement_indicator_superlevelSet_compl {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} (ht : distribution f t μ ≠ ∞) :
    rearrangement ((superlevelSet f t)ᶜ.indicator f) x μ
      = rearrangement f (x + distribution f t μ) μ := by
  rw [rearrangement]
  simp_rw [distribution_indicator_superlevelSet_compl hf ht, tsub_le_iff_right]
  rfl

#check MeasurableSet.induction_on_open
#check MeasurableSpace.induction_on_inter
#check Real.borel_eq_generateFrom_Ioi_rat
#check borel_eq_generateFrom_Ioi

lemma measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite {ε} [TopologicalSpace ε]
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
    simp only [Set.mem_Ioi, not_lt_zero, not_false_eq_true, Set.diff_singleton_eq_self,
      enorm_eq_self]
    exact distribution_rearrangement
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
        rw [ENNReal.bot_eq_zero]
        exact distribution_rearrangement
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
          rw [← distribution_zero_eq_measure_support, distribution_rearrangement]
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

lemma measure_enorm_mem_eq_volume_rearrangement_mem' {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {s : Set ℝ≥0∞}
  (hs : MeasurableSet s) (h : ∃ T, (∀ t ∈ s, T < t) ∧ distribution f T μ < ∞) :
    μ {x | ‖f x‖ₑ ∈ s \ {0}} = volume {x | rearrangement f x μ ∈ s \ {0}} := by
  rcases h with ⟨T, hT, hT'⟩
  have hμ : {x | ‖f x‖ₑ ∈ s \ {0}} = {x | ‖(superlevelSet f T).indicator f x‖ₑ ∈ s \ {0}} := by
    ext x
    unfold superlevelSet Set.indicator
    simp only [Set.mem_diff, Set.mem_singleton_iff, enorm_eq_zero, Set.mem_setOf_eq,
      ite_eq_right_iff, Classical.not_imp]
    aesop
  have hvolume : {x | rearrangement f x μ ∈ s \ {0}}
      = {x | (superlevelSet (rearrangement f · μ) T).indicator (rearrangement f · μ) x ∈ s \ {0}} := by
    ext x
    unfold superlevelSet Set.indicator
    aesop
  rw [hμ, hvolume]
  rw [measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite (μ := μ) _ _ hs]
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
      · rw [rearrangement_le_iff]
        convert zero_le'
        unfold distribution superlevelSet Set.indicator
        rw [← measure_empty (μ := μ)]
        congr 1
        ext x
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Set.mem_empty_iff_false,
          iff_false]
        split_ifs
        · assumption
        · simp
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
  (hs : MeasurableSet s) (hs' : ∀ t ∈ s, distribution f t μ < ∞) (inf_not_mem : sInf s ∉ s) :
    μ {x | ‖f x‖ₑ ∈ s \ {0}} = volume {x | rearrangement f x μ ∈ s \ {0}} := by
  /-
  by_cases s_inf : sInf s ∈ s
  · --push_neg at s_inf
    calc _
      _ = μ {x | ‖f x‖ₑ ∈ (s \ {sInf s}) \ {0}} + μ {x | ‖f x‖ₑ = sInf s ∧ ‖f x‖ₑ ≠ 0} := by
        rw [← measure_union₀, ← Set.setOf_or]
        · congr with x
          grind
        · --measurability
          sorry
        · apply Disjoint.aedisjoint
          rw [Set.disjoint_iff]
          intro x hx
          grind
      _ = volume {x | rearrangement f x μ ∈ (s \ {sInf s}) \ {0}} + volume {x | rearrangement f x μ = sInf s ∧ rearrangement f x μ ≠ 0} := by
        congr 1
        · apply measure_enorm_mem_eq_volume_rearrangement_mem' hf (by measurability)
          use sInf s
          simp only [Set.mem_diff, Set.mem_singleton_iff, and_imp, hs' _ s_inf, and_true]
          intro t ht ht'
          apply lt_of_le_of_ne (sInf_le ht)
          symm
          exact ht'
        · by_cases hs : sInf s = 0
          · rw [hs]
            simp
          have {a : ℝ≥0∞} : a = sInf s ∧ a ≠ 0 ↔ a = sInf s := by aesop
          simp_rw [this]
          sorry
      _ = volume {x | rearrangement f x μ ∈ s \ {0}} := by
        sorry
  -/
  by_cases s_nonempty : s = ∅
  · rw [s_nonempty]
    simp
  simp_rw [← Set.nonempty_iff_ne_empty] at s_nonempty
  have s_bddBelow : BddBelow s := by simp
  /-
  by_cases s_inf : sInf s ∈ s
  · have hμ : {x | ‖f x‖ₑ ∈ s \ {0}} = {x | ‖(superlevelSet f (sInf s)).indicator f x‖ₑ ∈ s \ {0}} := by
      ext x
      unfold superlevelSet Set.indicator
      simp only [Set.mem_diff, Set.mem_singleton_iff, enorm_eq_zero, Set.mem_setOf_eq,
        ite_eq_right_iff, Classical.not_imp]
      split_ifs with h
      · aesop
      · simp [h]
        intro h'
        exfalso
        simp at h
  -/
  rcases exists_seq_tendsto_sInf s_nonempty s_bddBelow with ⟨u, antitone_u, tendsto_u, hus⟩
  have hμ : {x | ‖f x‖ₑ ∈ s \ {0}} = ⋃ n, {x | ‖(superlevelSet f (u n)).indicator f x‖ₑ ∈ s \ {0}} := by
    ext x
    unfold superlevelSet Set.indicator
    aesop
    have : ∃ i, u i < ‖f x‖ₑ := by
      refine iInf_lt_iff.mp ?_
      rw [iInf_eq_of_tendsto antitone_u tendsto_u]
      apply lt_of_le_of_ne (sInf_le left)
      grind
    rcases this with ⟨i, hi⟩
    use i
    split_ifs
    use left
  have hvolume : {x | rearrangement f x μ ∈ s \ {0}}
      = ⋃ n, {x | (superlevelSet (rearrangement f · μ) (u n)).indicator (rearrangement f · μ) x ∈ s \ {0}} := by
    ext x
    unfold superlevelSet Set.indicator
    aesop
    have : ∃ i, u i < rearrangement f x μ := by
      refine iInf_lt_iff.mp ?_
      rw [iInf_eq_of_tendsto antitone_u tendsto_u]
      apply lt_of_le_of_ne (sInf_le left)
      grind
    rcases this with ⟨i, hi⟩
    use i
    split_ifs
    use left
  rw [hμ, hvolume, Monotone.measure_iUnion, Monotone.measure_iUnion]
  · congr with i
    rw [measure_enorm_mem_eq_volume_rearrangement_mem_of_support_finite (μ := μ) _ _ hs]
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
    · simp
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
    · simp
    · exact id

/-
--TODO: use some kind of induction on measurable sets?
lemma measure_enorm_mem_eq_volume_rearrangement_mem [TopologicalSpace ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    μ {x | ‖f x‖ₑ ∈ s} = volume {x | ‖rearrangement f x μ‖ₑ ∈ s} := by
  --let C (s : Set α) := sorry
  --apply MeasurableSpace.induction_on_inter
  have : μ {x | ‖f x‖ₑ ∈ s} = volume {x | ‖rearrangement f x μ‖ₑ ∈ s} ∧
         μ {x | ‖f x‖ₑ ∈ sᶜ} = volume {x | ‖rearrangement f x μ‖ₑ ∈ sᶜ} := by
    --induction s hs using MeasurableSpace.induction_on_inter
    sorry --TODO: apply induction to this
  --apply SigmaFinite
  sorry
-/

lemma distribution_comp_rearrangement  {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) (hf' : distribution f 0 μ ≠ ∞) {g : ℝ≥0∞ → ℝ≥0∞} {t : ℝ≥0∞}
  (hg : Measurable g) (g_zero : g 0 = 0) :
    distribution (g ∘ (rearrangement f · μ)) t volume = distribution (fun x ↦ g ‖f x‖ₑ) t μ := by
  unfold distribution
  simp only [enorm_eq_self]
  calc _
    _ = volume {s | rearrangement f s μ ∈ g ⁻¹' Set.Ioi t} := by rfl


--TODO: generalize this
lemma lintegral_comp_rearrangement {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) (hf' : distribution f 0 μ ≠ ∞) {g : ℝ≥0∞ → ℝ≥0∞}
  (hg : Measurable g) (g_zero : g 0 = 0) :
    ∫⁻ x, g ‖f x‖ₑ ∂μ = ∫⁻ t, g (rearrangement f t μ) := by

  rw [lintegral_eq_lintegral_distribution _ (by fun_prop)]
  symm
  rw [lintegral_eq_lintegral_distribution _ (by fun_prop)]
  congr with t
  unfold distribution
  simp only [enorm_eq_self]
  symm
  calc _
    _ = volume {s | rearrangement f s μ ∈ g ⁻¹' Set.Ioi t} :=
      measure_enorm_mem_eq_volume_rearrangement_mem hf (by measurability)

  sorry

/-
lemma measure_rearrangement {f : α → ε} {g : ℝ≥0∞ → ℝ≥0∞} {t : ℝ≥0∞} :
    μ {x | t < g ‖f x‖ₑ} = volume {x | t < g ‖rearrangement f x μ‖ₑ} := by
  sorry
-/

/-
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
lemma lintegral_rearrangement_pow [TopologicalSpace ε] (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
  ∫⁻ t, (rearrangement f t μ) ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := sorry

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
lemma distribution_indicator_le_distribution {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {f : α → ε} {X : Set α} (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ distribution f t μ := by
  apply distribution_mono_left
  filter_upwards
  intro x
  unfold Set.indicator
  split_ifs <;> simp

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_measure [TopologicalSpace ε] [Zero ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    distribution (X.indicator f) t μ ≤ μ X := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma rearrangement_indicator_le [TopologicalSpace ε] [Zero ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} (hX : MeasurableSet X) (t : ℝ≥0∞) (μ : Measure α) :
    rearrangement (X.indicator f) t μ ≤
      Set.indicator (Set.Iio (μ X)) (rearrangement f · μ) t := sorry

-- Lemma 1.1.24 of [Ian Tice]
lemma setLIntegral_enorm_le_lintegral_rearrangement [TopologicalSpace ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {X : Set α} : --(hX : MeasurableSet X)
    ∫⁻ x in X, ‖f x‖ₑ ∂μ ≤
      ∫⁻ t in (Set.Iio (μ X)), rearrangement f t μ := by
  sorry

--Theorem 4.15 in https://doi.org/10.1007/978-3-319-30034-4
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

lemma lintegral_rearrangement_eq' [TopologicalSpace ε] {f : α → ε} {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ = ∫⁻ s, min (distribution f s μ) t := by
  rw [lintegral_eq_lintegral_distribution _ (by fun_prop)]
  congr with s
  unfold distribution
  simp only [enorm_eq_self, measurableSet_Iio, Measure.restrict_apply']
  simp_rw [lt_rearrangement_iff, Set.Iio_def, Set.Iio_inter_Iio]
  rw [ENNReal.volume_Iio]
  rfl

lemma lintegral_rearrangement_eq'' {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio (distribution f t μ), rearrangement f s μ = ∫⁻ x in {y | t < ‖f y‖ₑ}, ‖f x‖ₑ ∂μ := by
  rw [lintegral_rearrangement_eq', setLIntegral_eq hf.enorm (nullMeasurableSet_lt measurable_const.aemeasurable hf.enorm)]
  congr with s
  rw [← distribution_mono_right'.map_max]
  unfold distribution
  congr 1
  ext x
  aesop

/-
lemma lintegral_rearrangement_eq' [TopologicalSpace ε] [NoAtoms μ] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ = ∫⁻ x in {y | rearrangement f t μ < ‖f y‖ₑ}, ‖f x‖ₑ ∂μ := by
  rw [lintegral_eq_lintegral_distribution] --← lintegral_indicator measurableSet_Iio,
  --rw [distribution_rearrangement]
  symm
  rw [lintegral_eq_lintegral_distribution]
  congr with s
  unfold distribution --rearrangement
  simp only [enorm_eq_self, measurableSet_Iio, Measure.restrict_apply']
  simp_rw [lt_rearrangement_iff, Set.Iio_def, Set.Iio_inter_Iio]
  --simp_rw [Set.Ioi_def, Set.Iio_def]
  grind
  rw [rearrangement_lt]
  rw [distribution_restrict]
  unfold distribution
  simp
  sorry
-/


/-
--Upgrade of Theorem 4.17 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_eq'' {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ =
      ⨆ (E : Set α) (_ : μ E ≤ t) (b ∈ Eᶜ), (∫⁻ x in E, ‖f x‖ₑ ∂μ + (t - μ E) * ‖f b‖ₑ) := by
  --simp_rw [setLIntegral_enorm_eq hf]
  apply le_antisymm
  · rw [lintegral_rearrangement_eq']
    apply le_iSup_of_le {y | rearrangement f t μ < ‖f y‖ₑ}
    apply le_iSup_of_le
    apply le_iSup_of_le
    · rw [setLIntegral_enorm_eq hf]
      gcongr with s
      by_cases h : distribution f s μ ≤ t
      · rw [min_eq_left h]
        simp_rw [rearrangement_le_iff]
        unfold distribution
        apply le_of_eq
        congr
        rw [Set.inter_eq_right.mpr]
        rfl
        simp only [Set.setOf_subset_setOf]
        intro x hx
        apply h.trans'
        apply distribution_mono_right hx.le
      · /-
        simp at h
        rw [min_eq_right h.le]
        --simp_rw [rearrangement_le_iff]
        rw [Set.inter_eq_right.mpr]
        exact h.le
        simp only [Set.setOf_subset_setOf]
        intro x hx
        apply hx.le.trans'
        rw [rearrangement_le_iff]
        -/
        simp at h
        rw [min_eq_right h.le]
        rw [Set.inter_eq_left.mpr]
        · unfold rearrangement
          sorry
        simp only [Set.setOf_subset_setOf]
        intro x hx
        rw [rearrangement_le_iff] at hx
        contrapose! hx
        apply h.trans_le
        exact distribution_mono_right hx




      --rw [← lintegral_indicator]
      · sorry
    --rw [iSup_]
    --apply le_iSup
    sorry
  · simp only [iSup_le_iff]
    intro s hs
    /-
    apply (lintegral_enorm_le_lintegral_rearrangement hf).trans
    rw [← lintegral_indicator measurableSet_Iio,
        ← lintegral_indicator measurableSet_Iio]
    gcongr with x
    -/
    sorry
    /-
    unfold Set.indicator
    simp only [Set.mem_Iio]
    split_ifs with h h'
    · rfl
    · exfalso
      apply h'
      rw [← ENNReal.coe_lt_coe]
      exact h.trans_le hs
    · simp
    · rfl
    -/
-/

--Theorem 4.17 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_eq {ε} [TopologicalSpace ε] [ContinuousENorm ε] [NoAtoms μ] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ = ⨆ (E : Set α) (_ : MeasurableSet E) (_ : μ E = t), ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
  --simp_rw [setLIntegral_enorm_eq hf]
  rw [lintegral_rearrangement_eq']
  apply le_antisymm
  · have : ∃ E, MeasurableSet E ∧ {y | rearrangement f t μ < ‖f y‖ₑ} ⊆ E ∧ E ⊆ {y | rearrangement f t μ ≤ ‖f y‖ₑ} ∧ μ E = t := by
      have lb := distribution_rearrangement_le (f := f) (μ := μ) (x := t)
      unfold distribution at lb
      have ub := distribution'_rearrangement_ge (f := f) (μ := μ) (t := t)
      sorry --use: `this` and `NoAtoms`
    rcases this with ⟨E, measE, hE, hE', hμE⟩
    apply le_iSup_of_le E
    apply le_iSup_of_le measE
    apply le_iSup_of_le hμE
    rw [setLIntegral_enorm_eq hf measE.nullMeasurableSet]
    gcongr with s
    by_cases h : distribution f s μ ≤ t
    · rw [min_eq_left h]
      rw [← rearrangement_le_iff] at h
      unfold distribution
      gcongr
      rw [Set.inter_eq_right.mpr]
      apply hE.trans'
      intro x hx
      simp only [Set.mem_setOf_eq] at *
      exact hx.trans_le' h
    · push_neg at h
      rw [min_eq_right h.le]
      rw [← lt_rearrangement_iff] at h
      rw [← hμE]
      gcongr
      rw [Set.inter_eq_left.mpr]
      apply hE'.trans
      intro x hx
      simp only [Set.mem_setOf_eq] at *
      exact h.trans_le hx
  · simp only [iSup_le_iff]
    intro E measE hμE
    rw [setLIntegral_enorm_eq hf measE.nullMeasurableSet]
    gcongr with s
    apply le_min
    · unfold distribution
      gcongr
      exact Set.inter_subset_right
    · rw [← hμE]
      gcongr
      exact Set.inter_subset_left

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


--Upgrade of Theorem 4.17 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_eq''' {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} :
    ∫⁻ s in Set.Iio t, rearrangement f s μ =
      ⨆ (d : α → ℝ≥0∞) (_ : ∀ x, d x ≤ 1) (_ : ∫⁻ x, d x ∂μ = t), (∫⁻ x, ‖f x‖ₑ ∂μ.withDensity d) := by
  --TODO: might need to require some measurability of d
  apply le_antisymm
  · /-
    have : ∃ E, MeasurableSet E ∧ {y | rearrangement f t μ < ‖f y‖ₑ} ⊆ E ∧ E ⊆ {y | rearrangement f t μ ≤ ‖f y‖ₑ} ∧ μ E = t := by
      have lb := distribution_rearrangement_le (f := f) (μ := μ) (x := t)
      unfold distribution at lb
      have ub := distribution'_rearrangement_ge (f := f) (μ := μ) (t := t)
      sorry --use: `this` and `NoAtoms`
    -/
    set d : α → ℝ≥0∞ := fun x ↦ if rearrangement f t μ < ‖f x‖ₑ then 1
                                else if rearrangement f t μ = ‖f x‖ₑ then
                                  (t - distribution f (rearrangement f t μ) μ) / (μ {y | rearrangement f t μ = ‖f y‖ₑ})
                                else 0
    have d_le_one : ∀ (x : α), d x ≤ 1 := by
      sorry
    have d_int : ∫⁻ x, d x ∂μ = t := by
      sorry
    apply le_iSup_of_le d
    apply le_iSup_of_le d_le_one
    apply le_iSup_of_le d_int
    apply le_of_eq
    have : Set.Iio t =
              Set.Iio (distribution f (rearrangement f t μ) μ) ∪
              Set.Ico (distribution f (rearrangement f t μ) μ) t := by
      symm
      apply Set.Iio_union_Ico_eq_Iio
      apply distribution_rearrangement_le
    rw [this, lintegral_union sorry (by grind), lintegral_rearrangement_eq'' hf] --TODO: measurability
    have : ∫⁻ (a : ℝ≥0∞) in Set.Ico (distribution f (rearrangement f t μ) μ) t, rearrangement f a μ
            = (t - distribution f (rearrangement f t μ) μ) / (μ {y | rearrangement f t μ = ‖f y‖ₑ})
                * ∫⁻ x in {y | rearrangement f t μ = ‖f y‖ₑ}, ‖f x‖ₑ ∂μ := by
      calc _
        _ = ∫⁻ (a : ℝ≥0∞) in Set.Ico (distribution f (rearrangement f t μ) μ) t, rearrangement f t μ := by
          apply setLIntegral_congr_fun measurableSet_Ico
          intro s ⟨hs, hs'⟩
          dsimp only
          apply le_antisymm
          · rwa [rearrangement_le_iff]
          · apply rearrangement_mono_right hs'.le
        _ = rearrangement f t μ * (t - distribution f (rearrangement f t μ) μ) := by
          rw [setLIntegral_const]
          congr
          rw [ENNReal.volume_Ico]
        _ = (t - distribution f (rearrangement f t μ) μ) / (μ {y | rearrangement f t μ = ‖f y‖ₑ})
                * ∫⁻ x in {y | rearrangement f t μ = ‖f y‖ₑ}, rearrangement f t μ ∂μ := by
          symm
          rw [setLIntegral_const, mul_comm, mul_assoc]
          congr
          by_cases h : μ {y | rearrangement f t μ = ‖f y‖ₑ} = 0
          · rw [h]
            simp only [zero_mul]
            sorry --TODO: does that work?
          by_cases h' : μ {y | rearrangement f t μ = ‖f y‖ₑ} = ⊤
          · rw [h']
            simp only [ENNReal.div_top, mul_zero]
            sorry --TODO: does that work?
          rw [ENNReal.mul_div_cancel h h']
        _ = (t - distribution f (rearrangement f t μ) μ) / (μ {y | rearrangement f t μ = ‖f y‖ₑ})
                * ∫⁻ x in {y | rearrangement f t μ = ‖f y‖ₑ}, ‖f x‖ₑ ∂μ := by
          congr 1
          apply setLIntegral_congr_fun sorry --TODO: measurability
          intro x hx
          exact hx
    rw [this, ← lintegral_const_mul'' _ hf.enorm.restrict]
    have : ∫⁻ (x : α), ‖f x‖ₑ ∂μ.withDensity d =
        (∫⁻ x in {y | rearrangement f t μ < ‖f y‖ₑ}, ‖f x‖ₑ ∂μ.withDensity d)
        + (∫⁻ x in {y | rearrangement f t μ = ‖f y‖ₑ}, ‖f x‖ₑ ∂μ.withDensity d)
        + (∫⁻ x in {y | rearrangement f t μ > ‖f y‖ₑ}, ‖f x‖ₑ ∂μ.withDensity d) := by
      rw [← lintegral_union sorry, ← lintegral_union sorry] --TODO: measurability
      · congr
        symm
        convert Measure.restrict_univ
        ext x
        simp only [gt_iff_lt, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [← le_iff_lt_or_eq]
        apply le_or_gt
      · rw [Set.disjoint_iff]
        intro x
        simp only [gt_iff_lt, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, imp_false, not_and, not_lt]
        intro hx
        apply le_of_lt_or_eq hx
      · rw [Set.disjoint_iff]
        intro x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, imp_false, not_and]
        intro hx
        exact hx.ne
    rw [this, setLIntegral_withDensity_eq_lintegral_mul₀ sorry sorry sorry,
        setLIntegral_withDensity_eq_lintegral_mul₀ sorry sorry sorry,
        setLIntegral_withDensity_eq_lintegral_mul₀ sorry sorry sorry, ← add_zero (_ + _)] --TODO: measurability
    unfold d
    congr 2
    · apply setLIntegral_congr_fun sorry --TODO: measurability
      intro x hx
      simp only [Pi.mul_apply, ite_mul, one_mul, zero_mul, left_eq_ite_iff, not_lt]
      grind
    · apply setLIntegral_congr_fun sorry --TODO: measurability
      intro x hx
      simp only [Pi.mul_apply, ite_mul, one_mul, zero_mul]
      grind
    · calc _
        _ = ∫⁻ x in {y | rearrangement f t μ > ‖f y‖ₑ}, 0 ∂μ := by simp
      apply setLIntegral_congr_fun sorry --TODO: measurability
      intro x hx
      simp only [Pi.mul_apply, ite_mul, one_mul, zero_mul]
      grind
  · simp only [iSup_le_iff]
    intro d d_le_one d_int
    apply (lintegral_withDensity_le_lintegral_rearrangement_withDensity hf sorry).trans --TODO: assume measurability for d?
    apply (Antitone.lintegral_withDensity_le rearrangement_mono_right' (by fun_prop) _ (by fun_prop)).trans_eq
    · congr
      --TODO: get this from d_int
      sorry
    · intro x
      rw [rearrangement_le_iff]
      simp only [Pi.one_apply]
      unfold distribution
      convert zero_le'
      convert OuterMeasureClass.measure_empty μ
      aesop



--Remark 4.18 in https://doi.org/10.1007/978-3-319-30034-4
lemma lintegral_rearrangement_add_rearrangement_le_add_lintegral {ε}
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [ContinuousAdd ε] [NoAtoms μ] {f g : α → ε}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {t : ℝ≥0∞} :
      ∫⁻ (s : ℝ≥0∞) in Set.Iio t, rearrangement (f + g) s μ
        ≤ (∫⁻ (s : ℝ≥0∞) in Set.Iio t, rearrangement f s μ)
          + ∫⁻ (s : ℝ≥0∞) in Set.Iio t, rearrangement g s μ := by
  /-
  rw [setLIntegral_eq (by fun_prop) measurableSet_Iio,
      setLIntegral_eq (by fun_prop) measurableSet_Iio,
      setLIntegral_eq (by fun_prop) measurableSet_Iio]
  -/
  rw [lintegral_rearrangement_eq (hf.add hg), lintegral_rearrangement_eq hf, lintegral_rearrangement_eq hg]
  calc _
    _ ≤ ⨆ E, ⨆ (_ : MeasurableSet E) (_ : μ E = t), ∫⁻ (x : α) in E, ‖f x‖ₑ + ‖g x‖ₑ ∂μ := by
      gcongr
      apply enorm_add_le
    _ = ⨆ E, ⨆ (_ : MeasurableSet E) (_ : μ E = t), (∫⁻ (x : α) in E, ‖f x‖ₑ ∂μ) + ∫⁻ (x : α) in E, ‖g x‖ₑ ∂μ := by
      congr with E
      congr with hE
      congr with hμE
      apply lintegral_add_left'
      fun_prop
    _ ≤ (⨆ E, ⨆ (_ : MeasurableSet E) (_ : μ E = t), ∫⁻ (x : α) in E, ‖f x‖ₑ ∂μ)
        + (⨆ E, ⨆ (_ : MeasurableSet E) (_ : μ E = t), ∫⁻ (x : α) in E, ‖g x‖ₑ ∂μ) := by
      --exact ENNReal.biSup_add_le_add_biSup
      sorry
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

-/

end rearrangement

end MeasureTheory
