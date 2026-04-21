import Carleson.ToMathlib.BoundedFiniteSupport
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

-- Upstreaming status: all of this should go into mathlib, eventually.
-- Most lemmas have the right form, but proofs can often be golfed.
-- Some enorm lemmas require some mathlib refactoring first, so they can be unified with their
-- analogue in current mathlib. Such refactorings include (1) adding a Weak(Pseudo)EMetricSpace
-- class, (2) generalising all lemmas about enorms and • to this setting.

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ ε₃ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  {t s x y : ℝ≥0∞} {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-- The superlevel set of a function `f`. -/
def superlevelSet (f : α → ε) (t : ℝ≥0∞) : Set α := {x | t < ‖f x‖ₑ}

lemma superlevelSet_antitone : Antitone (superlevelSet f) := by
  intro s t h
  unfold superlevelSet
  intro x hx
  exact lt_of_le_of_lt h hx

lemma superlevelSet_zero_eq_support {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] {f : α → ε} :
    superlevelSet f 0 = f.support := by
  unfold superlevelSet Function.support
  simp

@[measurability]
lemma nullMeasurableSet_superlevelSet {ε} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
  (hf : AEStronglyMeasurable f μ) :
    NullMeasurableSet (superlevelSet f t) μ := by
  unfold superlevelSet
  apply AEStronglyMeasurable.nullMeasurableSet_lt (by fun_prop) hf.enorm.aestronglyMeasurable

@[measurability]
lemma measurableSet_superlevelSet {ε} [TopologicalSpace ε] [ContinuousENorm ε] [MeasurableSpace ε]
  [OpensMeasurableSpace ε] {f : α → ε} (hf : Measurable f) :
    MeasurableSet (superlevelSet f t) := by
  unfold superlevelSet
  measurability

lemma superlevelSet_const {a : ε} :
    superlevelSet (const α a) t = if t < ‖a‖ₑ then univ else ∅ := by
  unfold superlevelSet
  split_ifs with ht <;> simp [ht]

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Todo: rename to something more Mathlib-appropriate. -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

lemma distribution_eq_measure_superlevelSet : distribution f t μ = μ (superlevelSet f t) := by rfl

@[simp]
lemma distibution_top (f : α → ε) (μ : Measure α) : distribution f ∞ μ = 0 := by simp [distribution]

@[gcongr]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : Antitone (fun t ↦ distribution f t μ) :=
  fun _ _ h ↦ distribution_mono_right h

@[congr]
lemma distribution_congr_ae (h : ∀ᵐ x ∂μ, f x = g x) :
    distribution f t μ = distribution g t μ := by
  apply measure_congr
  filter_upwards [h] with y hy
  have : {x | t < ‖f x‖ₑ} y = (t < ‖f y‖ₑ) := rfl
  rw [this, hy]
  rfl

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) :=
  Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  fun_prop

lemma distribution_toReal_le {f : α → ℝ≥0∞} :
    distribution (ENNReal.toReal ∘ f) t μ ≤ distribution f t μ := by
  simp_rw [distribution]
  gcongr with x
  simp [comp_apply, enorm_eq_self]

lemma distribution_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    distribution (ENNReal.toReal ∘ f) t μ = distribution f t μ := by
  refine measure_congr (.set_eq ?_)
  filter_upwards [hf] with x hx
  simp [hx]

lemma distribution_add_le_of_enorm {A : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  unfold distribution
  have h₁ : μ ({x | A * (t + s) < ‖f x‖ₑ} \
      ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
    apply measure_mono_null ?_ h
    intro x
    simpa using fun h₁ h₂ h₃ ↦ lt_of_le_of_lt (by gcongr) h₁
  calc
    μ {x | A * (t + s) < ‖f x‖ₑ}
      ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := measure_mono_ae' h₁
    _ ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := measure_union_le _ _

lemma approx_above_superset (t₀ : ℝ≥0∞) :
    ⋃ n, (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}) n = {x | t₀ < ‖f x‖ₑ} := by
  ext y
  constructor <;> intro h
  · obtain ⟨n, wn⟩ := exists_exists_eq_and.mp h
    calc
      t₀ ≤ t₀ + (↑n)⁻¹ := le_self_add
      _  < ‖f y‖ₑ      := wn
  · have h₁ : Iio (‖f y‖ₑ - t₀) ∈ 𝓝 0 := Iio_mem_nhds (tsub_pos_of_lt h)
    have h₂ := ENNReal.tendsto_inv_nat_nhds_zero h₁
    simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at h₂
    rcases h₂ with ⟨n, wn⟩
    simpa using ⟨n, lt_tsub_iff_left.mp (wn n (Nat.le_refl n))⟩

lemma tendsto_measure_iUnion_distribution (t₀ : ℝ≥0∞) :
    Filter.Tendsto (⇑μ ∘ (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}))
      Filter.atTop (nhds (μ ({x | t₀ < ‖f x‖ₑ}))) := by
  rw [← approx_above_superset]
  refine tendsto_measure_iUnion_atTop fun a b h x h₁ ↦ ?_
  calc
    _ ≤ t₀ + (↑a)⁻¹ := by gcongr
    _ < _ := h₁

-- TODO: better lemma name!
lemma select_neighborhood_distribution (t₀ : ℝ≥0∞) (l : ℝ≥0∞)
    (hu : l < distribution f t₀ μ) :
    ∃ n : ℕ, l < distribution f (t₀ + (↑n)⁻¹) μ := by
  have h := (tendsto_measure_iUnion_distribution t₀) (Ioi_mem_nhds hu)
  simp only [mem_map, mem_atTop_sets, mem_preimage, comp_apply, mem_Ioi] at h
  rcases h with ⟨n, wn⟩
  exact ⟨n, wn n (Nat.le_refl n)⟩

lemma continuousWithinAt_distribution (t₀ : ℝ≥0∞) :
    ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
  rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
  · rw [t₀top]
    apply continuousWithinAt_of_notMem_closure
    simp
  · unfold ContinuousWithinAt
    rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
    -- Case: distribution f t₀ μ = ⊤
    · simp only [db_top, ENNReal.tendsto_nhds_top_iff_nnreal]
      intro b
      have h₀ : ∃ n : ℕ, ↑b < distribution f (t₀ + (↑n)⁻¹) μ :=
        select_neighborhood_distribution _ _ (db_top ▸ coe_lt_top)
      rcases h₀ with ⟨n, wn⟩
      refine eventually_mem_set.mpr (mem_inf_iff_superset.mpr ⟨Iio (t₀ + (↑n)⁻¹), ?_, ?_⟩)
      · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top (ENNReal.inv_ne_zero.mpr (by finiteness)))
      · exact ⟨Ioi t₀, by simp, fun z h₁ ↦ wn.trans_le (distribution_mono_right (le_of_lt h₁.1))⟩
    -- Case: distribution f t₀ μ < ⊤
    · refine (ENNReal.tendsto_nhds db_not_top.ne_top).mpr fun ε ε_gt_0 ↦
        eventually_mem_set.mpr (mem_inf_iff_superset.mpr ?_)
      rcases eq_zero_or_pos (distribution f t₀ μ) with db_zero | db_not_zero
      -- Case: distribution f t₀ μ = 0
      · use Ico 0 (t₀ + 1)
        constructor
        · refine IsOpen.mem_nhds isOpen_Ico_zero ?_
          simp [lt_add_right t₀nottop.ne_top one_ne_zero]
        · use Ioi t₀
          refine ⟨by simp, fun z hz ↦ ?_⟩
          rw [db_zero]
          simp only [zero_le, tsub_eq_zero_of_le, zero_add]
          have h₂ : distribution f z μ ≤ distribution f t₀ μ :=
            distribution_mono_right (le_of_lt hz.2)
          rw [db_zero] at h₂
          change Icc 0 ε (distribution f z μ)
          rw [nonpos_iff_eq_zero.mp h₂]
          exact ⟨zero_le 0, zero_le ε⟩
      -- Case: 0 < distribution f t₀ μ
      · obtain ⟨n, wn⟩ :=
          select_neighborhood_distribution t₀ _
            (ENNReal.sub_lt_self db_not_top.ne_top db_not_zero.ne' ε_gt_0.ne')
        use Iio (t₀ + (↑n)⁻¹)
        constructor
        · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top (ENNReal.inv_ne_zero.mpr (by finiteness)))
        · refine ⟨Ioi t₀, by simp, fun z h ↦ ⟨?_, ?_⟩⟩
          · calc
              distribution f t₀ μ - ε
                ≤ distribution f (t₀ + (↑n)⁻¹) μ := le_of_lt wn
              _ ≤ distribution f z μ             := distribution_mono_right (le_of_lt h.1)
          · calc
              distribution f z μ
                ≤ distribution f t₀ μ := distribution_mono_right (le_of_lt h.2)
              _ ≤ distribution f t₀ μ + ε := le_self_add

-- TODO: investigate generalising this to enorm classes
-- This requires adding enorm versions of NormOneClass and NormMulClass
lemma distribution_pow (ε : Type*) [SeminormedRing ε] [NormOneClass ε] [NormMulClass ε] (f : α → ε)
    (t : ℝ≥0∞) (μ : Measure α) {n : ℕ} (hn : n ≠ 0) :
    distribution (f ^ n) (t ^ n) μ = distribution f t μ := by
  simp_rw [distribution, Pi.pow_apply]
  refine congrArg μ <| ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [mem_setOf_eq, enorm_pow (f x) n] at hx; simpa using lt_of_pow_lt_pow_left' n hx
  · rw [mem_setOf_eq, enorm_pow (f x) n]; exact ENNReal.pow_right_strictMono hn hx


section distribution

variable {ε' : Type*} [ENorm ε'] {f : α → ε} {g : α → ε'}

@[gcongr]
lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    distribution f t μ ≤ distribution g t μ := by
  have h₀ : {x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ} ⊆ {x | ¬‖f x‖ₑ ≤ ‖g x‖ₑ} := fun x ↦ by
    simp_rw [mem_diff, mem_setOf_eq, not_lt, not_le, and_imp]
    intro i₁ i₂; simpa using i₂.trans_lt i₁
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ})
      + μ ({x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ}) := measure_le_inter_add_diff μ _ _
    _ = μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ}) := by rw [measure_mono_null h₀ h, add_zero]
    _ ≤ _ := by apply measure_mono; simp

@[gcongr]
lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h₂ : t ≤ s) :
    distribution f s μ ≤ distribution g t μ :=
  (distribution_mono_left h₁).trans (distribution_mono_right h₂)

lemma distribution_eLpNormEssSup : distribution f (eLpNormEssSup f μ) μ = 0 :=
  meas_essSup_lt

lemma distribution_add_le' {A : ℝ≥0∞} {g₁ g₂ : α → ε}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  apply distribution_add_le_of_enorm
  simp [h]

lemma distribution_add_le {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f g : α → ε} :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ :=
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ}) := by
      refine measure_mono fun x h ↦ ?_
      simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
      contrapose! h
      exact (enorm_add_le _ _).trans (add_le_add h.1 h.2)
    _ ≤ _ := measure_union_le _ _

-- TODO: make this an iff?
lemma distribution_eq_zero_of_ae_zero_enorm {f : α → ε} (h : enorm ∘ f =ᵐ[μ] 0) :
    distribution f t μ = 0 := by
  unfold distribution
  rw [← nonpos_iff_eq_zero]
  calc _
    _ ≤ μ {x | 0 < ‖f x‖ₑ} := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      exact pos_of_gt hx
    _ = μ {x | ‖f x‖ₑ ≠ 0} := by
      congr
      ext x
      apply bot_lt_iff_ne_bot
    _ = 0 := by
      exact ae_iff.mp h

lemma distribution_eq_zero_of_ae_zero {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε}
  (h : f =ᵐ[μ] 0) :
    distribution f t μ = 0 := by
  apply distribution_eq_zero_of_ae_zero_enorm
  filter_upwards [h] with x hx using (by simp [hx])

@[simp] lemma distribution_zero {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] :
    distribution (0 : α → ε) t μ = 0 := by
  apply distribution_eq_zero_of_ae_zero ae_eq_rfl

lemma distribution_zero_eq_measure_support {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} :
    distribution f 0 μ = μ f.support := by
  unfold distribution support
  congr with x
  simp

lemma distribution_indicator_eq {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε}
  {X : Set α} :
    distribution (X.indicator f) x μ = μ (X ∩ superlevelSet f x) := by
  unfold distribution superlevelSet
  congr 1
  ext y
  unfold Set.indicator
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  split_ifs with hy <;> simp [hy]

-- Lemma 1.1.24 of [Ian Tice]
lemma distribution_indicator_le_measure {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {f : α → ε} {X : Set α} :
    distribution (X.indicator f) x μ ≤ μ X := by
  rw [distribution_indicator_eq]
  gcongr
  simp

lemma distribution_indicator_const {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {s : Set α} {a : ε} :
    distribution (s.indicator (Function.const α a)) t μ = (Set.Iio ‖a‖ₑ).indicator (fun _ ↦ μ s) t := by
  rw [distribution_indicator_eq, superlevelSet_const]
  unfold indicator
  simp only [mem_Iio]
  split_ifs with ht <;> simp

lemma distribution_indicator_superlevelSet {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} {t : ℝ≥0∞} :
    distribution ((superlevelSet f t).indicator f) x μ
      = min (distribution f t μ) (distribution f x μ) := by
  rw [distribution_indicator_eq]
  by_cases h : t ≤ x
  · rw [inter_eq_right.mpr (superlevelSet_antitone h), min_eq_right (distribution_mono_right h)]
    rfl
  · push_neg at h
    rw [inter_eq_left.mpr (superlevelSet_antitone h.le), min_eq_left (distribution_mono_right h.le)]
    rfl

lemma distribution_indicator_superlevelSet_compl {ε} [TopologicalSpace ε] [ENormedAddMonoid ε]
  {f : α → ε} (hf : AEStronglyMeasurable f μ) {t : ℝ≥0∞} (ht : distribution f t μ ≠ ∞) :
    distribution ((superlevelSet f t)ᶜ.indicator f) x μ
      = distribution f x μ - distribution f t μ := by
  rw [distribution_indicator_eq]
  by_cases h : t ≤ x
  · rw [tsub_eq_zero_of_le (distribution_mono_right h), ← measure_empty (μ := μ)]
    rw [← Set.diff_eq_compl_inter, Set.diff_eq_empty.mpr (superlevelSet_antitone h)]
  · push_neg at h
    rw [← Set.diff_eq_compl_inter,
      measure_diff (superlevelSet_antitone h.le) (nullMeasurableSet_superlevelSet hf) ht]
    rfl

lemma distribution_eq_zero_iff {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε} :
    distribution f t μ = 0 ↔ eLpNormEssSup f μ ≤ t := by
  rw [distribution, eLpNormEssSup]
  rw [← compl_compl {x | t < ‖f x‖ₑ}, ← mem_ae_iff, compl_def]
  simp only [mem_setOf_eq, not_lt]
  constructor
  · intro h
    apply essSup_le_of_ae_le
    filter_upwards [h]
    simp
  · rw [essSup]
    intro h
    rw [← Filter.Eventually]
    have : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ limsup (fun x ↦ ‖f x‖ₑ) (ae μ) := by
      apply ENNReal.eventually_le_limsup
    filter_upwards [this]
    intro x hx
    exact hx.trans h

lemma support_distribution {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε} :
    (fun t ↦ distribution f t μ).support = Iio (eLpNormEssSup f μ) := by
  ext t
  simp only [mem_support, ne_eq, mem_Iio]
  rw [distribution_eq_zero_iff]
  simp

lemma distribution_add {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f g : α → ε}
  (h : Disjoint (Function.support f) (Function.support g)) (hg : AEStronglyMeasurable g μ) :
    distribution (f + g) t μ = distribution f t μ + distribution g t μ := by
  unfold distribution
  rw [← measure_union₀]
  · congr 1
    ext x
    simp only [Pi.add_apply, mem_setOf_eq, mem_union]
    rcases (@or_not (x ∈ support f)) with hxf | hxf
    · have := disjoint_left.mp h hxf
      simp only [mem_support, ne_eq, not_not] at this
      rw [this]
      simp
    · simp only [mem_support, ne_eq, not_not] at hxf
      rw [hxf]
      simp
  · apply nullMeasurableSet_lt aemeasurable_const hg.enorm
  · apply Disjoint.aedisjoint
    apply disjoint_of_subset _ _ h
    · intro x
      simp only [mem_setOf_eq, mem_support, ne_eq]
      intro h'
      have := LT.lt.ne_bot h'
      rw [ENNReal.bot_eq_zero] at this
      contrapose! this
      rw [this, enorm_zero]
    · intro x
      simp only [mem_setOf_eq, mem_support, ne_eq]
      intro h'
      have := LT.lt.ne_bot h'
      rw [ENNReal.bot_eq_zero] at this
      contrapose! this
      rw [this, enorm_zero]

lemma distribution_const_smul {f : α → ℝ≥0∞}
  {a : ℝ≥0∞} (h : a ≠ 0 ∨ t ≠ 0) (h' : a ≠ ⊤ ∨ t ≠ ⊤) :
    distribution (a • f) t μ = distribution f (t / a) μ := by
  unfold distribution
  congr with x
  simp only [Pi.smul_apply, smul_eq_mul, enorm_eq_self]
  symm
  rw [mul_comm]
  apply ENNReal.div_lt_iff h h'

lemma distribution_indicator_add_of_support_subset {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  (enorm_add : ∀ a b : ε, ‖a + b‖ₑ = ‖a‖ₑ + ‖b‖ₑ) --TODO: new type class for this property?
  {f : α → ε} {c : ε} (hc : ‖c‖ₑ ≠ ⊤) {s : Set α}
  (hfs : Function.support f ⊆ s) :
    distribution (f + s.indicator (Function.const α c)) t μ = if t < ‖c‖ₑ then μ s else distribution f (t - ‖c‖ₑ) μ := by
  unfold distribution
  split_ifs with ht
  · congr 1 with x
    simp only [Pi.add_apply, mem_setOf_eq]
    constructor
    · intro h
      contrapose! h
      have : x ∉ support f := by exact fun a ↦ h (hfs a)
      simp only [mem_support, ne_eq, not_not] at this
      simp [this, h]
    · intro h
      unfold indicator
      rw [enorm_add, add_comm]
      split_ifs
      apply lt_add_of_lt_of_nonneg _ (zero_le _)
      simpa [h]
  · push_neg at ht
    congr 1 with x
    simp only [Pi.add_apply, mem_setOf_eq]
    rw [enorm_add, ENNReal.sub_lt_iff_lt_right hc ht]
    constructor
    · intro h
      apply h.trans_le
      gcongr
      unfold indicator
      split_ifs <;> simp
    · intro h
      apply h.trans_le
      gcongr
      unfold indicator
      split_ifs with hxs
      · simp
      exfalso
      have : x ∉ support f := by exact fun a ↦ hxs (hfs a)
      simp only [mem_support, ne_eq, not_not] at this
      rw [this, enorm_zero, zero_add] at h
      exact (lt_self_iff_false _).mp (h.trans_le ht)

/- ENNReal version of the previous lemma -/
lemma distribution_indicator_add_of_support_subset_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
  {s : Set α} (hfs : Function.support f ⊆ s) :
    distribution (f + s.indicator (Function.const α c)) t μ
      = if t < c then μ s else distribution f (t - c) μ := by
  convert distribution_indicator_add_of_support_subset (by simp) (by simpa) hfs

/- NNReal version of the previous lemma -/
lemma distribution_indicator_add_of_support_subset_nnreal {f : α → ℝ≥0} {c : ℝ≥0}
  {s : Set α} (hfs : Function.support f ⊆ s) :
    distribution (f + s.indicator (Function.const α c)) t μ
      = if t < c then μ s else distribution f (t - c) μ := by
  convert distribution_indicator_add_of_support_subset (by simp) (by simp) hfs

lemma distribution_eq_distribution_prod {ε}
  [ENorm ε] {f : α → ε} {t : ℝ≥0∞}
  {β : Type*} {m' : MeasurableSpace β} {ν : Measure β} [IsProbabilityMeasure ν] :
    distribution f t μ = distribution (fun x : α × β ↦ f x.1) t (μ.prod ν) := by
  unfold distribution
  have : {x : α × β | t < ‖f x.1‖ₑ} = {x | t < ‖f x‖ₑ} ×ˢ Set.univ := by
    ext ⟨x, y⟩
    rw [Set.mem_prod]
    simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]

end distribution

end ENorm

end MeasureTheory
