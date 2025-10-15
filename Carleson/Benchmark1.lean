import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

noncomputable section

open MeasureTheory Measure Set symmDiff Function
open scoped ENNReal NNReal Function

variable {ι : Type*}
section aux_lemmas

@[simp]
lemma Finset.sum_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) :
    ∑ x ∈ s, μ {x} = μ s := by
  sorry
  -- change ∑ x ∈ s, μ (id ⁻¹' {x}) = _
  -- rw [sum_measure_preimage_singleton]
  -- · simp
  -- · simp

@[simp]
lemma Finset.sum_toReal_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
    ∑ x ∈ s, (μ {x}).toReal = (μ s).toReal := by
  sorry
  -- rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  -- simp

-- probably don't need this version but it was stated previously and will need to search for and
-- eliminate any explicit uses
lemma sum_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) :
    ∑ x, μ {x} = μ Set.univ := by
  sorry
  -- simp

-- probably don't need this version but it was stated previously and will need to search for and
-- eliminate any explicit uses
lemma sum_toReal_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
    ∑ x : S, (μ {x}).toReal = (μ Set.univ).toReal := by
  sorry
  -- simp

end aux_lemmas

namespace MeasureTheory

variable {α : Type*} {β : Type*} {_ : MeasurableSpace α} (μ : Measure α)

/-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`. -/
protected def Measure.real (s : Set α) : ℝ := by
  exact (μ s).toReal

theorem measureReal_def (s : Set α) : μ.real s = (μ s).toReal := by
  sorry
  -- rfl

/-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`. -/
protected def Measure.nnreal (s : Set α) : ℝ≥0 := by
  exact (μ s).toNNReal

theorem measureNNReal_def (s : Set α) : μ.nnreal s = (μ s).toNNReal := by
  sorry
  -- rfl

theorem measureNNReal_toReal (s : Set α) : (μ.nnreal s).toReal = μ.real s := by
  sorry
  -- rfl

theorem measureNNReal_val (s : Set α) : (μ.nnreal s).val = μ.real s := by
  sorry
  -- rfl

variable {μ}
variable {s s₁ s₂ t : Set α}

section move_to_MeasureSpace.lean

theorem measure_ne_top_of_subset (h : s ⊆ t) (ht : μ t ≠ ∞) : μ s ≠ ∞ := by
  sorry
  -- exact (measure_lt_top_of_subset h ht).ne

theorem measure_diff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
  sorry
  -- contrapose! hs
  -- exact ((measure_mono (subset_diff_union s t)).trans_lt
  --   ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ := by
  sorry
  -- exact measure_mono_top subset_union_right (measure_diff_eq_top ht hs)

end move_to_MeasureSpace.lean

theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  sorry
  -- rw [Measure.real, ENNReal.toReal_eq_zero_iff]
  -- exact or_iff_left h

@[simp] theorem measureReal_zero (s : Set α) : (0 : Measure α).real s = 0 := by
  sorry
  -- rfl

@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := by
  sorry
  -- exact ENNReal.toReal_nonneg

@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by
  sorry
  -- simp [Measure.real]

@[simp] theorem IsProbabilityMeasure.measureReal_univ [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by
  sorry
  -- simp [Measure.real]

theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ := by
  sorry
  -- exact ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (measure_ne_top μ univ)

theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 := by
  sorry
  -- exact measureReal_univ_pos.ne'

theorem nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty := by
  sorry
  -- exact nonempty_iff_ne_empty.2 fun h' ↦ h <| h'.symm ▸ measureReal_empty

@[simp] theorem measureReal_smul_apply (c : ℝ≥0∞) : (c • μ).real s = c.toReal • μ.real s := by
  sorry
  -- rw [measureReal_def, smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  -- rfl

theorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) := by
  sorry
  -- rw [measureReal_def, map_apply hf hs]
  -- rfl

@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ ≤ μ.real s₂ := by
  sorry
  -- exact ENNReal.toReal_mono h₂ (measure_mono h)

theorem measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ = 0 := by
  sorry
  -- rw [measureReal_eq_zero_iff h'₂] at h₂
  -- simp [Measure.real, measure_mono_null h h₂]

theorem measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
    μ.real s ≤ μ.real (s ∪ t) := by
  sorry
  -- rcases eq_top_or_lt_top (μ s) with hs|hs
  -- · simp [Measure.real, hs]
  -- · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

theorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
    μ.real t ≤ μ.real (s ∪ t) := by
  sorry
  -- rw [union_comm]
  -- exact measureReal_le_measureReal_union_left h

theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
  sorry
  -- rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h|h
  -- · simp only [Measure.real, h, ENNReal.top_toReal]
  --   exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  -- · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne
  --   have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne
  --   simp only [Measure.real, ← ENNReal.toReal_add A B]
  --   exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)

theorem measureReal_biUnion_finset_le (s : Finset β) (f : β → Set α) :
    μ.real (⋃ b ∈ s, f b) ≤ ∑ p ∈ s, μ.real (f p) := by
  sorry
  -- classical
  -- induction' s using Finset.induction_on with x s hx IH
  -- · simp
  -- · simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
  --     Finset.sum_insert]
  --   exact (measureReal_union_le _ _).trans (by gcongr)

theorem measureReal_iUnion_fintype_le [Fintype β] (f : β → Set α) :
    μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p) := by
  sorry
  -- convert measureReal_biUnion_finset_le Finset.univ f
  -- simp

theorem measureReal_iUnion_fintype [Fintype β] {f : β → Set α} (hn : Pairwise (Disjoint on f))
    (h : ∀ i, MeasurableSet (f i)) (h' : ∀ i, μ (f i) ≠ ∞ := by finiteness) :
    μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by
  sorry
  -- rw [measureReal_def, measure_iUnion hn h, tsum_fintype, ENNReal.toReal_sum (fun i _hi ↦ h' i)]
  -- rfl

theorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
    μ.real (s₁ ∪ s₂) = 0 := by
  sorry
  -- exact le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg

@[simp]
theorem measureReal_union_null_iff
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 := by
  sorry
  -- exact ⟨fun h ↦ ⟨measureReal_mono_null subset_union_left h (measure_union_ne_top h₁ h₂),
  --     measureReal_mono_null subset_union_right h (measure_union_ne_top h₁ h₂)⟩,
  --       fun h ↦ measureReal_union_null h.1 h.2⟩

/-- If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`. -/
theorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
  sorry
  -- simp [Measure.real, measure_congr H]

theorem measureReal_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  sorry
  -- simp only [measureReal_def]
  -- rw [← ENNReal.toReal_add, measure_inter_add_diff₀ s ht]
  -- · exact measure_ne_top_of_subset inter_subset_left h
  -- · exact measure_ne_top_of_subset diff_subset h

theorem measureReal_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  sorry
  -- have : μ (s ∪ t) ≠ ∞ :=
  --   ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  -- rw [← measureReal_inter_add_diff₀ (s ∪ t) ht this, Set.union_inter_cancel_right, union_diff_right,
  --   ← measureReal_inter_add_diff₀ s ht h₁]
  -- ac_rfl

theorem measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  sorry
  -- rw [union_comm, inter_comm, measureReal_union_add_inter₀ t hs h₂ h₁, add_comm]

theorem measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  sorry
  -- simp only [Measure.real]
  -- rw [measure_union₀ ht hd, ENNReal.toReal_add h₁ h₂]

theorem measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  sorry
  -- rw [union_comm, measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁, add_comm]

theorem measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] {s : Set α}
    (hs : NullMeasurableSet s μ) :
    μ.real s + μ.real sᶜ = μ.real univ := by
  sorry
  -- rw [← measureReal_union₀' hs aedisjoint_compl_right, union_compl_self]

theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ := by
  sorry
  -- exact measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂

theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ := by
  sorry
  -- exact measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂

theorem measureReal_inter_add_diff (s : Set α) (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  sorry
  -- simp only [Measure.real]
  -- rw [← ENNReal.toReal_add, measure_inter_add_diff _ ht]
  -- · exact measure_ne_top_of_subset inter_subset_left h
  -- · exact measure_ne_top_of_subset diff_subset h

theorem measureReal_diff_add_inter (s : Set α) (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s \ t) + μ.real (s ∩ t) = μ.real s := by
  sorry
  -- exact (add_comm _ _).trans (measureReal_inter_add_diff s ht h)

theorem measureReal_union_add_inter (s : Set α) (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  sorry
  -- exact measureReal_union_add_inter₀ s ht.nullMeasurableSet h₁ h₂

theorem measureReal_union_add_inter' (hs : MeasurableSet s) (t : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  sorry
  -- exact measureReal_union_add_inter₀' hs.nullMeasurableSet t h₁ h₂

lemma measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ t) = μ.real (s \ t) + μ.real (t \ s) := by
  sorry
  -- simp only [Measure.real]
  -- rw [← ENNReal.toReal_add, measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  -- · exact measure_ne_top_of_subset diff_subset h₁
  -- · exact measure_ne_top_of_subset diff_subset h₂

lemma measureReal_symmDiff_le (s t u : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ u) ≤ μ.real (s ∆ t) + μ.real (t ∆ u) := by
  sorry
  -- rcases eq_top_or_lt_top (μ u) with hu|hu
  -- · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.top_toReal]
  --   exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  -- · exact le_trans (measureReal_mono (symmDiff_triangle s t u) (measure_union_ne_top
  --     (measure_symmDiff_ne_top h₁ h₂) (measure_symmDiff_ne_top h₂ hu.ne)))
  --       (measureReal_union_le (s ∆ t) (t ∆ u))

theorem measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = μ.real univ := by
  sorry
  -- exact measureReal_add_measureReal_compl₀ h.nullMeasurableSet

theorem measureReal_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ)
    (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) := by
  sorry
  -- simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]

theorem measureReal_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) := by
  sorry
  -- exact measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb ↦ (hm b hb).nullMeasurableSet) h

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measureReal_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) (h : ∀ a ∈ s, μ (f ⁻¹' {a}) ≠ ∞ := by finiteness) :
    (∑ b ∈ s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' ↑s) := by
  sorry
  -- simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

/-- If `s` is a `Finset`, then the sums of the real measures of the singletons in the set is the
real measure of the set. -/
@[simp] theorem Finset.sum_realMeasure_singleton [MeasurableSingletonClass α] [IsFiniteMeasure μ]
    (s : Finset α) :
    (∑ b ∈ s, μ.real {b}) = μ.real s := by
  sorry
  -- exact Finset.sum_toReal_measure_singleton ..

theorem measureReal_diff_null' (h : μ.real (s₁ ∩ s₂) = 0) (h' : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  sorry
  -- simp only [measureReal_def]
  -- rw [measure_diff_null']
  -- exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h

theorem measureReal_diff_null (h : μ.real s₂ = 0) (h' : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  sorry
  -- rcases eq_top_or_lt_top (μ s₁) with H|H
  -- · simp [measureReal_def, H, measure_diff_eq_top H h']
  -- · exact measureReal_diff_null' (measureReal_mono_null inter_subset_right h h') H.ne

theorem measureReal_add_diff (hs : MeasurableSet s) (t : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real s + μ.real (t \ s) = μ.real (s ∪ t) := by
  sorry
  -- rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
  --   (measure_ne_top_of_subset diff_subset h₂), union_diff_self]

theorem measureReal_diff' (s : Set α) (hm : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s \ t) = μ.real (s ∪ t) - μ.real t := by
  sorry
  -- rw [union_comm, ← measureReal_add_diff hm s h₂ h₁]
  -- ring

theorem measureReal_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ - μ.real s₂ := by
  sorry
  -- rw [measureReal_diff' _ h₂ h₁ (measure_ne_top_of_subset h h₁), union_eq_self_of_subset_right h]

theorem le_measureReal_diff (h : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ - μ.real s₂ ≤ μ.real (s₁ \ s₂) := by
  sorry
  -- simp only [tsub_le_iff_left]
  -- calc
  --   μ.real s₁ ≤ μ.real (s₂ ∪ s₁) := measureReal_le_measureReal_union_right h
  --   _ = μ.real (s₂ ∪ s₁ \ s₂) := congr_arg μ.real union_diff_self.symm
  --   _ ≤ μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

theorem measureReal_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (h : μ.real t < μ.real s + ε) (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) < ε := by
  sorry
  -- rw [measureReal_diff hst hs ht']; linarith

theorem measureReal_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) ≤ ε ↔ μ.real t ≤ μ.real s + ε := by
  sorry
  -- rw [measureReal_diff hst hs ht', tsub_le_iff_left]

theorem measureReal_eq_measureReal_of_null_diff {s t : Set α} (hst : s ⊆ t)
    (h_nulldiff : μ.real (t \ s) = 0) (h : μ (t \ s) ≠ ∞ := by finiteness) :
    μ.real s = μ.real t := by
  sorry
  -- rw [measureReal_eq_zero_iff h] at h_nulldiff
  -- simp [measureReal_def, measure_eq_measure_of_null_diff hst h_nulldiff]

theorem measureReal_eq_measureReal_of_between_null_diff {s₁ s₂ s₃ : Set α}
    (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ ∧ μ.real s₂ = μ.real s₃ := by
  sorry
  -- have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
  --   measure_eq_measure_of_between_null_diff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  -- simp [measureReal_def, A.1, A.2]

theorem measureReal_eq_measureReal_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ := by
  sorry
  -- exact (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').1

theorem measureReal_eq_measureReal_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₂ = μ.real s₃ := by
  sorry
  -- exact (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').2

theorem measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  sorry
  -- rw [compl_eq_univ_diff]
  -- exact measureReal_diff (subset_univ s) h₁

theorem measureReal_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂)
    (hsμ : μ.real s₂ ≤ μ.real s₁) (ht : t₁ ⊆ t₂) (htμ : μ.real t₂ ≤ μ.real t₁)
    (h₁ : μ s₂ ≠ ∞ := by finiteness) (h₂ : μ t₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ t₁) = μ.real (s₂ ∪ t₂) := by
  sorry
  -- simp only [measureReal_def]
  -- rw [measure_union_congr_of_subset hs _ ht]
  -- · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  -- · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ

theorem sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i ∈ s, μ.real (t i)) ≤ μ.real (univ : Set α) := by
  sorry
  -- simp only [measureReal_def]
  -- rw [← ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)]
  -- apply ENNReal.toReal_mono (measure_ne_top _ _)
  -- exact sum_measure_le_measure_univ (fun i mi ↦ (h i mi).nullMeasurableSet) H.aedisjoint

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal
    {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ.real (univ : Set α) < ∑ i ∈ s, μ.real (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  sorry
  -- apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
  --   (fun i mi ↦ (h i mi).nullMeasurableSet)
  -- apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) _).1
  -- · convert H
  --   rw [ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)]
  --   rfl
  -- · exact (ENNReal.sum_lt_top.mpr (fun i hi ↦ measure_lt_top ..)).ne

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measureReal_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  sorry
  -- apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
  -- apply (ENNReal.toReal_lt_toReal hu _).1
  -- · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
  --   exact h
  -- · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset h't hu⟩

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measureReal_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  sorry
  -- rw [add_comm] at h
  -- rw [inter_comm]
  -- exact nonempty_inter_of_measureReal_lt_add μ hs h't h's h hu

theorem measureReal_prod_prod [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
    (s : Set α) (t : Set β) : (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  sorry
  -- simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]

theorem ext_iff_measureReal_singleton {S} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    {μ1 μ2 : Measure S} [IsFiniteMeasure μ1] [IsFiniteMeasure μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  sorry
  -- rw [Measure.ext_iff_singleton]
  -- congr! with x
  -- rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  -- simp [measure_ne_top]

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: applications of `μ.real` are nonnegative. -/
@[positivity MeasureTheory.Measure.real _ _]
def evalMeasureReal : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _ a) b ← whnfR e | throwError "not measureReal"
  let p ← mkAppOptM ``MeasureTheory.measureReal_nonneg #[none, none, a, b]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity


section ENNReal

lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
  sorry
  -- if hfin : s.Finite then
  --   have hfin' : Finite s := hfin
  --   rw [tsum_def]
  --   simp only [ENNReal.summable, ↓reduceDIte]
  --   have hsup: support (fun (_ : s) ↦ (1 : ℝ≥0∞)) = Set.univ := by
  --     ext i
  --     simp only [mem_support, ne_eq, one_ne_zero, not_false_eq_true, mem_univ]
  --   have hsupfin: (Set.univ : Set s).Finite := finite_univ
  --   rw [← hsup] at hsupfin
  --   rw [if_pos hsupfin, hfin.encard_eq_coe_toFinset_card]
  --   simp only [ENat.toENNReal_coe]
  --   rw [Finset.card_eq_sum_ones]
  --   rw [finsum_eq_sum (fun (_ : s) ↦ (1 :ℝ≥0∞)) hsupfin]
  --   simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_inj]
  --   apply Finset.card_bij (fun a _ => a.val)
  --   · intro a
  --     simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
  --       Subtype.coe_prop, imp_self]
  --   · intro a _ a' _ heq
  --     ext
  --     exact heq
  --   · intro a ha
  --     use ⟨a,by
  --       simp only [Finite.mem_toFinset] at ha
  --       exact ha⟩
  --     simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
  --       exists_const]
  -- else
  -- have : Infinite s := infinite_coe_iff.mpr hfin
  -- rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num), Set.encard_eq_top_iff.mpr hfin]
  -- simp only [ENat.toENNReal_top]

lemma ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ℝ≥0∞) :
    ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
  sorry
  -- nth_rw 1 [← one_mul c]
  -- rw [ENNReal.tsum_mul_right,tsum_one_eq']

/-! ## `ENNReal` manipulation lemmas -/

lemma ENNReal.sum_geometric_two_pow_toNNReal {k : ℕ} (hk : k > 0) :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-k * n : ℤ) = (1 / (1 - 1 / 2 ^ k) : ℝ).toNNReal := by
  sorry
  -- conv_lhs =>
  --   enter [1, n]
  --   rw [← rpow_intCast, show (-k * n : ℤ) = (-k * n : ℝ) by simp, rpow_mul, rpow_natCast]
  -- rw [tsum_geometric, show (2 : ℝ≥0∞) = (2 : ℝ).toNNReal by simp,
  --   ← coe_rpow_of_ne_zero (by simp), ← Real.toNNReal_rpow_of_nonneg zero_le_two,
  --   ← coe_one, ← Real.toNNReal_one, ← coe_sub, NNReal.sub_def,
  --   Real.toNNReal_one, NNReal.coe_one, Real.coe_toNNReal', max_eq_left (by positivity),
  --   Real.rpow_neg zero_le_two, Real.rpow_natCast, one_div]
  -- have : ((1 : ℝ) - (2 ^ k)⁻¹).toNNReal ≠ 0 := by
  --   rw [ne_eq, Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add, not_le, inv_lt_one_iff₀]
  --   right; exact one_lt_pow₀ (M₀ := ℝ) _root_.one_lt_two hk.ne'
  -- rw [← coe_inv this, coe_inj, Real.toNNReal_inv, one_div]

lemma ENNReal.sum_geometric_two_pow_neg_one : ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-n : ℤ) = 2 := by
  sorry
  -- conv_lhs => enter [1, n]; rw [← one_mul (n : ℤ), ← neg_mul, ← Nat.cast_one]
  -- rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one]; norm_num

lemma ENNReal.sum_geometric_two_pow_neg_two :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-2 * n : ℤ) = ((4 : ℝ) / 3).toNNReal := by
  sorry
  -- conv_lhs => enter [1, n, 2]; rw [← Nat.cast_two]
  -- rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_two]; norm_num

lemma tsum_geometric_ite_eq_tsum_geometric {k c : ℕ} :
    (∑' (n : ℕ), if k ≤ n then (2 : ℝ≥0∞) ^ (-c * (n - k) : ℤ) else 0) =
    ∑' (n : ℕ), 2 ^ (-c * n : ℤ) := by
  sorry
  -- convert (Injective.tsum_eq (f := fun n ↦ if k ≤ n then (2 : ℝ≥0∞) ^ (-c * (n - k) : ℤ) else 0)
  --   (add_left_injective k) (fun n mn ↦ _)).symm
  -- · simp
  -- · rw [mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at mn
  --   use n - k, Nat.sub_add_cancel mn.1

lemma ENNReal.toReal_zpow (x : ℝ≥0∞) (z : ℤ) : x.toReal ^ z = (x ^ z).toReal := by
  sorry
  -- rw [← rpow_intCast, ← toReal_rpow, Real.rpow_intCast]

end ENNReal

section Indicator
attribute [gcongr] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
end Indicator


namespace MeasureTheory

/-! ## Partitioning an interval -/


lemma lintegral_Ioc_partition {a b : ℕ} {c : ℝ} {f : ℝ → ℝ≥0∞} (hc : 0 ≤ c) :
    ∫⁻ t in Ioc (a * c) (b * c), f t =
    ∑ l ∈ Finset.Ico a b, ∫⁻ t in Ioc (l * c) ((l + 1 : ℕ) * c), f t := by
  sorry
  -- rcases lt_or_le b a with h | h
  -- · rw [Finset.Ico_eq_empty (by omega), Ioc_eq_empty (by rw [not_lt]; gcongr),
  --     setLIntegral_empty, Finset.sum_empty]
  -- induction b, h using Nat.le_induction with
  -- | base =>
  --   rw [Finset.Ico_self, Ioc_self, setLIntegral_empty, Finset.sum_empty]
  -- | succ b h ih =>
  --   have li : a * c ≤ b * c := by gcongr
  --   rw [← Ioc_union_Ioc_eq_Ioc li (by gcongr; omega),
  --     lintegral_union measurableSet_Ioc Ioc_disjoint_Ioc_same,
  --     Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert Finset.right_not_mem_Ico,
  --     add_comm (lintegral ..), ih]

/-! ## Averaging -/

-- Named for consistency with `lintegral_add_left'`
-- Maybe add laverage/laverage theorems for all the other lintegral_add statements?
lemma laverage_add_left {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {f g : α → ENNReal} (hf : AEMeasurable f μ) :
    ⨍⁻ x, (f x + g x) ∂μ = ⨍⁻ x, f x ∂μ + ⨍⁻ x, g x ∂μ := by
  sorry
  -- simp_rw [laverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf]

-- Named for consistency with `lintegral_mono'`
lemma laverage_mono {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {f g : α → ENNReal} (h : ∀ x, f x ≤ g x) :
    ⨍⁻ x, f x ∂μ ≤ ⨍⁻ x, g x ∂μ := by
  sorry
  -- simp_rw [laverage_eq]
  -- exact ENNReal.div_le_div_right (lintegral_mono h) (μ univ)

lemma laverage_const_mul {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {f : α → ENNReal} {c : ENNReal} (hc : c ≠ ⊤) :
    c * ⨍⁻ x, f x ∂μ = ⨍⁻ x, c * f x ∂μ := by
  sorry
  -- simp_rw [laverage_eq, ← mul_div_assoc c, lintegral_const_mul' c f hc]

-- The following two lemmas are unused

-- Named for consistency with `lintegral_add_left'`
-- Maybe add laverage/setLaverage theorems for all the other lintegral_add statements?
lemma setLaverage_add_left' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {s : Set α} {f g : α → ENNReal} (hf : AEMeasurable f μ) :
    ⨍⁻ x in s, (f x + g x) ∂μ = ⨍⁻ x in s, f x ∂μ + ⨍⁻ x in s, g x ∂μ := by
  sorry
  -- simp_rw [setLaverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]

-- Named for consistency with `setLintegral_mono'`
lemma setLaverage_mono' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f g : α → ENNReal} (h : ∀ x ∈ s, f x ≤ g x) :
    ⨍⁻ x in s, f x ∂μ ≤ ⨍⁻ x in s, g x ∂μ := by
  sorry
  -- simp_rw [setLaverage_eq]
  -- exact ENNReal.div_le_div_right (setLIntegral_mono' hs h) (μ s)

end MeasureTheory

namespace MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
  {F : Type*} [NormedAddCommGroup F]

attribute [fun_prop] Continuous.comp_aestronglyMeasurable
  AEStronglyMeasurable.mul AEStronglyMeasurable.prod_mk
attribute [gcongr] Measure.AbsolutelyContinuous.prod -- todo: also add one-sided versions for gcongr

theorem AEStronglyMeasurable.ennreal_toReal {u : α → ℝ≥0∞} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x ↦ (u x).toReal) μ := by
  sorry
  -- refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  -- exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable

lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ := by
  sorry
  -- exact lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]
lemma setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ := by
  sorry
  -- exact laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self

lemma setLaverage_const_le {c : ℝ≥0∞} : ⨍⁻ _x in s, c ∂μ ≤ c := by
  sorry
  -- simp_rw [setLaverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
  --   univ_inter, div_eq_mul_inv, mul_assoc]
  -- conv_rhs => rw [← mul_one c]
  -- gcongr
  -- exact ENNReal.mul_inv_le_one (μ s)

theorem eLpNormEssSup_lt_top_of_ae_ennnorm_bound {f : α → F} {C : ℝ≥0∞}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : eLpNormEssSup f μ ≤ C := by
  sorry
  -- exact essSup_le_of_ae_le C hfC

@[simp]
lemma ENNReal.nnorm_toReal {x : ℝ≥0∞} : ‖x.toReal‖₊ = x.toNNReal := by
  sorry
  -- ext; simp [ENNReal.toReal]

theorem restrict_absolutelyContinuous : μ.restrict s ≪ μ := by
  sorry
  -- exact fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| zero_le _

end MeasureTheory

section

open MeasureTheory Bornology
variable {E X : Type*} {p : ℝ≥0∞} [NormedAddCommGroup E] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E}

---- now obsolete -> `BoundedCompactSupport.memℒp`
-- lemma _root_.HasCompactSupport.memℒp_of_isBounded (hf : HasCompactSupport f)
--     (h2f : IsBounded (range f))
--     (h3f : AEStronglyMeasurable f μ) {p : ℝ≥0∞} : Memℒp f p μ := by
--   obtain ⟨C, hC⟩ := h2f.exists_norm_le
--   simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
--   exact hf.memℒp_of_bound h3f C <| .of_forall hC

end

/-! ## `EquivalenceOn` -/

/-- An equivalence relation on the set `s`. -/
structure EquivalenceOn {α : Type*} (r : α → α → Prop) (s : Set α) : Prop where
  /-- An equivalence relation is reflexive: `x ~ x` -/
  refl  : ∀ x ∈ s, r x x
  /-- An equivalence relation is symmetric: `x ~ y` implies `y ~ x` -/
  symm  : ∀ {x y}, x ∈ s → y ∈ s → r x y → r y x
  /-- An equivalence relation is transitive: `x ~ y` and `y ~ z` implies `x ~ z` -/
  trans : ∀ {x y z}, x ∈ s → y ∈ s → z ∈ s → r x y → r y z → r x z

namespace EquivalenceOn

variable {α : Type*} {r : α → α → Prop} {s : Set α} {hr : EquivalenceOn r s} {x y : α}

variable (hr) in
/-- The setoid defined from an equivalence relation on a set. -/
protected def setoid : Setoid s where
  r x y := r x y
  iseqv := {
    refl := fun x ↦ hr.refl x x.2
    symm := fun {x y} ↦ hr.symm x.2 y.2
    trans := fun {x y z} ↦ hr.trans x.2 y.2 z.2
  }

include hr in
lemma exists_rep (x : α) : ∃ y, x ∈ s → y ∈ s ∧ r x y := by
  sorry
  -- exact ⟨x, fun hx ↦ ⟨hx, hr.refl x hx⟩⟩

open Classical in
variable (hr) in
/-- An arbitrary representative of `x` w.r.t. the equivalence relation `r`. -/
protected noncomputable def out (x : α) : α :=
  if hx : x ∈ s then (Quotient.out (s := hr.setoid) ⟦⟨x, hx⟩⟧ : s) else x

lemma out_mem (hx : x ∈ s) : hr.out x ∈ s := by
  sorry
  -- rw [EquivalenceOn.out, dif_pos hx]
  -- apply Subtype.prop

@[simp]
lemma out_mem_iff : hr.out x ∈ s ↔ x ∈ s := by
  sorry
  -- refine ⟨fun h ↦ ?_, out_mem⟩
  -- by_contra hx
  -- rw [EquivalenceOn.out, dif_neg hx] at h
  -- exact hx h

lemma out_rel (hx : x ∈ s) : r (hr.out x) x := by
  sorry
  -- rw [EquivalenceOn.out, dif_pos hx]
  -- exact @Quotient.mk_out _ (hr.setoid) ⟨x, hx⟩

lemma rel_out (hx : x ∈ s) : r x (hr.out x) := hr.symm (out_mem hx) hx (out_rel hx)

lemma out_inj (hx : x ∈ s) (hy : y ∈ s) (h : r x y) : hr.out x = hr.out y := by
  sorry
  -- simp_rw [EquivalenceOn.out, dif_pos hx, dif_pos hy]
  -- congr 1
  -- simp_rw [Quotient.out_inj, Quotient.eq]
  -- exact h

lemma out_inj' (hx : x ∈ s) (hy : y ∈ s) (h : r (hr.out x) (hr.out y)) : hr.out x = hr.out y := by
  sorry
  -- apply out_inj hx hy
  -- refine hr.trans hx ?_ hy (rel_out hx) <| hr.trans ?_ ?_ hy h <| out_rel hy
  -- all_goals simpa

variable (hr) in
/-- The set of representatives of an equivalence relation on a set. -/
def reprs : Set α := hr.out '' s

lemma out_mem_reprs (hx : x ∈ s) : hr.out x ∈ hr.reprs := by
  sorry
  -- exact ⟨x, hx, rfl⟩

lemma reprs_subset : hr.reprs ⊆ s := by
  sorry
  -- rintro _ ⟨x, hx, rfl⟩
  -- exact out_mem hx

lemma reprs_inj (hx : x ∈ hr.reprs) (hy : y ∈ hr.reprs) (h : r x y) : x = y := by
  sorry
  -- obtain ⟨x, hx, rfl⟩ := hx
  -- obtain ⟨y, hy, rfl⟩ := hy
  -- exact out_inj' hx hy h

end EquivalenceOn

namespace Set.Finite

lemma biSup_eq {α : Type*} {ι : Type*} [CompleteLinearOrder α] {s : Set ι}
    (hs : s.Finite) (hs' : s.Nonempty) (f : ι → α) :
    ∃ i ∈ s, ⨆ j ∈ s, f j = f i := by
  sorry
  -- simpa [sSup_image, eq_comm] using hs'.image f |>.csSup_mem (hs.image f)

end Set.Finite

lemma Real.self_lt_two_rpow (x : ℝ) : x < 2 ^ x := by
  sorry
  -- rcases lt_or_le x 0 with h | h
  -- · exact h.trans (rpow_pos_of_pos zero_lt_two x)
  -- · calc
  --     _ < (⌊x⌋₊.succ : ℝ) := Nat.lt_succ_floor x
  --     _ ≤ 2 ^ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.lt_pow_self one_lt_two
  --     _ ≤ _ := rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le h)

namespace Set

open ComplexConjugate

lemma indicator_eq_indicator_one_mul {ι M:Type*} [MulZeroOneClass M]
    (s : Set ι) (f : ι → M) (x : ι) : s.indicator f x = s.indicator 1 x * f x := by
  sorry
  -- simp only [indicator]; split_ifs <;> simp

lemma conj_indicator {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (s : Set α) (x : α):
    conj (s.indicator f x) = s.indicator (conj f) x := by
  sorry
  -- simp only [indicator]; split_ifs <;> simp

end Set

section Norm

open Complex

-- for mathlib?
lemma norm_indicator_one_le {α E}
    [SeminormedAddCommGroup E] [One E] [NormOneClass E] {s : Set α} (x : α) :
    ‖s.indicator (1 : α → E) x‖ ≤ 1 := by
  sorry
  -- exact Trans.trans (norm_indicator_le_norm_self 1 x) norm_one

lemma norm_exp_I_mul_ofReal (x : ℝ) : ‖exp (.I * x)‖ = 1 := by
  sorry
  -- rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_I_mul_sub_ofReal (x y: ℝ) : ‖exp (.I * (x - y))‖ = 1 := by
  sorry
  -- rw [mul_comm, ← ofReal_sub, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_I_mul_ofReal_sub_one {x : ℝ} : ‖exp (I * x) - 1‖ = ‖2 * Real.sin (x / 2)‖ := by
  sorry
  -- rw [show ‖2 * Real.sin (x / 2)‖ = ‖2 * sin (x / 2)‖ by norm_cast, two_sin]
  -- nth_rw 2 [← one_mul (_ - _), ← exp_zero]
  -- rw [← neg_add_cancel (x / 2 * I), exp_add, mul_assoc _ _ (_ - _), mul_sub, ← exp_add, ← exp_add,
  --   ← add_mul, ← add_mul]; norm_cast
  -- rw [add_neg_cancel, ofReal_zero, zero_mul, exp_zero, add_halves, ← neg_mul, norm_mul, norm_I,
  --   mul_one, norm_mul, show -(ofReal (x / 2)) = ofReal (-x / 2) by norm_cast; exact neg_div' 2 x,
  --   norm_exp_ofReal_mul_I, one_mul, ← norm_neg, neg_sub, mul_comm]

lemma norm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖exp (I * x) - 1‖ ≤ ‖x‖ := by
  sorry
  -- rw [norm_exp_I_mul_ofReal_sub_one]
  -- calc
  --   _ = 2 * |Real.sin (x / 2)| := by simp
  --   _ ≤ 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
  --   _ = _ := by rw [abs_div, Nat.abs_ofNat, Real.norm_eq_abs]; ring

lemma enorm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖exp (I * x) - 1‖ₑ ≤ ‖x‖ₑ := by
  sorry
  -- iterate 2 rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _)]
  -- exact ENNReal.ofReal_le_ofReal norm_exp_I_mul_ofReal_sub_one_le

end Norm

namespace MeasureTheory

open Metric Bornology
variable {𝕜: Type*}
variable [RCLike 𝕜]

variable {X α: Type*}

namespace HasCompactSupport

variable [Zero α] {f : X → α}

variable [PseudoMetricSpace X] [ProperSpace X]

theorem of_support_subset_closedBall {x : X}
    {r : ℝ} (hf : support f ⊆ closedBall x r) :
    HasCompactSupport f := by
  sorry
  -- exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall ..) hf

theorem of_support_subset_isBounded {s : Set X}
    (hs : IsBounded s) (hf : support f ⊆ s) :
    HasCompactSupport f := by
  sorry
  -- exact IsCompact.closure_of_subset hs.isCompact_closure <| Trans.trans hf subset_closure

end HasCompactSupport

namespace Integrable

variable [MeasureSpace X]

-- must be in mathlib but can't find it
theorem indicator_const {c : ℝ} {s: Set X}
    (hs: MeasurableSet s) (h2s : volume s < ⊤) : Integrable (s.indicator (fun _ ↦ c)) := by
  sorry
  -- exact (integrable_indicator_iff hs).mpr <| integrableOn_const.mpr <| Or.inr h2s

end Integrable

-- Currently unused.
-- The assumption `int_f` can likely be removed, as otherwise the integral is zero.

theorem setIntegral_biUnion_le_sum_setIntegral {X : Type*} {ι : Type*} [MeasurableSpace X]
    {f : X → ℝ} (s : Finset ι) {S : ι → Set X} {μ : Measure X}
    (f_ae_nonneg : ∀ᵐ (x : X) ∂μ.restrict (⋃ i ∈ s, S i), 0 ≤ f x)
    (int_f : IntegrableOn f (⋃ i ∈ s, S i) μ) :
    ∫ x in (⋃ i ∈ s, S i), f x ∂μ ≤ ∑ i ∈ s, ∫ x in S i, f x ∂μ := by
  -- classical
  -- have res_res : ∀ i ∈ s, (μ.restrict (⋃ i ∈ s, S i)).restrict (S i) = μ.restrict (S i) :=
  --   fun i hi ↦ by rw [Measure.restrict_restrict_of_subset]; exact (subset_biUnion_of_mem hi)
  -- -- Show that it suffices to prove the result in the case where the integrand is measurable
  -- set g := AEMeasurable.mk f int_f.aemeasurable with hg
  -- have g_ae_nonneg : ∀ᵐ (x : X) ∂μ.restrict (⋃ i ∈ s, S i), 0 ≤ g x := by
  --   apply f_ae_nonneg.congr ∘ int_f.aemeasurable.ae_eq_mk.mp
  --   exact Filter.Eventually.of_forall (fun _ h ↦ by rw [h])
  -- have int_g : ∀ i ∈ s, Integrable g (μ.restrict (S i)) := by
  --   intro i hi
  --   have := (int_f.congr int_f.aemeasurable.ae_eq_mk).restrict (s := S i)
  --   rwa [res_res i hi] at this
  -- have : ∑ i ∈ s, ∫ (x : X) in S i, f x ∂μ = ∑ i ∈ s, ∫ (x : X) in S i, g x ∂μ := by
  --   refine Finset.sum_congr rfl (fun i hi ↦ integral_congr_ae ?_)
  --   convert int_f.aemeasurable.ae_eq_mk.restrict (s := S i) using 2
  --   rw [Measure.restrict_restrict_of_subset]
  --   exact (subset_biUnion_of_mem hi)
  -- rw [this, integral_congr_ae int_f.aemeasurable.ae_eq_mk]
  -- -- Now prove the result for the measurable integrand `g`
  -- have meas : MeasurableSet {x | 0 ≤ g x} :=
  --   have : {x | 0 ≤ g x} = g ⁻¹' (Ici 0) := by simp [preimage, mem_Ici]
  --   this ▸ (AEMeasurable.measurable_mk int_f.aemeasurable) measurableSet_Ici
  -- rw [← integral_finset_sum_measure int_g]
  -- set μ₀ : ι → Measure X := fun i ↦ ite (i ∈ s) (μ.restrict (S i)) 0
  -- refine integral_mono_measure ?_ ?_ (integrable_finset_sum_measure.mpr int_g)
  -- · refine Measure.le_iff.mpr (fun T hT ↦ ?_)
  --   simp_rw [μ.restrict_apply hT, Measure.coe_finset_sum, s.sum_apply, inter_iUnion]
  --   apply le_trans <| measure_biUnion_finset_le s (T ∩ S ·)
  --   exact s.sum_le_sum (fun _ _ ↦ ge_of_eq (μ.restrict_apply hT))
  -- · have : ∑ i ∈ s, μ.restrict (S i) = Measure.sum μ₀ := by
  --     ext T hT
  --     simp only [Measure.sum_apply (hs := hT), Measure.coe_finset_sum, s.sum_apply, μ₀]
  --     rw [tsum_eq_sum (s := s) (fun b hb ↦ by simp [hb])]
  --     exact Finset.sum_congr rfl (fun i hi ↦ by simp [hi, res_res])
  --   rw [Filter.EventuallyLE, this, Measure.ae_sum_iff' (by exact meas)]
  --   intro i
  --   by_cases hi : i ∈ s
  --   · simp only [Pi.zero_apply, hi, reduceIte, μ₀, ← res_res i hi, ae_restrict_iff meas, ← hg]
  --     exact g_ae_nonneg.mono (fun _ h _ ↦ h)
  --   · simp [hi, μ₀]

-- Analogous to `MeasureTheory.integral_smul_const` in Mathlib
theorem average_smul_const {X : Type*} {E : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*}
    [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E] (f : X → 𝕜) (c : E) :
    ⨍ (x : X), f x • c ∂μ = (⨍ (x : X), f x ∂μ) • c := by
  sorry
  -- exact integral_smul_const f c

end MeasureTheory

namespace ENNReal

theorem lintegral_Lp_smul {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : p > 0) (c : NNReal) :
    (∫⁻ x : α, (c • f) x ^ p ∂μ) ^ (1 / p) = c • (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) := by
  sorry
  -- simp_rw [smul_def, Pi.smul_apply, smul_eq_mul, mul_rpow_of_nonneg _ _ hp.le,
  --   MeasureTheory.lintegral_const_mul'' _ (hf.pow_const p),
  --   mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le), ← rpow_mul, mul_one_div_cancel hp.ne.symm,
  --   rpow_one]

-- Analogous to `ENNReal.ofReal_pow` in Mathlib
-- Currently unused
theorem ofReal_zpow {p : ℝ} (hp : 0 < p) (n : ℤ) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  sorry
  -- rw [ofReal_eq_coe_nnreal hp.le, ← coe_zpow, ← ofReal_coe_nnreal, NNReal.coe_zpow, NNReal.coe_mk]
  -- exact NNReal.coe_ne_zero.mp hp.ne.symm

end ENNReal

section ENorm

open ENNReal NNReal

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

@[simp] lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by
  sorry
  -- simp [← ofReal_norm, ofReal_toReal_le]

@[simp] lemma enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
  sorry
  -- simp [hx, ← ofReal_norm_eq_enorm]

/-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`.
Note: do we want to unbundle this (at least separate out `TopologicalSpace E`?)
Note: not sure if this is the "right" class to add to Mathlib. -/
class ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
  continuous_enorm : Continuous enorm
  -- the topology is somehow defined by the enorm.

-- todo: maybe generalize to ENormedMonoid and use `to_additive` if necessary for Mathlib.
/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddMonoid (E : Type*) extends ContinuousENorm E, AddMonoid E where
  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0
  -- enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
  enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommMonoid (E : Type*) extends ENormedAddMonoid E, AddCommMonoid E where

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommSubMonoid (E : Type*) extends ENormedAddCommMonoid E, Sub E where
  sub_add_cancel_of_enorm_le : ∀ ⦃x y : E⦄, ‖y‖ₑ ≤ ‖x‖ₑ → x - y + y = x
  add_right_cancel_of_enorm_lt_top : ∀ ⦃x : E⦄, ‖x‖ₑ < ⊤ → ∀ {y z : E}, y + x = z + x → y = z
  esub_self : ∀ x : E, x - x = 0

/-- An enormed space is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedSpace (E : Type*) extends ENormedAddCommMonoid E, Module ℝ≥0 E where
  enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export ENormedAddMonoid (enorm_eq_zero enorm_add_le)
export ENormedAddCommSubMonoid
  (sub_add_cancel_of_enorm_le add_right_cancel_of_enorm_lt_top esub_self)
export ENormedSpace (enorm_smul)

-- mathlib has these (in the _root_ namespace), in a less general setting
attribute [simp] ENormedAddMonoid.enorm_eq_zero ENormedSpace.enorm_smul

-- mathlib has this (unprimed), for a SeminormedAddGroup E
@[simp] lemma enorm_zero' {ε} [ENormedAddMonoid ε] : ‖(0 : ε)‖ₑ = 0 := by simp

instance : ENormedSpace ℝ≥0∞ where
  enorm := id
  enorm_eq_zero := by simp
  -- enorm_neg := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := continuous_id
  enorm_smul := by simp

instance [SeminormedAddGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm

instance [NormedAddGroup E] : ENormedAddMonoid E where
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  -- enorm_neg := by
  --   simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
  enorm_add_le := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]

instance [NormedAddCommGroup E] : ENormedAddCommMonoid E where
  add_comm := by simp [add_comm]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
  enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory
section ContinuousENorm
variable {α E : Type*} {m : MeasurableSpace α} [ContinuousENorm E] {μ : Measure α}

export ContinuousENorm (continuous_enorm)

@[fun_prop]
protected theorem Continuous.enorm {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) : Continuous (fun x => (‖f x‖ₑ)) := by
  sorry
  -- exact continuous_enorm.comp hf

-- mathlib has this, but only for a NormedAddCommGroup
@[fun_prop]
theorem measurable_enorm [MeasurableSpace E] [OpensMeasurableSpace E] :
    Measurable (fun a : E => (‖a‖ₑ)) := by
  sorry
  -- exact continuous_enorm.measurable

-- mathlib has this, but only for a NormedAddCommGroup
@[fun_prop]
protected theorem AEMeasurable.enorm [MeasurableSpace E] [OpensMeasurableSpace E] {f : α → E}
    (hf : AEMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ := by
  sorry
  -- exact measurable_enorm.comp_aemeasurable hf

-- TODO: generalise the mathlib version (unprimed), then replace by that one
@[fun_prop]
protected theorem AEStronglyMeasurable.enorm' {f : α → E}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ := by
  sorry
  -- exact continuous_enorm.comp_aestronglyMeasurable hf |>.aemeasurable

end ContinuousENorm

lemma esub_zero [ENormedAddCommSubMonoid E] {x : E} : x - 0 = x := by
  sorry
  -- rw [← add_zero (x - 0)]
  -- apply sub_add_cancel_of_enorm_le
  -- simp_rw [enorm_zero', zero_le]

end MeasureTheory

end ENorm

section WeakType


open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

section move


variable {α 𝕜 E : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞}

-- todo: move/rename/and perhaps reformulate in terms of ‖.‖ₑ
lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) : ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ := by
  sorry
  -- exact (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)

lemma ENNNorm_add_le (y z : E) : ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ := by
  sorry
  -- exact (toReal_le_toReal coe_ne_top coe_ne_top).mp (nnnorm_add_le ..)

lemma measure_mono_ae' {A B : Set α} (h : μ (B \ A) = 0) :
    μ B ≤ μ A := by
  sorry
  -- apply measure_mono_ae
  -- change μ {x | ¬ B x ≤ A x} = 0
  -- simp only [le_Prop_eq, Classical.not_imp]
  -- exact h

lemma eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ := by
  sorry
  -- simp_rw [eLpNormEssSup, enorm_eq_self]
  -- apply essSup_mono_ae _
  -- apply Eventually.of_forall
  -- simp [implies_true]

lemma eLpNormEssSup_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ = eLpNormEssSup f μ := by
  sorry
  -- simp_rw [eLpNormEssSup, enorm_eq_self]
  -- apply essSup_congr_ae
  -- filter_upwards [hf] with x hx
  -- simp [hx]

lemma eLpNorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ ≤ eLpNorm' f p μ := by
  sorry
  -- simp_rw [eLpNorm', enorm_eq_self]
  -- gcongr
  -- simp

lemma eLpNorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ = eLpNorm' f p μ := by
  sorry
  -- simp_rw [eLpNorm', enorm_eq_self]
  -- congr 1
  -- apply lintegral_congr_ae
  -- filter_upwards [hf] with x hx
  -- simp [hx]

lemma eLpNorm_toReal_le {f : α → ℝ≥0∞} :
    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ := by
  sorry
  -- simp_rw [eLpNorm]
  -- split_ifs
  -- · rfl
  -- · exact eLpNormEssSup_toReal_le
  -- · exact eLpNorm'_toReal_le toReal_nonneg

lemma eLpNorm_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm (ENNReal.toReal ∘ f) p μ = eLpNorm f p μ := by
  sorry
  -- simp_rw [eLpNorm]
  -- split_ifs
  -- · rfl
  -- · exact eLpNormEssSup_toReal_eq hf
  -- · exact eLpNorm'_toReal_eq hf

end move

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ ε₃ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)
  {t s x y : ℝ≥0∞}
  {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Todo: rename to something more Mathlib-appropriate. -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

@[gcongr]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ := by
  sorry
  -- exact measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : (Antitone (fun t ↦ distribution f t μ)) := by
  sorry
  -- exact fun _ _ h ↦ distribution_mono_right h

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) := by
  sorry
  -- exact Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  sorry
  -- fun_prop

lemma distribution_toReal_le {f : α → ℝ≥0∞} :
    distribution (ENNReal.toReal ∘ f) t μ ≤ distribution f t μ := by
  sorry
  -- simp_rw [distribution]
  -- apply measure_mono
  -- simp_rw [comp_apply, enorm_eq_self, setOf_subset_setOf]
  -- exact fun x hx ↦ hx.trans_le enorm_toReal_le

lemma distribution_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    distribution (ENNReal.toReal ∘ f) t μ = distribution f t μ := by
  sorry
  -- refine measure_congr (.set_eq ?_)
  -- filter_upwards [hf] with x hx
  -- simp [hx]

lemma distribution_add_le_of_enorm {A : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  sorry
  -- unfold distribution
  -- have h₁ : μ ({x | A * (t + s) < ‖f x‖ₑ} \
  --     ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
  -- --   apply measure_mono_null ?_ h
  --   intro x
  --   simp only [mem_diff, mem_setOf_eq, mem_union, not_or, not_lt, mem_compl_iff, not_le, and_imp]
  --   refine fun h₁ h₂ h₃ ↦ lt_of_le_of_lt ?_ h₁
  --   gcongr
  -- calc
  --   μ {x | A * (t + s) < ‖f x‖ₑ}
  --     ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := measure_mono_ae' h₁
  --   _ ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := measure_union_le _ _

lemma approx_above_superset (t₀ : ℝ≥0∞) :
    ⋃ n, (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}) n = {x | t₀ < ‖f x‖ₑ} := by
  sorry
  -- ext y
  -- constructor <;> intro h
  -- · obtain ⟨n, wn⟩ := exists_exists_eq_and.mp h
  --   calc
  --     t₀ ≤ t₀ + (↑n)⁻¹ := le_self_add
  --     _  < ‖f y‖ₑ      := wn
  -- · have h₁ : Iio (‖f y‖ₑ - t₀) ∈ 𝓝 0 := Iio_mem_nhds (tsub_pos_of_lt h)
  --   have h₂ := ENNReal.tendsto_inv_nat_nhds_zero h₁
  --   simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at h₂
  --   rcases h₂ with ⟨n, wn⟩
  --   simp only [mem_iUnion, mem_setOf_eq]
  --   exact ⟨n, lt_tsub_iff_left.mp (wn n (Nat.le_refl n))⟩

lemma tendsto_measure_iUnion_distribution (t₀ : ℝ≥0∞) :
    Filter.Tendsto (⇑μ ∘ (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}))
      Filter.atTop (nhds (μ ({x | t₀ < ‖f x‖ₑ}))) := by
  sorry
  -- rw [← approx_above_superset]
  -- refine tendsto_measure_iUnion_atTop fun a b h x h₁ ↦ ?_
  -- calc
  --   _ ≤ t₀ + (↑a)⁻¹ := by gcongr
  --   _ < _ := h₁

lemma select_neighborhood_distribution (t₀ : ℝ≥0∞) (l : ℝ≥0∞)
    (hu : l < distribution f t₀ μ) :
    ∃ n : ℕ, l < distribution f (t₀ + (↑n)⁻¹) μ := by
  sorry
  -- have h := (tendsto_measure_iUnion_distribution t₀) (Ioi_mem_nhds hu)
  -- simp only [mem_map, mem_atTop_sets, mem_preimage, comp_apply, mem_Ioi] at h
  -- rcases h with ⟨n, wn⟩
  -- exact ⟨n, wn n (Nat.le_refl n)⟩

lemma continuousWithinAt_distribution (t₀ : ℝ≥0∞) :
    ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
  sorry
  -- rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
  -- · rw [t₀top]
  --   apply continuousWithinAt_of_not_mem_closure
  --   simp
  -- · unfold ContinuousWithinAt
  --   rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
  --   -- Case: distribution f t₀ μ = ⊤
  --   · simp only [db_top, ENNReal.tendsto_nhds_top_iff_nnreal]
  --     intro b
  --     have h₀ : ∃ n : ℕ, ↑b < distribution f (t₀ + (↑n)⁻¹) μ :=
  --       select_neighborhood_distribution _ _ (db_top ▸ coe_lt_top)
  --     rcases h₀ with ⟨n, wn⟩
  --     refine eventually_mem_set.mpr (mem_inf_iff_superset.mpr ⟨Iio (t₀ + (↑n)⁻¹), ?_, ?_⟩)
  --     · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top
  --         (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
  --     · exact ⟨Ioi t₀, by simp, fun z h₁ ↦ wn.trans_le (distribution_mono_right (le_of_lt h₁.1))⟩
  --   -- Case: distribution f t₀ μ < ⊤
  --   · refine (ENNReal.tendsto_nhds db_not_top.ne_top).mpr fun ε ε_gt_0 ↦
  --       eventually_mem_set.mpr (mem_inf_iff_superset.mpr ?_)
  --     rcases eq_zero_or_pos (distribution f t₀ μ) with db_zero | db_not_zero
  --     -- Case: distribution f t₀ μ = 0
  --     · use Ico 0 (t₀ + 1)
  --       constructor
  --       · refine IsOpen.mem_nhds isOpen_Ico_zero ?_
  --         simp only [mem_Ico, zero_le, lt_add_right t₀nottop.ne_top one_ne_zero, and_self]
  --       · use Ioi t₀
  --         refine ⟨by simp, fun z hz ↦ ?_⟩
  --         rw [db_zero]
  --         simp only [ge_iff_le, zero_le, tsub_eq_zero_of_le, zero_add]
  --         have h₂ : distribution f z μ ≤ distribution f t₀ μ :=
  --           distribution_mono_right (le_of_lt hz.2)
  --         rw [db_zero] at h₂
  --         change Icc 0 ε (distribution f z μ)
  --         rw [nonpos_iff_eq_zero.mp h₂]
  --         exact ⟨zero_le 0, zero_le ε⟩
  --     -- Case: 0 < distribution f t₀ μ
  --     · obtain ⟨n, wn⟩ :=
  --         select_neighborhood_distribution t₀ _ (ENNReal.sub_lt_self db_not_top.ne_top
  --             (ne_of_lt db_not_zero).symm (ne_of_lt ε_gt_0).symm)
  --       use Iio (t₀ + (↑n)⁻¹)
  --       constructor
  --       · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top
  --           (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
  --       · refine ⟨Ioi t₀, by simp, fun z h ↦ ⟨?_, ?_⟩⟩
  --         · calc
  --             distribution f t₀ μ - ε
  --               ≤ distribution f (t₀ + (↑n)⁻¹) μ := le_of_lt wn
  --             _ ≤ distribution f z μ             := distribution_mono_right (le_of_lt h.1)
  --         · calc
  --             distribution f z μ
  --               ≤ distribution f t₀ μ := distribution_mono_right (le_of_lt h.2)
  --             _ ≤ distribution f t₀ μ + ε := le_self_add

/- The lemmas below are almost already in Mathlib, see
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`. -/

-- /-- The layer-cake theorem, or Cavalieri's principle for functions into `ℝ≥0∞` -/
-- lemma lintegral_norm_pow_eq_measure_lt {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
--     {p : ℝ} (hp : 1 ≤ p) :
--     ∫⁻ x, (f x) ^ p ∂μ =
--     ∫⁻ t in Ioi (0 : ℝ), .ofReal (p * t ^ (p - 1)) * μ { x | ENNReal.ofReal t < f x } := by
--   sorry

/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' (f : α → ε) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

lemma wnorm'_zero (f : α → ε) (μ : Measure α) : wnorm' f 0 μ = ∞ := by
  sorry
  -- simp only [wnorm', GroupWithZero.inv_zero, ENNReal.rpow_zero, mul_one, iSup_eq_top]
  -- refine fun b hb ↦ ⟨b.toNNReal + 1, ?_⟩
  -- rw [ENNReal.coe_add, ENNReal.coe_one, coe_toNNReal hb.ne_top]
  -- exact lt_add_right hb.ne_top one_ne_zero

lemma wnorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    wnorm' (ENNReal.toReal ∘ f) p μ ≤ wnorm' f p μ := by
  sorry
  -- refine iSup_mono fun x ↦ ?_
  -- gcongr
  -- exact distribution_toReal_le

lemma wnorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    wnorm' (ENNReal.toReal ∘ f) p μ = wnorm' f p μ := by
  sorry
  -- simp_rw [wnorm', distribution_toReal_eq hf]

/-- The weak L^p norm of a function. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

lemma wnorm_zero : wnorm f 0 μ = ∞ := by
  sorry
  -- simp [wnorm, wnorm'_zero]

@[simp]
lemma wnorm_top : wnorm f ⊤ μ = eLpNormEssSup f μ := by
  sorry
  -- simp [wnorm]

lemma wnorm_coe {p : ℝ≥0} : wnorm f p μ = wnorm' f p μ := by
  sorry
  -- simp [wnorm]

lemma wnorm_ofReal {p : ℝ} (hp : 0 ≤ p) : wnorm f (.ofReal p) μ = wnorm' f p μ := by
  sorry
  -- simp [wnorm, hp]

lemma wnorm_toReal_le {f : α → ℝ≥0∞} {p : ℝ≥0∞} :
    wnorm (ENNReal.toReal ∘ f) p μ ≤ wnorm f p μ := by
  sorry
  -- induction p
  -- · simp [eLpNormEssSup_toReal_le]
  -- exact wnorm'_toReal_le toReal_nonneg

lemma wnorm_toReal_eq {f : α → ℝ≥0∞} {p : ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    wnorm (ENNReal.toReal ∘ f) p μ = wnorm f p μ := by
  sorry
  -- simp_rw [wnorm, eLpNormEssSup_toReal_eq hf, wnorm'_toReal_eq hf]

end ENorm

section ContinuousENorm

variable [ContinuousENorm ε] [ContinuousENorm ε₁] [ContinuousENorm ε₂] [ContinuousENorm ε₃]
    {f : α → ε} {f₁ : α → ε₁}

lemma wnorm'_le_eLpNorm' (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    wnorm' f p μ ≤ eLpNorm' f p μ := by
  sorry
  -- refine iSup_le (fun t ↦ ?_)
  -- simp_rw [distribution, eLpNorm']
  -- have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  -- have p0' : 0 ≤ 1 / p := (div_pos one_pos p0).le
  -- have set_eq : {x | ofNNReal t < ‖f x‖ₑ} = {x | ofNNReal t ^ p < ‖f x‖ₑ ^ p} := by
  -- --   simp [ENNReal.rpow_lt_rpow_iff p0]
  -- have : ofNNReal t = (ofNNReal t ^ p) ^ (1 / p) := by simp [p0.ne.symm]
  -- nth_rewrite 1 [inv_eq_one_div p, this, ← mul_rpow_of_nonneg _ _ p0', set_eq]
  -- refine rpow_le_rpow ?_ p0'
  -- refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.enorm'.pow_const p) (ofNNReal t ^ p)
  -- gcongr
  -- exact setOf_subset_setOf.mpr (fun _ h ↦ h.le)

lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wnorm f p μ ≤ eLpNorm f p μ := by
  sorry
  -- by_cases h : p = ⊤
  -- · simp [h, wnorm, eLpNorm]
  -- · have p0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne.symm
  --   simpa [h, wnorm, eLpNorm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWℒp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma MemLp.memWℒp (hp : 1 ≤ p) (hf : MemLp f p μ) : MemWℒp f p μ := by
  sorry
  -- exact ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩

lemma MemWℒp_zero : ¬ MemWℒp f 0 μ := by
  sorry
  -- simp [MemWℒp, wnorm_zero]

lemma MemWℒp.aeStronglyMeasurable (hf : MemWℒp f p μ) : AEStronglyMeasurable f μ := by
  sorry
  -- exact hf.1

lemma MemWℒp.wnorm_lt_top (hf : MemWℒp f p μ) : wnorm f p μ < ⊤ :=
  sorry
  -- exact hf.2

lemma MemWℒp.ennreal_toReal {f : α → ℝ≥0∞} (hf : MemWℒp f p μ) :
    MemWℒp (ENNReal.toReal ∘ f) p μ := by
  sorry
  -- exact ⟨hf.aeStronglyMeasurable.ennreal_toReal, wnorm_toReal_le.trans_lt hf.2⟩

/-- If a function `f` is `MemWℒp`, then its norm is almost everywhere finite.-/
theorem MemWℒp.ae_ne_top {f : α → ε} {p : ℝ≥0∞} {μ : Measure α}
    (hf : MemWℒp f p μ) : ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
  sorry
  -- by_cases hp_inf : p = ∞
  -- · rw [hp_inf] at hf
  --   simp_rw [← lt_top_iff_ne_top]
  --   exact ae_lt_of_essSup_lt hf.2
  -- by_cases hp_zero : p = 0
  -- · exact (MemWℒp_zero <| hp_zero ▸ hf).elim
  -- set A := {x | ‖f x‖ₑ = ∞} with hA
  -- unfold MemWℒp wnorm wnorm' at hf
  -- simp only [hp_inf] at hf
  -- rw [Filter.eventually_iff, mem_ae_iff]
  -- simp only [ne_eq, compl_def, mem_setOf_eq, Decidable.not_not, ← hA]
  -- have hp_toReal_zero := toReal_ne_zero.mpr ⟨hp_zero, hp_inf⟩
  -- have h1 (t : ℝ≥0) : μ A ≤ distribution f t μ := by
  --   refine μ.mono ?_
  --   simp_all only [setOf_subset_setOf, coe_lt_top, implies_true, A]
  -- set C := ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹
  -- by_cases hC_zero : C = 0
  -- · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
  --   specialize hC_zero 1
  --   simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_lt, and_false, or_false,
  --     false_or] at hC_zero
  --   exact measure_mono_null (setOf_subset_setOf.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
  -- by_contra h
  -- have h2 : C < ∞ := by aesop
  -- have h3 (t : ℝ≥0) : distribution f t μ ≤ (C / t) ^ p.toReal := by
  --   rw [← rpow_inv_rpow hp_toReal_zero (distribution ..)]
  --   refine rpow_le_rpow ?_ toReal_nonneg
  --   rw [ENNReal.le_div_iff_mul_le (Or.inr hC_zero) (Or.inl coe_ne_top), mul_comm]
  --   exact le_iSup_iff.mpr fun _ a ↦ a t
  -- have h4 (t : ℝ≥0) : μ A ≤ (C / t) ^ p.toReal := (h1 t).trans (h3 t)
  -- have h5 : μ A ≤ μ A / 2 := by
  --   convert h4 (C * (2 / μ A) ^ p.toReal⁻¹).toNNReal
  --   rw [coe_toNNReal ?_]
  --   swap
  --   · refine mul_ne_top h2.ne_top (rpow_ne_top_of_nonneg (inv_nonneg.mpr toReal_nonneg) ?_)
  --     simp [div_eq_top, h]
  --   nth_rw 1 [← mul_one C]
  --   rw [ENNReal.mul_div_mul_left _ _ hC_zero h2.ne_top, div_rpow_of_nonneg _ _ toReal_nonneg,
  --     ENNReal.rpow_inv_rpow hp_toReal_zero, ENNReal.one_rpow, one_div,
  --       ENNReal.inv_div (Or.inr ofNat_ne_top) (Or.inr (NeZero.ne' 2).symm)]
  -- have h6 : μ A = 0 := by
  --   convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top (rpow_ne_top_of_nonneg
  --     toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt h5.not_lt
  --   tauto
  -- exact h h6

/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from L^p to weak-L^q.
`HasWeakType T p p' μ ν c` means that `T` has weak type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasWeakType`. -/
def HasBoundedWeakType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {α α' : Type*}
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-! ### Lemmas about `HasWeakType` -/

lemma HasWeakType.memWℒp (h : HasWeakType T p p' μ ν c) (hf₁ : MemLp f₁ p μ) :
    MemWℒp (T f₁) p' ν := by
  sorry
  -- exact ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasWeakType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasWeakType T p p' μ ν c) :
    HasWeakType (T · · |>.toReal) p p' μ ν c := by
  sorry
  -- exact fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, wnorm_toReal_le.trans (h f hf).2 ⟩

-- unused, probably delete
open Classical in
lemma toReal_ofReal_preimage' {s : Set ℝ≥0∞} : ENNReal.toReal ⁻¹' (ENNReal.ofReal ⁻¹' s) =
    if ∞ ∈ s ↔ 0 ∈ s then s else if 0 ∈ s then s ∪ {∞} else s \ {∞} := by
  sorry
  -- split_ifs <;> ext (_|_) <;> simp_all

-- move
open Classical in
lemma toReal_ofReal_preimage {s : Set ℝ≥0∞} : letI t := ENNReal.toReal ⁻¹' (ENNReal.ofReal ⁻¹' s)
  s = if ∞ ∈ s ↔ 0 ∈ s then t else if 0 ∈ s then t \ {∞} else t ∪ {∞} := by
  sorry
  -- split_ifs <;> ext (_|_) <;> simp_all

-- move
lemma aestronglyMeasurable_ennreal_toReal_iff {f : α → ℝ≥0∞}
    (hf : NullMeasurableSet (f ⁻¹' {∞}) μ) :
    AEStronglyMeasurable (ENNReal.toReal ∘ f) μ ↔ AEStronglyMeasurable f μ := by
  sorry
  -- refine ⟨fun h ↦ AEMeasurable.aestronglyMeasurable (NullMeasurable.aemeasurable fun s hs ↦ ?_),
  --   fun h ↦ h.ennreal_toReal⟩
  -- have := h.aemeasurable.nullMeasurable (hs.preimage measurable_ofReal)
  -- simp_rw [preimage_comp] at this
  -- rw [toReal_ofReal_preimage (s := s)]
  -- split_ifs
  -- · exact this
  -- · simp_rw [preimage_diff]
  --   exact this.diff hf
  -- · simp_rw [preimage_union]
  --   exact this.union hf

lemma hasWeakType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
    HasWeakType (T · · |>.toReal) p p' μ ν c ↔ HasWeakType T p p' μ ν c := by
  sorry
  -- refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
  -- obtain ⟨h1, h2⟩ := h f hf
  -- refine ⟨?_, by rwa [← wnorm_toReal_eq (hT f hf)]⟩
  -- rwa [← aestronglyMeasurable_ennreal_toReal_iff]
  -- refine .of_null <| measure_zero_iff_ae_nmem.mpr ?_
  -- filter_upwards [hT f hf] with x hx
  -- simp [hx]

/-! ### Lemmas about `HasBoundedWeakType` -/

lemma HasBoundedWeakType.memWℒp [Zero ε₁] (h : HasBoundedWeakType T p p' μ ν c)
    (hf₁ : MemLp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞) :
    MemWℒp (T f₁) p' ν := by
  sorry
  -- exact ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasWeakType.hasBoundedWeakType [Zero ε₁] (h : HasWeakType T p p' μ ν c) :
    HasBoundedWeakType T p p' μ ν c := by
  sorry
  -- exact fun f hf _ _ ↦ h f hf

/-! ### Lemmas about `HasStrongType` -/

lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : MemLp f₁ p μ) :
    MemLp (T f₁) p' ν := by
  sorry
  -- exact ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasStrongType.hasWeakType (hp' : 1 ≤ p')
    (h : HasStrongType T p p' μ ν c) : HasWeakType T p p' μ ν c := by
  sorry
  -- exact fun f hf ↦ ⟨(h f hf).1, wnorm_le_eLpNorm (h f hf).1 hp' |>.trans (h f hf).2⟩

lemma HasStrongType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasStrongType T p p' μ ν c) :
    HasStrongType (T · · |>.toReal) p p' μ ν c := by
  sorry
  -- exact fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, eLpNorm_toReal_le.trans (h f hf).2 ⟩

lemma hasStrongType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
    HasStrongType (T · · |>.toReal) p p' μ ν c ↔ HasStrongType T p p' μ ν c := by
  sorry
  -- refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
  -- obtain ⟨h1, h2⟩ := h f hf
  -- refine ⟨?_, by rwa [← eLpNorm_toReal_eq (hT f hf)]⟩
  -- rwa [← aestronglyMeasurable_ennreal_toReal_iff]
  -- refine .of_null <| measure_zero_iff_ae_nmem.mpr ?_
  -- filter_upwards [hT f hf] with x hx
  -- simp [hx]

/-! ### Lemmas about `HasBoundedStrongType` -/

lemma HasBoundedStrongType.memLp [Zero ε₁] (h : HasBoundedStrongType T p p' μ ν c)
    (hf₁ : MemLp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞) :
    MemLp (T f₁) p' ν := by
  sorry
  -- exact ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasStrongType.hasBoundedStrongType [Zero ε₁] (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c := by
  sorry
  -- exact fun f hf _ _ ↦ h f hf

lemma HasBoundedStrongType.hasBoundedWeakType [Zero ε₁] (hp' : 1 ≤ p')
    (h : HasBoundedStrongType T p p' μ ν c) : HasBoundedWeakType T p p' μ ν c := by
  sorry
  -- exact fun f hf h2f h3f ↦
  --   ⟨(h f hf h2f h3f).1, wnorm_le_eLpNorm (h f hf h2f h3f).1 hp' |>.trans (h f hf h2f h3f).2⟩

end ContinuousENorm

section NormedGroup

-- todo: generalize various results to ENorm.

variable {f g : α → ε}
section
variable [ContinuousENorm ε]

lemma distribution_eq_nnnorm {f : α → E} : distribution f t μ =  μ { x | t < ‖f x‖₊ } := rfl

@[gcongr]
lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    distribution f t μ ≤ distribution g t μ := by
  sorry
  -- have h₀ : {x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ} ⊆ {x | ¬‖f x‖ₑ ≤ ‖g x‖ₑ} := fun x ↦ by
  --   simp_rw [mem_diff, mem_setOf_eq, not_lt, not_le, and_imp]
  --   intro i₁ i₂; simpa using i₂.trans_lt i₁
  -- calc
  --   _ ≤ μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ})
  --     + μ ({x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ}) := measure_le_inter_add_diff μ _ _
  --   _ = μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ}) := by rw [measure_mono_null h₀ h, add_zero]
  --   _ ≤ _ := by apply measure_mono; simp

@[gcongr]
lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h₂ : t ≤ s) :
    distribution f s μ ≤ distribution g t μ := by
  sorry
  -- exact (distribution_mono_left h₁).trans (distribution_mono_right h₂)

lemma distribution_snormEssSup : distribution f (eLpNormEssSup f μ) μ = 0 := by
  sorry
  -- exact meas_essSup_lt -- meas_eLpNormEssSup_lt

lemma distribution_smul_left {f : α → E} {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖₊) μ := by
  sorry
  -- simp_rw [distribution_eq_nnnorm]
  -- have h₀ : ofNNReal ‖c‖₊ ≠ 0 := ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hc)
  -- congr with x
  -- simp only [Pi.smul_apply, mem_setOf_eq]
  -- rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖₊) _ (‖c‖₊) h₀ coe_ne_top,
  --   ENNNorm_absolute_homogeneous _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]

lemma distribution_add_le' {A : ℝ≥0∞} {g₁ g₂ : α → ε}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  sorry
  -- apply distribution_add_le_of_enorm
  -- simp (discharger := positivity) [← ofReal_mul, ← ofReal_add, h]

lemma HasStrongType.const_smul {𝕜 E' α α' : Type*} [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → E')}
    {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (h : HasStrongType T p p' μ ν c)
    [NormedRing 𝕜] [MulActionWithZero 𝕜 E'] [BoundedSMul 𝕜 E'] (k : 𝕜) :
    HasStrongType (k • T) p p' μ ν (‖k‖₊ * c) := by
  sorry
  -- refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le.trans ?_⟩
  -- simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc]
  -- gcongr
  -- exact (h f hf).2

lemma HasStrongType.const_mul {E' α α' : Type*} [NormedRing E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → E')} {p p' : ℝ≥0∞}
    {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (h : HasStrongType T p p' μ ν c) (e : E') :
    HasStrongType (fun f x ↦ e * T f x) p p' μ ν (‖e‖₊ * c) := by
  sorry
  -- exact h.const_smul e

lemma distribution_smul_left' {f : α → E} {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖ₑ) μ := by
  sorry
  -- have h₀ : ‖c‖ₑ ≠ 0 := enorm_ne_zero.mpr hc
  -- unfold distribution
  -- congr with x
  -- simp only [Pi.smul_apply, mem_setOf_eq]
  -- rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖ₑ) _ (‖c‖ₑ) h₀ coe_ne_top,
  --   _root_.enorm_smul _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]

lemma wnorm_const_smul_le' (hp : p ≠ 0) {f : α → E} (k : 𝕜) :
    wnorm (k • f) p μ ≤ ‖k‖ₑ * wnorm f p μ := by
  sorry
  -- by_cases ptop : p = ⊤
  -- · simp only [ptop, wnorm_top]
  --   apply eLpNormEssSup_const_smul_le
  -- simp only [wnorm, ptop, ↓reduceIte, wnorm', iSup_le_iff]
  -- by_cases k_zero : k = 0
  -- · simp only [distribution, k_zero, Pi.smul_apply, zero_smul, enorm_zero, not_lt_zero', setOf_false,
  --     measure_empty, coe_lt_enorm, zero_mul, nonpos_iff_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero,
  --     ENNReal.rpow_eq_zero_iff, inv_pos, true_and, zero_ne_top, inv_neg'', false_and, or_false]
  --   intro _
  --   right
  --   exact toReal_pos hp ptop
  -- simp only [distribution_smul_left' k_zero]
  -- intro t
  -- rw [ENNReal.mul_iSup]
  -- have knorm_ne_zero : ‖k‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr k_zero
  -- have : t * distribution f (t / ‖k‖ₑ) μ ^ p.toReal⁻¹ =
  --     ‖k‖ₑ * ((t / ‖k‖ₑ) * distribution f (t / ‖k‖ₑ) μ ^ p.toReal⁻¹) := by
  --   nth_rewrite 1 [← mul_div_cancel₀ t knorm_ne_zero]
  --   simp only [coe_mul, mul_assoc]
  --   congr
  --   exact coe_div knorm_ne_zero
  -- erw [this]
  -- apply le_iSup_of_le (↑t / ↑‖k‖₊)
  -- apply le_of_eq
  -- congr <;> exact (coe_div knorm_ne_zero).symm

lemma HasWeakType.const_smul {E' α α' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → E')}
    {p p' : ℝ≥0∞} (hp' : p' ≠ 0){μ : Measure α} {ν : Measure α'} {c : ℝ≥0}
    (h : HasWeakType T p p' μ ν c)
    (k : 𝕜) :
    HasWeakType (k • T) p p' μ ν (‖k‖₊ * c) := by
  sorry
  -- intro f hf
  -- refine ⟨aestronglyMeasurable_const.smul (h f hf).1, ?_⟩
  -- calc wnorm ((k • T) f) p' ν
  --   _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le' hp']
  --   _ ≤ ‖k‖ₑ * (c * eLpNorm f p μ) := by
  -- --     gcongr
  --     apply (h f hf).2
  --   _ = (‖k‖ₑ * c) * eLpNorm f p μ := by simp [coe_mul, mul_assoc]

end

lemma distribution_add_le [ENormedAddMonoid ε] :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ := by
  sorry
  -- exact calc
  --   _ ≤ μ ({x | t < ↑‖f x‖ₑ} ∪ {x | s < ↑‖g x‖ₑ}) := by
  --     refine measure_mono fun x h ↦ ?_
  --     simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
  --     contrapose! h
  --     exact (ENormedAddMonoid.enorm_add_le _ _).trans (add_le_add h.1 h.2)
  --   _ ≤ _ := measure_union_le _ _

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖₊ * t * s) μ ≤
    distribution f t μ + distribution g s μ := by
  sorry
  -- -- unfold distribution
  -- have h₀ : {x | ↑‖L‖₊ * t * s < ↑‖(fun x ↦ (L (f x)) (g x)) x‖₊} ⊆
  --     {x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊} := fun z hz ↦ by
  --   simp only [mem_union, mem_setOf_eq, Pi.add_apply] at hz ⊢
  --   contrapose! hz
  --   calc
  --     (‖(L (f z)) (g z)‖₊ : ℝ≥0∞) ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ := by
  --       refine (toNNReal_le_toNNReal coe_ne_top coe_ne_top).mp ?_
  --       simp only [toNNReal_coe, coe_mul, toNNReal_mul]
  --       calc
  --         _ ≤ ↑‖L (f z)‖₊ * ↑‖g z‖₊ := ContinuousLinearMap.le_opNNNorm (L (f z)) (g z)
  --         _ ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ :=
  --           mul_le_mul' (ContinuousLinearMap.le_opNNNorm L (f z)) (by rfl)
  --     _ ≤ _ := mul_le_mul' (mul_le_mul_left' hz.1 ↑‖L‖₊) hz.2
  -- calc
  --   _ ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := measure_mono h₀
  --   _ ≤ _ := measure_union_le _ _

section BorelSpace

variable [ContinuousENorm ε] [MeasurableSpace E] [BorelSpace E]

/-- The layer-cake theorem, or Cavalieri's principle for functions into a normed group. -/
lemma lintegral_norm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ := by
  sorry
  -- have h2p : 0 ≤ p := hp.le
  -- have := lintegral_rpow_eq_lintegral_meas_lt_mul μ (f := fun x ↦ ‖f x‖)
  --   (Eventually.of_forall fun x ↦ norm_nonneg _) hf.norm hp
  -- simp only [← enorm_eq_nnnorm, norm_nonneg, ← ofReal_rpow_of_nonneg, mul_comm (μ _), ne_eq,
  --   ofReal_ne_top, not_false_eq_true, ← lintegral_const_mul', ← mul_assoc,
  --   ← ofReal_norm_eq_enorm, ofReal_mul, distribution, h2p] at this ⊢
  -- convert this using 1
  -- refine setLIntegral_congr_fun measurableSet_Ioi (Eventually.of_forall fun x hx ↦ ?_)
  -- simp_rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hx)]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`. -/
lemma eLpNorm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0} (hp : 0 < p) :
    eLpNorm f p μ ^ (p : ℝ) =
    ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
  sorry
  -- have h2p : 0 < (p : ℝ) := hp
  -- simp_rw [eLpNorm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
  --   inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
  --   ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`, without
    taking powers. -/
lemma eLpNorm_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (.ofReal p) μ =
    (ENNReal.ofReal p  * ∫⁻ t in Ioi (0 : ℝ), distribution f (.ofReal t) μ *
        ENNReal.ofReal (t ^ (p - 1)) ) ^ p⁻¹ := by
  sorry
  -- unfold eLpNorm
  -- split_ifs with sgn_p sz_p
  -- · exact False.elim (not_le_of_lt hp (ofReal_eq_zero.mp sgn_p))
  -- · exact False.elim (coe_ne_top sz_p)
  -- · unfold eLpNorm'
  --   rw [toReal_ofReal (le_of_lt hp), one_div]
  --   congr 1
  --   rw [← lintegral_const_mul']
  --   on_goal 2 => exact coe_ne_top
  --   rw [lintegral_norm_pow_eq_distribution hf hp]
  --   congr 1 with x; rw [ofReal_mul] <;> [ring; positivity]

lemma lintegral_pow_mul_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : -1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * distribution f (.ofReal t) μ =
    ENNReal.ofReal (p + 1)⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ (p + 1) ∂μ := by
  sorry
  -- have h2p : 0 < p + 1 := by linarith
  -- have h3p : 0 ≤ p + 1 := by linarith
  -- have h4p : p + 1 ≠ 0 := by linarith
  -- simp [*, lintegral_norm_pow_eq_distribution, ← lintegral_const_mul', ← ofReal_mul, ← mul_assoc]

end BorelSpace

end NormedGroup

end MeasureTheory

end WeakType






section Extra

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {t : ℝ≥0∞}
lemma distribution_zero {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε} (h : f =ᵐ[μ] 0) :
    distribution f t μ = 0 := by
  sorry
  -- unfold distribution
  -- rw[← le_zero_iff]
  -- calc _
  --   _ ≤ μ {x | 0 < ‖f x‖ₑ} := by
  --     apply measure_mono
  --     intro x hx
  --     simp only [Set.mem_setOf_eq] at hx
  --     exact pos_of_gt hx
  --   _ = μ {x | ‖f x‖ₑ ≠ 0} := by
  --     congr
  --     ext x
  --     simp
  --     sorry
  --   _ = 0 := by
  --     refine ae_iff.mp ?_
  --     filter_upwards [h] with x hx
  --     simpa using hx

end Extra

















section NNReal

noncomputable
instance NNReal.MeasureSpace : MeasureSpace ℝ≥0 := ⟨Measure.Subtype.measureSpace.volume⟩

lemma NNReal.volume_val {s : Set ℝ≥0} : volume s = volume (Subtype.val '' s) := by
  sorry
  -- apply comap_subtype_coe_apply measurableSet_Ici

noncomputable
instance : MeasureSpace ℝ≥0∞ where
  volume := (volume : Measure ℝ≥0).map ENNReal.ofNNReal

--TODO: move these lemmas somewhere else?
lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} (h : ∞ ∉ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  sorry
  -- ext x
  -- simp only [mem_image, mem_preimage]
  -- constructor
  -- · rintro ⟨y, hys, hyx⟩
  --   have : y ≠ ∞ := ne_of_mem_of_not_mem hys h
  --   use y.toNNReal
  --   rw [coe_toNNReal this]
  --   use hys
  --   rwa [coe_toNNReal_eq_toReal]
  -- · rintro ⟨y, hys, hyx⟩
  --   use ENNReal.ofNNReal y, hys, hyx

lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal' {s : Set ℝ≥0∞} (h : ∞ ∈ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) ∪ {0} := by
  sorry
  -- ext x
  -- simp only [mem_image, mem_preimage]
  -- constructor
  -- · rintro ⟨y, hys, hyx⟩
  --   by_cases hy : y = ∞
  --   · rw [← hyx, hy]
  --     simp
  --   left
  --   use y.toNNReal
  --   simp only [mem_preimage]
  --   rw [coe_toNNReal hy]
  --   use hys
  --   rwa [coe_toNNReal_eq_toReal]
  -- · rintro (⟨y, hys, hyx⟩ | hx)
  --   · use ENNReal.ofNNReal y, hys, hyx
  --   · use ∞, h
  --     simp only [toReal_top, hx.symm]

lemma ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} :
    ENNReal.toReal '' s =ᵐ[volume] NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  sorry
  -- by_cases h : ∞ ∈ s
  -- · rw [ENNReal.map_toReal_eq_map_toReal_comap_ofReal' h, union_singleton]
  --   apply insert_ae_eq_self
  -- rw [ENNReal.map_toReal_eq_map_toReal_comap_ofReal h]


lemma ENNReal.volume_val {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.toReal '' s) := by
  sorry
  -- calc volume s
  --   _ = volume (ENNReal.ofNNReal ⁻¹' s) :=
  --     MeasureTheory.Measure.map_apply_of_aemeasurable (by fun_prop) hs
  --   _ = volume (NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s)) := NNReal.volume_val
  --   _ = volume (ENNReal.toReal '' s) := Eq.symm (measure_congr ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal)

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Icc_eq_Icc {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Icc a b = Set.Icc a.toReal b.toReal := by
  sorry
  -- ext x
  -- simp only [mem_image, mem_Icc]
  -- constructor
  -- · rintro ⟨y, hy, hyx⟩
  --   rwa [← hyx,
  --         toReal_le_toReal ha (lt_top_iff_ne_top.mp (hy.2.trans_lt (lt_top_iff_ne_top.mpr hb))),
  --         toReal_le_toReal (lt_top_iff_ne_top.mp (hy.2.trans_lt (lt_top_iff_ne_top.mpr hb))) hb ]
  -- · rintro hx
  --   use ENNReal.ofReal x
  --   constructor
  --   · rwa [le_ofReal_iff_toReal_le ha (le_trans toReal_nonneg hx.1), ofReal_le_iff_le_toReal hb]
  --   · rw [toReal_ofReal_eq_iff]
  --     exact (le_trans toReal_nonneg hx.1)

-- sanity check: this measure is what you expect
theorem sanity_check : volume (Set.Icc (3 : ℝ≥0∞) 42) = 39 := by
  sorry
  -- rw [ENNReal.volume_val measurableSet_Icc]
  -- rw [ENNReal.toReal_Icc_eq_Icc, Real.volume_Icc]
  -- all_goals norm_num

lemma integral_nnreal {f : ℝ≥0 → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ici (0 : ℝ), f x.toNNReal := by
  sorry
  -- change ∫⁻ (x : ℝ≥0), f x = ∫⁻ (x : ℝ) in Ici 0, (f ∘ Real.toNNReal) x
  -- rw [← lintegral_subtype_comap measurableSet_Ici]
  -- simp
  -- rfl

lemma integral_nnreal' {f : ℝ≥0∞ → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) :=
  sorry

-- TODO: prove these integral lemmas and name them properly
lemma todo' (f : ℝ≥0 → ℝ≥0∞) : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (Real.toNNReal x) :=
  sorry

lemma todo'' (f : ℝ → ℝ≥0∞) : ∫⁻ x : ℝ≥0, f (x.toReal) = ∫⁻ x in Ioi (0 : ℝ), f x :=
  sorry

end NNReal



section Lorentz
variable {α ε ε' : Type*} {m m0 : MeasurableSpace α}
variable [ENorm ε] [ENorm ε'] {p : ℝ≥0∞} {q : ℝ}


/-- The Lorentz norm of a function, for `p < ∞` -/
def eLorentzNorm' (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  p ^ r⁻¹.toReal * eLpNorm (fun (t : ℝ≥0) ↦ t * distribution f t μ ^ p⁻¹.toReal) r
    (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

/-- The Lorentz norm of a function -/
def eLorentzNorm (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then
    0 else if p = ∞ then
    if r = 0 then
      0 else if r = ∞ then
        eLpNormEssSup f μ else
        ∞ * eLpNormEssSup f μ else
    eLorentzNorm' f p r μ

@[simp]
lemma eLorentzNorm_eq_eLorentzNorm' {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α}
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLorentzNorm f p r μ = eLorentzNorm' f p r μ := by
  sorry
  -- unfold eLorentzNorm
  -- simp [hp_ne_zero, hp_ne_top]

@[simp]
lemma eLorentzNorm_zero {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} (hp : p = 0) :
    eLorentzNorm f p r μ = 0 := by
  sorry
  -- unfold eLorentzNorm
  -- simp [hp]

@[simp]
lemma eLorentzNorm_zero' {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} (hr : r = 0) :
    eLorentzNorm f p r μ = 0 := by
  sorry
  -- unfold eLorentzNorm eLorentzNorm'
  -- simp [hr]


--TODO: make this an iff, for p, r ≠ 0?
lemma eLorentzNorm_zero_of_ae_zero {E : Type*} [NormedAddCommGroup E] {p r : ℝ≥0∞} {μ : Measure α}
    {f : α → E} (h : f =ᵐ[μ] 0) : eLorentzNorm f p r μ = 0 := by
  sorry
  -- unfold eLorentzNorm
  -- simp only [ite_eq_left_iff]
  -- intro p_ne_zero
  -- rw [eLpNormEssSup_eq_zero_iff.mpr h]
  -- simp only [mul_zero, ite_self, ite_eq_left_iff]
  -- intro p_ne_top
  -- unfold eLorentzNorm'
  -- conv in ↑t * distribution f _ μ ^ p⁻¹.toReal =>
  --   rw [distribution_zero h,
  --   ENNReal.zero_rpow_of_pos (by simp only [ENNReal.toReal_inv, inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top),
  --   mul_zero]
  -- simp [*, ← Pi.zero_def]
  -- sorry -- this is actually tricky, because Mathlib is missing some lemmas in this version


section decreasing_rearrangement

variable [ENorm ε] [ENorm ε']

def decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0) : ℝ≥0 :=
  sInf {σ | distribution f σ μ ≤ t}

lemma decreasing_rearrangement_antitone {f : α → ε} {μ : Measure α} :
    Antitone (decreasing_rearrangement f μ) := by
  unfold decreasing_rearrangement distribution
  sorry

lemma distribution_decreasing_rearrangement (f : α → ℝ≥0∞) (hf : Measurable f) 
    (μ : Measure α) (t : ℝ≥0) :
    distribution f t μ = distribution (decreasing_rearrangement f μ) t volume := by
  delta distribution decreasing_rearrangement
  extract_goal

/- Alternative definition. Not used at the moment. -/
lemma eLorentzNorm_eq {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} :
    eLorentzNorm f p r μ
      = eLpNorm (fun t ↦ t ^ p⁻¹.toReal * decreasing_rearrangement f μ t) r
          (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  sorry

end decreasing_rearrangement

@[simp]
lemma eLorentzNorm_top_top {E : Type*} [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} :
    eLorentzNorm f ∞ ∞ μ = eLpNormEssSup f μ := by
  sorry
  -- unfold eLorentzNorm
  -- simp

lemma eLorentzNorm_eq_Lp {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    {μ : Measure α} {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0∞}  :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  sorry
  -- unfold eLorentzNorm
  -- by_cases p_zero : p = 0
  -- · simp [p_zero]
  -- by_cases p_eq_top : p = ∞
  -- · simp [p_eq_top]
  -- have p_eq : p = .ofReal p.toReal := by simp [p_eq_top]
  -- simp only [p_zero, ↓reduceIte, p_eq_top]
  -- unfold eLorentzNorm'
  -- calc _
  --   _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
  --     ENNReal.ofReal t ^ (p.toReal - 1) ) ^ p⁻¹.toReal := by
  --       rw [← p_eq, eLpNorm_eq_eLpNorm' p_zero p_eq_top, eLpNorm'_eq_lintegral_enorm,
  --         ENNReal.mul_rpow_of_nonneg, lintegral_withDensity_eq_lintegral_mul_non_measurable]
  --       · simp only [ENNReal.toReal_inv, enorm_eq_self, one_div]
  --         congr 2
  --         simp only [Pi.mul_apply]
  --         rw [@integral_nnreal' (fun x ↦ x⁻¹ * (x * distribution f x μ ^ p.toReal⁻¹)^ p.toReal)]
  --         apply setLIntegral_congr_fun measurableSet_Ioi
  --         apply ae_of_all
  --         intro t ht
  --         rw [Set.mem_Ioi] at ht
  --         rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← mul_assoc, ← ENNReal.rpow_neg_one,
  --             ← ENNReal.rpow_add _ _ (by simpa) (by simp), mul_comm]
  --         congr 2
  --         · rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨p_zero,p_eq_top⟩), ENNReal.rpow_one]
  --         · exact neg_add_eq_sub 1 p.toReal
  --       · exact Measurable.inv measurable_coe_nnreal_ennreal
  --       · rw[Filter.eventually_iff_exists_mem]
  --         use {x | x ≠ 0}
  --         constructor
  --         · refine mem_ae_iff.mpr ?_
  --           rw [NNReal.volume_val]
  --           simp
  --         · intro x hx
  --           rw[ENNReal.inv_lt_top, ENNReal.coe_pos]
  --           exact pos_of_ne_zero hx
  --       · simp
  --   _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
  --     ENNReal.ofReal (t ^ (p.toReal - 1)) ) ^ p.toReal⁻¹ := by
  --       rw [ENNReal.toReal_inv]
  --       congr 2
  --       apply setLIntegral_congr_fun measurableSet_Ioi
  --       apply ae_of_all
  --       intro t ht
  --       congr
  --       exact ENNReal.ofReal_rpow_of_pos ht
  --   _ = eLpNorm f (.ofReal p.toReal) μ := (eLpNorm_eq_distribution hf (ENNReal.toReal_pos p_zero p_eq_top)).symm
  --   _ = eLpNorm f p μ := by congr; exact p_eq.symm




lemma eLorentzNorm_eq_wnorm {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    {f : α → E} {p : ℝ≥0∞} (hp : p ≠ 0) {μ : Measure α} : eLorentzNorm f p ∞ μ = wnorm f p μ := by
  sorry
  -- by_cases p_eq_top : p = ∞
  -- · rw [p_eq_top]
  --   simp
  -- rw [eLorentzNorm_eq_eLorentzNorm' hp p_eq_top, wnorm_ne_top p_eq_top]
  -- unfold eLorentzNorm' wnorm'
  -- simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, ENNReal.toReal_inv,
  --   eLpNorm_exponent_top, one_mul]
  -- unfold eLpNormEssSup
  -- --rw [Continuous.essSup]
  -- simp only [enorm_eq_self]
  -- --TODO: somehow use continuity properties of the distribution function here
  -- sorry

variable [TopologicalSpace ε] [ContinuousENorm ε]
/-- A function is in the Lorentz space L_{pr} if it is (strongly a.e.)-measurable and has finite Lorentz norm. -/
def MemLorentz (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ eLorentzNorm f p r μ < ∞

-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_nested {f : α → ε} {p r₁ r₂ : ℝ≥0∞} {μ : Measure α}
    (h : r₁ ≤ r₂) (hf : MemLorentz f p r₁ μ) :
    MemLorentz f p r₂ μ := by
  sorry


variable {α' ε₁ ε₂ : Type*} {m : MeasurableSpace α'} [TopologicalSpace ε₁] [ContinuousENorm ε₁]
    [TopologicalSpace ε₂] [ContinuousENorm ε₂] --[TopologicalSpace ε₃] [ContinuousENorm ε₃]
    {f : α → ε} {f₁ : α → ε₁}

/-- An operator has Lorentz type `(p, r, q, s)` if it is bounded as a map
from `L^{q, s}` to `L^{p, r}`. `HasLorentzType T p r q s μ ν c` means that
`T` has Lorentz type `(p, r, q, s)` w.r.t. measures `μ`, `ν` and constant `c`. -/
def HasLorentzType (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧
    eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ

--TODO: what exactly should be the requirements on 𝕂? Actually, we only need a 1 here.
--TODO: This could be more general, it currently assumes T f ≥ 0
variable {𝕂 : Type*} [TopologicalSpace 𝕂] [ContinuousENorm 𝕂] [NormedField 𝕂]

/-- Defines when an operator "has restricted weak type". This is an even weaker version
of `HasBoundedWeakType`. -/
def HasRestrictedWeakType (T : (α → 𝕂) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal

lemma HasRestrictedWeakType.HasLorentzType {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] {T : (α → 𝕂) → (α' → E)} {p p' : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞}
  (hT : HasRestrictedWeakType T p p' μ ν c) (hpp' : p.HolderConjugate p') :
    --TODO: might have to adjust the constant
    HasLorentzType T p 1 p ∞ μ ν c := by
  sorry
--   intro f hf
--   have claim : ∀ (G : Set α'), (MeasurableSet G) → (ν G < ∞) → eLpNorm (T f) 1 (ν.restrict G)
--     ≤ c * eLorentzNorm f p 1 μ * (ν G) ^ p'⁻¹.toReal := by
--       -- Get this for simple functions first?
--       sorry
--   -- Apply claim to a special G
--   --let G := {x | ‖T x‖ₑ > }
--   constructor
--   · sorry
--   · by_cases h : p = ⊤
--     · rw [h]
--       rw [eLorentzNorm_eq_Lp sorry]
--       by_cases h' : f =ᵐ[μ] 0
--       · sorry
--       · sorry
--     · rw [eLorentzNorm_eq_wnorm sorry, wnorm_ne_top h]
--       unfold wnorm'
--       apply iSup_le
--       intro l
--       unfold distribution
--       set G := {x | ↑l < ‖T f x‖ₑ}
-- --      set G'
--       --rw [div_le_div__right]
--       calc _
--         _ = ↑l * ν G / ν G ^ p'⁻¹.toReal := by
--           rw [mul_div_assoc]
--           congr
--           rw [ENNReal.holderConjugate_iff] at hpp'
--           rw [ENNReal.eq_div_iff sorry sorry, ← ENNReal.rpow_add, ← ENNReal.toReal_inv, ← ENNReal.toReal_add, add_comm, hpp']
--           · simp only [ENNReal.toReal_one, ENNReal.rpow_one]
--           · rw [ne_eq, ENNReal.inv_eq_top]
--             sorry
--           · rw [ne_eq, ENNReal.inv_eq_top]
--             sorry
--           · sorry
--           · sorry
--         _ ≤ (∫⁻ (x : α') in G, ‖T f x‖ₑ ∂ν) / ν G ^ p'⁻¹.toReal := by
--           gcongr
--           --rw [setLIntegral]
--           rw [← Measure.restrict_eq_self _ (subset_refl G)]
--           calc _
--             _ ≤ ↑l * (ν.restrict G) {x | ↑l ≤ ‖T f x‖ₑ} := by
--               gcongr
--               intro x hx
--               unfold G at hx
--               simp only [coe_lt_enorm, Set.mem_setOf_eq] at hx
--               simp only [coe_le_enorm, Set.mem_setOf_eq, hx.le]
--           apply mul_meas_ge_le_lintegral₀
--           sorry
--         _ = eLpNorm (T f) 1 (ν.restrict G) / ν G ^ p'⁻¹.toReal := by
--           rw [eLpNorm_one_eq_lintegral_enorm]
--         _ ≤ (c * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal) / ν G ^ p'⁻¹.toReal := by
--           gcongr
--           apply claim
--           · sorry
--           · sorry
--         _ ≤ c * eLorentzNorm f p 1 μ * 1 := by
--           rw [mul_div_assoc]
--           gcongr
--           exact ENNReal.div_self_le_one
--         _ = c * eLorentzNorm f p 1 μ := by ring

end Lorentz
