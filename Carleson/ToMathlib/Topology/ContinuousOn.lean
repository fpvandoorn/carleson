module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Carleson.ToMathlib.MeasureTheory.Function.EssSup
public import Carleson.ToMathlib.MeasureTheory.Measure.NNReal

--Upstreaming status: some results should probably be generalized, see TODOs

public section

open NNReal ENNReal

theorem ContinuousWithinAt.ennreal_mul {X : Type*}
  [TopologicalSpace X] {f g : X → ℝ≥0∞} {s : Set X} {t : X} (hf : ContinuousWithinAt f s t)
  (hg : ContinuousWithinAt g s t) (h₁ : f t ≠ 0 ∨ g t ≠ ∞) (h₂ : g t ≠ 0 ∨ f t ≠ ∞) :
    ContinuousWithinAt (fun x ↦ f x * g x) s t := fun _ hx =>
  ENNReal.Tendsto.mul hf h₁ hg h₂ hx

open MeasureTheory

--TODO: generalize?
lemma ContinuousWithinAt.measure_lt_ne_zero {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
  [OrderTopology α] [ClosedIicTopology α] [μ.IsOpenPosMeasure] {f : α → ℝ≥0∞} {x : α}
  (hx : ¬IsMax x) (hf : ContinuousWithinAt f (Set.Ioi x) x)
  {a : ℝ≥0∞} (ha : a < f x) :
    μ {y | a < f y} ≠ 0 := by
  unfold ContinuousWithinAt at hf
  set s := Set.Ioi a
  have mem_nhds_s : s ∈ nhds (f x) := by
    rw [IsOpen.mem_nhds_iff isOpen_Ioi]
    simpa
  have := hf mem_nhds_s
  simp only [Filter.mem_map] at this
  rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot]
  rw [mem_nhdsWithin] at this
  rcases this with ⟨u, u_open, x_in_u, u_inter_subset⟩
  calc _
    _ < μ (u ∩ Set.Ioi x) := by
      rw [bot_lt_iff_ne_bot]
      apply IsOpen.measure_ne_zero
      · apply u_open.inter isOpen_Ioi
      apply nonempty_nhds_inter_Ioi (IsOpen.mem_nhds u_open x_in_u) hx
    _ ≤ μ (f ⁻¹' s) := by
      apply measure_mono u_inter_subset
    _ ≤ μ {y | a < f y} := by
      apply measure_mono
      unfold s Set.preimage
      simp only [Set.mem_Ioi, Set.setOf_subset_setOf]
      intro y h
      exact h

--TODO: generalize?
--currently unused
lemma eLpNormEssSup_eq_iSup' {f : ℝ≥0∞ → ℝ≥0∞}
  (hf : ∀ (a : ℝ≥0∞) (x : ℝ≥0∞), a < f x → ContinuousWithinAt f (Set.Ioi x) x) (f_top : f ⊤ = ⊥) :
    eLpNormEssSup f volume = ⨆ x, f x := by
  apply le_antisymm
  · apply essSup_le_iSup
  · apply iSup_le_essSup
    intro x a ha
    apply (hf a x ha).measure_lt_ne_zero (x := x) (μ := volume) _ ha
    contrapose! ha
    rw [isMax_iff_eq_top] at ha
    rw [ha, f_top]
    exact zero_le

--TODO: generalize?
lemma eLpNormEssSup_nnreal_eq_iSup_nnreal {f : ℝ≥0∞ → ℝ≥0∞}
  (hf : ∀ (a : ℝ≥0∞) (x : ℝ≥0), a < f x → ContinuousWithinAt f (Set.Ioi ↑x) ↑x) :
    eLpNormEssSup (fun t : ℝ≥0 ↦ f t) volume = ⨆ (x : ℝ≥0), f x := by
  apply le_antisymm
  · apply essSup_le_iSup
  · apply iSup_le_essSup
    intro x a ha
    apply ContinuousWithinAt.measure_lt_ne_zero (x := x) (μ := volume) (by simp) _ ha
    have : ContinuousWithinAt (ENNReal.ofNNReal) Set.univ x := by
      fun_prop
    convert ContinuousWithinAt.comp_inter_of_eq (g := f) (hf a x ha) this rfl
    simp only [Set.univ_inter]
    ext y
    simp
