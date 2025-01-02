import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic

open scoped ENNReal
open MeasureTheory Set

/- The lemmas in this file generalize `MonotoneOn.IntegrableOn` and friends (since being integrable
is the same as bein in `L^1`). The latter should be derived from the former once these are moved
in mathlib. -/

section Monotone

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [NormedAddCommGroup E] [OrderTopology X] [OrderTopology E] [SecondCountableTopology E]
  {f : X → E} {s : Set X} {μ : Measure X} {p : ℝ≥0∞}

open Bornology

theorem MonotoneOn.memℒp_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    Memℒp f ⊤ (μ.restrict s) := by
  borelize E
  have : CompactIccSpace E := by infer_instance
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcases isBounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  have A : Memℒp (fun _ => C) ⊤ (μ.restrict s) := memℒp_top_const _
  apply Memℒp.mono A (aemeasurable_restrict_of_monotoneOn h's hmono).aestronglyMeasurable
  apply (ae_restrict_iff' h's).mpr
  apply ae_of_all _ fun y hy ↦ ?_
  exact (hC _ (mem_image_of_mem f hy)).trans (le_abs_self _)

theorem MonotoneOn.memℒp_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    Memℒp f p (μ.restrict s) :=
  (hmono.memℒp_top ha hb h's).memℒp_of_exponent_le_of_measure_support_ne_top (s := univ)
    (by simp) (by simpa using hs) le_top

theorem MonotoneOn.memℒp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : Memℒp f p (μ.restrict s) := by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp
  · exact
      hmono.memℒp_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
        hs.measure_lt_top.ne hs.measurableSet

theorem AntitoneOn.memℒp_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    Memℒp f ⊤ (μ.restrict s) :=
  MonotoneOn.memℒp_top (E := Eᵒᵈ) hanti ha hb h's

theorem AntitoneOn.memℒp_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) :
    Memℒp f p (μ.restrict s) :=
  MonotoneOn.memℒp_of_measure_ne_top (E := Eᵒᵈ) hanti ha hb hs h's

theorem AntitoneOn.memℒp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : Memℒp f p (μ.restrict s) :=
  MonotoneOn.memℒp_isCompact (E := Eᵒᵈ) hs hanti

end Monotone
