import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open scoped ENNReal
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E]
  {f : X → E}

@[simp] lemma memℒp_zero_measure {p : ℝ≥0∞} : Memℒp f p (0 : Measure X) := by simp [Memℒp]
