import Mathlib.MeasureTheory.Function.AEEqFun
import Carleson.ToMathlib.Misc

open MeasureTheory Finset

--TODO: to mathlib
theorem AEEqFun.mk_sum {α E ι : Type*} {m0 : MeasurableSpace α}
    {μ : Measure α} [inst : NormedAddCommGroup E] [DecidableEq ι] {s : Finset ι} {f : ι → α → E}
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
      AEEqFun.mk (∑ i ∈ s, f i) (Finset.aestronglyMeasurable_sum' s hf) =
      ∑ i ∈ s.attach, AEEqFun.mk (f ↑i) (hf i (Finset.coe_mem i)) := by
  induction' s using Finset.induction_on with i s hi h
  . aesop
  · simp_rw [sum_insert hi]
    rw [sum_attach_insert hi, ← AEEqFun.mk_add_mk, h fun i hi ↦ hf i (mem_insert_of_mem hi)]
