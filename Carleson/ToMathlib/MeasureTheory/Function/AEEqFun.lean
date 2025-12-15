import Mathlib.MeasureTheory.Function.AEEqFun
import Carleson.ToMathlib.Misc

open MeasureTheory Finset

-- Upstreaming status: seems ready for upstreaming

theorem AEEqFun.mk_sum {α E ι : Type*} {m0 : MeasurableSpace α}
    {μ : Measure α} [inst : NormedAddCommGroup E] {s : Finset ι} {f : ι → α → E}
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
      AEEqFun.mk (∑ i ∈ s, f i) (Finset.aestronglyMeasurable_sum s hf) =
      ∑ i ∈ s.attach, AEEqFun.mk (f ↑i) (hf i (Finset.coe_mem i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, attach_empty]; rfl
  | insert i s hi h =>
    simp_rw [sum_insert hi]
    have := fun i hi ↦ hf i (mem_insert_of_mem hi)
    rw [sum_attach_insert hi, ← AEEqFun.mk_add_mk _ _ _ (aestronglyMeasurable_sum s this), h this]
