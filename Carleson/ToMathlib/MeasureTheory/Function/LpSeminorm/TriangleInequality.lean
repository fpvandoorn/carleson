import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.MeasureTheory.Function.AEEqFun

open MeasureTheory

lemma MemLp.toLp_sum {α : Type*} {E : Type*} {m0 : MeasurableSpace α} {p : ENNReal}
    {μ : Measure α} [NormedAddCommGroup E] {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp.toLp (∑ i ∈ s, f i) (memLp_finset_sum' s hf) = ∑ i : ↑s, (MemLp.toLp (f i) (hf i (Finset.coe_mem i))) := by
  rw [Finset.univ_eq_attach]
  refine Lp.ext_iff.mpr ?_
  unfold MemLp.toLp
  rw [Subtype.val]
  rw [AddSubgroup.val_finset_sum]
  refine AEEqFun.ext_iff.mp ?_
  apply AEEqFun.mk_sum (fun i hi ↦ (hf i hi).aestronglyMeasurable)
