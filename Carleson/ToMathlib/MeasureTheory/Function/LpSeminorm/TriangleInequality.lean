import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.MeasureTheory.Function.AEEqFun

open MeasureTheory

-- Upstreaming status: seems ready to go; need dependencies merged first

lemma MemLp.toLp_sum {α E : Type*} {m0 : MeasurableSpace α} {p : ENNReal}
    {μ : Measure α} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι)
    {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp.toLp (∑ i ∈ s, f i) (memLp_finset_sum' s hf) =
      ∑ i : ↑s, (MemLp.toLp (f i) (hf i (Finset.coe_mem i))) := by
  ext
  rw [Subtype.val, AddSubgroup.val_finset_sum]
  exact AEEqFun.ext_iff.mp (AEEqFun.mk_sum (fun i hi ↦ (hf i hi).aestronglyMeasurable))
