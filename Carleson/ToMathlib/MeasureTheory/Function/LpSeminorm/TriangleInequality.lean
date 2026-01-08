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

namespace MeasureTheory

theorem one_le_LpAddConst {p : ENNReal} : 1 ≤ LpAddConst p := by
  unfold LpAddConst
  split_ifs with h
  · apply ENNReal.one_le_rpow (by norm_num)
    simp only [one_div, sub_pos]
    rw [one_lt_inv_iff₀]
    constructor
    · apply ENNReal.toReal_pos h.1.ne' h.2.ne_top
    · apply ENNReal.toReal_lt_of_lt_ofReal
      simp only [ENNReal.ofReal_one]
      exact h.2
  · rfl

end MeasureTheory
