import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

open MeasureTheory

lemma ContinuousMap.MemLp {α : Type*} {E : Type*} {m0 : MeasurableSpace α} {p : ENNReal} (μ : Measure α)
    [NormedAddCommGroup E] [TopologicalSpace α] [BorelSpace α] [SecondCountableTopologyEither α E] [CompactSpace α]
    [IsFiniteMeasure μ] (𝕜 : Type*) [Fact (1 ≤ p)] [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) : MemLp f p μ := by
  have := Subtype.val_prop (ContinuousMap.toLp p μ 𝕜 f)
  have := Lp.mem_Lp_iff_memLp.mp this
  rw [ContinuousMap.coe_toLp, memLp_congr_ae (ContinuousMap.coeFn_toAEEqFun _ _)] at this
  exact this
