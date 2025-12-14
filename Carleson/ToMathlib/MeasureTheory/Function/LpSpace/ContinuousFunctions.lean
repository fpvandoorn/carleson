import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

open MeasureTheory

-- Upstreaming status: rename to `memLp`, then ready for upstreaming.

lemma ContinuousMap.memLp {α E : Type*} {m0 : MeasurableSpace α} {p : ENNReal} (μ : Measure α)
    [NormedAddCommGroup E] [TopologicalSpace α] [BorelSpace α] [SecondCountableTopologyEither α E]
    [CompactSpace α] [IsFiniteMeasure μ] [Fact (1 ≤ p)]
    (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) : MemLp f p μ := by
  have := Lp.mem_Lp_iff_memLp.mp (Subtype.val_prop (ContinuousMap.toLp p μ 𝕜 f))
  rw [ContinuousMap.coe_toLp, memLp_congr_ae (ContinuousMap.coeFn_toAEEqFun _ _)] at this
  exact this
