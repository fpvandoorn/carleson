module

public import Mathlib.Analysis.Convolution

public section

open scoped Convolution

namespace MeasureTheory

variable {𝕜 G E E' F : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace G] {μ : Measure G}
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  (L : E →L[𝕜] E' →L[𝕜] F) [AddGroup G] {f f' : G → E} {g g' : G → E'}

theorem convolution_congr_left (h : f =ᵐ[μ] f') : f ⋆[L, μ] g = f' ⋆[L, μ] g := by
  ext x
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

theorem convolution_congr_right [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ]
    [μ.IsAddLeftInvariant] (h : g =ᵐ[μ] g') : f ⋆[L, μ] g = f ⋆[L, μ] g' := by
  ext x
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_sub_left μ x).ae h] with t ht
  rw [ht]

end MeasureTheory
