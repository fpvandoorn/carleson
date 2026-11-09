module

public import Mathlib.Analysis.Convolution

public section

open scoped Convolution

namespace MeasureTheory

variable {𝕜 G E E' F : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace G] {μ : Measure G}
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  {L : E →L[𝕜] E' →L[𝕜] F} [AddGroup G] {f : G → E} {g : G → E'}

theorem convolution_eq_zero_of_ae_eq_zero_left (hf : f =ᵐ[μ] 0) : f ⋆[L, μ] g = 0 := by
  ext x
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hf] with t ht
  simp [ht]

theorem convolution_eq_zero_of_ae_eq_zero_right [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ]
    [μ.IsAddLeftInvariant] (hg : g =ᵐ[μ] 0) : f ⋆[L, μ] g = 0 := by
  ext x
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(quasiMeasurePreserving_sub_left μ x).ae hg] with t ht
  simp [ht]

end MeasureTheory
