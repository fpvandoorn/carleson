import Carleson.Classical.Basic

open MeasureTheory AddCircle

--TODO: add version of partialFourierSum for the AddCircle?
--TODO: completely reformulate partialFourierSum in terms of more abstract structures?

lemma spectral_projection_bound {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∫ t : AddCircle T, ‖partialFourierSum' f N t‖ ^ 2 ∂haarAddCircle ≤ ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle := by
  --calc ‖partialFourierSum' f N t‖
  sorry


#check hasSum_fourier_series_L2
#check tsum_sq_fourierCoeff
#check hasSum_fourier_series_of_summable
