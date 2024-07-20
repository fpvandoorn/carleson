import Carleson.Classical.Basic

open MeasureTheory AddCircle

--TODO: add version of partialFourierSum for the AddCircle?
noncomputable section
def partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (f : AddCircle T → ℂ) (N : ℕ) : Lp ℂ p (@haarAddCircle T hT) :=
    ∑ n in Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourierLp p n


--TODO: completely reformulate partialFourierSum in terms of more abstract structures?

lemma partialFourierSumL2_norm {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ (2 : ENNReal))] (f : AddCircle T → ℂ) (N : ℕ) :
    ‖partialFourierSumLp 2 f N‖ ^ 2 = ∑ n in Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ 2 := by
  --have : Fact (1 ≤ 2) := by
  --  rw [fact_iff]; norm_num
  calc ‖partialFourierSumLp 2 f N‖ ^ 2
    _ = ‖partialFourierSumLp 2 f N‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast]; rfl
    _ = ‖fourierBasis.repr (partialFourierSumLp 2 f N)‖ ^ (2 : ℝ) := by
      rw [fourierBasis.repr.norm_map (partialFourierSumLp 2 f N)]
    _ = ‖∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • (fourierBasis.repr (@fourierLp T hT 2 h2 n))‖ ^ (2 : ℝ) := by
      rw [partialFourierSumLp, map_sum]
      simp_rw [LinearMapClass.map_smul]
    _ = ∑ n in Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ (2 : ℝ) := by
      rw [← coe_fourierBasis]
      simp only [LinearIsometryEquiv.apply_symm_apply, lp.coeFn_smul, Pi.smul_apply, ← lp.single_smul]
      have : 2 = (2 : ENNReal).toReal := by simp
      rw [this, ← lp.norm_sum_single (by simp), ← this]
      congr 2
      apply Finset.sum_congr (by simp)
      intro n _
      congr
      . --TODO: Why?????
        sorry
      simp
    _ = ∑ n in Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ 2 := by
      simp_rw [← Real.rpow_natCast]; rfl

lemma spectral_projection_bound' {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ (2 : ENNReal))] (N : ℕ) (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 f N‖ ≤ ‖f‖ := by
  sorry

lemma spectral_projection_bound {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∫ t : AddCircle T, ‖partialFourierSumLp 2 f N t‖ ^ 2 ∂haarAddCircle ≤ ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle := by
  --calc ‖partialFourierSum' f N t‖
  /- The following three hypotheses are taken from the proof of tsum_sq_fourierCoeff -/
  have H₁ : ‖fourierBasis.repr f‖ ^ 2 = ∑' i, ‖fourierBasis.repr f i‖ ^ 2 := by
    apply_mod_cast lp.norm_rpow_eq_tsum ?_ (fourierBasis.repr f)
    norm_num
  have H₂ : ‖fourierBasis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re (L2.integrable_inner f f)] at H₃
  simp only [← norm_sq_eq_inner] at H₃
  --  rw [← H₁, H₂, H₃]
  /-
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_inner] at H₃
    rw [← H₁, H₂, H₃]
  · exact L2.integrable_inner f f
  -/
  calc ∫ t : AddCircle T, ‖partialFourierSumLp 2 f N t‖ ^ 2 ∂haarAddCircle
    _ = ‖partialFourierSumLp 2 f N‖ ^ 2 := by
      rw [Lp.norm_def, snorm]
      simp only [Complex.norm_eq_abs, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.two_ne_top,
        ENNReal.toReal_ofNat]
      rw [snorm']
      simp
      sorry
    _ = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ 2 := partialFourierSumL2_norm f N
    _ ≤  ∑' (n : ℤ), ‖fourierCoeff f n‖ ^ 2 := by
      apply sum_le_tsum
      . intro n _
        simp
      --rw [← OrthogonalFamily.summable_iff_norm_sq_summable]
      sorry
    _ = ∫ (t : AddCircle T), ‖f t‖ ^ 2 ∂haarAddCircle := tsum_sq_fourierCoeff f


#check hasSum_fourier_series_L2
#check tsum_sq_fourierCoeff
#check hasSum_fourier_series_of_summable
