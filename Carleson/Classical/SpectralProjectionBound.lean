import Carleson.Classical.Basic

open MeasureTheory AddCircle


--TODO: move somewhere else?
lemma L2norm_sq_eq {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖f‖ ^ 2 = ∫ (x : AddCircle T), ‖f x‖ ^ 2 ∂haarAddCircle := by
  /- The proof is inspired by parts of the proof of tsum_sq_fourierCoeff. -/
  rw [@norm_sq_eq_inner ℂ, @L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f, ← integral_re (L2.integrable_inner f f)]
  simp only [← norm_sq_eq_inner]

lemma fourierCoeff_eq_innerProduct {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ 2)] {f : ↥(Lp ℂ 2 haarAddCircle)} {n : ℤ} :
    fourierCoeff f n = ⟪@fourierLp T hT 2 h2 n, f⟫_ℂ := by
  rw [← coe_fourierBasis, ← fourierBasis_repr]
  exact HilbertBasis.repr_apply_apply fourierBasis f n


--TODO: add version of partialFourierSum for the AddCircle?
noncomputable section
def partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (f : ↥(Lp ℂ 2 (@haarAddCircle T hT))) (N : ℕ) : Lp ℂ p (@haarAddCircle T hT) :=
    ∑ n in Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourierLp p n

--TODO: add some lemma relating partialFourierSum and partialFourierSumLp

/-
lemma partialFourierSumLp_apply {T : ℝ} [hT : Fact (0 < T)] {p : ENNReal} [Fact (1 ≤ p)] {f : ↥(Lp ℂ 2 (@haarAddCircle T hT))} {N : ℕ} {x : AddCircle T} :
    partialFourierSumLp p f N x = partialFourierSum f N x := by
-/

--TODO: completely reformulate partialFourierSum in terms of more abstract structures?

--#check Finset.sum

lemma partialFourierSumL2_norm {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ (2 : ENNReal))] {f : ↥(Lp ℂ 2 haarAddCircle)} {N : ℕ} :
    ‖partialFourierSumLp 2 f N‖ ^ 2 = ∑ n in Finset.Icc (-Int.ofNat N) N, ‖@fourierCoeff T hT _ _ _ f n‖ ^ 2 := by
  --TODO: this can probably be simplified
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
      --TODO: Why do we need to manually replace set the DecidableEq argument??
      rw [this, ← @lp.norm_sum_single _ _ _ _ (fun (a : ℤ) (b : ℤ) ↦ Classical.propDecidable (a = b)) (by simp), ← this]
      congr 2
      apply Finset.sum_congr (by simp)
      intro n _
      simp
    _ = ∑ n in Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ 2 := by
      simp_rw [← Real.rpow_natCast]; rfl

lemma spectral_projection_bound_sq {T : ℝ} [hT : Fact (0 < T)] (N : ℕ) (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 f N‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [partialFourierSumL2_norm]
  simp_rw [fourierCoeff_eq_innerProduct]
  apply orthonormal_fourier.sum_inner_products_le

lemma spectral_projection_bound_sq_integral {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∫ t : AddCircle T, ‖partialFourierSumLp 2 f N t‖ ^ 2 ∂haarAddCircle ≤ ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle := by
  rw [← L2norm_sq_eq, ← L2norm_sq_eq]
  apply spectral_projection_bound_sq

lemma spectral_projection_bound {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 f N‖ ≤ ‖f‖ := by
  rw [← abs_norm, ← abs_norm f, ← sq_le_sq]
  apply spectral_projection_bound_sq




-- Bessel's inequality
#check Orthonormal.sum_inner_products_le
#check OrthogonalFamily.norm_sum
#check orthonormal_fourier
