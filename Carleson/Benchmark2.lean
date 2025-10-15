import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Convolution

open FourierTransform MeasureTheory Real Lp MemLp Filter Complex Topology InnerProductSpace ComplexConjugate

namespace MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

-- The Fourier transform of conj f is the conjugate of the inverse Fourier transform
lemma fourier_conj {f : V → ℂ} : 𝓕 (conj f) = conj (𝓕 (f ∘ (fun x ↦ -x))) := by
  unfold fourierIntegral VectorFourier.fourierIntegral
  ext w
  simp
  rw [← integral_conj, ← integral_neg_eq_self]
  apply congrArg (integral volume)
  ext v
  have : 𝐞 (-⟪v, w⟫_ℝ) • f (-v) = 𝐞 (-⟪v, w⟫_ℝ) * f (-v) := rfl
  rw [this, starRingEnd_apply, starRingEnd_apply, star_mul']
  have : 𝐞 (-⟪-v, w⟫_ℝ) • star (f (-v)) = 𝐞 (-⟪-v, w⟫_ℝ) * star (f (-v)) := rfl
  rw [this]
  simp
  left
  unfold Real.fourierChar
  simp [← Complex.exp_conj, Complex.exp_neg, inv_inv, conj_ofNat]

-- The fourier transform of a convolution is the product of the individual Fourier transforms
lemma fourier_convolution {f g : V → ℂ} (hf : Integrable f volume) (hg : Integrable g volume) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = (𝓕 f) * (𝓕 g) := by
  unfold convolution fourierIntegral VectorFourier.fourierIntegral
  simp
  ext x
  simp
  symm
  calc (∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • f v) * ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • g v
    _ = ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • f v * ∫ (w : V), 𝐞 (-⟪w, x⟫_ℝ) • g w := Eq.symm (integral_mul_right _ _)
    _ = ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • f v * ∫ (w : V), 𝐞 (-⟪w - v,x⟫_ℝ) • g (w - v) := ?_
    _ = ∫ (v : V) (w : V), 𝐞 (-⟪v, x⟫_ℝ) * 𝐞 (-⟪w - v,x⟫_ℝ) * (f v * g (w - v)) := ?_
    _ = ∫ (v : V) (w : V), 𝐞 (-⟪w, x⟫_ℝ) * (f v * g (w - v)) := ?_
    _ = ∫ (w : V) (v : V), 𝐞 (-⟪w, x⟫_ℝ) * (f v * g (w - v)) := ?_
    _ = ∫ (w : V), 𝐞 (-⟪w, x⟫_ℝ) * ∫ (v : V), f v * g (w - v) :=
        congrArg (integral volume) <| (Set.eqOn_univ _ _).1 fun _ _ ↦ integral_mul_left _ _
    _ = ∫ (v : V), 𝐞 (-⟪v, x⟫_ℝ) • ∫ (t : V), f t * g (v - t) := rfl
  · apply congrArg (integral volume)
    ext v
    simp
    left
    exact (@integral_sub_right_eq_self V ℂ _ _ _ volume _ _ _ (fun w ↦ 𝐞 (-⟪w,x⟫_ℝ) • g w) v).symm
  · apply congrArg (integral volume)
    ext v
    rw [← integral_mul_left]
    apply congrArg (integral volume)
    ext w
    have h1 : 𝐞 (-⟪v, x⟫_ℝ) • f v = 𝐞 (-⟪v, x⟫_ℝ) * f v := rfl
    have h2 : 𝐞 (-⟪w - v, x⟫_ℝ) • g (w - v) = 𝐞 (-⟪w - v, x⟫_ℝ) * g (w - v) := rfl
    rw [h1, h2]
    ring
  · apply congrArg (integral volume)
    ext v
    apply congrArg (integral volume)
    ext w
    apply mul_eq_mul_right_iff.2
    left
    unfold Real.fourierChar
    simp only [AddChar.coe_mk, mul_neg, coe_inv_unitSphere, Circle.coe_exp, ofReal_mul, ofReal_ofNat]
    rw [← Complex.exp_add]
    apply congrArg (cexp)
    simp
    have : ⟪w, x⟫_ℝ = ⟪v, x⟫_ℝ + ⟪w - v, x⟫_ℝ := by
      rw [← InnerProductSpace.add_left, add_sub_cancel]
    rw [this]
    push_cast
    ring
  · apply integral_integral_swap
    rw [integrable_prod_iff]
    constructor
    · simp
      apply ae_of_all volume
      intro v
      have h : AEStronglyMeasurable (fun a ↦ f v * g (a - v)) volume := by
        apply AEStronglyMeasurable.mul aestronglyMeasurable_const
        apply AEStronglyMeasurable.comp_measurePreserving (Integrable.aestronglyMeasurable hg)
        exact measurePreserving_sub_right volume v
      apply (integrable_norm_iff ?_).1
      · have : (∀ b, (fun a ↦ ‖(𝐞 (-⟪a,x⟫_ℝ) : ℂ) * (f v * g (a - v))‖) b = (fun a ↦ ‖f v * g (a - v)‖) b) := by
          simp
        apply (integrable_congr (ae_of_all volume this)).2
        apply (integrable_norm_iff h).2
        apply Integrable.const_mul
        exact Integrable.comp_sub_right hg v
      apply AEStronglyMeasurable.mul _ h
      have : (fun y ↦ ↑(𝐞 (-⟪y, x⟫_ℝ))) = (Complex.exp ∘ ((- 2 * (π : ℂ) * I) • (fun y ↦ (⟪y, x⟫_ℝ : ℂ)))) := by
        ext y
        unfold Real.fourierChar
        simp[Complex.exp_neg]
        exact congrArg cexp (by ring)
      rw [this]
      apply aestronglyMeasurable_iff_aemeasurable.2
      apply Measurable.comp_aemeasurable Complex.measurable_exp
      apply AEMeasurable.const_smul (Continuous.aemeasurable ?_)
      have : (fun y ↦ (⟪y, x⟫_ℝ : ℂ)) = ((fun x ↦ (x : ℂ)) : ℝ → ℂ) ∘ ((fun y ↦ ⟪y, x⟫_ℝ) : V → ℝ) := by
        ext y; simp
      rw [this]
      exact Continuous.comp continuous_ofReal (Continuous.inner continuous_id' continuous_const)
    · simp
      have : (fun x ↦ ∫ (y : V), norm (f x) * norm (g (y - x))) = (fun x ↦ ‖f x‖ * ∫ (y : V), norm (g y)) := by
        ext x
        rw [← integral_add_right_eq_self _ x]
        simp
        exact integral_mul_left (norm (f x)) fun a ↦ norm (g a)
      rw [this]
      apply Integrable.mul_const
      apply (integrable_norm_iff ?_).2 hf
      exact Integrable.aestronglyMeasurable hf
    · apply AEStronglyMeasurable.mul
      · have : AEStronglyMeasurable (fun a ↦ (𝐞 (-⟪a, x⟫_ℝ) : ℂ)) volume := by
          unfold Real.fourierChar
          simp 

          apply aestronglyMeasurable_iff_aemeasurable.2
          apply Measurable.comp_aemeasurable measurable_inv
          apply Measurable.comp_aemeasurable Complex.measurable_exp
          apply AEMeasurable.mul_const _ I
          apply AEMeasurable.const_mul
          apply Continuous.aemeasurable
          have : (fun y ↦ (⟪y, x⟫_ℝ : ℂ)) = ((fun x ↦ (x : ℂ)) : ℝ → ℂ) ∘ ((fun y ↦ ⟪y, x⟫_ℝ) : V → ℝ) := by
            ext y; simp
          rw [this]
          exact Continuous.comp continuous_ofReal (Continuous.inner continuous_id' continuous_const)
        exact @AEStronglyMeasurable.snd V V _ _ volume volume _ _ _ _ this
      apply AEStronglyMeasurable.mul
      · exact AEStronglyMeasurable.fst (Integrable.aestronglyMeasurable hf)
      have : ((fun a : V × V ↦ g (a.2 - a.1)) = (fun a ↦ g (a.1 - a.2)) ∘ (fun a ↦ (a.2,a.1))) := by
        ext a; simp
      rw [this]
      apply AEStronglyMeasurable.comp_measurePreserving _ (Measure.measurePreserving_swap)
      apply AEStronglyMeasurable.comp_aemeasurable
      · apply AEStronglyMeasurable.mono_ac (quasiMeasurePreserving_sub_of_right_invariant volume volume).absolutelyContinuous
        exact hg.1
      exact Measurable.aemeasurable measurable_sub


lemma integrable_selfConvolution {f : V → ℂ} (hf : Integrable f volume) : Integrable (convolution f (conj (fun x ↦ f (-x))) (ContinuousLinearMap.mul ℂ ℂ)) volume := by
  apply MeasureTheory.Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  apply (integrable_norm_iff _).1
  · have : (fun a ↦ ‖(starRingEnd (V → ℂ)) (fun x ↦ f (-x)) a‖) = (fun a ↦ ‖f (-a)‖) := by
      ext a; simp
    rw [this]
    apply (integrable_norm_iff _).2
    · exact Integrable.comp_neg hf
    rw [show (fun a ↦ f (-a)) = (f ∘ (fun a ↦ -a)) from by ext a; simp]
    apply AEStronglyMeasurable.comp_aemeasurable
    · rw [Measure.map_neg_eq_self]
      exact hf.aestronglyMeasurable
    exact AEMeasurable.neg aemeasurable_id
  · rw [show ((starRingEnd (V → ℂ)) fun x ↦ f (-x)) = ((starRingEnd ℂ) ∘ (fun x ↦ f (-x))) from ?_]
    · apply AEStronglyMeasurable.comp_aemeasurable
      · apply Continuous.aestronglyMeasurable
        exact continuous_conj
      rw [show (fun a ↦ f (-a)) = (f ∘ (fun a ↦ -a)) from by ext a; simp]
      apply AEMeasurable.comp_aemeasurable
      · rw [Measure.map_neg_eq_self]
        exact hf.aemeasurable
      exact AEMeasurable.neg aemeasurable_id
    ext x
    simp

/- This lemma follows easily from the following fact:
   f ⋆ g is continuous if f ∈ L^p and g ∈ L^q with p,q conjugate.
   This is listed as TODO in Mathlib.Analysis.Convolution -/
lemma continuous_selfConvolution {f : V → ℂ} (hf : MemLp f 2) :
    Continuous (convolution f (conj (fun x ↦ f (-x))) (ContinuousLinearMap.mul ℂ ℂ)) := by
  sorry


lemma fourier_selfConvolution {f : V → ℂ}  (hf : Integrable f) :
    𝓕 (convolution f (conj (fun x ↦ f (-x))) (ContinuousLinearMap.mul ℂ ℂ)) = fun x ↦ (‖𝓕 f x‖ : ℂ) ^ 2 := by
  rw [fourier_convolution hf, fourier_conj]
  · ext x
    simp
    have : ((fun x ↦ f (-x)) ∘ fun x ↦ -x) = f := by ext x; simp
    rw [this, mul_conj']
  apply (integrable_norm_iff ?_).1
  · have : (fun a ↦ ‖conj (fun x ↦ f (-x)) a‖) = (fun a ↦ ‖f (-a)‖) := by
      ext a
      simp
    rw [this]
    exact Integrable.norm (Integrable.comp_neg hf)
  · apply aestronglyMeasurable_iff_aemeasurable.2
    apply Measurable.comp_aemeasurable (Continuous.measurable continuous_conj)
    exact Integrable.aemeasurable (Integrable.comp_neg hf)


-- In the proofs we sometimes have to convert between ∫ and ∫⁻. This is surprisingly tricky,
-- the following two lemmas are helpful
lemma l2norm_bochnerIntegral {f : V → ℂ} (h2f : MemLp f 2) : eLpNorm f 2 volume =
    ENNReal.ofReal ((∫ v : V, ‖f v‖ ^ 2) ^ ((1 : ℝ) / 2)) := by
  unfold eLpNorm; simp; unfold eLpNorm'; simp
  rw [← ENNReal.ofReal_rpow_of_nonneg]
  · apply congrArg (fun x ↦ (x ^ (2 : ℝ)⁻¹))
    rw [ofReal_integral_eq_lintegral_ofReal]
    · apply congrArg (lintegral volume)
      ext x
      rw [ENNReal.ofReal_pow]
      · apply congrArg (fun x ↦ x ^ 2)
        rw [← ofReal_norm_eq_enorm]
      simp
    · rw [Integrable.eq_1]; constructor
      · rw [show (fun v ↦ norm (f v) ^ 2) = (fun x ↦ x ^ 2) ∘ (fun v ↦ norm (f v)) from by ext v; simp]
        apply aestronglyMeasurable_iff_aemeasurable.2
        apply Measurable.comp_aemeasurable
        · exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) 2
        apply Measurable.comp_aemeasurable (Continuous.measurable continuous_norm)
        exact aestronglyMeasurable_iff_aemeasurable.1 h2f.1
      · rw [hasFiniteIntegral_def]
        rw [show (fun a ↦ (‖norm (f a) ^ 2‖ₑ)) = (fun a ↦ (‖f a‖ₑ ^ 2 : ENNReal)) from ?_]
        · have : eLpNorm f 2 volume < ⊤ := h2f.2
          unfold eLpNorm at this; simp at this; unfold eLpNorm' at this; simp at this
          have : ((∫⁻ (a : V), ↑‖f a‖₊ ^ 2) ^ (2 : ℝ)⁻¹) ^ (2 : ℝ) < ⊤ := by
            rw [ENNReal.rpow_two]
            exact ENNReal.pow_lt_top this 2
          rw [← ENNReal.rpow_mul] at this
          simp at this
          exact this
        ext v
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow]
        · simp
        exact norm_nonneg (f v)
    · apply ae_of_all volume; simp
  · apply integral_nonneg
    intro v
    simp
  · simp


lemma integrable_iff_memℒ2 {f : V → ℂ} : MemLp f 2 ↔
    AEStronglyMeasurable f volume ∧ Integrable (fun v ↦ ‖f v‖ ^ 2) := by
  constructor
  · intro h
    constructor
    · exact h.1
    constructor
    · apply aestronglyMeasurable_iff_aemeasurable.2
      rw [show (fun v ↦ ‖f v‖ ^ 2) = (fun v ↦ ‖v‖ ^ 2) ∘ f from by ext v; rfl]
      apply Measurable.comp_aemeasurable _ (aestronglyMeasurable_iff_aemeasurable.1 h.1)
      exact Continuous.measurable <| Continuous.comp (continuous_pow 2) (continuous_norm)
    · unfold HasFiniteIntegral
      simp
      rw [show ∫⁻ (a : V), ‖f a‖ₑ ^ 2 = ∫⁻ (a : V), ‖f a‖ₑ ^ (2 : ℝ) from ?_]
      · exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by simp) (by simp)).1 h.2
      simp
  intro h
  constructor
  · exact h.1
  unfold Integrable HasFiniteIntegral at h
  unfold eLpNorm eLpNorm'; simp
  rw [show ∫⁻ (a : V), ‖(fun v ↦ ‖f v‖ ^ 2) a‖ₑ = ∫⁻ (a : V), ‖f a‖ₑ ^ 2 from ?_] at h
  · exact (ENNReal.rpow_lt_top_iff_of_pos (by simp)).2 h.2.2
  apply congrArg (lintegral volume)
  ext a
  simp



lemma Complex.ofReal_integrable (f : V → ℝ) :
    Integrable (fun x ↦ f x) ↔ Integrable (fun x ↦ (f x : ℂ)) := by
  constructor
  · exact Integrable.ofReal
  intro h
  have : Integrable (fun x ↦ (f x : ℂ).re) volume := MeasureTheory.Integrable.re h
  simp at this
  exact this


-- I really don't know why I can't show this, it should be easy.
lemma Complex.ofReal_integral (f : V → ℝ) : ∫ (v : V), f v = ∫ (v : V), (f v : ℂ) := by
  sorry



/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform has the same
`L²` norm as that of `f`. -/
theorem eLpNorm_fourierIntegral {f : V → ℂ} (hf : Integrable f) (h2f : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  have hpos : {c : ℝ | c > 0} ∈ atTop := by
      simp only [gt_iff_lt, mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
      use 1; intro b h; linarith
  have lim1 : Tendsto (fun (c : ℝ) ↦ ∫ v : V, cexp (-c⁻¹ * ‖v‖ ^ 2) * 𝓕 (selfConvolution f) v)
      atTop (𝓝 (∫ v : V, ‖f v‖ ^ 2)) := by
    have : (fun (c : ℝ) ↦ (∫ v : V, 𝓕 (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2)) v * (selfConvolution f v))) =ᶠ[atTop] (fun c ↦ ∫ v : V, cexp (-c⁻¹ * ‖v‖ ^ 2) * 𝓕 (selfConvolution f) v) := by
      apply Filter.eventuallyEq_of_mem hpos
      intro c hc
      dsimp
      unfold fourierIntegral
      rw [show ∫ (v : V), VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (fun w ↦ cexp (-c⁻¹ * ↑‖w‖ ^ 2)) v * selfConvolution f v =
          ∫ (v : V), (ContinuousLinearMap.mul ℂ ℂ) (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) (fun w ↦ cexp (-c⁻¹ * ↑‖w‖ ^ 2)) v) (selfConvolution f v) from ?_]; swap
      · apply congrArg (integral volume)
        simp
      rw [VectorFourier.integral_bilin_fourierIntegral_eq_flip]
      simp -- slow
      · exact continuous_fourierChar
      · simp
        exact continuous_inner
      · simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) 0 (0 : V)
      · exact integrable_selfConvolution hf
    apply Tendsto.congr' this
    apply Tendsto.congr' (show ((fun (c : ℝ) ↦
      ∫ v : V, ((π * c) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖0 - v‖^2)) *
        (selfConvolution f v)) =ᶠ[atTop]
        (fun c ↦ ∫ v : V, 𝓕 (fun w ↦ cexp (-c⁻¹ * ‖w‖ ^ 2)) v * (selfConvolution f v))) from ?_)
    swap
    · apply Filter.eventuallyEq_of_mem hpos
      intro c hc
      simp at hc
      dsimp
      apply congrArg (integral volume)
      ext v
      simp only [mul_eq_mul_right_iff]
      left
      rw [fourierIntegral_gaussian_innerProductSpace]
      simp
      constructor
      ring_nf
      simpa
    have : ∫ v : V, (‖f v‖ : ℂ) ^ 2 = selfConvolution f 0 := by
      unfold selfConvolution convolution
      simp
      apply congrArg (integral volume)
      ext v
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
      simp
    rw [this]
    apply tendsto_integral_gaussian_smul' (integrable_selfConvolution hf)
    exact Continuous.continuousAt (continuous_selfConvolution h2f)
  have lim2 : Tendsto (fun (c : ℝ) ↦ ∫ v : V, cexp (- c⁻¹ * ‖v‖ ^ 2) * 𝓕 (selfConvolution f) v) atTop
      (𝓝 (∫ v : V, ‖𝓕 f v‖ ^ 2)) := by
    rw [fourier_selfConvolution hf]
    by_cases hF : Integrable (fun x ↦ (‖𝓕 f x‖ ^ 2)) volume
    · apply tendsto_integral_filter_of_dominated_convergence _ _ _ hF
      apply ae_of_all volume
      intro v
      rw [show (‖𝓕 f v‖ ^ 2) = cexp (- (0 : ℝ) * ‖v‖ ^ 2) * (‖𝓕 f v‖ ^ 2) by simp]
      apply (Tendsto.cexp _).smul_const
      exact tendsto_inv_atTop_zero.ofReal.neg.mul_const _
      simp
      use (1 : ℝ)
      intro b hb
      apply AEStronglyMeasurable.mul
      apply Integrable.aestronglyMeasurable
      have hb : 0 < (b : ℂ)⁻¹.re := by simpa using by linarith
      simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : V)
      apply Integrable.aestronglyMeasurable
      simp at hF
      norm_cast
      exact Integrable.ofReal hF
      simp
      use 1
      intro b hb
      apply ae_of_all volume
      intro v
      rw [← one_mul (norm (𝓕 f v)), mul_pow, ← mul_assoc, show ((1 : ℝ) ^ 2 = 1) from by simp, mul_one]
      apply mul_le_mul_of_nonneg_right
      rw [norm_exp]
      simp
      apply Left.mul_nonneg
      simpa using by linarith
      rw [show ((‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 from by norm_cast]
      exact sq_nonneg ‖v‖
      exact sq_nonneg (norm (𝓕 f v))
    · have : ¬Integrable (fun v ↦ (‖𝓕 f v‖ : ℂ) ^ 2) := by
        norm_cast
        intro h
        rw [← Complex.ofReal_integrable] at h
        exact hF h
      rw [integral_undef this]
      have : ∀ᶠ (c : ℝ) in atTop, ¬Integrable (fun v ↦ cexp (-↑c⁻¹ * (‖v‖ : ℂ) ^ 2) * (fun x ↦ (‖𝓕 f x‖ : ℂ) ^ 2) v) := by
        by_contra h
        simp at h
        absurd this
        sorry
      have : ∀ᶠ (c : ℝ) in atTop, 0 = ∫ (v : V), cexp (-↑c⁻¹ * (‖v‖ : ℂ) ^ 2) * (fun x ↦ (‖𝓕 f x‖ : ℂ) ^ 2) v := by
        simp
        simp at this
        obtain ⟨a, ha⟩ := this
        use a
        intro b hb
        rw [integral_undef (ha b hb)]
      apply Tendsto.congr' this
      rw [tendsto_def]
      intro s hs
      simp
      use 0
      intro _ _
      exact mem_of_mem_nhds hs
  have hm : AEStronglyMeasurable (𝓕 f) := by
    apply Continuous.aestronglyMeasurable
    apply VectorFourier.fourierIntegral_continuous continuous_fourierChar
        (by simp only [innerₗ_apply]; exact continuous_inner) hf
  have : ∫ (v : V), (‖𝓕 f v‖ : ℂ) ^ 2 = ∫ (v : V), (‖f v‖ : ℂ) ^ 2 := tendsto_nhds_unique lim2 lim1
  have : ∫ (v : V), ‖𝓕 f v‖ ^ 2 = ∫ (v : V), ‖f v‖ ^ 2 := by
    norm_cast at this
    apply ofReal_inj.1
    rw [Complex.ofReal_integral, Complex.ofReal_integral, this]
  rw [l2norm_bochnerIntegral h2f, l2norm_bochnerIntegral, this]
  constructor; exact hm
  by_cases H : eLpNorm f 2 volume = 0
  · rw [eLpNorm_eq_zero_iff] at H
    have : ∀ w, (fun v ↦ 𝐞 (-⟪v, w⟫_ℝ) • f v) =ᶠ[ae volume] 0 := by
      intro w
      rw [eventuallyEq_iff_exists_mem]
      rw [eventuallyEq_iff_exists_mem] at H
      obtain ⟨s,hs,h⟩ := H
      use s
      constructor
      exact hs
      intro x hx
      simp
      rw [h hx]
      simp
    have : 𝓕 f = 0 := by
      unfold fourierIntegral VectorFourier.fourierIntegral
      ext w
      simp
      exact integral_eq_zero_of_ae (this w)
    rw [this]
    simp
    exact hf.1
    simp
  have : MemLp (𝓕 f) 2 := by
    apply integrable_iff_memℒ2.2
    constructor
    exact hm
    apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [this]
    unfold eLpNorm eLpNorm' at H; simp at H
    have : 0 < ∫⁻ (v : V), ‖f v‖₊ ^ 2 := by
      apply lt_of_le_of_ne (zero_le _) (fun a ↦ H (id (Eq.symm a)))
    have : 0 < ENNReal.ofReal (∫ (v : V), ‖f v‖ ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal]
      norm_cast at this
      apply lt_of_lt_of_le this (le_of_eq _)
      apply congrArg (lintegral volume)
      ext v
      simp [← ofReal_norm_eq_enorm]
      rw [ENNReal.ofReal_pow (norm_nonneg (f v))]
      all_goals sorry
      -- exact (integrable_iff_memL2.1 h2f).2
      -- apply ae_of_all
      -- intro a
      -- simp
    rw [ENNReal.ofReal_pos] at this
    exact Ne.symm (ne_of_lt this)
  exact this.2


/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its Fourier transform is
also in `L²`. -/
theorem MemLp_fourierIntegral {f : V → ℂ} (hf : Integrable f) (h2f : MemLp f 2) :
    MemLp (𝓕 f) 2 := by
  unfold MemLp; constructor
  · apply Continuous.aestronglyMeasurable
    exact VectorFourier.fourierIntegral_continuous continuous_fourierChar
        (by simp only [innerₗ_apply]; exact continuous_inner) hf
  · rw [eLpNorm_fourierIntegral hf h2f]
    exact h2f.2

/-- Part of **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform is
also in `L²`. -/
theorem MemLp_fourierIntegralInv {f : V → ℂ} (hf : Integrable f) (h2f : MemLp f 2) :
    MemLp (𝓕⁻ f) 2 := by
  rw [fourierIntegralInv_eq_fourierIntegral_comp_neg]
  apply MemLp_fourierIntegral (Integrable.comp_neg hf)
  apply MemLp.comp_of_map
  · simpa
  exact AEMeasurable.neg aemeasurable_id

/-- **Plancherel theorem**: if `f` is in `L¹ ∩ L²` then its inverse Fourier transform has the same
`L²` norm as that of `f`. -/
theorem eLpNorm_fourierIntegralInv {f : V → ℂ} (hf : Integrable f) (h2f : MemLp f 2) :
    eLpNorm (𝓕⁻ f) 2 volume = eLpNorm f 2 volume := by
  trans eLpNorm (𝓕 f) 2 volume
  · unfold eLpNorm; simp; unfold eLpNorm'
    apply congrArg (fun x ↦ x ^ (1 / 2))
    trans ∫⁻ (a : V), ‖𝓕 f (-a)‖₊ ^ (2 : ℝ)
    · sorry
      -- apply lintegral_rw₁ _ id
      -- apply Germ.coe_eq.1 (congrArg Germ.ofFun _)
      -- ext a
      -- rw [fourierIntegralInv_eq_fourierIntegral_neg]
    · rw [← @lintegral_map' _ _ _ _ _ (fun x ↦ (‖𝓕 f x‖₊ : ENNReal) ^ 2) (fun x ↦ -x) _ (AEMeasurable.neg aemeasurable_id)]
      simp
      have : (fun x ↦ (‖𝓕 f x‖₊ : ENNReal) ^ 2) = (fun x ↦ x ^ 2) ∘ (fun x ↦ (‖𝓕 f x‖₊ : ENNReal)) := by
        ext x; simp
      rw [this]
      apply Measurable.comp_aemeasurable (Measurable.pow_const (fun ⦃t⦄ a ↦ a) 2)
      have : (fun x ↦ (‖𝓕 f x‖₊ : ENNReal)) = (fun x ↦ (‖x‖₊ : ENNReal)) ∘ (fun x ↦ 𝓕 f x) := by
        ext x; simp
      rw [this]
      exact Measurable.comp_aemeasurable (Continuous.measurable <| ENNReal.continuous_coe_iff.2 continuous_nnnorm) <|
        AEStronglyMeasurable.aemeasurable (MemLp_fourierIntegral hf h2f).1
  · exact eLpNorm_fourierIntegral hf h2f



def L12 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] : AddSubgroup (V →₂[volume] ℂ) where
  carrier := {f | eLpNorm f 1 volume < ⊤}
  add_mem' := by
    simp
    intro a _ b _ h2a h2b
    have h1a : MemLp a 1 volume := mem_Lp_iff_MemLp.1 (mem_Lp_iff_eLpNorm_lt_top.2 h2a)
    have h1b : MemLp b 1 volume := mem_Lp_iff_MemLp.1 (mem_Lp_iff_eLpNorm_lt_top.2 h2b)
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add a b)]
    apply lt_of_le_of_lt (eLpNorm_add_le h1a.1 h1b.1 _)
    exact ENNReal.add_lt_top.2 ⟨h2a, h2b⟩
    rfl
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  neg_mem' := by simp[eLpNorm_congr_ae (AEEqFun.coeFn_neg _)]

instance : NormedAddCommGroup (L12 V) := AddSubgroup.normedAddCommGroup

scoped[MeasureTheory] notation:25 α " →₁₂[" μ "] " E =>
    ((α →₁[μ] E) ⊓ (α →₂[μ] E) : AddSubgroup (α →ₘ[μ] E))
/-
/- Note: `AddSubgroup.normedAddCommGroup` is almost this, but not quite. -/
instance : NormedAddCommGroup (V →₁₂[volume] ℂ) :=
  AddGroupNorm.toNormedAddCommGroup {
    toFun := fun ⟨f,_⟩ ↦ ENNReal.toReal <| eLpNorm f 2 volume
    map_zero' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
    add_le' := fun ⟨f, _, hf⟩ ⟨g, _, hg⟩ ↦ ENNReal.toReal_le_add (by
        simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
              eLpNorm_add_le ((Lp.mem_Lp_iff_MemLp.1 hf).1) ((Lp.mem_Lp_iff_MemLp.1 hg).1)])
      ((Lp.mem_Lp_iff_eLpNorm_lt_top.1 hf).ne) ((Lp.mem_Lp_iff_eLpNorm_lt_top.1 hg).ne)
    neg' := by simp [eLpNorm_congr_ae (AEEqFun.coeFn_neg _)]
    eq_zero_of_map_eq_zero' := by
      intro ⟨f, _, hf⟩ h
      simp [ENNReal.toReal_eq_zero_iff] at h
      rcases h with h | h; swap
      · absurd h; exact (Lp.mem_Lp_iff_eLpNorm_lt_top.1 hf).ne
      ext
      apply ae_eq_trans <| (eLpNorm_eq_zero_iff ((Lp.mem_Lp_iff_MemLp.1 hf).1) (by simp)).1 h
      apply ae_eq_trans (Lp.coeFn_zero E 2 volume).symm; rfl
  }-/
lemma memℒ12_iff {f : V → ℂ} (hf : MemLp f 2 volume) :
    (hf.toLp) ∈ L12 V ↔ Integrable f := by
  constructor
  · intro h
    unfold L12 at h
    simp at h
    unfold Integrable
    constructor
    exact hf.1
    unfold HasFiniteIntegral
    unfold eLpNorm eLpNorm' at h
    simp at h
    have : ∫⁻ (a : V), ‖f a‖₊ = ∫⁻ (a : V), ‖toLp f hf a‖₊ := by
      sorry
    rw [this]
    exact h
  · sorry

lemma memL12_iff {f : V →₂[volume] ℂ} : f ∈ L12 V ↔ Integrable (↑f) := by
  constructor
  · intro h
    apply (memℒ12_iff _).1
    rw [toLp_coeFn]
    exact h
    rw [← mem_Lp_iff_MemLp]
    simp
  · intro h
    rw [← toLp_coeFn f, memℒ12_iff]
    exact h
    rw [← mem_Lp_iff_MemLp]
    simp

instance : NormedSpace ℝ (L12 V) where
  smul := fun a f ↦ by
    use a • f
    sorry
  one_smul := by
    intro ⟨f, hf⟩
    sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry
  norm_smul_le := sorry

/- The Fourier integral as a continuous linear map `L^1(V, E) ∩ L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2OfL12Fun : (V →₁₂[volume] ℂ) → (V →₂[volume] ℂ) := sorry
  --fun ⟨f,hf,hf2⟩ ↦ (MemLp_fourierIntegral (MemLp_one_iff_integrable.1 <|
  --    Lp.mem_Lp_iff_MemLp.1 (by sorry)) (Lp.mem_Lp_iff_MemLp.1 hf2)).toLp <| 𝓕 f

--def fourierIntegralL2OfL12 : (V →₁₂[volume] ℂ) →L[ℝ] (V →₂[volume] ℂ) := sorry
  /-have : IsBoundedLinearMap ℝ fourierIntegralL2OfL12Fun := {
    map_add := by
      intro f g
    map_smul := sorry
    bound := sorry
  }
  IsBoundedLinearMap.toContinuousLinearMap this-/

/- The Fourier integral as a continuous linear map `L^2(V, E) → L^2(V, E)`. -/
def fourierIntegralL2 : (V →₂[volume] ℂ) →L[ℝ] (V →₂[volume] ℂ) :=
  sorry

end MeasureTheory
