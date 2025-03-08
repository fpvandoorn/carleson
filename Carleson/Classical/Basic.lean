/- This file contains basic definitions and lemmas. -/

import Carleson.MetricCarleson
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convolution

import Carleson.Classical.Helper

open Finset Real MeasureTheory AddCircle

noncomputable section


--TODO: to mathlib
theorem AEEqFun.mk_sum {α E ι : Type*} {m0 : MeasurableSpace α}
    {μ : Measure α} [inst : NormedAddCommGroup E] [DecidableEq ι] {s : Finset ι} {f : ι → α → E}
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
      AEEqFun.mk (∑ i ∈ s, f i) (Finset.aestronglyMeasurable_sum' s hf) = ∑ i ∈ s.attach, AEEqFun.mk (f ↑i) (hf i (Finset.coe_mem i)) := by
  induction' s using Finset.induction_on with i s hi h
  . simp_rw [Finset.attach_empty, Finset.sum_empty]
    exact rfl
  . simp_rw [Finset.attach_insert]
    simp_rw [Finset.sum_insert hi]
    have hi' : @Subtype.mk ι (fun x ↦ x ∈ insert i s) i (Finset.mem_insert_self i s) ∉ @Finset.image { x // x ∈ s } { x // x ∈ insert i s } (fun a b ↦ a.instDecidableEq b) (fun x ↦ ⟨↑x, Finset.mem_insert_of_mem x.property⟩) s.attach := by
      simp [hi]
    simp_rw [Finset.sum_insert hi']
    rw [← AEEqFun.mk_add_mk _ _ (hf _ (Finset.mem_insert_self i s)) (Finset.aestronglyMeasurable_sum' s (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))]
    congr
    -- use induction hypothesis here
    rw [h (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

    simp only [Finset.mem_attach, Subtype.mk.injEq, forall_const, Subtype.forall, imp_self,
      implies_true, Finset.sum_image]

--TODO: to mathlib
lemma ContinuousMap.MemLp {α : Type*} {E : Type*} {m0 : MeasurableSpace α} {p : ENNReal} (μ : Measure α)
    [NormedAddCommGroup E] [TopologicalSpace α] [BorelSpace α] [SecondCountableTopologyEither α E] [CompactSpace α]
    [IsFiniteMeasure μ] (𝕜 : Type*) [Fact (1 ≤ p)] [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) : MemLp f p μ := by
  have := Subtype.val_prop (ContinuousMap.toLp p μ 𝕜 f)
  have := Lp.mem_Lp_iff_memLp.mp this
  rw [ContinuousMap.coe_toLp, memLp_congr_ae (ContinuousMap.coeFn_toAEEqFun _ _)] at this
  exact this

--TODO: to mathlib
lemma MemLp.toLp_sum {α : Type*} {E : Type*} {m0 : MeasurableSpace α} {p : ENNReal}
    {μ : Measure α} [NormedAddCommGroup E] {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp.toLp (∑ i ∈ s, f i) (memLp_finset_sum' s hf) = ∑ i : ↑s, (MemLp.toLp (f i) (hf i (Finset.coe_mem i))) := by
  rw [Finset.univ_eq_attach]
  refine Lp.ext_iff.mpr ?_
  unfold MemLp.toLp
  rw [Subtype.val]
  rw [AddSubgroup.val_finset_sum]
  refine AEEqFun.ext_iff.mp ?_
  apply AEEqFun.mk_sum (fun i hi ↦ (hf i hi).aestronglyMeasurable)

/-
--TODO: move to AddCircle
lemma AddCircle.coe_liftIoc_apply.{u_1, u_2} {𝕜 : Type u_1} {B : Type u_2} [LinearOrderedAddCommGroup 𝕜] {p : 𝕜}
    [hp : Fact (0 < p)] {a : 𝕜} [Archimedean 𝕜] {f : 𝕜 → B} {x : AddCircle p} : liftIoc p a f x = f (x : 𝕜) := by
  sorry
-/

--TODO: move to AddCircle
lemma AddCircle.coe_eq_coe_iff_of_mem_Ioc.{u_1} {𝕜 : Type u_1} [LinearOrderedAddCommGroup 𝕜] {p : 𝕜} [hp : Fact (0 < p)]
    {a : 𝕜} [Archimedean 𝕜] {x y : 𝕜} (hx : x ∈ Set.Ioc a (a + p)) (hy : y ∈ Set.Ioc a (a + p)) : (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Set.Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x, hx⟩, ← (equivIoc p a).right_inv ⟨y, hy⟩]
  exact h

--TODO: move to AddCircle
lemma AddCircle.eq_coe_Ioc.{u_1} {𝕜 : Type u_1} [LinearOrderedAddCommGroup 𝕜] {p : 𝕜} [hp : Fact (0 < p)] [Archimedean 𝕜]
    (a : AddCircle p) : ∃ b ∈ Set.Ioc 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩

--TODO: move to fourier file
--TODO: I think the measurability assumptions might be unnecessary
theorem fourierCoeff_eq_fourierCoeff_of_aeeq {T : ℝ} [hT : Fact (0 < T)] {n : ℤ} {f g : AddCircle T → ℂ}
    (hf : AEStronglyMeasurable f haarAddCircle) (hg : AEStronglyMeasurable g haarAddCircle)
    (h : f =ᶠ[ae haarAddCircle] g) : fourierCoeff f n = fourierCoeff g n := by
  unfold fourierCoeff
  apply integral_congr_ae
  change @DFunLike.coe C(AddCircle T, ℂ) (AddCircle T) (fun x ↦ ℂ) ContinuousMap.instFunLike (fourier (-n)) * f =ᶠ[ae haarAddCircle] @DFunLike.coe C(AddCircle T, ℂ) (AddCircle T) (fun x ↦ ℂ) ContinuousMap.instFunLike (fourier (-n)) * g
  have fourier_measurable : AEStronglyMeasurable (⇑(@fourier T (-n))) haarAddCircle := (ContinuousMap.measurable _).aestronglyMeasurable

  rw [← AEEqFun.mk_eq_mk (hf := fourier_measurable.mul hf) (hg := fourier_measurable.mul hg),
      ← AEEqFun.mk_mul_mk _ _ fourier_measurable hf, ← AEEqFun.mk_mul_mk _ _ fourier_measurable hg]
  congr 1
  rwa [AEEqFun.mk_eq_mk]


def partialFourierSum (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * π))

def partialFourierSum' {T : ℝ} [hT : Fact (0 < T)] (N : ℕ) (f : AddCircle T → ℂ) : C(AddCircle T, ℂ) :=
    ∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourier n

def partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : AddCircle T → ℂ) : Lp ℂ p (@haarAddCircle T hT) :=
    ∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourierLp p n


lemma partialFourierSum_eq_partialFourierSum' [hT : Fact (0 < 2 * Real.pi)] (N : ℕ) (f : ℝ → ℂ) :
    liftIoc (2 * Real.pi) 0 (partialFourierSum N f) = partialFourierSum' N (liftIoc (2 * Real.pi) 0 f) := by
  ext x
  unfold partialFourierSum partialFourierSum' liftIoc
  simp only [
    Function.comp_apply, Set.restrict_apply, Int.ofNat_eq_coe, ContinuousMap.coe_sum,
    ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr
  ext n
  rw [← liftIoc, fourierCoeff_liftIoc_eq]
  congr 2
  . rw [zero_add (2 * Real.pi)]
  . rcases (eq_coe_Ioc x) with ⟨b, hb, rfl⟩
    rw [← zero_add (2 * Real.pi)] at hb
    rw [coe_eq_coe_iff_of_mem_Ioc (Subtype.coe_prop _) hb]
    have : (liftIoc (2 * Real.pi) 0 (fun x ↦ x)) b = (fun x ↦ x) b := liftIoc_coe_apply hb
    unfold liftIoc at this
    rw [Function.comp_apply, Set.restrict_apply] at this
    exact this

lemma partialFourierSupLp_eq_partialFourierSupLp_of_aeeq {T : ℝ} [hT : Fact (0 < T)] {p : ENNReal} [Fact (1 ≤ p)] {N : ℕ} {f g : AddCircle T → ℂ}
    (hf : AEStronglyMeasurable f haarAddCircle) (hg : AEStronglyMeasurable g haarAddCircle)
    (h : f =ᶠ[ae haarAddCircle] g) : partialFourierSumLp p N f = partialFourierSumLp p N g := by
  unfold partialFourierSumLp
  congr
  ext n : 1
  congr 1
  exact fourierCoeff_eq_fourierCoeff_of_aeeq hf hg h


lemma partialFourierSum'_eq_partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : AddCircle T → ℂ) :
    partialFourierSumLp p N f = MemLp.toLp (partialFourierSum' N f) ((partialFourierSum' N f).MemLp haarAddCircle ℂ)  := by
  unfold partialFourierSumLp partialFourierSum'
  unfold fourierLp
  simp_rw [ContinuousMap.coe_sum, ContinuousMap.coe_smul]
  rw [MemLp.toLp_sum _ (by intro n hn; apply MemLp.const_smul (ContinuousMap.MemLp haarAddCircle ℂ (fourier n)))]
  rw [Finset.univ_eq_attach]
  rw [← Finset.sum_attach]
  rfl


lemma partialFourierSum_aeeq_partialFourierSumLp [hT : Fact (0 < 2 * Real.pi)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : ℝ → ℂ) (h_mem_ℒp :  MemLp (liftIoc (2 * Real.pi) 0 f) 2 haarAddCircle):
    liftIoc (2 * Real.pi) 0 (partialFourierSum N f) =ᶠ[ae haarAddCircle] ↑↑(partialFourierSumLp p N (MemLp.toLp (liftIoc (2 * Real.pi) 0 f) h_mem_ℒp)) := by
  rw [partialFourierSupLp_eq_partialFourierSupLp_of_aeeq (Lp.aestronglyMeasurable _) h_mem_ℒp.aestronglyMeasurable (MemLp.coeFn_toLp h_mem_ℒp)]
  rw [partialFourierSum'_eq_partialFourierSumLp, partialFourierSum_eq_partialFourierSum']
  symm
  apply MemLp.coeFn_toLp



local notation "S_" => partialFourierSum

@[simp]
lemma fourierCoeffOn_mul {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {c : ℂ} {n : ℤ} :
  fourierCoeffOn hab (fun x ↦ c * f x) n = c * (fourierCoeffOn hab f n):= by
  simp only [fourierCoeffOn_eq_integral, one_div, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', mul_comm, Complex.ofReal_sub, smul_eq_mul, mul_assoc,
    intervalIntegral.integral_const_mul, Complex.real_smul, Complex.ofReal_inv]
  ring

@[simp]
lemma fourierCoeffOn_neg {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {n : ℤ} :
  fourierCoeffOn hab (-f) n = - (fourierCoeffOn hab f n):= by
  simp only [fourierCoeffOn_eq_integral, one_div, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', Complex.ofReal_sub, Pi.neg_apply, smul_eq_mul, mul_neg,
    intervalIntegral.integral_neg, smul_neg, Complex.real_smul, Complex.ofReal_inv]

@[simp]
lemma fourierCoeffOn_add {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f + g) n = fourierCoeffOn hab f n + fourierCoeffOn hab g n:= by
  simp only [fourierCoeffOn_eq_integral, one_div, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', Complex.ofReal_sub, Pi.add_apply, smul_eq_mul, mul_add, Complex.real_smul,
    Complex.ofReal_inv]
  rw [← mul_add, ← intervalIntegral.integral_add]
  · ring_nf
    apply hf.continuousOn_mul (Continuous.continuousOn _)
    exact Complex.continuous_conj.comp' (by fun_prop)
  · apply hg.continuousOn_mul (Continuous.continuousOn _)
    exact Complex.continuous_conj.comp' (by fun_prop)

@[simp]
lemma fourierCoeffOn_sub {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f - g) n = fourierCoeffOn hab f n - fourierCoeffOn hab g n:= by
  rw [sub_eq_add_neg, fourierCoeffOn_add hf hg.neg, fourierCoeffOn_neg, ← sub_eq_add_neg]

@[simp]
lemma partialFourierSum_add {f g : ℝ → ℂ} {N : ℕ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * π))
    (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * π)) :
  S_ N (f + g) = S_ N f + S_ N g := by
  ext x
  simp only [partialFourierSum, fourierCoeffOn_add hf hg, fourier_apply, fourier_coe_apply',
    Complex.ofReal_mul, Complex.ofReal_ofNat, add_mul, sum_add_distrib, Pi.add_apply]

@[simp]
lemma partialFourierSum_sub {f g : ℝ → ℂ} {N : ℕ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * π))
    (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * π)) :
    S_ N (f - g) = S_ N f - S_ N g := by
  ext x
  simp only [partialFourierSum, fourierCoeffOn_sub hf hg, fourier_apply, fourier_coe_apply',
    Complex.ofReal_mul, Complex.ofReal_ofNat, sub_mul, sum_sub_distrib, Pi.sub_apply]

@[simp]
lemma partialFourierSum_mul {f: ℝ → ℂ} {a : ℂ} {N : ℕ}:
  S_ N (fun x ↦ a * f x) = fun x ↦ a * S_ N f x := by
  ext x
  simp only [partialFourierSum, fourierCoeffOn_mul, fourier_apply, fourier_coe_apply', mul_assoc,
    Complex.ofReal_mul, Complex.ofReal_ofNat, mul_sum]

lemma fourier_periodic {n : ℤ} :
    (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * π))).Periodic (2 * π) := by
  simp

lemma partialFourierSum_periodic {f : ℝ → ℂ} {N : ℕ} : (S_ N f).Periodic (2 * π) := by
  simp [partialFourierSum]

--TODO: maybe generalize to (hc : ContinuousOn f (Set.Icc 0 T)) and leave out condition (hT : 0 < T)
lemma Function.Periodic.uniformContinuous_of_continuous {f : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (hc : ContinuousOn f (Set.Icc (-T) (2 * T))) :
    UniformContinuous f := by
  have : IsCompact (Set.Icc (-T) (2 * T)) := isCompact_Icc
  have unicont_on_Icc := this.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at unicont_on_Icc
  rw [Metric.uniformContinuous_iff]
  intro ε εpos
  rcases (unicont_on_Icc ε εpos) with ⟨δ, δpos, h⟩
  use min δ T, lt_min δpos hT
  have h1 : min δ T ≤ T := min_le_right ..
  intro x y hxy
  rcases (hp.exists_mem_Ico₀' hT x) with ⟨n, ha, hxa⟩
  have hyb: f y = f (y - n • T) := (hp.sub_zsmul_eq n).symm
  rw [hxa, hyb]
  apply h (x - n • T) _ (y - n • T)
  on_goal 1 => rw [Real.dist_eq, abs_lt] at hxy
  constructor <;> linarith [ha.1, ha.2]
  · rw [Real.dist_eq,zsmul_eq_mul, sub_sub_sub_cancel_right, ← Real.dist_eq]
    exact hxy.trans_le (min_le_left ..)
  · constructor <;> linarith [ha.1, ha.2]

lemma fourier_uniformContinuous {n : ℤ} :
    UniformContinuous (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * π))) := by
  apply fourier_periodic.uniformContinuous_of_continuous Real.two_pi_pos (Continuous.continuousOn _)
  continuity

lemma partialFourierSum_uniformContinuous {f : ℝ → ℂ} {N : ℕ} : UniformContinuous (S_ N f) := by
  apply partialFourierSum_periodic.uniformContinuous_of_continuous Real.two_pi_pos
    (Continuous.continuousOn (continuous_finset_sum ..))
  continuity

theorem strictConvexOn_cos_Icc : StrictConvexOn ℝ (Set.Icc (π / 2) (π + π / 2)) Real.cos := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc ..) Real.continuousOn_cos fun x hx => ?_
  rw [interior_Icc] at hx
  simp [Real.cos_neg_of_pi_div_two_lt_of_lt hx.1 hx.2]

lemma lower_secant_bound_aux {η : ℝ} (ηpos : 0 < η) {x : ℝ} (le_abs_x : η ≤ x)
    (abs_x_le : x ≤ 2 * π - η) (x_le_pi : x ≤ π) (h : π / 2 < x) :
    2 / π * η ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
  calc (2 / π) * η
    _ ≤ (2 / π) * x := by gcongr
    _ = 1 - ((1 - (2 / π) * (x - π / 2)) * Real.cos (π / 2) + ((2 / π) * (x - π / 2)) * Real.cos (π)) := by
      field_simp -- a bit slow
      ring
    _ ≤ 1 - (Real.cos ((1 - (2 / π) * (x - π / 2)) * (π / 2) + (((2 / π) * (x - π / 2)) * (π)))) := by
      gcongr
      apply (strictConvexOn_cos_Icc.convexOn).2 (by simp [pi_nonneg])
      · simp
        constructor <;> linarith [pi_nonneg]
      · rw [sub_nonneg, mul_comm]
        exact mul_le_of_le_div₀ (by norm_num) (div_nonneg (by norm_num) pi_nonneg) (by simpa)
      · exact mul_nonneg (div_nonneg (by norm_num) pi_nonneg) (by linarith [h])
      · simp
    _ = 1 - Real.cos x := by congr; field_simp; ring -- slow
    _ ≤ Real.sqrt ((1 - Real.cos x) ^ 2) := by
      exact Real.sqrt_sq_eq_abs _ ▸ le_abs_self _
    _ ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
        rw [mul_comm, Complex.exp_mul_I, Complex.norm_eq_sqrt_sq_add_sq]
        simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.sin_ofReal_im, Complex.I_im, Complex.sub_im, Complex.one_im, Complex.add_im,
          Complex.cos_ofReal_im, Complex.mul_im]
        rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
        apply (Real.sqrt_le_sqrt_iff _).mpr
        · simp only [mul_zero, mul_one, sub_self, add_zero, zero_add, zero_sub, even_two,
          Even.neg_pow, le_add_iff_nonneg_right, pow_two_nonneg]
        · linarith [pow_two_nonneg (1 - Real.cos x), pow_two_nonneg (Real.sin x)]

lemma lower_secant_bound' {η : ℝ}  {x : ℝ} (le_abs_x : η ≤ |x|) (abs_x_le : |x| ≤ 2 * π - η) :
    (2 / π) * η ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
  by_cases ηpos : η ≤ 0
  · calc (2 / π) * η
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_two pi_pos.le) ηpos
    _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := norm_nonneg _
  push_neg at ηpos
  wlog x_nonneg : 0 ≤ x generalizing x
  · convert (@this (-x) _ (by simpa) (by linarith)) using 1
    · rw [← Complex.norm_conj, map_sub, map_one, Complex.ofReal_neg, mul_neg,
        ← Complex.exp_conj, map_mul, Complex.conj_I, neg_mul,
        Complex.conj_ofReal]
    · rwa [abs_neg]
  rw [abs_of_nonneg x_nonneg] at *
  wlog x_le_pi : x ≤ π generalizing x
  · convert (@this (2 * π - x) ..) using 1
    · rw [← Complex.norm_conj]
      simp [← Complex.exp_conj, mul_sub, Complex.conj_ofReal, Complex.exp_sub,
        mul_comm Complex.I (2 * π), ← Complex.exp_neg]
    all_goals linarith
  by_cases h : x ≤ π / 2
  · calc (2 / π) * η
    _ ≤ (2 / π) * x := by gcongr
    _ = (1 - (2 / π) * x) * Real.sin 0 + ((2 / π) * x) * Real.sin (π / 2) := by simp
    _ ≤ Real.sin ((1 - (2 / π) * x) * 0 + ((2 / π) * x) * (π / 2)) := by
      apply (strictConcaveOn_sin_Icc.concaveOn).2 (by simp [pi_nonneg])
      · simp
        constructor <;> linarith [pi_nonneg]
      · rw [sub_nonneg, mul_comm]
        exact mul_le_of_le_div₀ (by norm_num) (div_nonneg (by norm_num) pi_nonneg) (by simpa)
      · exact mul_nonneg (div_nonneg (by norm_num) pi_nonneg) x_nonneg
      · simp
    _ = Real.sin x := by field_simp
    _ ≤ Real.sqrt ((Real.sin x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      apply le_abs_self
    _ ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
        rw [mul_comm, Complex.exp_mul_I, Complex.norm_eq_sqrt_sq_add_sq]
        simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.cos_ofReal_re,
          Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, Complex.sin_ofReal_im, Complex.I_im,
          Complex.sub_im, Complex.one_im, Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im]
        apply (Real.sqrt_le_sqrt_iff _).mpr
        · simp [pow_two_nonneg]
        · linarith [pow_two_nonneg (1 - Real.cos x), pow_two_nonneg (Real.sin x)]
  · push_neg at h
    exact lower_secant_bound_aux ηpos le_abs_x abs_x_le x_le_pi h

/- Slightly weaker version of Lemma 11..1.9 (lower secant bound) with simplified constant. -/
lemma lower_secant_bound {η : ℝ} {x : ℝ} (xIcc : x ∈ Set.Icc (-2 * π + η) (2 * π - η)) (xAbs : η ≤ |x|) :
    η / 2 ≤ ‖(1 - Complex.exp (Complex.I * x))‖ := by
  by_cases ηpos : η < 0
  · calc η / 2
    _ ≤ 0 := by linarith
    _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := norm_nonneg _
  push_neg at ηpos
  calc η / 2
  _ ≤ (2 / π) * η := by
    ring_nf
    rw [mul_assoc]
    gcongr
    field_simp
    rw [div_le_div_iff₀ (by norm_num) pi_pos]
    linarith [pi_le_four]
  _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
    apply lower_secant_bound' xAbs
    rw [abs_le, neg_sub', sub_neg_eq_add, neg_mul_eq_neg_mul]
    exact xIcc
