/- This file contains the proof of Lemma 11.1.10 (spectral projection bound).
   At the moment, its results are not used as the section about truncated Hilbert transforms
   is still missing.
   Thus, the result here might not yet have the exact form needed later.
-/

import Carleson.Classical.Basic

open MeasureTheory AddCircle
open scoped InnerProductSpace

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

lemma AddCircle.eq_coe_Ioc.{u_1} {𝕜 : Type u_1} [LinearOrderedAddCommGroup 𝕜] {p : 𝕜} [hp : Fact (0 < p)] [Archimedean 𝕜]
    (a : AddCircle p) : ∃ b ∈ Set.Ioc 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩

noncomputable section

def partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : AddCircle T → ℂ) : Lp ℂ p (@haarAddCircle T hT) :=
    ∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourierLp p n

def partialFourierSum' {T : ℝ} [hT : Fact (0 < T)] (N : ℕ) (f : AddCircle T → ℂ) : C(AddCircle T, ℂ) :=
    ∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourier n

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

--TODO: I think the measurability assumptions might be unnecessary
theorem fourierCoeff_eq_fourierCoeff_of_aeeq {T : ℝ} [hT : Fact (0 < T)] {n : ℤ} {f g : AddCircle T → ℂ}
    (hf : AEStronglyMeasurable f haarAddCircle) (hg : AEStronglyMeasurable g haarAddCircle)
    (h : f =ᶠ[ae haarAddCircle] g) : fourierCoeff f n = fourierCoeff g n := by
  unfold fourierCoeff
  apply integral_congr_ae
  change @DFunLike.coe C(AddCircle T, ℂ) (AddCircle T) (fun x ↦ ℂ) ContinuousMap.instFunLike (fourier (-n)) * f =ᶠ[ae haarAddCircle] @DFunLike.coe C(AddCircle T, ℂ) (AddCircle T) (fun x ↦ ℂ) ContinuousMap.instFunLike (fourier (-n)) * g
  have fourier_measurable : AEStronglyMeasurable (⇑(@fourier T (-n))) haarAddCircle := (ContinuousMap.measurable _).aestronglyMeasurable

  rw [← @AEEqFun.mk_eq_mk _ _ _ _ _ _ _ (fourier_measurable.mul hf) (fourier_measurable.mul hg),
      ← AEEqFun.mk_mul_mk _ _ fourier_measurable hf, ← AEEqFun.mk_mul_mk _ _ fourier_measurable hg]
  congr 1
  rwa [AEEqFun.mk_eq_mk]

lemma partialFourierSupLp_eq_partialFourierSupLp_of_aeeq {T : ℝ} [hT : Fact (0 < T)] {p : ENNReal} [Fact (1 ≤ p)] {N : ℕ} {f g : AddCircle T → ℂ}
    (hf : AEStronglyMeasurable f haarAddCircle) (hg : AEStronglyMeasurable g haarAddCircle)
    (h : f =ᶠ[ae haarAddCircle] g) : partialFourierSumLp p N f = partialFourierSumLp p N g := by
  unfold partialFourierSumLp
  congr
  ext n : 1
  congr 1
  exact fourierCoeff_eq_fourierCoeff_of_aeeq hf hg h

--TODO: to mathlib
lemma ContinuousMap.memℒp {α : Type*} {E : Type*} {m0 : MeasurableSpace α} {p : ENNReal} (μ : Measure α)
    [NormedAddCommGroup E] [TopologicalSpace α] [BorelSpace α] [SecondCountableTopologyEither α E] [CompactSpace α]
    [IsFiniteMeasure μ] (𝕜 : Type*) [Fact (1 ≤ p)] [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) : Memℒp f p μ := by
  have := Subtype.val_prop (ContinuousMap.toLp p μ 𝕜 f)
  have := Lp.mem_Lp_iff_memℒp.mp this
  rw [ContinuousMap.coe_toLp, memℒp_congr_ae (ContinuousMap.coeFn_toAEEqFun _ _)] at this
  exact this

--TODO: to mathlib
theorem AEEqFun.mk_sum.{u_3, u_2, u_1} {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α}
    {μ : Measure α} [inst : NormedAddCommGroup E] {ι : Type u_3} [DecidableEq ι] {s : Finset ι} {f : ι → α → E}
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
lemma Memℒp.toLp_sum {α : Type*} {E : Type*} {m0 : MeasurableSpace α} {p : ENNReal}
    {μ : Measure α} [NormedAddCommGroup E] {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp.toLp (∑ i ∈ s, f i) (memℒp_finset_sum' s hf) = ∑ i : ↑s, (Memℒp.toLp (f i) (hf i (Finset.coe_mem i))) := by
  rw [Finset.univ_eq_attach]
  refine Lp.ext_iff.mpr ?_
  unfold Memℒp.toLp
  rw [Subtype.val]
  rw [AddSubgroup.val_finset_sum]
  refine AEEqFun.ext_iff.mp ?_
  apply AEEqFun.mk_sum (fun i hi ↦ (hf i hi).aestronglyMeasurable)


lemma partialFourierSum'_eq_partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : AddCircle T → ℂ) :
    partialFourierSumLp p N f = Memℒp.toLp (partialFourierSum' N f) ((partialFourierSum' N f).memℒp haarAddCircle ℂ)  := by
  unfold partialFourierSumLp partialFourierSum'
  unfold fourierLp
  simp_rw [ContinuousMap.coe_sum, ContinuousMap.coe_smul]
  rw [Memℒp.toLp_sum _ (by intro n hn; apply Memℒp.const_smul (ContinuousMap.memℒp haarAddCircle ℂ (fourier n)))]
  rw [Finset.univ_eq_attach]
  rw [← Finset.sum_attach]
  rfl


lemma partialFourierSum_aeeq_partialFourierSumLp [hT : Fact (0 < 2 * Real.pi)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : ℝ → ℂ) (h_mem_ℒp :  Memℒp (liftIoc (2 * Real.pi) 0 f) 2 haarAddCircle):
    liftIoc (2 * Real.pi) 0 (partialFourierSum N f) =ᶠ[ae haarAddCircle] ↑↑(partialFourierSumLp p N (Memℒp.toLp (liftIoc (2 * Real.pi) 0 f) h_mem_ℒp)) := by
  rw [partialFourierSupLp_eq_partialFourierSupLp_of_aeeq (Lp.aestronglyMeasurable _) h_mem_ℒp.aestronglyMeasurable (Memℒp.coeFn_toLp h_mem_ℒp)]
  rw [partialFourierSum'_eq_partialFourierSumLp, partialFourierSum_eq_partialFourierSum']
  symm
  apply Memℒp.coeFn_toLp


lemma partialFourierSumL2_norm {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ (2 : ENNReal))] {f : ↥(Lp ℂ 2 haarAddCircle)} {N : ℕ} :
    ‖partialFourierSumLp 2 N f‖ ^ 2 = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖@fourierCoeff T hT _ _ _ f n‖ ^ 2 := by
  calc ‖partialFourierSumLp 2 N f‖ ^ 2
    _ = ‖partialFourierSumLp 2 N f‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast]; rfl
    _ = ‖fourierBasis.repr (partialFourierSumLp 2 N f)‖ ^ (2 : ℝ) := by
      rw [fourierBasis.repr.norm_map (partialFourierSumLp 2 N f)]
    _ = ‖∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • (fourierBasis.repr (@fourierLp T hT 2 h2 n))‖ ^ (2 : ℝ) := by
      rw [partialFourierSumLp, map_sum]
      simp_rw [LinearMapClass.map_smul]
    _ = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ (2 : ℝ) := by
      rw [← coe_fourierBasis]
      simp only [LinearIsometryEquiv.apply_symm_apply, lp.coeFn_smul, Pi.smul_apply, ← lp.single_smul]
      have : 2 = (2 : ENNReal).toReal := by simp
      rw [this, ← lp.norm_sum_single (by simp), ← this]
      congr 2
      refine Finset.sum_congr (by simp) fun n ↦ ?_
      simp only [smul_eq_mul, mul_one]
      congr!
    _ = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ 2 := by
      simp_rw [← Real.rpow_natCast]; rfl

lemma spectral_projection_bound_sq {T : ℝ} [hT : Fact (0 < T)] (N : ℕ) (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 N f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [partialFourierSumL2_norm]
  simp_rw [fourierCoeff_eq_innerProduct]
  exact orthonormal_fourier.sum_inner_products_le _

lemma spectral_projection_bound_sq_integral {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∫ t : AddCircle T, ‖partialFourierSumLp 2 N f t‖ ^ 2 ∂haarAddCircle ≤ ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle := by
  rw [← L2norm_sq_eq, ← L2norm_sq_eq]
  exact spectral_projection_bound_sq _ _

lemma spectral_projection_bound_lp {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 N f‖ ≤ ‖f‖ := by
  rw [← abs_norm, ← abs_norm f, ← sq_le_sq]
  exact spectral_projection_bound_sq _ _
