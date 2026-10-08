module

public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic
public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic

@[expose] public section

/-!
# Weak `L^p` norm

The weak `L^p` (quasi)norm `wnorm f p μ`, defined as the Lorentz norm `eLorentzNorm f p ∞ μ`, the
explicit formula `wnorm'` for it, and the predicate `MemWLp`.
-/

-- Upstreaming status: all of this should go into mathlib, eventually.
-- Most lemmas have the right form, but proofs can often be golfed.
-- Some enorm lemmas require some mathlib refactoring first, so they can be unified with their
-- analogue in current mathlib. Such refactorings include (1) adding a Weak(Pseudo)EMetricSpace
-- class, (2) generalising all lemmas about enorms and • to this setting.

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ ε₃ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  {t s x y : ℝ≥0∞} {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' (f : α → ε) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

lemma wnorm'_zero (f : α → ε) (μ : Measure α) : wnorm' f 0 μ = ∞ := by
  simp only [wnorm', GroupWithZero.inv_zero, ENNReal.rpow_zero, mul_one, iSup_eq_top]
  refine fun b hb ↦ ⟨b.toNNReal + 1, ?_⟩
  rw [coe_add, ENNReal.coe_one, coe_toNNReal hb.ne_top]
  exact lt_add_right hb.ne_top one_ne_zero

lemma wnorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    wnorm' (ENNReal.toReal ∘ f) p μ ≤ wnorm' f p μ := by
  refine iSup_mono fun x ↦ ?_
  gcongr
  simp

lemma wnorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    wnorm' (ENNReal.toReal ∘ f) p μ = wnorm' f p μ := by
  simp_rw [wnorm', distribution_toReal_eq hf]

theorem wnorm'_eq_iSup_rpow_mul_rearrangement {p : ℝ} (hp : 0 < p) {f : α → ε} {μ : Measure α} :
    wnorm' f p μ = ⨆ t : ℝ≥0, t ^ p⁻¹ * rearrangement f t μ :=
  iSup_mul_distribution_rpow_eq_iSup_rpow_mul_rearrangement hp

section TopologicalSpace

variable [TopologicalSpace ε]

/-- The weak L^p norm of a function, defined as the Lorentz norm with second exponent `∞`. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  eLorentzNorm f p ∞ μ

lemma wnorm_of_not_aestronglyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : wnorm f p μ = ∞ :=
  eLorentzNorm_of_not_aestronglyMeasurable hf

@[simp]
lemma wnorm_zero (hf : AEStronglyMeasurable f μ) : wnorm f 0 μ = 0 :=
  eLorentzNorm_exponent_zero hf

@[simp]
lemma wnorm_top (hf : AEStronglyMeasurable f μ) : wnorm f ⊤ μ = eLpNormEssSup f μ :=
  eLorentzNorm_exponent_top_top hf

lemma wnorm_ne_top (hf : AEStronglyMeasurable f μ) (h₀ : p ≠ 0) (h : p ≠ ⊤) :
    wnorm f p μ = wnorm' f p.toReal μ := by
  rw [wnorm, eLorentzNorm_eq_eLorentzNorm' h₀ h hf, eLorentzNorm'_exponent_top, wnorm']

lemma wnorm_coe {p : ℝ≥0} (hf : AEStronglyMeasurable f μ) (hp : p ≠ 0) :
    wnorm f p μ = wnorm' f p μ := by
  rw [wnorm_ne_top hf (by simpa) coe_ne_top, coe_toReal]

lemma wnorm_ofReal {p : ℝ} (hf : AEStronglyMeasurable f μ) (hp : 0 < p) :
    wnorm f (.ofReal p) μ = wnorm' f p μ := by
  rw [wnorm_ne_top hf (by simpa) ofReal_ne_top, toReal_ofReal hp.le]

lemma wnorm_toReal_le {f : α → ℝ≥0∞} {p : ℝ≥0∞} :
    wnorm (ENNReal.toReal ∘ f) p μ ≤ wnorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_mono_enorm_ae hf.ennreal_toReal <| .of_forall fun x ↦ by
      simpa [Real.enorm_eq_ofReal_abs] using ofReal_toReal_le
  · simp [wnorm_of_not_aestronglyMeasurable hf]

lemma wnorm_toReal_eq {f : α → ℝ≥0∞} {p : ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    wnorm (ENNReal.toReal ∘ f) p μ = wnorm f p μ := by
  have hfin : NullMeasurableSet (f ⁻¹' {∞}) μ := .of_null <| measure_eq_zero_iff_ae_notMem.mpr <| by
    filter_upwards [hf] with x hx
    simp [hx]
  by_cases hm : AEStronglyMeasurable f μ
  swap
  · rw [wnorm_of_not_aestronglyMeasurable hm, wnorm_of_not_aestronglyMeasurable
      (by rwa [aestronglyMeasurable_ennreal_toReal_iff hfin])]
  refine eLorentzNorm_congr_enorm_ae hm.ennreal_toReal hm ?_
  filter_upwards [hf] with x hx
  simp [Real.enorm_eq_ofReal_abs, ofReal_toReal hx]

theorem wnorm_eq_iSup_rpow_mul_rearrangement {p : ℝ≥0∞} (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  {f : α → ε} {μ : Measure α} (hf : AEStronglyMeasurable f μ) :
    wnorm f p μ = ⨆ t : ℝ≥0, t ^ p.toReal⁻¹ * rearrangement f t μ := by
  rw [wnorm_ne_top hf p_nonzero p_ne_top]
  apply wnorm'_eq_iSup_rpow_mul_rearrangement (ENNReal.toReal_pos p_nonzero p_ne_top)

lemma eLorentzNorm_eq_wnorm {f : α → ε} {μ : Measure α} :
    eLorentzNorm f p ∞ μ = wnorm f p μ := rfl

end TopologicalSpace

lemma wnorm'_mono_enorm_ae {ε' : Type*} [ENorm ε'] {f : α → ε} {g : α → ε'} {p : ℝ} (hp : 0 ≤ p)
  (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    wnorm' f p μ ≤ wnorm' g p μ := by
  unfold wnorm'
  apply iSup_le
  intro t
  calc _
    _ ≤ ↑t * distribution g (↑t) μ ^ p⁻¹ := by gcongr
  apply le_iSup _ t

lemma wnorm_mono_enorm_ae [TopologicalSpace ε] {ε' : Type*} [TopologicalSpace ε'] [ENorm ε']
  {f : α → ε} {g : α → ε'} (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    wnorm f p μ ≤ wnorm g p μ :=
  eLorentzNorm_mono_enorm_ae hf h

theorem wnorm_indicator_const {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {a : ε}
    {s : Set α} (hs : MeasurableSet s) (h₀ : p ≠ 0) (h₁ : p ≠ ⊤) :
    wnorm (s.indicator (Function.const α a)) p μ = μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  simp [← eLorentzNorm_eq_wnorm, eLorentzNorm_indicator_const hs, h₀, h₁]

lemma wnorm_iSup_of_monotone {α : Type*} [MeasurableSpace α] {p : ℝ≥0∞} (hp : p ≠ 0)
    (f : ℕ → α → ℝ≥0∞) (hf : Monotone f) (μ : Measure α) (hf' : ∀ n, AEMeasurable (f n) μ) :
    wnorm (fun x => ⨆ n, f n x) p μ = ⨆ n, wnorm (f n) p μ := by
  have hm : ∀ n, AEStronglyMeasurable (f n) μ := fun n ↦ (hf' n).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun x ↦ ⨆ n, f n x) μ := (AEMeasurable.iSup hf').aestronglyMeasurable
  by_cases hp' : p = ⊤
  · simp_rw [hp', wnorm_top hm', wnorm_top (hm _)]
    apply eLpNormEssSup_iSup
  · simp_rw [wnorm_ne_top hm' hp hp', wnorm_ne_top (hm _) hp hp']
    unfold wnorm' distribution
    rw [iSup_comm]; congr with t
    rw [←ENNReal.mul_iSup]; congr
    rw [←(iSup_rpow (toReal_pos hp hp' |> inv_pos_of_pos))]; congr
    simp only [enorm_eq_self]
    rw [←Monotone.measure_iUnion, iUnion_ofPred]
    · congr with x
      exact lt_iSup_iff
    · apply monotone_ofPred
      intro x
      exact monotone_lt.comp (hf.apply₂ x)

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWLp [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma memWLp_iff_memLorentz [TopologicalSpace ε] : MemWLp f p μ ↔ MemLorentz f p ∞ μ :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨h.aestronglyMeasurable, h⟩⟩

lemma MemWLp.aeStronglyMeasurable [TopologicalSpace ε] (hf : MemWLp f p μ) : AEStronglyMeasurable f μ := hf.1

lemma MemWLp.wnorm_lt_top [TopologicalSpace ε] (hf : MemWLp f p μ) : wnorm f p μ < ⊤ := hf.2

lemma MemWLp.ennreal_toReal {f : α → ℝ≥0∞} (hf : MemWLp f p μ) :
    MemWLp (ENNReal.toReal ∘ f) p μ :=
  ⟨hf.aeStronglyMeasurable.ennreal_toReal, wnorm_toReal_le.trans_lt hf.2⟩

/-- If a function `f` is `MemWLp` for `p ≠ 0`, then its norm is almost everywhere finite. -/
-- XXX: is this a good finiteness rule, given that `p` might be hard to infer?
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem MemWLp.ae_ne_top [TopologicalSpace ε] (hf : MemWLp f p μ) (hp_zero : p ≠ 0) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
  by_cases hp_inf : p = ∞
  · rw [hp_inf, MemWLp, wnorm_top hf.1] at hf
    simp_rw [← lt_top_iff_ne_top]
    exact ae_lt_of_essSup_lt hf.2
  set A := {x | ‖f x‖ₑ = ∞} with hA
  replace hf : wnorm' f p.toReal μ < ∞ := wnorm_ne_top hf.1 hp_zero hp_inf ▸ hf.2
  unfold wnorm' at hf
  rw [Filter.eventually_iff, mem_ae_iff]
  simp only [ne_eq, compl_def, mem_ofPred_eq, Decidable.not_not, ← hA]
  have hp_toReal_zero := toReal_ne_zero.mpr ⟨hp_zero, hp_inf⟩
  have h1 (t : ℝ≥0) : μ A ≤ distribution f t μ := by
    refine μ.mono ?_
    simp_all only [ofPred_subset_ofPred, coe_lt_top, implies_true, A]
  set C := ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹
  by_cases hC_zero : C = 0
  · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
    specialize hC_zero 1
    simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_gt, and_false, or_false,
      false_or] at hC_zero
    exact measure_mono_null (ofPred_subset_ofPred.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
  by_contra h
  have h2 : C < ∞ := hf
  have h3 (t : ℝ≥0) : distribution f t μ ≤ (C / t) ^ p.toReal := by
    rw [← rpow_inv_rpow hp_toReal_zero (distribution ..)]
    refine rpow_le_rpow ?_ toReal_nonneg
    rw [ENNReal.le_div_iff_mul_le (Or.inr hC_zero) (Or.inl coe_ne_top), mul_comm]
    exact le_iSup_iff.mpr fun _ a ↦ a t
  have h4 (t : ℝ≥0) : μ A ≤ (C / t) ^ p.toReal := (h1 t).trans (h3 t)
  have h5 : μ A ≤ μ A / 2 := by
    convert h4 (C * (2 / μ A) ^ p.toReal⁻¹).toNNReal
    rw [coe_toNNReal (mul_ne_top h2.ne (rpow_ne_top_of_nonneg (by simp)
      (ENNReal.div_ne_top ofNat_ne_top h)))]
    nth_rw 1 [← mul_one C]
    rw [ENNReal.mul_div_mul_left _ _ hC_zero h2.ne_top, div_rpow_of_nonneg _ _ toReal_nonneg,
      ENNReal.rpow_inv_rpow hp_toReal_zero, ENNReal.one_rpow, one_div,
        ENNReal.inv_div (Or.inr ofNat_ne_top) (Or.inr (NeZero.ne' 2).symm)]
  have h6 : μ A = 0 := by
    convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top
      (rpow_ne_top_of_nonneg toReal_nonneg ((div_one C).symm ▸ h2.ne_top))
      (h4 1))).mt h5.not_gt
    tauto
  exact h h6

end ENorm

section ContinuousENorm

variable [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}

lemma wnorm'_le_eLpNorm' (hf : AEStronglyMeasurable f μ) {p : ℝ} (p0 : 0 < p) :
    wnorm' f p μ ≤ eLpNorm' f p μ := by
  refine iSup_le (fun t ↦ ?_)
  simp_rw [distribution, eLpNorm']
  have p0' : 0 ≤ 1 / p := (div_pos one_pos p0).le
  have set_eq : {x | ofNNReal t < ‖f x‖ₑ} = {x | ofNNReal t ^ p < ‖f x‖ₑ ^ p} := by
    simp [ENNReal.rpow_lt_rpow_iff p0]
  have : ofNNReal t = (ofNNReal t ^ p) ^ (1 / p) := by simp [p0.ne']
  nth_rewrite 1 [inv_eq_one_div p, this, ← mul_rpow_of_nonneg _ _ p0', set_eq]
  refine rpow_le_rpow ?_ p0'
  refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const p) (ofNNReal t ^ p)
  gcongr
  exact fun x ↦ le_of_lt x

lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 0 < p) :
    wnorm f p μ ≤ eLpNorm f p μ := by
  by_cases h : p = ⊤
  · simp [h, wnorm_top hf]
  · rw [wnorm_ne_top hf hp.ne' h, eLpNorm_eq_eLpNorm' hp.ne' h]
    exact wnorm'_le_eLpNorm' hf (toReal_pos hp.ne' h)

lemma MemLp.memWLp (hp : 0 < p) (hf : MemLp f p μ) : MemWLp f p μ :=
  memWLp_iff_memLorentz.mpr (MemLorentz_of_MemLorentz_ge hp le_top (MemLorentz_iff_MemLp.mpr hf))

lemma wnorm_eq_zero_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) (hp : p ≠ 0) :
    wnorm f p μ = 0 ↔ (fun x ↦ ‖f x‖ₑ) =ᵐ[μ] 0 := by
  rw [← eLorentzNorm_eq_wnorm, ← eLorentzNorm_enorm hf, eLorentzNorm_eq_zero_iff hp (by simp)]

end ContinuousENorm

section ConstSMul

variable [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [NormSMulClass 𝕜 E]

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  [Module ℝ≥0 ε'] [ENormSMulClass ℝ≥0 ε'] [ContinuousConstSMul ℝ≥0 ε'] in
lemma wnorm_const_smul_le (hp : p ≠ 0) {f : α → ε'} (hf : AEStronglyMeasurable f μ) (k : ℝ≥0) :
    wnorm (k • f) p μ ≤ ‖k‖ₑ * wnorm f p μ := by
  by_cases ptop : p = ⊤
  · simp only [ptop, wnorm_top hf, wnorm_top (hf.const_smul k)]
    apply eLpNormEssSup_const_nnreal_smul_le
  rw [wnorm_ne_top (hf.const_smul k) hp ptop, wnorm_ne_top hf hp ptop]
  simp only [wnorm', iSup_le_iff]
  by_cases k_zero : k = 0
  · simp [distribution, k_zero, toReal_pos hp ptop]
  simp only [distribution_smul_left k_zero]
  intro t
  rw [ENNReal.mul_iSup]
  have : t * distribution f (t / ‖k‖ₑ) μ ^ p.toReal⁻¹ =
      ‖k‖ₑ * ((t / ‖k‖ₑ) * distribution f (t / ‖k‖ₑ) μ ^ p.toReal⁻¹) := by
    nth_rewrite 1 [← mul_div_cancel₀ t k_zero]
    simp only [coe_mul, mul_assoc]
    congr
    exact coe_div k_zero
  rw [this]
  apply le_iSup_of_le (↑t / ↑‖k‖₊)
  apply le_of_eq
  congr <;> exact (coe_div k_zero).symm

lemma wnorm_const_smul_le' [IsBoundedSMul 𝕜 E] (hp : p ≠ 0) {f : α → E}
    (hf : AEStronglyMeasurable f μ) (k : 𝕜) :
    wnorm (k • f) p μ ≤ ‖k‖ₑ * wnorm f p μ := by
  have hkf : AEStronglyMeasurable (k • f) μ := aestronglyMeasurable_const.smul hf
  by_cases ptop : p = ⊤
  · simp only [ptop, wnorm_top hf, wnorm_top hkf]
    apply eLpNormEssSup_const_smul_le
  rw [wnorm_ne_top hkf hp ptop, wnorm_ne_top hf hp ptop]
  simp only [wnorm', iSup_le_iff]
  by_cases k_zero : k = 0
  · simp [distribution, k_zero, toReal_pos hp ptop]
  simp only [distribution_smul_left' k_zero]
  intro t
  rw [ENNReal.mul_iSup]
  have knorm_ne_zero : ‖k‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr k_zero
  have : t * distribution f (t / ‖k‖ₑ) μ ^ p.toReal⁻¹ =
      ‖k‖ₑ * ((t / ‖k‖ₑ) * distribution f (t / ‖k‖ₑ) μ ^ p.toReal⁻¹) := by
    nth_rewrite 1 [← mul_div_cancel₀ t knorm_ne_zero]
    simp only [coe_mul, mul_assoc]
    congr
    exact coe_div knorm_ne_zero
  erw [this]
  apply le_iSup_of_le (↑t / ↑‖k‖₊)
  apply le_of_eq
  congr <;> exact (coe_div knorm_ne_zero).symm

end ConstSMul

end MeasureTheory
