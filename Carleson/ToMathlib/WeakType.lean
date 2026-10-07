module

public import Carleson.ToMathlib.BoundedFiniteSupport
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic
public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

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

-- unused, probably delete
open Classical in
lemma toReal_ofReal_preimage' {s : Set ℝ≥0∞} : ENNReal.toReal ⁻¹' (ENNReal.ofReal ⁻¹' s) =
    if ∞ ∈ s ↔ 0 ∈ s then s else if 0 ∈ s then s ∪ {∞} else s \ {∞} := by
  split_ifs <;> ext (_|_) <;> simp_all

open Classical in
lemma toReal_ofReal_preimage {s : Set ℝ≥0∞} : letI t := ENNReal.toReal ⁻¹' (ENNReal.ofReal ⁻¹' s)
  s = if ∞ ∈ s ↔ 0 ∈ s then t else if 0 ∈ s then t \ {∞} else t ∪ {∞} := by
  split_ifs <;> ext (_|_) <;> simp_all

lemma aestronglyMeasurable_ennreal_toReal_iff {f : α → ℝ≥0∞}
    (hf : NullMeasurableSet (f ⁻¹' {∞}) μ) :
    AEStronglyMeasurable (ENNReal.toReal ∘ f) μ ↔ AEStronglyMeasurable f μ := by
  refine ⟨fun h ↦ AEMeasurable.aestronglyMeasurable (NullMeasurable.aemeasurable fun s hs ↦ ?_),
    fun h ↦ h.ennreal_toReal⟩
  have := h.aemeasurable.nullMeasurable (hs.preimage measurable_ofReal)
  simp_rw [preimage_comp] at this
  rw [toReal_ofReal_preimage (s := s)]
  split_ifs
  · exact this
  · simp_rw [preimage_sdiff]
    exact this.diff hf
  · simp_rw [preimage_union]
    exact this.union hf

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

lemma distribution_le [MeasurableSpace ε] [OpensMeasurableSpace ε]
    {c : ℝ≥0∞} (hc : c ≠ 0) {μ : Measure α} (hf : AEMeasurable f μ) :
    distribution f c μ ≤ c⁻¹ * (∫⁻ y, ‖f y‖ₑ ∂μ) := by
  by_cases hc_top : c = ⊤
  · simp [hc_top]
  apply (mul_le_iff_le_inv hc hc_top).mp
  simp_rw [distribution, ← setLIntegral_one, ← lintegral_const_mul' _ _ hc_top, mul_one]
  refine le_trans (lintegral_mono_ae ?_) (setLIntegral_le_lintegral _ _)
  apply ae_restrict_mem₀ _ |>.mono
  · grind
  · exact hf.enorm.nullMeasurableSet_preimage measurableSet_Ioi

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

section Defs

variable [ENorm ε₁] [ENorm ε₂] [TopologicalSpace ε₁] [TopologicalSpace ε₂]
/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from `L^p` to weak `L^q`.
`HasWeakType T p p' μ ν c` means that `T` has weak type `(p, p')` w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasWeakType`. -/
def HasBoundedWeakType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, BoundedFiniteSupport f μ →
  AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- An operator has strong type `(p, q)` if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasStrongType {α α' : Type*}
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

-- `HasBoundedStrongType` has moved to `Defs.lean`

end Defs

/-! ### Lemmas about `HasWeakType` -/

section HasWeakType

variable [TopologicalSpace ε₁] [ContinuousENorm ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {f₁ : α → ε₁}

lemma HasWeakType.memWLp (h : HasWeakType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemWLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasWeakType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasWeakType T p p' μ ν c) :
    HasWeakType (T · · |>.toReal) p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, wnorm_toReal_le.trans (h f hf).2 ⟩

lemma hasWeakType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
    HasWeakType (T · · |>.toReal) p p' μ ν c ↔ HasWeakType T p p' μ ν c := by
  refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
  obtain ⟨h1, h2⟩ := h f hf
  refine ⟨?_, by rwa [← wnorm_toReal_eq (hT f hf)]⟩
  rwa [← aestronglyMeasurable_ennreal_toReal_iff]
  refine .of_null <| measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [hT f hf] with x hx
  simp [hx]

lemma hasWeakType_iSup_of_monotone {f : ℕ → (α → ε₁) → (α' → ℝ≥0∞)} (hf : Monotone f)
    (hp' : p' ≠ 0) (hwtf : ∀ n, HasWeakType (f n) p p' μ ν c) :
    HasWeakType (fun u x => ⨆ n, f n u x) p p' μ ν c := by
  intro v mlpv
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    -- should StronglyMeasurable.iSup exist?
    apply AEMeasurable.iSup
    exact (hwtf · v mlpv |>.left.aemeasurable)
  · rw [wnorm_iSup_of_monotone hp' _ (hf.apply₂ v) _ (hwtf · v mlpv |>.left.aemeasurable)]
    exact iSup_le fun n => hwtf n v mlpv |>.right

-- lemma comp_left [MeasurableSpace ε₂] {ν' : Measure ε₂} {f : ε₂ → ε₃} (h : HasWeakType T p p' μ ν c)
--     (hf : MemLp f p' ν') :
--     HasWeakType (f ∘ T ·) p p' μ ν c := by
--   intro u hu
--   refine ⟨h u hu |>.1.comp_measurable hf.1, ?_⟩

end HasWeakType

/-! ### Lemmas about `HasBoundedWeakType` -/

section HasBoundedWeakType

variable [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ENorm ε₂]
    {f₁ : α → ε₁}

lemma HasBoundedWeakType.memWLp (h : HasBoundedWeakType T p p' μ ν c)
    (hf₁ : BoundedFiniteSupport f₁ μ) (hc : c < ⊤ := by finiteness) :
    MemWLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc (hf₁.memLp p).2⟩

lemma HasWeakType.hasBoundedWeakType (h : HasWeakType T p p' μ ν c) :
    HasBoundedWeakType T p p' μ ν c :=
  fun f hf ↦ h f (hf.memLp _)

end HasBoundedWeakType

/-! ### Lemmas about `HasStrongType` -/

section HasStrongType

variable [TopologicalSpace ε₁] [ContinuousENorm ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {f₁ : α → ε₁}

lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasStrongType.hasWeakType (hp' : 0 < p')
    (h : HasStrongType T p p' μ ν c) : HasWeakType T p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1, wnorm_le_eLpNorm (h f hf).1 hp' |>.trans (h f hf).2⟩

lemma HasStrongType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasStrongType T p p' μ ν c) :
    HasStrongType (T · · |>.toReal) p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, eLpNorm_toReal_le.trans (h f hf).2 ⟩

lemma hasStrongType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
    HasStrongType (T · · |>.toReal) p p' μ ν c ↔ HasStrongType T p p' μ ν c := by
  refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
  obtain ⟨h1, h2⟩ := h f hf
  refine ⟨?_, by rwa [← eLpNorm_toReal_eq (hT f hf)]⟩
  rwa [← aestronglyMeasurable_ennreal_toReal_iff]
  refine .of_null <| measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [hT f hf] with x hx
  simp [hx]

lemma hasStrongType_iSup_of_monotone {f : ℕ → (α → ε₁) → (α' → ℝ≥0∞)} (hf : Monotone f)
    (hstf : ∀ n, HasStrongType (f n) p p' μ ν c) :
    HasStrongType (fun u x => ⨆ n, f n u x) p p' μ ν c := by
  intro v mlpv
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    -- should StronglyMeasurable.iSup exist?
    apply AEMeasurable.iSup
    exact (hstf · v mlpv |>.left.aemeasurable)
  · rw [eLpNorm_iSup']
    · exact iSup_le fun n => hstf n v mlpv |>.right
    · exact fun n => hstf n v mlpv |>.left.aemeasurable
    · apply ae_of_all
      intro a
      exact (hf.apply₂ _).apply₂ _

end HasStrongType

/-! ### Lemmas about `HasBoundedStrongType` -/

section HasBoundedStrongType

variable [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {f₁ : α → ε₁}

lemma HasBoundedStrongType.memLp (h : HasBoundedStrongType T p p' μ ν c)
    (hf₁ : BoundedFiniteSupport f₁ μ) (hc : c < ⊤ := by finiteness) :
    MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc (hf₁.memLp _).2⟩

lemma HasStrongType.hasBoundedStrongType (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c :=
  fun f hf ↦ h f (hf.memLp _)

lemma HasBoundedStrongType.hasBoundedWeakType (hp' : 0 < p')
    (h : HasBoundedStrongType T p p' μ ν c) :
    HasBoundedWeakType T p p' μ ν c :=
  fun f hf ↦
    ⟨(h f hf).1, wnorm_le_eLpNorm (h f hf).1 hp' |>.trans (h f hf).2⟩

set_option backward.isDefEq.respectTransparency false in
lemma HasBoundedStrongType.const_smul {T : (α → ε₁) → α' → ℝ≥0∞}
    (h : HasBoundedStrongType T p p' μ ν c) (r : ℝ≥0) :
    HasBoundedStrongType (r • T) p p' μ ν (r • c) := by
  intro f hf
  rw [Pi.smul_apply, MeasureTheory.eLpNorm_const_smul' (ε' := ℝ≥0∞)]
  exact ⟨(h f hf).1.const_smul _, le_of_le_of_eq (mul_le_mul_right (h f hf).2 ‖r‖ₑ) (by simp; rfl)⟩

end HasBoundedStrongType

variable {f g : α → ε}

section

variable {ε ε' : Type*} [TopologicalSpace ε] [ENorm ε]
variable [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε'] [SMul ℝ≥0 ε']
  [ENormSMulClass ℝ≥0 ε']

-- TODO: this lemma and its primed version could be unified using a `NormedSemifield` typeclass
-- (which includes NNReal and normed fields like ℝ and ℂ), i.e. assuming 𝕜 is a normed semifield.
-- Investigate if this is worthwhile when upstreaming this to mathlib.
lemma distribution_smul_left {f : α → ε'} {c : ℝ≥0} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖ₑ) μ := by
  have h₀ : ‖c‖ₑ ≠ 0 := by
    have : ‖c‖ₑ = ‖(c : ℝ≥0∞)‖ₑ := rfl
    rw [this, enorm_ne_zero]
    exact ENNReal.coe_ne_zero.mpr hc
  unfold distribution
  congr with x
  simp only [Pi.smul_apply]
  rw [← @ENNReal.mul_lt_mul_iff_left (t / ‖c‖ₑ) _ (‖c‖ₑ) h₀ coe_ne_top,
    enorm_smul _, ENNReal.div_mul_cancel h₀ coe_ne_top, mul_comm]

variable [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [NormSMulClass 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [NormSMulClass 𝕜 E']

lemma distribution_smul_left' {f : α → E} {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖ₑ) μ := by
  have h₀ : ‖c‖ₑ ≠ 0 := enorm_ne_zero.mpr hc
  unfold distribution
  congr with x
  simp only [Pi.smul_apply]
  rw [← @ENNReal.mul_lt_mul_iff_left (t / ‖c‖ₑ) _ (‖c‖ₑ) h₀ coe_ne_top,
    enorm_smul _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]

lemma HasStrongType.const_smul [ContinuousConstSMul ℝ≥0 ε']
    {T : (α → ε) → (α' → ε')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (k : ℝ≥0) :
    HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  refine fun f hf ↦
    ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_nnreal_smul_le.trans ?_⟩
  rw [mul_assoc]
  gcongr
  exact (h f hf).2

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
variable {𝕜 E' : Type*} [NormedRing 𝕜] [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E'] in
lemma HasStrongType.const_smul'
    {T : (α → ε) → (α' → E')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (k : 𝕜) :
    HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le.trans ?_⟩
  rw [mul_assoc]
  gcongr
  exact (h f hf).2

lemma HasStrongType.const_mul
    {T : (α → ε) → (α' → ℝ≥0∞)} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (e : ℝ≥0) :
    HasStrongType (fun f x ↦ e * T f x) p p' μ ν (‖e‖ₑ * c) :=
  h.const_smul e

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
variable {E' : Type*} [NormedRing E'] in
lemma HasStrongType.const_mul'
    {T : (α → ε) → (α' → E')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (e : E') :
    HasStrongType (fun f x ↦ e * T f x) p p' μ ν (‖e‖ₑ * c) :=
  h.const_smul' e

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

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  [Module ℝ≥0 ε'] [ENormSMulClass ℝ≥0 ε'] in
lemma HasWeakType.const_smul [ContinuousConstSMul ℝ≥0 ε']
    {T : (α → ε) → (α' → ε')} (hp' : p' ≠ 0) {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (k : ℝ≥0) :
    HasWeakType (k • T) p p' μ ν (k * c) := by
  intro f hf
  refine ⟨(h f hf).1.const_smul k, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ k * wnorm (T f) p' ν := by simpa using wnorm_const_smul_le hp' (h f hf).1 _ (ε' := ε')
    _ ≤ k * (c * eLpNorm f p μ) := by
      gcongr
      apply (h f hf).2
    _ = (k * c) * eLpNorm f p μ := by rw [mul_assoc]

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
lemma HasWeakType.const_smul' [IsBoundedSMul 𝕜 E'] {T : (α → ε) → (α' → E')} (hp' : p' ≠ 0)
    {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (k : 𝕜) :
    HasWeakType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  intro f hf
  refine ⟨aestronglyMeasurable_const.smul (h f hf).1, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le' hp' (h f hf).1]
    _ ≤ ‖k‖ₑ * (c * eLpNorm f p μ) := by
      gcongr
      apply (h f hf).2
    _ = (‖k‖ₑ * c) * eLpNorm f p μ := by rw [mul_assoc]

lemma HasWeakType.const_mul {T : (α → ε) → (α' → ℝ≥0∞)} (hp' : p' ≠ 0)
    {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (e : ℝ≥0) :
    HasWeakType (fun f x ↦ e * T f x) p p' μ ν (e * c) :=
  h.const_smul hp' e

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
lemma HasWeakType.const_mul' {T : (α → ε) → (α' → 𝕜)} (hp' : p' ≠ 0)
    {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (e : 𝕜) :
    HasWeakType (fun f x ↦ e * T f x) p p' μ ν (‖e‖ₑ * c) :=
  h.const_smul' hp' e

end

section NormedGroup

variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃) :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖ₑ * t * s) μ ≤
    distribution f t μ + distribution g s μ := by
  have h₀ : {x | ‖L‖ₑ * t * s < ‖(fun x ↦ (L (f x)) (g x)) x‖ₑ} ⊆
      {x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ} := fun z hz ↦ by
    simp only [mem_union, mem_ofPred_eq] at hz ⊢
    contrapose! hz
    calc
      ‖(L (f z)) (g z)‖ₑ ≤ ‖L‖ₑ * ‖f z‖ₑ * ‖g z‖ₑ := by calc
          _ ≤ ‖L (f z)‖ₑ * ‖g z‖ₑ := ContinuousLinearMap.le_opENorm (L (f z)) (g z)
          _ ≤ ‖L‖ₑ * ‖f z‖ₑ * ‖g z‖ₑ :=
            mul_le_mul' (ContinuousLinearMap.le_opENorm L (f z)) (by rfl)
      _ ≤ _ := mul_le_mul' (mul_le_mul_right hz.1 ‖L‖ₑ) hz.2
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ}) := measure_mono h₀
    _ ≤ _ := measure_union_le _ _

end NormedGroup


end MeasureTheory
