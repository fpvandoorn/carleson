import Carleson.ToMathlib.Rearrangement

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
    wnorm' f p μ = ⨆ t : ℝ≥0, t ^ p⁻¹ * rearrangement f t μ := by
  have hp' : 0 < p⁻¹ := by simpa
  unfold wnorm'
  calc _
    _ = ⨆ t, t * distribution f t μ ^ p⁻¹ := by
      rw [ENNReal.iSup_ennreal]
      simp only [distibution_top, left_eq_sup]
      rw [ENNReal.zero_rpow_of_pos hp', mul_zero]
      exact zero_le _
  symm
  calc _
    _ = ⨆ t, t ^ p⁻¹ * rearrangement f t μ := by
      rw [ENNReal.iSup_ennreal]
      simp
  symm
  apply le_antisymm
  · apply iSup_le
    intro t
    apply le_of_forall_lt
    intro a ha
    by_cases! a_ne_zero : a = 0
    · rw [a_ne_zero]
      rw [a_ne_zero] at ha
      rw [lt_iSup_iff]
      contrapose! ha
      simp only [nonpos_iff_eq_zero, mul_eq_zero] at *
      simp_rw [ENNReal.rpow_eq_zero_iff_of_pos hp'] at *
      by_cases ht : t = 0
      · left
        assumption
      · right
        rw [← nonpos_iff_eq_zero]
        apply _root_.le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add, ← rearrangement_le_iff_distribution_le]
        rcases ha ε with h | h
        · order
        rw [h]
        exact zero_le t
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use (a / t) ^ p
    rw [ENNReal.rpow_rpow_inv hp.ne']
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
    · exact a_ne_top
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul, lt_rearrangement_iff_lt_distribution]
    apply (ENNReal.lt_rpow_inv_iff hp).mp
    rwa [ENNReal.div_lt_iff (by right; assumption) (by right; assumption), mul_comm]
  · apply iSup_le
    intro t
    apply le_of_forall_lt
    intro a ha
    by_cases! a_ne_zero : a = 0
    · rw [a_ne_zero]
      rw [a_ne_zero] at ha
      rw [lt_iSup_iff]
      contrapose! ha
      simp only [nonpos_iff_eq_zero, mul_eq_zero] at *
      simp_rw [ENNReal.rpow_eq_zero_iff_of_pos hp'] at *
      by_cases ht : t = 0
      · left
        assumption
      · right
        rw [← nonpos_iff_eq_zero]
        apply _root_.le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add, rearrangement_le_iff_distribution_le]
        rcases ha ε with h | h
        · order
        rw [h]
        exact zero_le t
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use a / t ^ p⁻¹
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
    · exact a_ne_top
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul]
    gcongr
    rw [← lt_rearrangement_iff_lt_distribution]
    rwa [ENNReal.div_lt_iff (by right; assumption) (by right; assumption), mul_comm]

/-- The weak L^p norm of a function. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (p.toReal) μ

@[simp]
lemma wnorm_zero : wnorm f 0 μ = ∞ := by
  simp [wnorm, wnorm'_zero]

@[simp]
lemma wnorm_top : wnorm f ⊤ μ = eLpNormEssSup f μ := by simp [wnorm]

lemma wnorm_ne_top (h : p ≠ ⊤) : wnorm f p μ = wnorm' f p.toReal μ := by simp [wnorm, h]

lemma wnorm_coe {p : ℝ≥0} : wnorm f p μ = wnorm' f p μ := by simp [wnorm]

lemma wnorm_ofReal {p : ℝ} (hp : 0 ≤ p) : wnorm f (.ofReal p) μ = wnorm' f p μ := by
  simp [wnorm, hp]

lemma wnorm_toReal_le {f : α → ℝ≥0∞} {p : ℝ≥0∞} :
    wnorm (ENNReal.toReal ∘ f) p μ ≤ wnorm f p μ := by
  induction p
  · simp [eLpNormEssSup_toReal_le]
  exact wnorm'_toReal_le toReal_nonneg

lemma wnorm_toReal_eq {f : α → ℝ≥0∞} {p : ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    wnorm (ENNReal.toReal ∘ f) p μ = wnorm f p μ := by
  simp_rw [wnorm, eLpNormEssSup_toReal_eq hf, wnorm'_toReal_eq hf]

theorem wnorm_eq_iSup_rpow_mul_rearrangement {p : ℝ≥0∞} (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  {f : α → ε} {μ : Measure α} :
    wnorm f p μ = ⨆ t : ℝ≥0, t ^ p.toReal⁻¹ * rearrangement f t μ := by
  rw [wnorm_ne_top p_ne_top]
  apply wnorm'_eq_iSup_rpow_mul_rearrangement (ENNReal.toReal_pos p_nonzero p_ne_top)

lemma wnorm'_mono_enorm_ae {ε' : Type*} [ENorm ε'] {f : α → ε} {g : α → ε'} {p : ℝ} (hp : 0 ≤ p)
  (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    wnorm' f p μ ≤ wnorm' g p μ := by
  unfold wnorm'
  apply iSup_le
  intro t
  calc _
    _ ≤ ↑t * distribution g (↑t) μ ^ p⁻¹ := by
      gcongr
      assumption
  apply le_iSup _ t

lemma wnorm_mono_enorm_ae {ε' : Type*} [ENorm ε'] {f : α → ε} {g : α → ε'}
  (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    wnorm f p μ ≤ wnorm g p μ := by
  unfold wnorm
  split_ifs with h'
  · exact essSup_mono_ae h
  · exact wnorm'_mono_enorm_ae (by simp) h

theorem wnorm_indicator_const {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {a : ε} {s : Set α} {p : ℝ≥0∞}
  (h₀ : ¬p = 0) (h₁ : ¬p = ⊤) :
    wnorm (s.indicator (Function.const α a)) p μ = μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  have hp : 0 < p.toReal⁻¹ := by
    simp only [inv_pos]
    exact ENNReal.toReal_pos h₀ h₁
  rw [wnorm_ne_top h₁]
  unfold wnorm'
  simp_rw [distribution_indicator_const]
  apply le_antisymm
  · apply iSup_le
    intro t
    unfold indicator
    split_ifs with ht
    · rw [mul_comm]
      gcongr
      exact ht.le
    · rw [ENNReal.zero_rpow_of_pos]
      · simp
      simp only [inv_pos]
      apply ENNReal.toReal_pos h₀ h₁
  · by_cases h : μ s = 0
    · rw [h]
      simp only [indicator_zero]
      rw [ENNReal.zero_rpow_of_pos hp]
      simp
    by_cases ha : ‖a‖ₑ = 0
    · rw [ha]
      simp
    by_cases ha' : ‖a‖ₑ = ⊤
    · rw [ha']
      simp only [mem_Iio, coe_lt_top, indicator_of_mem]
      rw [← ENNReal.iSup_mul, mul_comm]
      gcongr
      simp only [top_le_iff]
      exact WithTop.iSup_coe_eq_top'
    by_cases h' : μ s = ⊤
    · rw [h', ENNReal.top_rpow_of_pos hp, ENNReal.top_mul ha]
      simp only [top_le_iff]
      rw [iSup_eq_top]
      intro b hb
      use ‖a‖ₑ.toNNReal / 2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, coe_div, coe_ofNat]
      rwa [ENNReal.coe_toNNReal ha', indicator, ite_cond_eq_true, ENNReal.top_rpow_of_pos hp, ENNReal.mul_top]
      · simpa
      · simp only [mem_Iio, eq_iff_iff, iff_true]
        apply ENNReal.div_lt_of_lt_mul'
        nth_rw 1 [← one_mul ‖a‖ₑ]
        gcongr
        · exact ha'
        · norm_num
    apply le_of_forall_lt_imp_le_of_dense
    intro c hc
    apply le_iSup_of_le (c / (μ s ^ p.toReal⁻¹)).toNNReal
    have hc' : c / μ s ^ p.toReal⁻¹ ≠ ⊤ := by
      contrapose! hc
      rw [div_eq_top] at hc
      rcases hc with ⟨_, hc⟩ | hc
      · rw [ENNReal.rpow_eq_zero_iff_of_pos hp] at hc
        contradiction
      · rw [hc.1]
        exact le_top
    rw [indicator_apply, ite_cond_eq_true, ENNReal.coe_toNNReal hc', ENNReal.div_mul_cancel]
    · simp only [ne_eq, ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', not_or, not_and, not_lt,
      toReal_nonneg, implies_true, and_true]
      intro h
      contradiction
    · simp only [ne_eq, rpow_eq_top_iff, inv_neg'', inv_pos, not_or, not_and, not_lt,
      toReal_nonneg, implies_true, true_and]
      intro h
      contradiction
    · rw [ENNReal.coe_toNNReal hc']
      simp only [mem_Iio, eq_iff_iff, iff_true]
      apply ENNReal.div_lt_of_lt_mul' hc


/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWLp [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma MemWLp_zero [TopologicalSpace ε] : ¬ MemWLp f 0 μ := by
  simp [MemWLp, wnorm_zero]

lemma MemWLp.aeStronglyMeasurable [TopologicalSpace ε] (hf : MemWLp f p μ) : AEStronglyMeasurable f μ := hf.1

lemma MemWLp.wnorm_lt_top [TopologicalSpace ε] (hf : MemWLp f p μ) : wnorm f p μ < ⊤ := hf.2

lemma MemWLp.ennreal_toReal {f : α → ℝ≥0∞} (hf : MemWLp f p μ) :
    MemWLp (ENNReal.toReal ∘ f) p μ :=
  ⟨hf.aeStronglyMeasurable.ennreal_toReal, wnorm_toReal_le.trans_lt hf.2⟩

/-- If a function `f` is `MemWLp`, then its norm is almost everywhere finite. -/
-- XXX: is this a good finiteness rule, given that `p` might be hard to infer?
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem MemWLp.ae_ne_top [TopologicalSpace ε] (hf : MemWLp f p μ) : ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
  by_cases hp_inf : p = ∞
  · rw [hp_inf] at hf
    simp_rw [← lt_top_iff_ne_top]
    exact ae_lt_of_essSup_lt hf.2
  by_cases hp_zero : p = 0
  · exact (MemWLp_zero <| hp_zero ▸ hf).elim
  set A := {x | ‖f x‖ₑ = ∞} with hA
  simp only [MemWLp, wnorm, wnorm', hp_inf] at hf
  rw [Filter.eventually_iff, mem_ae_iff]
  simp only [ne_eq, compl_def, mem_setOf_eq, Decidable.not_not, ← hA]
  have hp_toReal_zero := toReal_ne_zero.mpr ⟨hp_zero, hp_inf⟩
  have h1 (t : ℝ≥0) : μ A ≤ distribution f t μ := by
    refine μ.mono ?_
    simp_all only [setOf_subset_setOf, coe_lt_top, implies_true, A]
  set C := ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹
  by_cases hC_zero : C = 0
  · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
    specialize hC_zero 1
    simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_gt, and_false, or_false,
      false_or] at hC_zero
    exact measure_mono_null (setOf_subset_setOf.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
  by_contra h
  have h2 : C < ∞ := by aesop
  have h3 (t : ℝ≥0) : distribution f t μ ≤ (C / t) ^ p.toReal := by
    rw [← rpow_inv_rpow hp_toReal_zero (distribution ..)]
    refine rpow_le_rpow ?_ toReal_nonneg
    rw [ENNReal.le_div_iff_mul_le (Or.inr hC_zero) (Or.inl coe_ne_top), mul_comm]
    exact le_iSup_iff.mpr fun _ a ↦ a t
  have h4 (t : ℝ≥0) : μ A ≤ (C / t) ^ p.toReal := (h1 t).trans (h3 t)
  have h5 : μ A ≤ μ A / 2 := by
    convert h4 (C * (2 / μ A) ^ p.toReal⁻¹).toNNReal
    rw [coe_toNNReal (by finiteness)]
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
  simp only [Filter.Eventually, ae, mem_ofCountableUnion]
  rw [Measure.restrict_apply₀']
  · convert measure_empty (μ := μ); ext; simpa using le_of_lt
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

lemma distribution_lt_top (hf : MemLp f p μ) (p_pos : 0 < p) (p_ne_top : p ≠ ∞)
    {t : ℝ≥0} (ht : 0 < t) :
    distribution f t μ < ∞ := by
  have := wnorm'_le_eLpNorm' hf.1 (toReal_pos p_pos.ne' p_ne_top)
  rw [← eLpNorm_eq_eLpNorm' p_pos.ne' p_ne_top] at this
  have := this.trans_lt hf.2
  rw [wnorm', iSup_lt_iff] at this
  rcases this with ⟨b,b_lt_top, h⟩
  have := (h t).trans_lt b_lt_top
  rw [mul_lt_top_iff] at this
  rcases this with ⟨t_lt_top, h⟩| (t_zero| h)
  · rwa [rpow_lt_top_iff_of_pos] at h
    simp only [inv_pos]
    exact toReal_pos p_pos.ne' p_ne_top
  · rw [ENNReal.coe_eq_zero] at t_zero
    exfalso
    exact ht.ne' t_zero
  · rw [ENNReal.rpow_eq_zero_iff_of_pos (by simp only [inv_pos]; exact toReal_pos p_pos.ne' p_ne_top)] at h
    rw [h]
    simp only [zero_lt_top]

lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 0 < p) :
    wnorm f p μ ≤ eLpNorm f p μ := by
  by_cases h : p = ⊤
  · simp [h, wnorm, eLpNorm]
  · simpa [h, wnorm, eLpNorm, hp.ne'] using wnorm'_le_eLpNorm' hf (toReal_pos hp.ne' h)

lemma MemLp.memWLp (hp : 0 < p) (hf : MemLp f p μ) : MemWLp f p μ :=
  ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩

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

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, BoundedFiniteSupport f μ →
  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

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

-- unused, probably delete
open Classical in
lemma toReal_ofReal_preimage' {s : Set ℝ≥0∞} : ENNReal.toReal ⁻¹' (ENNReal.ofReal ⁻¹' s) =
    if ∞ ∈ s ↔ 0 ∈ s then s else if 0 ∈ s then s ∪ {∞} else s \ {∞} := by
  split_ifs <;> ext (_|_) <;> simp_all

-- move
open Classical in
lemma toReal_ofReal_preimage {s : Set ℝ≥0∞} : letI t := ENNReal.toReal ⁻¹' (ENNReal.ofReal ⁻¹' s)
  s = if ∞ ∈ s ↔ 0 ∈ s then t else if 0 ∈ s then t \ {∞} else t ∪ {∞} := by
  split_ifs <;> ext (_|_) <;> simp_all

-- move
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
  · simp_rw [preimage_diff]
    exact this.diff hf
  · simp_rw [preimage_union]
    exact this.union hf

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

lemma HasBoundedStrongType.const_smul {T : (α → ε₁) → α' → ℝ≥0∞}
    (h : HasBoundedStrongType T p p' μ ν c) (r : ℝ≥0) :
    HasBoundedStrongType (r • T) p p' μ ν (r • c) := by
  intro f hf
  rw [Pi.smul_apply, MeasureTheory.eLpNorm_const_smul']
  exact ⟨(h f hf).1.const_smul _, le_of_le_of_eq (mul_le_mul_right (h f hf).2 ‖r‖ₑ) (by simp; rfl)⟩

end HasBoundedStrongType

variable {f g : α → ε}

section

variable {ε ε' : Type*} [TopologicalSpace ε] [ENorm ε]
variable [TopologicalSpace ε'] [ENormedSpace ε']

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
    enorm_smul_eq_mul (c := c) _, ENNReal.div_mul_cancel h₀ coe_ne_top, mul_comm]

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

lemma wnorm_const_smul_le (hp : p ≠ 0) {f : α → ε'} (k : ℝ≥0) :
    wnorm (k • f) p μ ≤ ‖k‖ₑ * wnorm f p μ := by
  by_cases ptop : p = ⊤
  · simp only [ptop, wnorm_top]
    apply eLpNormEssSup_const_nnreal_smul_le
  simp only [wnorm, ptop, ↓reduceIte, wnorm', iSup_le_iff]
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

lemma wnorm_const_smul_le' [IsBoundedSMul 𝕜 E] (hp : p ≠ 0) {f : α → E} (k : 𝕜) :
    wnorm (k • f) p μ ≤ ‖k‖ₑ * wnorm f p μ := by
  by_cases ptop : p = ⊤
  · simp only [ptop, wnorm_top]
    apply eLpNormEssSup_const_smul_le
  simp only [wnorm, ptop, ↓reduceIte, wnorm', iSup_le_iff]
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

lemma HasWeakType.const_smul [ContinuousConstSMul ℝ≥0 ε']
    {T : (α → ε) → (α' → ε')} (hp' : p' ≠ 0) {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (k : ℝ≥0) :
    HasWeakType (k • T) p p' μ ν (k * c) := by
  intro f hf
  refine ⟨(h f hf).1.const_smul k, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ k * wnorm (T f) p' ν := by simpa using wnorm_const_smul_le hp' _
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
    _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le' hp']
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
    simp only [mem_union, mem_setOf_eq] at hz ⊢
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

section Layercake

variable [TopologicalSpace ε] [ContinuousENorm ε]

/-- The layer-cake theorem, or Cavalieri's principle for functions into a space with a continuous
enorm. -/
lemma lintegral_norm_pow_eq_distribution {f : α → ε} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ := by
  have := lintegral_rpow_eq_lintegral_meas_lt_mul μ (f := fun x ↦ ENNReal.toReal ‖f x‖ₑ)
    (Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg) hf.enorm.ennreal_toReal hp
  simp only [mul_comm (μ _), ne_eq, ofReal_ne_top, not_false_eq_true, ← lintegral_const_mul',
    ← mul_assoc, ofReal_mul, distribution, hp.le] at this ⊢
  -- TODO: clean up this whole proof
  by_cases! ae_finite : μ {x | ‖f x‖ₑ = ∞} = 0
  · -- main case
    convert this using 1
    · apply lintegral_congr_ae
      rw [Filter.eventuallyEq_iff_exists_mem]
      use {x | ‖f x‖ₑ ≠ ∞}
      rw [mem_ae_iff, compl_setOf]
      simp only [ne_eq, Decidable.not_not]
      use ae_finite
      intro x hx
      dsimp only
      rw [toReal_rpow, ofReal_toReal (by finiteness)]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    congr 1
    symm
    apply measure_eq_measure_of_null_diff
    · intro x hx
      simp only [mem_setOf_eq] at *
      rwa [ofReal_lt_iff_lt_toReal ht.le]
      by_contra hfx
      rw [hfx] at hx
      simp only [toReal_top] at hx
      linarith [hx, mem_Ioi.mp ht]
    dsimp [sdiff, Set.diff]
    apply measure_mono_null _ ae_finite
    intro x hx
    dsimp only [mem_setOf_eq] at *
    by_contra hf_top
    rw [ofReal_lt_iff_lt_toReal ht.le hf_top] at hx
    exact hx.2 hx.1
  · rw [lintegral_eq_top_of_measure_eq_top_ne_zero]
    · symm
      rw [← enorm_pos] at ae_finite
      rw [eq_top_iff]
      calc
      _ = ENNReal.ofReal p *
          (∫⁻ (t : ℝ) in Ioi 0, ENNReal.ofReal (t ^ (p - 1))) * μ {x | ‖f x‖ₑ = ∞} := by
        convert (top_mul ae_finite.ne').symm
        convert mul_top (ENNReal.ofReal_pos.mpr hp).ne'
        rw [← not_ne_iff, lintegral_ofReal_ne_top_iff_integrable]; rotate_left
        · exact (measurable_id.pow_const (p - 1)).aestronglyMeasurable.restrict
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x mx ↦ ?_
          simp_rw [Pi.zero_apply]; rw [mem_Ioi] at mx; positivity
        exact not_integrableOn_Ioi_rpow (p - 1)
      _ = ∫⁻ (t : ℝ) in Ioi 0, ENNReal.ofReal p * ENNReal.ofReal (t ^ (p - 1))
            * μ {x | ‖f x‖ₑ = ∞} := by
        rw [lintegral_mul_const, lintegral_const_mul] <;> fun_prop
      _ ≤ ∫⁻ (t : ℝ) in Ioi 0, ENNReal.ofReal p * ENNReal.ofReal (t ^ (p - 1))
            * μ {x | ENNReal.ofReal t < ‖f x‖ₑ} := by
        gcongr with t x
        intro hfx
        simp [hfx]
    · fun_prop
    · simp_rw [rpow_eq_top_iff_of_pos hp]
      exact ae_finite

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`. -/
lemma eLpNorm_pow_eq_distribution {f : α → ε} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0} (hp : 0 < p) :
    eLpNorm f p μ ^ (p : ℝ) =
    ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 < (p : ℝ) := hp
  simp_rw [eLpNorm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
    ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`, without
    taking powers. -/
lemma eLpNorm_eq_distribution {f : α → ε} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (.ofReal p) μ =
    (ENNReal.ofReal p  * ∫⁻ t in Ioi (0 : ℝ), distribution f (.ofReal t) μ *
        ENNReal.ofReal (t ^ (p - 1)) ) ^ p⁻¹ := by
  unfold eLpNorm
  split_ifs with sgn_p sz_p
  · exact False.elim (not_le_of_gt hp (ofReal_eq_zero.mp sgn_p))
  · exact False.elim (coe_ne_top sz_p)
  · unfold eLpNorm'
    rw [toReal_ofReal hp.le, one_div]
    congr 1
    rw [← lintegral_const_mul' _ _ (by finiteness), lintegral_norm_pow_eq_distribution hf hp]
    congr 1 with x; rw [ofReal_mul] <;> [ring; positivity]

lemma lintegral_pow_mul_distribution {f : α → ε} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : -1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * distribution f (.ofReal t) μ =
    ENNReal.ofReal (p + 1)⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ (p + 1) ∂μ := by
  have h2p : 0 < p + 1 := by linarith
  have h3p : 0 ≤ p + 1 := by linarith
  have h4p : p + 1 ≠ 0 := by linarith
  simp [*, -ofReal_inv_of_pos, lintegral_norm_pow_eq_distribution, ← lintegral_const_mul',
    ← ofReal_mul, ← mul_assoc]

end Layercake

end MeasureTheory
