module

public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic
public import Carleson.ToMathlib.Rearrangement

@[expose] public section

/-!
# Weak `L^p` norm

The weak `L^p` (quasi)norm `wnorm f p μ` and the predicate `MemWLp`.
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
    wnorm' f p μ = ⨆ t : ℝ≥0, t ^ p⁻¹ * rearrangement f t μ := by
  have hp' : 0 < p⁻¹ := by simpa
  unfold wnorm'
  calc _
    _ = ⨆ t, t * distribution f t μ ^ p⁻¹ := by
      rw [ENNReal.iSup_ennreal]
      simp only [distibution_top, left_eq_sup]
      rw [ENNReal.zero_rpow_of_pos hp', mul_zero]
      exact zero_le
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
        exact zero_le
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use (a / t) ^ p
    rw [ENNReal.rpow_rpow_inv hp.ne']
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
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
        exact zero_le
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use a / t ^ p⁻¹
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
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
    _ ≤ ↑t * distribution g (↑t) μ ^ p⁻¹ := by gcongr
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
      rwa [ENNReal.coe_toNNReal ha', indicator, ite_eq_left_of_eq_true, ENNReal.top_rpow_of_pos hp, ENNReal.mul_top]
      · simpa
      · simp only [mem_Iio, eq_iff_iff, iff_true]
        apply ENNReal.div_lt_of_lt_mul'
        nth_rw 1 [← one_mul ‖a‖ₑ]
        gcongr
        norm_num
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
    rw [indicator_apply, ite_eq_left_of_eq_true, ENNReal.coe_toNNReal hc', ENNReal.div_mul_cancel]
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

lemma wnorm_iSup_of_monotone {α : Type*} [MeasurableSpace α] {p : ℝ≥0∞} (hp : p ≠ 0) (f : ℕ → α → ℝ≥0∞)
    (hf : Monotone f) (μ : Measure α) : wnorm (fun x => ⨆ n, f n x) p μ = ⨆ n, wnorm (f n) p μ := by
  unfold wnorm wnorm' distribution
  split_ifs with hp'
  · apply eLpNormEssSup_iSup
  · rw [iSup_comm]; congr with t
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

lemma wnorm_eq_zero_iff {f : α → ε} {p : ℝ≥0∞} (hp : p ≠ 0) :
    wnorm f p μ = 0 ↔ (fun x ↦ ‖f x‖ₑ) =ᵐ[μ] 0 := by
  unfold wnorm
  split_ifs with h₀
  · rw [← eLpNorm_exponent_top, ← eLpNorm_enorm f]
    exact eLpNormEssSup_eq_zero_iff
  · refine Iff.trans ⟨?_, ?_⟩ eLpNormEssSup_eq_zero_iff <;> intro h
    · have iSup_wnorm := iSup_eq_zero.mp h
      by_contra h₁
      have : 0 < eLpNormEssSup f μ := pos_iff_ne_zero.mpr h₁
      unfold eLpNormEssSup at this
      rw [essSup_eq_sInf] at this
      let b := (min (sInf {a : ℝ≥0∞ | μ {x | a < ‖f x‖ₑ} = 0}) 1) / 2
      have b_lt_inf : b < min (sInf {a : ℝ≥0∞ | μ {x | a < ‖f x‖ₑ} = 0}) 1 :=
        ENNReal.half_lt_self (lt_min this zero_lt_one).ne'
          (lt_of_le_of_lt (min_le_right _ 1) one_lt_top).ne
      have meas_ne_zero : μ {x | b < ‖f x‖ₑ} ≠ 0 := by
        intro h
        have obs : sInf {a | μ {x | a < ‖f x‖ₑ} = 0} ≤ b := csInf_le' h
        contrapose! obs
        calc
        _ < _ := b_lt_inf
        _ ≤ _ := min_le_left ..
      have b_ne_0 : b ≠ 0 := (ENNReal.half_pos (lt_min this zero_lt_one).ne').ne'
      have p_toReal_inv_pos : 0 < p.toReal⁻¹ := inv_pos_of_pos (toReal_pos hp h₀)
      have coe_b : ENNReal.ofNNReal b.toNNReal = b := coe_toNNReal b_lt_inf.ne_top
      have : distribution f b μ = 0 := by
        refine (rpow_eq_zero_iff_of_pos p_toReal_inv_pos).mp ?_
        refine eq_zero_of_ne_zero_of_mul_left_eq_zero b_ne_0 ?_
        rw [← coe_b]
        exact iSup_wnorm b.toNNReal
      exact meas_ne_zero this
    · refine iSup_eq_zero.mpr fun t ↦ mul_eq_zero.mpr
        (Or.inr ((rpow_eq_zero_iff_of_pos (inv_pos_of_pos (toReal_pos hp h₀))).mpr (nonpos_iff_eq_zero.mp ?_)))
      calc
        _ ≤ distribution f 0 μ := by gcongr; exact zero_le
        _ = distribution f (eLpNormEssSup f μ) μ := by congr; exact h.symm
        _ = 0 := distribution_eLpNormEssSup

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
  · simp [h, wnorm, eLpNorm]
  · simpa [h, wnorm, eLpNorm, hp.ne'] using wnorm'_le_eLpNorm' hf (toReal_pos hp.ne' h)

lemma MemLp.memWLp (hp : 0 < p) (hf : MemLp f p μ) : MemWLp f p μ :=
  ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩

end ContinuousENorm

section ConstSMul

variable [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [NormSMulClass 𝕜 E]

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  [Module ℝ≥0 ε'] [ENormSMulClass ℝ≥0 ε'] in
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
end ConstSMul

end MeasureTheory
