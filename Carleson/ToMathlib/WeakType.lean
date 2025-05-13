import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.Misc

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

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Todo: rename to something more Mathlib-appropriate. -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

@[gcongr]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : (Antitone (fun t ↦ distribution f t μ)) :=
  fun _ _ h ↦ distribution_mono_right h

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) :=
  Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  fun_prop

lemma distribution_toReal_le {f : α → ℝ≥0∞} :
    distribution (ENNReal.toReal ∘ f) t μ ≤ distribution f t μ := by
  simp_rw [distribution]
  apply measure_mono
  simp_rw [comp_apply, enorm_eq_self, setOf_subset_setOf]
  exact fun x hx ↦ hx.trans_le enorm_toReal_le

lemma distribution_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    distribution (ENNReal.toReal ∘ f) t μ = distribution f t μ := by
  refine measure_congr (.set_eq ?_)
  filter_upwards [hf] with x hx
  simp [hx]

lemma distribution_add_le_of_enorm {A : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  unfold distribution
  have h₁ : μ ({x | A * (t + s) < ‖f x‖ₑ} \
      ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
    apply measure_mono_null ?_ h
    intro x
    simp only [mem_diff, mem_setOf_eq, mem_union, not_or, not_lt, mem_compl_iff, not_le, and_imp]
    refine fun h₁ h₂ h₃ ↦ lt_of_le_of_lt ?_ h₁
    gcongr
  calc
    μ {x | A * (t + s) < ‖f x‖ₑ}
      ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := measure_mono_ae' h₁
    _ ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := measure_union_le _ _

lemma approx_above_superset (t₀ : ℝ≥0∞) :
    ⋃ n, (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}) n = {x | t₀ < ‖f x‖ₑ} := by
  ext y
  constructor <;> intro h
  · obtain ⟨n, wn⟩ := exists_exists_eq_and.mp h
    calc
      t₀ ≤ t₀ + (↑n)⁻¹ := le_self_add
      _  < ‖f y‖ₑ      := wn
  · have h₁ : Iio (‖f y‖ₑ - t₀) ∈ 𝓝 0 := Iio_mem_nhds (tsub_pos_of_lt h)
    have h₂ := ENNReal.tendsto_inv_nat_nhds_zero h₁
    simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at h₂
    rcases h₂ with ⟨n, wn⟩
    simpa using ⟨n, lt_tsub_iff_left.mp (wn n (Nat.le_refl n))⟩

lemma tendsto_measure_iUnion_distribution (t₀ : ℝ≥0∞) :
    Filter.Tendsto (⇑μ ∘ (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}))
      Filter.atTop (nhds (μ ({x | t₀ < ‖f x‖ₑ}))) := by
  rw [← approx_above_superset]
  refine tendsto_measure_iUnion_atTop fun a b h x h₁ ↦ ?_
  calc
    _ ≤ t₀ + (↑a)⁻¹ := by gcongr
    _ < _ := h₁

lemma select_neighborhood_distribution (t₀ : ℝ≥0∞) (l : ℝ≥0∞)
    (hu : l < distribution f t₀ μ) :
    ∃ n : ℕ, l < distribution f (t₀ + (↑n)⁻¹) μ := by
  have h := (tendsto_measure_iUnion_distribution t₀) (Ioi_mem_nhds hu)
  simp only [mem_map, mem_atTop_sets, mem_preimage, comp_apply, mem_Ioi] at h
  rcases h with ⟨n, wn⟩
  exact ⟨n, wn n (Nat.le_refl n)⟩

lemma continuousWithinAt_distribution (t₀ : ℝ≥0∞) :
    ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
  rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
  · rw [t₀top]
    apply continuousWithinAt_of_not_mem_closure
    simp
  · unfold ContinuousWithinAt
    rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
    -- Case: distribution f t₀ μ = ⊤
    · simp only [db_top, ENNReal.tendsto_nhds_top_iff_nnreal]
      intro b
      have h₀ : ∃ n : ℕ, ↑b < distribution f (t₀ + (↑n)⁻¹) μ :=
        select_neighborhood_distribution _ _ (db_top ▸ coe_lt_top)
      rcases h₀ with ⟨n, wn⟩
      refine eventually_mem_set.mpr (mem_inf_iff_superset.mpr ⟨Iio (t₀ + (↑n)⁻¹), ?_, ?_⟩)
      · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top
          (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
      · exact ⟨Ioi t₀, by simp, fun z h₁ ↦ wn.trans_le (distribution_mono_right (le_of_lt h₁.1))⟩
    -- Case: distribution f t₀ μ < ⊤
    · refine (ENNReal.tendsto_nhds db_not_top.ne_top).mpr fun ε ε_gt_0 ↦
        eventually_mem_set.mpr (mem_inf_iff_superset.mpr ?_)
      rcases eq_zero_or_pos (distribution f t₀ μ) with db_zero | db_not_zero
      -- Case: distribution f t₀ μ = 0
      · use Ico 0 (t₀ + 1)
        constructor
        · refine IsOpen.mem_nhds isOpen_Ico_zero ?_
          simp [lt_add_right t₀nottop.ne_top one_ne_zero]
        · use Ioi t₀
          refine ⟨by simp, fun z hz ↦ ?_⟩
          rw [db_zero]
          simp only [zero_le, tsub_eq_zero_of_le, zero_add]
          have h₂ : distribution f z μ ≤ distribution f t₀ μ :=
            distribution_mono_right (le_of_lt hz.2)
          rw [db_zero] at h₂
          change Icc 0 ε (distribution f z μ)
          rw [nonpos_iff_eq_zero.mp h₂]
          exact ⟨zero_le 0, zero_le ε⟩
      -- Case: 0 < distribution f t₀ μ
      · obtain ⟨n, wn⟩ :=
          select_neighborhood_distribution t₀ _ (ENNReal.sub_lt_self db_not_top.ne_top
              (ne_of_lt db_not_zero).symm (ne_of_lt ε_gt_0).symm)
        use Iio (t₀ + (↑n)⁻¹)
        constructor
        · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top
            (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
        · refine ⟨Ioi t₀, by simp, fun z h ↦ ⟨?_, ?_⟩⟩
          · calc
              distribution f t₀ μ - ε
                ≤ distribution f (t₀ + (↑n)⁻¹) μ := le_of_lt wn
              _ ≤ distribution f z μ             := distribution_mono_right (le_of_lt h.1)
          · calc
              distribution f z μ
                ≤ distribution f t₀ μ := distribution_mono_right (le_of_lt h.2)
              _ ≤ distribution f t₀ μ + ε := le_self_add

/- The lemmas below are almost already in Mathlib, see
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`. -/

-- /-- The layer-cake theorem, or Cavalieri's principle for functions into `ℝ≥0∞` -/
-- lemma lintegral_norm_pow_eq_measure_lt {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
--     {p : ℝ} (hp : 1 ≤ p) :
--     ∫⁻ x, (f x) ^ p ∂μ =
--     ∫⁻ t in Ioi (0 : ℝ), .ofReal (p * t ^ (p - 1)) * μ { x | ENNReal.ofReal t < f x } := by
--   sorry

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
  exact distribution_toReal_le

lemma wnorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    wnorm' (ENNReal.toReal ∘ f) p μ = wnorm' f p μ := by
  simp_rw [wnorm', distribution_toReal_eq hf]

/-- The weak L^p norm of a function. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

lemma wnorm_zero : wnorm f 0 μ = ∞ := by
  simp [wnorm, wnorm'_zero]

@[simp]
lemma wnorm_top : wnorm f ⊤ μ = eLpNormEssSup f μ := by simp [wnorm]

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

end ENorm

section ContinuousENorm

variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε₁] [ContinuousENorm ε₁]
    [TopologicalSpace ε₂] [ContinuousENorm ε₂] [TopologicalSpace ε₃] [ContinuousENorm ε₃]
    {f : α → ε} {f₁ : α → ε₁}

lemma wnorm'_le_eLpNorm' (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    wnorm' f p μ ≤ eLpNorm' f p μ := by
  refine iSup_le (fun t ↦ ?_)
  simp_rw [distribution, eLpNorm']
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have p0' : 0 ≤ 1 / p := (div_pos one_pos p0).le
  have set_eq : {x | ofNNReal t < ‖f x‖ₑ} = {x | ofNNReal t ^ p < ‖f x‖ₑ ^ p} := by
    simp [ENNReal.rpow_lt_rpow_iff p0]
  have : ofNNReal t = (ofNNReal t ^ p) ^ (1 / p) := by simp [p0.ne.symm]
  nth_rewrite 1 [inv_eq_one_div p, this, ← mul_rpow_of_nonneg _ _ p0', set_eq]
  refine rpow_le_rpow ?_ p0'
  refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const p) (ofNNReal t ^ p)
  gcongr
  exact setOf_subset_setOf.mpr (fun _ h ↦ h.le)

lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wnorm f p μ ≤ eLpNorm f p μ := by
  by_cases h : p = ⊤
  · simp [h, wnorm, eLpNorm]
  · have p0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne.symm
    simpa [h, wnorm, eLpNorm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWLp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma MemLp.memWLp (hp : 1 ≤ p) (hf : MemLp f p μ) : MemWLp f p μ :=
  ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩

lemma MemWLp_zero : ¬ MemWLp f 0 μ := by
  simp [MemWLp, wnorm_zero]

lemma MemWLp.aeStronglyMeasurable (hf : MemWLp f p μ) : AEStronglyMeasurable f μ := hf.1

lemma MemWLp.wnorm_lt_top (hf : MemWLp f p μ) : wnorm f p μ < ⊤ := hf.2

lemma MemWLp.ennreal_toReal {f : α → ℝ≥0∞} (hf : MemWLp f p μ) :
    MemWLp (ENNReal.toReal ∘ f) p μ :=
  ⟨hf.aeStronglyMeasurable.ennreal_toReal, wnorm_toReal_le.trans_lt hf.2⟩

/-- If a function `f` is `MemWLp`, then its norm is almost everywhere finite. -/
theorem MemWLp.ae_ne_top {f : α → ε} {μ : Measure α} (hf : MemWLp f p μ) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
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
    simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_lt, and_false, or_false,
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
    rw [coe_toNNReal ?_]
    swap
    · refine mul_ne_top h2.ne_top (rpow_ne_top_of_nonneg (inv_nonneg.mpr toReal_nonneg) ?_)
      simp [div_eq_top, h]
    nth_rw 1 [← mul_one C]
    rw [ENNReal.mul_div_mul_left _ _ hC_zero h2.ne_top, div_rpow_of_nonneg _ _ toReal_nonneg,
      ENNReal.rpow_inv_rpow hp_toReal_zero, ENNReal.one_rpow, one_div,
        ENNReal.inv_div (Or.inr ofNat_ne_top) (Or.inr (NeZero.ne' 2).symm)]
  have h6 : μ A = 0 := by
    convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top (rpow_ne_top_of_nonneg
      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt h5.not_lt
    tauto
  exact h h6

/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from `L^p` to weak `L^q`.
`HasWeakType T p p' μ ν c` means that `T` has weak type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasWeakType`. -/
def HasBoundedWeakType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
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
  ∀ f : α → ε₁, MemLp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-! ### Lemmas about `HasWeakType` -/

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
  refine .of_null <| measure_zero_iff_ae_nmem.mpr ?_
  filter_upwards [hT f hf] with x hx
  simp [hx]

-- lemma comp_left [MeasurableSpace ε₂] {ν' : Measure ε₂} {f : ε₂ → ε₃} (h : HasWeakType T p p' μ ν c)
--     (hf : MemLp f p' ν') :
--     HasWeakType (f ∘ T ·) p p' μ ν c := by
--   intro u hu
--   refine ⟨h u hu |>.1.comp_measurable hf.1, ?_⟩

/-! ### Lemmas about `HasBoundedWeakType` -/

lemma HasBoundedWeakType.memWLp [Zero ε₁] (h : HasBoundedWeakType T p p' μ ν c)
    (hf₁ : MemLp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞)
    (hc : c < ⊤ := by finiteness) :
    MemWLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasWeakType.hasBoundedWeakType [Zero ε₁] (h : HasWeakType T p p' μ ν c) :
    HasBoundedWeakType T p p' μ ν c :=
  fun f hf _ _ ↦ h f hf

/-! ### Lemmas about `HasStrongType` -/

lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasStrongType.hasWeakType (hp' : 1 ≤ p')
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
  refine .of_null <| measure_zero_iff_ae_nmem.mpr ?_
  filter_upwards [hT f hf] with x hx
  simp [hx]

/-! ### Lemmas about `HasBoundedStrongType` -/

lemma HasBoundedStrongType.memLp [Zero ε₁] (h : HasBoundedStrongType T p p' μ ν c)
    (hf₁ : MemLp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞)
    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasStrongType.hasBoundedStrongType [Zero ε₁] (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c :=
  fun f hf _ _ ↦ h f hf

lemma HasBoundedStrongType.hasBoundedWeakType [Zero ε₁] (hp' : 1 ≤ p')
    (h : HasBoundedStrongType T p p' μ ν c) : HasBoundedWeakType T p p' μ ν c :=
  fun f hf h2f h3f ↦
    ⟨(h f hf h2f h3f).1, wnorm_le_eLpNorm (h f hf h2f h3f).1 hp' |>.trans (h f hf h2f h3f).2⟩

section distribution

variable {f g : α → ε}

@[gcongr]
lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    distribution f t μ ≤ distribution g t μ := by
  have h₀ : {x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ} ⊆ {x | ¬‖f x‖ₑ ≤ ‖g x‖ₑ} := fun x ↦ by
    simp_rw [mem_diff, mem_setOf_eq, not_lt, not_le, and_imp]
    intro i₁ i₂; simpa using i₂.trans_lt i₁
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ})
      + μ ({x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ}) := measure_le_inter_add_diff μ _ _
    _ = μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ}) := by rw [measure_mono_null h₀ h, add_zero]
    _ ≤ _ := by apply measure_mono; simp

@[gcongr]
lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h₂ : t ≤ s) :
    distribution f s μ ≤ distribution g t μ :=
  (distribution_mono_left h₁).trans (distribution_mono_right h₂)

lemma distribution_snormEssSup : distribution f (eLpNormEssSup f μ) μ = 0 :=
  meas_essSup_lt -- meas_eLpNormEssSup_lt

lemma distribution_add_le' {A : ℝ≥0∞} {g₁ g₂ : α → ε}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  apply distribution_add_le_of_enorm
  simp (discharger := positivity) [← ofReal_mul, ← ofReal_add, h]

lemma distribution_add_le {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f g : α → ε} :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ :=
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ}) := by
      refine measure_mono fun x h ↦ ?_
      simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
      contrapose! h
      exact (ENormedAddMonoid.enorm_add_le _ _).trans (add_le_add h.1 h.2)
    _ ≤ _ := measure_union_le _ _

end distribution

end ContinuousENorm

section NormedGroup

variable {f g : α → ε}

section

variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
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
  simp only [Pi.smul_apply, mem_setOf_eq]
  rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖ₑ) _ (‖c‖ₑ) h₀ coe_ne_top,
    enorm_smul_eq_mul (c := c) _, ENNReal.div_mul_cancel h₀ coe_ne_top, mul_comm]

variable [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E']

lemma distribution_smul_left' {f : α → E} {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖ₑ) μ := by
  have h₀ : ‖c‖ₑ ≠ 0 := enorm_ne_zero.mpr hc
  unfold distribution
  congr with x
  simp only [Pi.smul_apply, mem_setOf_eq]
  rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖ₑ) _ (‖c‖ₑ) h₀ coe_ne_top,
    enorm_smul _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]

lemma HasStrongType.const_smul [ContinuousConstSMul ℝ≥0 ε']
    {T : (α → ε) → (α' → ε')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (k : ℝ≥0) :
    HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le'.trans ?_⟩
  simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc]
  gcongr
  exact (h f hf).2

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
variable {𝕜 E' : Type*} [NormedRing 𝕜] [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E'] in
lemma HasStrongType.const_smul'
    {T : (α → ε) → (α' → E')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (k : 𝕜) :
    HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le.trans ?_⟩
  simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc]
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
    apply eLpNormEssSup_const_smul_le'
  simp only [wnorm, ptop, ↓reduceIte, wnorm', iSup_le_iff]
  by_cases k_zero : k = 0
  · simp only [distribution, k_zero, Pi.smul_apply, zero_smul, enorm_zero, not_lt_zero', setOf_false,
      measure_empty, coe_lt_enorm, zero_mul, nonpos_iff_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero,
      ENNReal.rpow_eq_zero_iff, inv_pos, true_and, zero_ne_top, inv_neg'', false_and, or_false]
    intro _
    right
    exact toReal_pos hp ptop
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

lemma wnorm_const_smul_le' (hp : p ≠ 0) {f : α → E} (k : 𝕜) :
    wnorm (k • f) p μ ≤ ‖k‖ₑ * wnorm f p μ := by
  by_cases ptop : p = ⊤
  · simp only [ptop, wnorm_top]
    apply eLpNormEssSup_const_smul_le
  simp only [wnorm, ptop, ↓reduceIte, wnorm', iSup_le_iff]
  by_cases k_zero : k = 0
  · simp only [distribution, k_zero, Pi.smul_apply, zero_smul, enorm_zero, not_lt_zero', setOf_false,
      measure_empty, coe_lt_enorm, zero_mul, nonpos_iff_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero,
      ENNReal.rpow_eq_zero_iff, inv_pos, true_and, zero_ne_top, inv_neg'', false_and, or_false]
    intro _
    right
    exact toReal_pos hp ptop
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
    HasWeakType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  intro f hf
  refine ⟨(h f hf).1.const_smul k, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le hp']
    _ ≤ ‖k‖ₑ * (c * eLpNorm f p μ) := by
      gcongr
      apply (h f hf).2
    _ = (‖k‖ₑ * c) * eLpNorm f p μ := by simp [coe_mul, mul_assoc]

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
lemma HasWeakType.const_smul' {T : (α → ε) → (α' → E')} (hp' : p' ≠ 0)
    {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (k : 𝕜) :
    HasWeakType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  intro f hf
  refine ⟨aestronglyMeasurable_const.smul (h f hf).1, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le' hp']
    _ ≤ ‖k‖ₑ * (c * eLpNorm f p μ) := by
      gcongr
      apply (h f hf).2
    _ = (‖k‖ₑ * c) * eLpNorm f p μ := by simp [coe_mul, mul_assoc]

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

variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃) :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖ₑ * t * s) μ ≤
    distribution f t μ + distribution g s μ := by
  have h₀ : {x | ‖L‖ₑ * t * s < ‖(fun x ↦ (L (f x)) (g x)) x‖ₑ} ⊆
      {x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ} := fun z hz ↦ by
    simp only [mem_union, mem_setOf_eq, Pi.add_apply] at hz ⊢
    contrapose! hz
    calc
      ‖(L (f z)) (g z)‖ₑ ≤ ‖L‖ₑ * ‖f z‖ₑ * ‖g z‖ₑ := by calc
          _ ≤ ‖L (f z)‖ₑ * ‖g z‖ₑ := ContinuousLinearMap.le_opENorm (L (f z)) (g z)
          _ ≤ ‖L‖ₑ * ‖f z‖ₑ * ‖g z‖ₑ :=
            mul_le_mul' (ContinuousLinearMap.le_opENorm L (f z)) (by rfl)
      _ ≤ _ := mul_le_mul' (mul_le_mul_left' hz.1 ‖L‖ₑ) hz.2
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ}) := measure_mono h₀
    _ ≤ _ := measure_union_le _ _

section BorelSpace

variable [TopologicalSpace ε] [ContinuousENorm ε]
  [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

/-- The layer-cake theorem, or Cavalieri's principle for functions into a normed group. -/
lemma lintegral_norm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 ≤ p := hp.le
  have := lintegral_rpow_eq_lintegral_meas_lt_mul μ (f := fun x ↦ ‖f x‖)
    (Eventually.of_forall fun x ↦ norm_nonneg _) hf.norm hp
  simp only [← enorm_eq_nnnorm, norm_nonneg, ← ofReal_rpow_of_nonneg, mul_comm (μ _), ne_eq,
    ofReal_ne_top, not_false_eq_true, ← lintegral_const_mul', ← mul_assoc,
    ← ofReal_norm_eq_enorm, ofReal_mul, distribution, h2p] at this ⊢
  convert this using 1
  refine setLIntegral_congr_fun measurableSet_Ioi (Eventually.of_forall fun x hx ↦ ?_)
  simp_rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hx)]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`. -/
lemma eLpNorm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0} (hp : 0 < p) :
    eLpNorm f p μ ^ (p : ℝ) =
    ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 < (p : ℝ) := hp
  simp_rw [eLpNorm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
    ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`, without
    taking powers. -/
lemma eLpNorm_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (.ofReal p) μ =
    (ENNReal.ofReal p  * ∫⁻ t in Ioi (0 : ℝ), distribution f (.ofReal t) μ *
        ENNReal.ofReal (t ^ (p - 1)) ) ^ p⁻¹ := by
  unfold eLpNorm
  split_ifs with sgn_p sz_p
  · exact False.elim (not_le_of_lt hp (ofReal_eq_zero.mp sgn_p))
  · exact False.elim (coe_ne_top sz_p)
  · unfold eLpNorm'
    rw [toReal_ofReal (le_of_lt hp), one_div]
    congr 1
    rw [← lintegral_const_mul']
    on_goal 2 => exact coe_ne_top
    rw [lintegral_norm_pow_eq_distribution hf hp]
    congr 1 with x; rw [ofReal_mul] <;> [ring; positivity]

lemma lintegral_pow_mul_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : -1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * distribution f (.ofReal t) μ =
    ENNReal.ofReal (p + 1)⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ (p + 1) ∂μ := by
  have h2p : 0 < p + 1 := by linarith
  have h3p : 0 ≤ p + 1 := by linarith
  have h4p : p + 1 ≠ 0 := by linarith
  simp [*, lintegral_norm_pow_eq_distribution, ← lintegral_const_mul', ← ofReal_mul, ← mul_assoc]

end BorelSpace

end NormedGroup

end MeasureTheory
