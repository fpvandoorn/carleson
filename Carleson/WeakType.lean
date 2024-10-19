import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

variable {α α' 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)
  {f g : α → E} {t s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}

-- #check meas_ge_le_mul_pow_eLpNorm -- Chebyshev's inequality

namespace MeasureTheory
/- If we need more properties of `E`, we can add `[RCLike E]` *instead of* the above type-classes-/
-- #check _root_.RCLike

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution [NNNorm E] (f : α → E) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖₊ }

@[gcongr]
lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    distribution f t μ ≤ distribution g t μ := by
  have h₀ : {x | t < ‖f x‖₊} \ {x | t < ‖g x‖₊} ⊆ {x | ¬‖f x‖ ≤ ‖g x‖} := fun x ↦ by
    simp only [mem_diff, mem_setOf_eq, not_lt, not_le, and_imp]
    intro i₁ i₂; simpa using i₂.trans_lt i₁
  calc
    _ ≤ μ ({x | t < ‖f x‖₊} ∩ {x | t < ‖g x‖₊})
      + μ ({x | t < ‖f x‖₊} \ {x | t < ‖g x‖₊}) := measure_le_inter_add_diff μ _ _
    _ = μ ({x | t < ‖f x‖₊} ∩ {x | t < ‖g x‖₊}) := by rw [measure_mono_null h₀ h, add_zero]
    _ ≤ _ := by apply measure_mono; simp

@[gcongr]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : (Antitone (fun t ↦ distribution f t μ)) :=
  fun _ _ h ↦ distribution_mono_right h

@[gcongr]
lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) (h₂ : t ≤ s) :
    distribution f s μ ≤ distribution g t μ :=
  (distribution_mono_left h₁).trans (distribution_mono_right h₂)

lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) : ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ :=
  (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)

lemma distribution_snormEssSup : distribution f (eLpNormEssSup f μ) μ = 0 :=
  meas_eLpNormEssSup_lt

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) :=
  Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  fun_prop

/-@[measurability, deprecated]
lemma distribution_measurable_from_real :
    Measurable (fun t : ℝ ↦ distribution f (.ofReal t) μ) :=
  distribution_measurable measurable_ofReal-/

lemma ENNNorm_add_le (y z : E) : ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ :=
  (toReal_le_toReal coe_ne_top coe_ne_top).mp (nnnorm_add_le ..)

lemma distribution_smul_left {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖₊) μ := by
  unfold distribution
  have h₀ : ofNNReal ‖c‖₊ ≠ 0 := ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hc)
  congr; ext x
  simp only [Pi.smul_apply, mem_setOf_eq]
  rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖₊) _ (‖c‖₊) h₀ coe_ne_top,
    ENNNorm_absolute_homogeneous _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]

lemma measure_mono_ae' {A B : Set α} (h : μ (B \ A) = 0) :
    μ B ≤ μ A := by
  apply measure_mono_ae
  change μ {x | ¬ B x ≤ A x} = 0
  simp only [le_Prop_eq, Classical.not_imp]
  exact h

lemma distribution_add_le' {A : ℝ} (hA : A ≥ 0) (g₁ g₂ : α → E)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ A * (‖g₁ x‖ + ‖g₂ x‖)) :
    distribution f (ENNReal.ofReal A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  unfold distribution
  have h₁ : μ ({x | ENNReal.ofReal A * (t + s) < ↑‖f x‖₊} \
      ({x | t < ↑‖g₁ x‖₊} ∪ {x | s < ↑‖g₂ x‖₊})) = 0 := by
    apply measure_mono_null ?_ h
    intro x
    simp only [mem_diff, mem_setOf_eq, mem_union, not_or, not_lt, mem_compl_iff, not_le, and_imp]
    intro h₁ h₂ h₃
    refine (ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp ?_
    rw [ofReal_mul, ofReal_add] <;> try positivity
    repeat rw [ofReal_norm_eq_coe_nnnorm] <;> try positivity
    refine lt_of_le_of_lt ?_ h₁
    gcongr
  calc
    μ {x | ENNReal.ofReal A * (t + s) < ‖f x‖₊}
      ≤ μ ({x | t < ↑‖g₁ x‖₊} ∪ {x | s < ↑‖g₂ x‖₊}) := by apply measure_mono_ae' h₁
    _ ≤ μ {x | t < ↑‖g₁ x‖₊} + μ {x | s < ↑‖g₂ x‖₊} := by apply measure_union_le

lemma distribution_add_le :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ :=
  calc
    _ ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := by
      refine measure_mono fun x h ↦ ?_
      simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
      contrapose! h
      exact (ENNNorm_add_le _ _).trans (add_le_add h.1 h.2)
    _ ≤ _ := measure_union_le _ _

lemma approx_above_superset (t₀ : ℝ≥0∞) :
    ⋃ n, (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ↑‖f x‖₊}) n = {x | t₀ < ‖f x‖₊} := by
  ext y
  constructor <;> intro h
  · obtain ⟨n, wn⟩ := exists_exists_eq_and.mp h
    calc
      t₀ ≤ t₀ + (↑n)⁻¹ := le_self_add
      _  < ↑‖f y‖₊     := wn
  · have h₁ : Iio (↑‖f y‖₊ - t₀) ∈ 𝓝 0 := Iio_mem_nhds (tsub_pos_of_lt h)
    have h₂ := ENNReal.tendsto_inv_nat_nhds_zero h₁
    simp at h₂
    rcases h₂ with ⟨n, wn⟩
    simp only [mem_iUnion, mem_setOf_eq]
    use n
    exact lt_tsub_iff_left.mp (wn n (Nat.le_refl n))

lemma tendsto_measure_iUnion_distribution (t₀ : ℝ≥0∞) :
    Filter.Tendsto (⇑μ ∘ (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖₊}))
      Filter.atTop (nhds (μ ({x | t₀ < ‖f x‖₊}))) := by
  rw [← approx_above_superset]
  apply tendsto_measure_iUnion_atTop
  intro a b h x h₁
  calc
    _ ≤ t₀ + (↑a)⁻¹ := by gcongr
    _ < _ := h₁

lemma select_neighborhood_distribution (t₀ : ℝ≥0∞) (l : ℝ≥0∞) (hu : l < distribution f t₀ μ) :
    ∃ n : ℕ, l < distribution f (t₀ + (↑n)⁻¹) μ := by
  have h₁ : Ioi l ∈ (𝓝 (distribution f t₀ μ)) := Ioi_mem_nhds hu
  have h₂ := (tendsto_measure_iUnion_distribution t₀) h₁
  simp at h₂
  rcases h₂ with ⟨n, wn⟩
  use n; exact wn n (Nat.le_refl n)

lemma continuousWithinAt_distribution (t₀ : ℝ≥0∞) :
    ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
  rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
  · rw [t₀top]
    apply continuousWithinAt_of_not_mem_closure
    simp
  · unfold ContinuousWithinAt
    rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
    -- Case: distribution f t₀ μ = ⊤
    · simp
      rw [db_top, ENNReal.tendsto_nhds_top_iff_nnreal]
      intro b
      have h₀ : ∃ n : ℕ, ↑b < distribution f (t₀ + (↑n)⁻¹) μ :=
        select_neighborhood_distribution _ _ (db_top ▸ coe_lt_top)
      rcases h₀ with ⟨n, wn⟩
      refine eventually_mem_set.mpr (mem_inf_iff_superset.mpr ?_)
      use Iio (t₀ + (↑n)⁻¹)
      constructor
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
          simp only [mem_Ico, zero_le, lt_add_right t₀nottop.ne_top one_ne_zero, and_self]
        · use Ioi t₀
          refine ⟨by simp, fun z hz ↦ ?_⟩
          rw [db_zero]
          simp only [ge_iff_le, zero_le, tsub_eq_zero_of_le, zero_add]
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
        · use Ioi t₀
          refine ⟨by simp, fun z h ↦ ⟨?_, ?_⟩⟩
          · calc
              distribution f t₀ μ - ε
                ≤ distribution f (t₀ + (↑n)⁻¹) μ := le_of_lt wn
              _ ≤ distribution f z μ             := distribution_mono_right (le_of_lt h.1)
          · calc
              distribution f z μ
                ≤ distribution f t₀ μ := distribution_mono_right (le_of_lt h.2)
              _ ≤ distribution f t₀ μ + ε := le_self_add

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖₊ * t * s) μ ≤
    distribution f t μ + distribution g s μ := by
  unfold distribution
  have h₀ : {x | ↑‖L‖₊ * t * s < ↑‖(fun x ↦ (L (f x)) (g x)) x‖₊} ⊆
      {x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊} := fun z hz ↦ by
    simp only [mem_union, mem_setOf_eq, Pi.add_apply] at hz ⊢
    contrapose! hz
    calc
      (‖(L (f z)) (g z)‖₊ : ℝ≥0∞) ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ := by
        refine (toNNReal_le_toNNReal coe_ne_top coe_ne_top).mp ?_
        calc
          _ ≤ ↑‖L (f z)‖₊ * ↑‖g z‖₊ := ContinuousLinearMap.le_opNNNorm (L (f z)) (g z)
          _ ≤ _ := mul_le_mul' (ContinuousLinearMap.le_opNNNorm L (f z)) (by rfl)
      _ ≤ _ := mul_le_mul' (mul_le_mul_left' hz.1 ↑‖L‖₊) hz.2
  calc
    _ ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := measure_mono h₀
    _ ≤ _ := measure_union_le _ _

/- The lemmas below are almost already in Mathlib, see
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`. -/

-- /-- The layer-cake theorem, or Cavalieri's principle for functions into `ℝ≥0∞` -/
-- lemma lintegral_norm_pow_eq_measure_lt {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
--     {p : ℝ} (hp : 1 ≤ p) :
--     ∫⁻ x, (f x) ^ p ∂μ =
--     ∫⁻ t in Ioi (0 : ℝ), .ofReal (p * t ^ (p - 1)) * μ { x | ENNReal.ofReal t < f x } := by
--   sorry

section BorelSpace

variable [MeasurableSpace E] [BorelSpace E] (hf : AEMeasurable f μ)
include hf

/-- The layer-cake theorem, or Cavalieri's principle for functions into a normed group. -/
lemma lintegral_norm_pow_eq_distribution {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ‖f x‖₊ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 ≤ p := hp.le
  have := lintegral_rpow_eq_lintegral_meas_lt_mul μ (f := fun x ↦ ‖f x‖)
    (Eventually.of_forall fun x ↦ norm_nonneg _) hf.norm hp
  simp [*, ENNReal.coe_rpow_of_nonneg, ← ENNReal.ofReal_rpow_of_nonneg, ← ofReal_norm_eq_coe_nnnorm,
    ofReal_mul, ← lintegral_const_mul', ← mul_assoc, mul_comm (μ _), distribution]
    at this ⊢
  convert this using 1
  refine setLIntegral_congr_fun measurableSet_Ioi (Eventually.of_forall fun x hx ↦ ?_)
  simp_rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hx)]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`. -/
lemma eLpNorm_pow_eq_distribution {p : ℝ≥0} (hp : 0 < p) :
    eLpNorm f p μ ^ (p : ℝ) =
    ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 < (p : ℝ) := hp
  simp_rw [eLpNorm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
    ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]

/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`, without
    taking powers. -/
lemma eLpNorm_eq_distribution {p : ℝ} (hp : 0 < p) :
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
    rw [← lintegral_const_mul']; swap; exact coe_ne_top
    rw [lintegral_norm_pow_eq_distribution hf hp]
    congr 1; ext x; rw [ofReal_mul] <;> [ring; positivity]

lemma lintegral_pow_mul_distribution {p : ℝ} (hp : -1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * distribution f (.ofReal t) μ =
    ENNReal.ofReal (p + 1)⁻¹ * ∫⁻ x, ‖f x‖₊ ^ (p + 1) ∂μ := by
  have h2p : 0 < p + 1 := by linarith
  have h3p : 0 ≤ p + 1 := by linarith
  have h4p : p + 1 ≠ 0 := by linarith
  simp [*, lintegral_norm_pow_eq_distribution, ← lintegral_const_mul', ← ofReal_mul, ← mul_assoc]

end BorelSpace

/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' [NNNorm E] (f : α → E) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

lemma wnorm'_le_eLpNorm' {f : α → E} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    wnorm' f p μ ≤ eLpNorm' f p μ := by
  refine iSup_le (fun t ↦ ?_)
  unfold eLpNorm' distribution
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have p0' : 0 ≤ 1 / p := (div_pos one_pos p0).le
  have set_eq : {x | ofNNReal t < ‖f x‖₊} = {x | ofNNReal t ^ p < ‖f x‖₊ ^ p} := by
    simp [ENNReal.rpow_lt_rpow_iff p0]
  have : ofNNReal t = (ofNNReal t ^ p) ^ (1 / p) := by simp [p0.ne.symm]
  nth_rewrite 1 [inv_eq_one_div p, this, ← mul_rpow_of_nonneg _ _ p0', set_eq]
  refine rpow_le_rpow ?_ p0'
  refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.ennnorm.pow_const p) (ofNNReal t ^ p)
  gcongr
  exact setOf_subset_setOf.mpr (fun _ h ↦ h.le)

/-- The weak L^p norm of a function. -/
def wnorm [NNNorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

lemma wnorm_le_eLpNorm {f : α → E} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wnorm f p μ ≤ eLpNorm f p μ := by
  by_cases h : p = ⊤
  · simp [h, wnorm]
  · have p0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne.symm
    simpa [h, wnorm, eLpNorm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWℒp [NNNorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma Memℒp.memWℒp {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : Memℒp f p μ) :
    MemWℒp f p μ :=
  ⟨hf.1, lt_of_le_of_lt (wnorm_le_eLpNorm hf.1 hp) hf.2⟩

/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from L^p to weak-L^q.
`HasWeakType T p p' μ ν c` means that `T` has weak type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasWeakType (T : (α → E₁) → (α' → E₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0) : Prop :=
  ∀ f : α → E₁, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

lemma HasStrongType.hasWeakType (hp' : 1 ≤ p')
    (h : HasStrongType T p p' μ ν c) : HasWeakType T p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1, (wnorm_le_eLpNorm (h f hf).1 hp').trans (h f hf).2⟩

lemma HasStrongType.hasBoundedStrongType (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c :=
  fun f hf _ _ ↦ h f hf

/- Equation (2.0.46).
Easy from `hasStrongType_maximalFunction`. Ideally prove separately
`HasStrongType.const_smul` and `HasStrongType.const_mul`.-/

-- lemma HasStrongType.const_smul

lemma HasStrongType.const_mul {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [Mul E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → E) → (α' → E')}
    {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (h : HasStrongType T p p' μ ν c) (e : E') :
    HasStrongType (fun f x ↦ e * T f x) p p' μ ν c := by
  sorry

end MeasureTheory
