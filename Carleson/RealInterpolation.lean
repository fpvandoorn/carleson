import Carleson.WeakType
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField ℝ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)
  {f g : α → E} {t : ℝ} {s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}


namespace MeasureTheory

def trunc' (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

def trunc'' (f : α → E) (t : ℝ) :=
  {x | ¬ ‖f x‖ ≤ t}.indicator (fun x ↦ if 0 < t then (t * (max t ‖f x‖)⁻¹) • f x else 0)

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else
    if 0 < t then (t * ‖f x‖⁻¹) • f x else 0

def trnc (j : Bool) (f : α → E) (t : ℝ) :=
    if j then trunc f t else (f - trunc f t)

lemma trunc_buildup : trunc f t = trunc' f t + trunc'' f t := by
  ext x
  unfold trunc trunc' trunc''
  simp
  split <;> rename_i h₀
  · simp
    intro h
    have _ : ¬ t < ‖f x‖ := by exact not_lt.mpr h₀
    contradiction
  · have h₁ : max t ‖f x‖ = ‖f x‖ := by
      apply max_eq_right_of_lt
      exact lt_of_not_ge h₀
    unfold indicator
    simp
    split
    · rewrite [h₁]
      split <;> rename_i h₂
      · rfl
      · have _ : ‖f x‖ ≤ t := by exact le_of_not_lt h₂
        contradiction
    · exact Eq.symm (ite_self 0)

lemma stronglyMeasurable_inv (hf : StronglyMeasurable f) (ht : 0 < t):
    StronglyMeasurable (fun y ↦ (max t ‖f y‖)⁻¹):= by
  apply Continuous.comp_stronglyMeasurable (g := fun z ↦ (max t ‖z‖)⁻¹) (hf := hf)
  · apply Continuous.inv₀
    · apply Continuous.max
      · exact continuous_const
      · exact continuous_norm
    · intro z
      exact Ne.symm (ne_of_lt (lt_max_of_lt_left ht))

lemma aestronglyMeasurable_trunc' (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc' f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc' g t)
  constructor
  · apply MeasureTheory.StronglyMeasurable.indicator (s := {x | ‖g x‖ ≤ t})
    · exact wg1
    · apply StronglyMeasurable.measurableSet_le
      apply StronglyMeasurable.norm
      · exact wg1
      · exact stronglyMeasurable_const
  apply measure_mono_null ?_ wg2
  intro x
  contrapose
  simp
  intro h₂
  unfold trunc'
  rewrite [h₂]
  rfl

lemma aestronglyMeasurable_trunc'' (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc'' f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc'' g t)
  constructor
  · apply MeasureTheory.StronglyMeasurable.indicator
    · split <;> rename_i h₀
      · apply StronglyMeasurable.smul
        · apply StronglyMeasurable.mul
          · exact stronglyMeasurable_const
          · apply stronglyMeasurable_inv wg1 h₀
        · exact wg1
      · exact stronglyMeasurable_const
    · have h₂ : {x | ¬ ‖g x‖ ≤ t} = { x | t < ‖g x‖ } := by
        ext x
        exact not_le
      rewrite [h₂]
      apply StronglyMeasurable.measurableSet_lt
      · exact stronglyMeasurable_const
      · apply StronglyMeasurable.norm
        exact wg1

  apply measure_mono_null ?_ wg2
  intro x
  contrapose
  simp
  intro h₂
  unfold trunc''
  unfold indicator
  simp
  rewrite [h₂]
  rfl

lemma aestronglyMeasurable_trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := by
  rewrite [trunc_buildup]
  apply AEStronglyMeasurable.add
  · exact aestronglyMeasurable_trunc' hf
  · exact aestronglyMeasurable_trunc'' hf

lemma weakℒp_interpolate_lower {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ico 1 p) {f : α → E₁}
    (hf : MemWℒp f p μ) (hμf : μ (Function.support f) < ⊤) :
    Memℒp f q μ := by
  sorry

lemma weakℒp_interpolate_higher {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ioi p) {f : α → E₁}
    (hf : MemWℒp f p μ) (hfinf : snormEssSup f μ < ⊤) :
    Memℒp f q μ := by
  unfold Memℒp; unfold MemWℒp at hf
  constructor
  · exact hf.1
  · have h₀ : snorm f q.toNNReal μ ^ (q.toNNReal.toReal) < ⊤ := by
      rewrite [snorm_pow_eq_distribution]
      let β := (snormEssSup f μ).toReal
      rw [← lintegral_inter_add_diff (B := Ioc (0 : ℝ) β) (hB := measurableSet_Ioc)]
      simp
      constructor
      · sorry
      · sorry
      sorry
    sorry

lemma trunc_Lp {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ici p) {f : α → E₁}
    (hf : Memℒp f q μ) (a : ℝ) : Memℒp (trunc f a) q μ := by
  sorry
  -- unfold Memℒp; unfold Memℒp at hf
  -- rcases hf with ⟨hf₁, hf₂⟩
  -- constructor
  -- · exact aestronglyMeasurable_trunc hf₁
  -- · apply?

lemma trunc_comp_Lp {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Icc 1 p) {f : α → E₁}
    (hf : Memℒp f q μ) (a : ℝ) : Memℒp (f - trunc f a) q μ := by
  unfold Memℒp; unfold Memℒp at hf
  rcases hf with ⟨hf₁, hf₂⟩
  constructor
  · exact AEStronglyMeasurable.sub hf₁ (aestronglyMeasurable_trunc hf₁)
  · sorry

lemma distribution_shift_trunc (t : ℝ) (s : ℝ≥0∞) :
    distribution (f - (trunc f t)) s μ = distribution f (s + t.toNNReal) μ := by
  -- TODO: clean up
  unfold distribution trunc
  split <;> rename_i h₀
  · have h₁ :
        {x | s < ↑‖(f - fun x ↦ if ‖f x‖ ≤ t then f x else (t * ‖f x‖⁻¹) • f x) x‖₊}
        = {x | (t.toNNReal + s) < ↑‖f x‖₊} := by
      ext x
      simp
      split <;> rename_i h₂
      · simp
        calc
        ‖f x‖₊ ≤ ofNNReal t.toNNReal := by
          refine ENNReal.coe_le_coe.mpr (le_toNNReal_of_coe_le h₂)
        _      ≤ t.toNNReal + s := le_self_add
      · rcases (eq_or_ne s ⊤) with s_eq_top | s_ne_top
        · constructor
          · intro h
            have h₃ : ofNNReal ↑‖f x - (t * ‖f x‖⁻¹) • f x‖₊ < ⊤ := by
              exact coe_lt_top
            have h₄ : s < ⊤ := gt_trans h₃ h
            have _ : ¬ (s < ⊤) := by exact not_lt_top.mpr s_eq_top
            contradiction
          · intro h
            have h₅ : s < ⊤ := by exact gt_trans coe_lt_top (lt_of_le_of_lt le_add_self h)
            have _ : ¬ (s < ⊤) := by exact not_lt_top.mpr s_eq_top
            contradiction
        · rewrite [Iff.symm (toNNReal_lt_toNNReal s_ne_top coe_ne_top)]
          have h_sum_ne_top : ofNNReal t.toNNReal + s ≠ ⊤ :=
            add_ne_top.mpr (ite_ne_left_iff.mp (id (Ne.symm s_ne_top)))
          rewrite [Iff.symm (toNNReal_lt_toNNReal h_sum_ne_top coe_ne_top)]
          change (s.toNNReal.toReal < ‖f x - (t * ‖f x‖⁻¹) • f x‖ ↔
              (↑t.toNNReal + s).toNNReal.toReal < ‖f x‖)
          nth_rewrite 1 [← MulAction.one_smul (α := ℝ) (f x)]
          rewrite [← (sub_smul), norm_smul]
          have h₄ : ‖f x‖⁻¹ < t⁻¹ := inv_lt_inv_of_lt h₀ (lt_of_not_ge h₂)
          have h₅ : t * ‖f x‖⁻¹ < t * t⁻¹ := (_root_.mul_lt_mul_left h₀).mpr h₄
          rewrite [((mul_inv_eq_one₀ (Ne.symm (ne_of_lt h₀))).mpr rfl)] at h₅
          have h₆ : 1 - t * ‖f x‖⁻¹ > 0 := sub_pos.mpr h₅
          rewrite [Real.norm_of_nonneg (le_of_lt h₆)]
          have h₁₁ : (1 - t * ‖f x‖⁻¹)*‖f x‖ = ‖f x‖ - t * (‖f x‖*‖f x‖⁻¹) := by linarith
          have h₁₂ : ‖f x‖*‖f x‖⁻¹ = 1 := by
            apply mul_inv_cancel
            linarith
          rewrite [h₁₂] at h₁₁
          rewrite [h₁₁]
          simp
          rewrite [toNNReal_add coe_ne_top s_ne_top]
          simp
          rewrite [max_eq_left_of_lt h₀]
          constructor
          · intro h
            linarith
          · intro h
            linarith
    rewrite [h₁]
    rw [add_comm]
  · have h₂ : (fun x ↦ if ‖f x‖ ≤ t then f x else 0) = (fun x ↦ 0) := by
      ext x
      split
      · have _ : ‖f x‖ ≥ 0 := norm_nonneg (f x)
        have h₃ : ‖f x‖ = 0 := by linarith
        exact norm_eq_zero.mp h₃
      · rfl
    rw [h₂]
    simp
    rw [Real.toNNReal_of_nonpos (le_of_not_lt h₀)]
    simp

lemma distribution_trunc (t : ℝ) :
    distribution (trunc f t) s μ =
    if s < ENNReal.ofReal t then distribution f s μ else 0 := by
  have simp_norm : ∀ x, t > 0 → ¬ ‖f x‖ ≤  t → ‖(t * ‖f x‖⁻¹) • f x‖.toNNReal = t.toNNReal := by
    intro x t_pos ne_norm_le_t
    have norm_pos := (lt_trans t_pos (not_le.mp ne_norm_le_t))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (le_of_lt t_pos) (le_of_lt (inv_pos_of_pos norm_pos))),
        mul_assoc, mul_comm ‖f x‖⁻¹, mul_inv_cancel (ne_of_gt norm_pos), mul_one]
  split <;> rename_i h₀
  · apply congrArg μ
    ext x
    simp
    unfold trunc
    rw [← norm_toNNReal, ← norm_toNNReal]
    split <;> rename_i h₁
    · rfl
    · split <;> rename_i h₂
      · have coe_t_lt_norm : ENNReal.ofReal t < ENNReal.ofReal ‖f x‖ :=
          (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₂)).mpr (not_le.mp h₁)
        rw [simp_norm x h₂ h₁]
        exact { mp := fun _ ↦ lt_trans h₀ coe_t_lt_norm, mpr := fun _ ↦ h₀ }
      · rw [norm_zero, Real.toNNReal_zero, ENNReal.coe_zero]
        exact
          { mp := fun h ↦ False.elim (not_lt_zero h),
            mpr := False.elim
              (not_lt_zero (lt_of_lt_of_le h₀ (ofReal_le_of_le_toReal (not_lt.mp h₂)))) }
  · unfold distribution trunc
    refine measure_mono_null ?_ (OuterMeasureClass.measure_empty μ)
    intro x
    simp
    rw [← norm_toNNReal]
    split <;> rename_i h₁
    · exact le_trans (ofReal_le_ofReal h₁) (not_lt.mp h₀)
    · split <;> rename_i h₂
      · rw [simp_norm x h₂ h₁]
        exact not_lt.mp h₀
      · rw [norm_zero, Real.toNNReal_zero, ENNReal.coe_zero]
        exact zero_le s

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (MeasureTheory.trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

def Subadditive (T : (α → E₁) → α' → E₂) : Prop :=
  ∃ A > 0, ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

def Subadditive' (T : (α → E₁) → α' → E₂) {A : ℝ} (hA : A > 0) : Prop :=
  ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

def Sublinear (T : (α → E₁) → α' → E₂) : Prop :=
  Subadditive T ∧ ∀ (f : α → E₁) (c : ℝ), T (c • f) = c • T f

/-- Proposition that expresses that the map `T` map between function spaces preserves
    AE strong measurability on L^p. -/
def PreservesAEStrongMeasurability (T : (α → E₁) → α' → E₂) (p : ℝ≥0∞) : Prop :=
    ∀ (f : α → E₁), Memℒp f p μ → AEStronglyMeasurable (T f) ν

/-- Marcinkiewicz real interpolation theorem, for the case of equal domain: p₀ = p₁. -/
lemma exists_hasStrongType_real_interpolation' {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (hp₀₁ : p₀ = p₁) :
    ∃ C > 0, HasStrongType T p q μ ν C := by
  let Cfinal : ℝ≥0 := C₀
  exists Cfinal
  constructor
  · sorry
  · have p_eq_p₀ : p = p₀ := by sorry
    intros f f_mem
    rewrite [p_eq_p₀] at f_mem
    have h₀T_ap := (h₀T f f_mem).2
    rewrite [hp₀₁] at f_mem
    have h₁T_ap := (h₁T f f_mem).2
    constructor
    · exact (h₁T f f_mem).1
    · unfold wnorm at h₀T_ap
      split at h₀T_ap
      · have q_eq_top : q = ⊤ := sorry
        rewrite [← p_eq_p₀] at h₀T_ap
        unfold snorm
        split
        · apply zero_le
        · exact h₀T_ap
      · sorry

/-- Marcinkiewicz real interpolation theorem, for the case p₀ ≠ p₁ and all exponents
    are less than ∞.
    TODO: So far the assymption that p₀ ≠ p₁ is not added -/
lemma exists_hasStrongType_real_interpolation'' {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hq₀ : q₀ < ∞) (hq₁ : q₁ < ∞) :
    ∃ C > 0, HasStrongType T p q μ ν C := sorry

lemma measure_preserving_shift {a : ℝ} :
    MeasurePreserving (fun x ↦ a + x) volume volume := by
  exact measurePreserving_add_left volume a

lemma measureable_embedding_shift {a : ℝ} :
    MeasurableEmbedding (fun x ↦ a + x) := by
  exact measurableEmbedding_addLeft a

lemma measure_preserving_scaling {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun x ↦ a * x) volume ((ENNReal.ofReal |a⁻¹|) • volume) := by
  refine { measurable := ?measurable, map_eq := ?map_eq }
  · exact measurable_const_mul a
  · exact Real.map_volume_mul_left ha

lemma lintegral_shift (f : ℝ → ENNReal) {a : ℝ} :
    ∫⁻ x : ℝ, (f (x + a)) = ∫⁻ x : ℝ, f x :=
  by exact lintegral_add_right_eq_self f a

lemma lintegral_shift' (f : ℝ → ENNReal) {a : ℝ} {s : Set ℝ}:
    ∫⁻ (x : ℝ) in (fun z : ℝ ↦ z + a)⁻¹' s, f (x + a) = ∫⁻ (x : ℝ) in s, f x := by
  rw [MeasurePreserving.set_lintegral_comp_preimage_emb
      (measurePreserving_add_right volume a) (measurableEmbedding_addRight a)]

lemma lintegral_add_right_Ioi (f : ℝ → ENNReal) {a b : ℝ} :
    ∫⁻ (x : ℝ) in Ioi (b - a), f (x + a) = ∫⁻ (x : ℝ) in Ioi b, f x := by
  nth_rewrite 2 [← lintegral_shift' (a := a)]
  simp

lemma lintegral_scale_constant (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0):
    ∫⁻ x : ℝ, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x := by
  rw [← @lintegral_smul_measure]
  rw [MeasurePreserving.lintegral_comp_emb]
  · exact measure_preserving_scaling h
  · exact measurableEmbedding_mulLeft₀ h

lemma lintegral_scale_constant_preimage (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0)
    {s : Set ℝ}:
    ∫⁻ x : ℝ in (fun z : ℝ ↦ a * z)⁻¹' s, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in s, f x := by
  rw [← @lintegral_smul_measure]
  -- TODO: note that the function below has been renamed recently
  rw [MeasurePreserving.set_lintegral_comp_preimage_emb (measure_preserving_scaling h)
      (measurableEmbedding_mulLeft₀ h)]
  rw [@Measure.restrict_smul]

lemma lintegral_scale_constant_halfspace (f: ℝ → ENNReal) {a : ℝ} (h : 0 < a) :
    ∫⁻ x : ℝ in Ioi 0, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [← lintegral_scale_constant_preimage f (Ne.symm (ne_of_lt h))]
  have h₀ : (fun z ↦ a * z) ⁻¹' Ioi 0 = Ioi 0 := by
    unfold preimage
    ext x
    simp
    constructor
    · intro h₁
      exact (pos_iff_pos_of_mul_pos h₁).mp h
    · intro h₁
      exact Real.mul_pos h h₁
  rw [h₀]

lemma lintegral_scale_constant_halfspace' {f: ℝ → ENNReal} {a : ℝ} (h : 0 < a) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ in Ioi 0, f (a*x) = ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [lintegral_scale_constant_halfspace f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a),
      @abs_inv, mul_inv_cancel (abs_ne_zero.mpr (Ne.symm (ne_of_lt h)))]
  simp

lemma lintegral_scale_constant' {f: ℝ → ENNReal} {a : ℝ} (h : a ≠ 0):
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a), @abs_inv,
      mul_inv_cancel (abs_ne_zero.mpr h)]
  simp

lemma lintegral_double_restrict_set {A B: Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := set_lintegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]



lemma estimate_trunc_compl {p₀ : ℝ} (hp₀ : 1 ≤ p₀) {f : α → E} {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ x, ‖(f - trunc f a) x‖₊ ^ p₀ ∂μ =
    ∫⁻ s : ℝ in Ioi (0 : ℝ), ENNReal.ofReal p₀ * ENNReal.ofReal (s ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal (s + a)) μ := by
  rewrite [lintegral_norm_pow_eq_distribution hp₀]
  apply set_lintegral_congr_fun measurableSet_Ioi
  apply ae_of_all
  simp
  intros t t_gt_0
  have h₀ : (fun x ↦ f x - trunc f a x) = f - trunc f a := by rfl
  rw [h₀]
  rw [distribution_shift_trunc]
  congr
  · rw [ofReal_mul]; linarith
  · rw [ofReal_add (le_of_lt t_gt_0) ha]; rfl

lemma estimate_trunc_compl' {p₀ : ℝ} {f : α → E} {a : ℝ} :
    ∫⁻ s : ℝ in Ioi (0 : ℝ), ENNReal.ofReal p₀ * ENNReal.ofReal (s ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal (s + a)) μ =
    ∫⁻ s : ℝ in Ioi (a : ℝ), ENNReal.ofReal p₀ * ENNReal.ofReal ((s - a) ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal s) μ := by
  nth_rewrite 2 [← lintegral_add_right_Ioi (a := a)]
  simp

lemma estimate_trunc_compl'' {p₀ : ℝ} {a : ℝ} (hp₀ : 1 ≤ p₀) (ha : 0 ≤ a) :
    ∫⁻ x, ‖(f - trunc f a) x‖₊ ^ p₀ ∂μ ≤
    ∫⁻ s : ℝ in Ioi a, ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
    distribution f (ENNReal.ofReal s) μ := by
  rw [estimate_trunc_compl hp₀ ha, estimate_trunc_compl']
  apply set_lintegral_mono' measurableSet_Ioi
  intros t t_gt_a
  rw [mem_Ioi] at t_gt_a
  refine mul_le_mul_three (le_of_eq rfl) ?_ (le_of_eq rfl)
  rw [ofReal_rpow_of_pos (lt_of_le_of_lt ha t_gt_a)]
  apply ofReal_le_ofReal_iff'.mpr; left; apply Real.rpow_le_rpow <;> linarith

lemma estimate_snorm_trunc_compl {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (f : α → E) {a : ℝ} (ha : 0 ≤ a) :
  snorm (f - trunc f a) (ENNReal.ofReal p₀) μ ≤
  (∫⁻ s : ℝ in Ioi a, ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
    distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
  have p₀_gt_0 : p₀ > 0 := gt_of_ge_of_gt hp₀ (Real.zero_lt_one)
  have p₀_coe : (ENNReal.ofReal p₀).toReal = p₀ := toReal_ofReal (le_of_lt p₀_gt_0)
  refine (ENNReal.rpow_one_div_le_iff (inv_pos_of_pos p₀_gt_0)).mp ?_
  unfold snorm
  split <;> rename_i h₁
  · contrapose! h₁; exact Ne.symm (ne_of_lt (ofReal_pos.mpr p₀_gt_0))
  · split <;> rename_i h₂
    · contrapose! h₂; exact coe_ne_top
    · unfold snorm'
      simp
      rw [p₀_coe, ENNReal.rpow_inv_rpow (ne_of_gt p₀_gt_0)]
      exact estimate_trunc_compl'' hp₀ ha

lemma estimate_distribution_subadditive {q : ℝ} (hq : 1 ≤ q) (f : α → E₁) (t : ℝ)
    (ht : t > 0)(a : ℝ) {A : ℝ} (hA : A > 0) (h : Subadditive' T hA) :
    distribution (T f) (ENNReal.ofReal ((2 : ℝ) * t)) ν ≤
    distribution ((A • T) (trunc f a)) (ENNReal.ofReal t) ν +
    distribution ((A • T) (f - trunc f a)) (ENNReal.ofReal t) ν := by
  rw [← one_add_one_eq_two, add_mul, one_mul, ofReal_add (le_of_lt ht) (le_of_lt ht)]
  apply distribution_add_le'
  apply ae_of_all
  intro x
  have h₀ : ∀ g : α → E₁, (A • T) g = A • (T g) := by intro g; rfl
  have h₁ : ∀ (g : α → E₁) (x : α'), (A • (T g)) x = A • (T g x) := by intros g x; rfl
  rw [h₀, h₀, h₁, h₁, norm_smul, norm_smul, Real.norm_eq_abs, (abs_of_pos hA), ← mul_add]
  have h₂ : f = trunc f a + (f - trunc f a) := by rw [@add_sub_cancel]
  nth_rewrite 1 [h₂]
  apply h

lemma estimate_distribution_subadditive' {q : ℝ} (hq : 1 ≤ q) (f : α → E₁) (t : ℝ)
    (ht : t > 0) (a : ℝ) {A : ℝ} (hA : A > 0) (h : Subadditive' T hA) :
    distribution (T f) (ENNReal.ofReal ((2 : ℝ) * t)) ν ≤
    distribution (T (trunc f a)) (ENNReal.ofReal (t / A)) ν +
    distribution (T (f - trunc f a)) (ENNReal.ofReal (t / A)) ν := by
  rw [ofReal_div_of_pos hA, ← Real.ennnorm_eq_ofReal (le_of_lt hA)]
  -- TODO : fix, cannot seem to use the results on the field
  sorry

-- lemma test_9 (a b c : ℝ≥0∞) :
--   a = b → a * c = b * c := by
--   exact fun a_1 ↦ congrFun (congrArg HMul.hMul a_1) c

lemma _rewrite_norm_func (q : ℝ) (g : α' → E) (hq : 1 ≤ q) :
    ∫⁻ x, ‖g x‖₊ ^q ∂ν  =
    ENNReal.ofReal (2^q * q) * ∫⁻ s in Ioi (0 : ℝ),
    ENNReal.ofReal (s^(q - 1)) * distribution g ((ENNReal.ofReal 2)*(ENNReal.ofReal s)) ν := by
  rewrite [lintegral_norm_pow_eq_distribution hq]
  have two_gt_0 : (2 : ℝ) > 0 := by linarith
  nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := 2) two_gt_0]
  have h₄ : ENNReal.ofReal |2| ≠ ⊤ := coe_ne_top
  have h₅ : ENNReal.ofReal (2^q * q) ≠ ⊤ := coe_ne_top
  rewrite [← lintegral_const_mul' (hr := h₄), ← lintegral_const_mul' (hr := h₅)]
  rewrite [← lintegral_indicator (hs := measurableSet_Ioi),
           ← lintegral_indicator (hs := measurableSet_Ioi)]
  apply congr_arg
  simp
  ext t
  unfold indicator
  simp
  split <;> rename_i zero_lt_t
  · rw [ofReal_mul' (le_of_lt zero_lt_t), ofReal_eq_ofNat.mpr rfl, ← mul_assoc, ← mul_assoc]
    refine congrFun (congrArg ?_ ?_) ?_
    rw [Real.mul_rpow (le_of_lt two_gt_0) (le_of_lt zero_lt_t), ← mul_assoc]
    rw [ofReal_mul]
    · rw [← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      · rw [← ofReal_eq_ofNat.mpr rfl, ← ofReal_mul]
        apply congr_arg
        rw [mul_comm q, ← mul_assoc]
        congr
        · have h₁₀ : (2 : ℝ) = 2 ^ (1 : ℝ)  := by exact Eq.symm (Real.rpow_one 2)
          nth_rewrite 1 [h₁₀]
          rewrite [← Real.rpow_add]
          · rw [add_sub_cancel]
          · exact two_gt_0
        · exact le_of_lt two_gt_0
    · apply mul_nonneg
      · linarith
      · apply Real.rpow_nonneg
        exact le_of_lt two_gt_0
  · rfl



lemma lintegral_const_mul_set' {r : ℝ≥0∞} (hr : r ≠ ⊤) (s : Set α) (f : α → ℝ≥0∞):
    r * ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, r * f x ∂μ :=
  Eq.symm (lintegral_const_mul' r (fun a ↦ f a) hr)



lemma weaktype_estimate {C₀ : ℝ≥0} {p : ℝ≥0} {q : ℝ≥0} (hq : 1 ≤ q)
  {f : α → E₁} (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p q μ ν C₀) (t : ℝ) (ht : t > 0) :
    distribution (T f) (ENNReal.ofReal t) ν ≤ ((t⁻¹).toNNReal * C₀ * snorm f p μ) ^ q.toReal := by
  refine (ENNReal.rpow_one_div_le_iff
      (NNReal.coe_pos.mpr (gt_of_ge_of_gt hq (zero_lt_one' _)))).mp ?_
  rw [one_div]
  refine (ENNReal.mul_le_mul_left (a := ↑t.toNNReal) ?_ coe_ne_top).mp ?_
  · apply ENNReal.coe_ne_zero.mpr
    simp; exact ht
  · rw [← mul_assoc, ← mul_assoc]
    have h₁ : ENNReal.ofNNReal t.toNNReal * ENNReal.ofNNReal t⁻¹.toNNReal = ENNReal.ofNNReal
      (t.toNNReal * t⁻¹.toNNReal) := rfl
    rw [h₁, ← Real.toNNReal_mul (le_of_lt ht), mul_inv_cancel (Ne.symm (ne_of_lt ht))]
    simp
    have h₀ := (h₀T f hf).2
    unfold wnorm wnorm' at h₀
    simp at h₀
    exact (h₀ (t.toNNReal))

def φ₀ (μ : Measure α) (f : α → E₁) (p₀ q₀ q : ℝ) (β : ℝ) (s t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal s ^ ((q - q₀ - 1) * p₀ / q₀) * ENNReal.ofReal t ^ (p₀ - 1) *
  if t > β then
  distribution f (ENNReal.ofReal t) μ
  else 0

def φ₁ (μ : Measure α) (f : α → E₁) (p₁ q₁ q : ℝ) (β : ℝ) (s t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal s ^ ((q - q₁ - 1) * p₁ / q₁) * ENNReal.ofReal t ^ (p₁ - 1) *
  if t < β then
  distribution f (ENNReal.ofReal t) μ
  else 0

lemma estimate_trunc_comp_integral (f : α → E₁) (q p₀ q₀ : ℝ) (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀)
    (β : ℝ) (hβ : β ≥ 0) :
    ∫⁻ (s : ℝ) in Ioi 0,
    ENNReal.ofReal s ^ (q - q₀ - 1) * (snorm (f - trunc f β) (ENNReal.ofReal p₀) μ) ^ q₀ ≤
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₀) * (φ₀ μ f p₀ q₀ q β s t )) ^ (q₀ / p₀) := by
  apply set_lintegral_mono' measurableSet_Ioi
  intro s hs
  refine Preorder.le_trans ?_
      (ENNReal.ofReal s ^ (q - q₀ - 1) *
      ((∫⁻ (s : ℝ) in Ioi β,
        ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) * distribution f (ENNReal.ofReal s) μ) ^
      p₀⁻¹) ^ q₀) ?_ ?_ ?_
  · apply mul_le_mul_left'
    have hq₀ : q₀ ≥ 0 := by linarith
    have h₀ : snorm (f - trunc f β) (ENNReal.ofReal p₀) μ ≤
        (∫⁻ s : ℝ in Ioi β, ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
        distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
      apply estimate_snorm_trunc_compl hp₀
      linarith
    exact ENNReal.rpow_le_rpow h₀ hq₀
  · have hq₀ : q₀ ≠ 0 := by linarith
    have hp₀inv : p₀⁻¹ ≠ 0 := by
      refine inv_ne_zero ?_
      linarith
    have hp₀ : (ENNReal.ofReal p₀).toReal = p₀ := by
      refine toReal_ofReal ?_
      linarith
    have h₁ : p₀⁻¹ * q₀ ≠ 0 := by sorry
    have h₂ : p₀⁻¹ * q₀ ≥ 0 := by sorry
    -- rw [hp₀]
    rw [← ENNReal.rpow_mul, div_eq_inv_mul]
    rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₀ - 1))]
    rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
    rw [← mul_rpow_of_nonneg (hz := h₂)]
    have h₃ : (ENNReal.ofReal s ^ (q - q₀ - q₀ / q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ≠ ⊤ := by sorry
    rw [← lintegral_const_mul' (hr := h₃)]
    refine ENNReal.rpow_le_rpow ?_ h₂
    unfold φ₀
    have h₃ : Ioi (0 : ℝ) ∩ Ioi β = Ioi β := by
      unfold Ioi
      simp
      sorry
    nth_rewrite 2 [lintegral_double_restrict_set (B := Ioi β) _ measurableSet_Ioi]
    · rw [h₃]
      apply set_lintegral_mono_ae' (measurableSet_Ioi)
      apply ae_of_all
      intro t ht; simp at ht
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₀)]
      split
      · apply mul_le_mul_right'
        rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
        apply mul_le_mul_right'
        apply mul_le_mul_left'
        apply le_of_eq
        rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₀, ← mul_assoc]
        rfl
      · contradiction
    · apply ae_of_all
      simp
      intro t ht ht2 ht3
      contrapose! ht3; exact ht2
    · exact measurableSet_Ioi

lemma eq_trunc_integral (f : α → E₁) (q p₁ q₁ : ℝ) (β : ℝ) :
    ∫⁻ (s : ℝ) in Ioi 0,
    ENNReal.ofReal s ^ (q - q₁ - 1) * (snorm (trunc f β) (ENNReal.ofReal p₁) μ) ^ q₁ =
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁ ) * (φ₁ μ f p₁ q₁ q β s t )) ^ (q₁ / p₁) := by
  apply set_lintegral_congr_fun measurableSet_Ioi
  apply ae_of_all
  intro s hs
  rw [estimate_trunc]
  have hq₀ : q₁ ≠ 0 := by sorry
  have hp₀inv : p₁⁻¹ ≠ 0 := by sorry
  have hp₀ : (ENNReal.ofReal p₁).toReal = p₁ := by
    refine toReal_ofReal sorry
  have h₁ : p₁⁻¹ * q₁ ≠ 0 := by sorry
  have h₂ : p₁⁻¹ * q₁ ≥ 0 := by sorry
  rw [hp₀]
  rw [← ENNReal.rpow_mul, div_eq_inv_mul]
  rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₁ - 1))]
  rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
  rw [← mul_rpow_of_nonneg (hz := h₂)]
  have h₃ : (ENNReal.ofReal s ^ (q - q₁ - q₁ / q₁)) ^ (p₁⁻¹ * q₁)⁻¹ ≠ ⊤ := by sorry
  rw [← lintegral_const_mul' (hr := h₃)]
  refine congrFun (congrArg HPow.hPow ?_) (p₁⁻¹ * q₁)
  unfold φ₁
  nth_rewrite 2 [lintegral_double_restrict_set (B := Ioo (0 : ℝ) (s ^ σ)) _ measurableSet_Ioo]
  · have h₃ : Ioi (0 : ℝ) ∩ Ioo (0 : ℝ) (s ^ σ) = Ioo (0 : ℝ) (s ^ σ) := by
      unfold Ioi Ioo
      simp
      tauto
    rw [h₃]
    apply set_lintegral_congr_fun (measurableSet_Ioo)
    apply ae_of_all
    intro t ht; simp at ht
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₁)]
    split
    · refine congrFun (congrArg ?_ ?_) ?_
      rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      apply congrArg
      rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₁, ← mul_assoc]
      rfl
    · tauto
  · apply ae_of_all
    simp
    intro t ht1 ht2 ht3
    contrapose! ht3; exact ht2 ht1
  · exact measurableSet_Ioi

-- Build a structure
-- [function f : ℝ → ℝ
-- f Monotone on Ioi 0 ∨ f Antitone on Ioi 0
-- [function g : ℝ → ℝ]
-- function g : ℝ → ℝ,
-- forall x ∈ Ioi 0, f x ∈ Ioi 0
-- forall x ∈ Ioi 0, g x ∈ Ioi 0
--

structure ScaledPowerFunction where
  σ : ℝ
  d : ℝ
  hd : d > 0
  hσ : (σ > 0) ∨ (σ < 0)

class ToneCouple where
  ton : ℝ → ℝ
  inv : ℝ → ℝ
  mon : Bool
  ran_inv : ∀ t ∈ Ioi (0 : ℝ), inv t ∈ Ioi 0
  -- ton_is_ton : if mon then StrictMonoOn ton (Ioi 0) else StrictAntiOn ton (Ioi 0)
  inv_pf : if mon
      then ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ s < inv t) ∧ (t < ton s ↔ inv t < s)
      else ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ inv t < s) ∧ (t < ton s ↔ s < inv t)

instance spf_to_tc (spf : ScaledPowerFunction) : ToneCouple := by
  let ton := fun s : ℝ ↦ (s / spf.d) ^ spf.σ
  let inv := fun t : ℝ ↦ spf.d * t ^ spf.σ⁻¹
  let mon := if (spf.σ > 0) then true else false
  refine ⟨ ton, inv, mon, ?_, ?_ ⟩
  · exact fun t ht ↦Real.mul_pos spf.hd (Real.rpow_pos_of_pos ht spf.σ⁻¹)
  · unfold_let mon
    split <;> rename_i sgn_σ
    · simp
      intro s hs t ht
      constructor
      · unfold_let ton inv; simp
        rw [← Real.lt_rpow_inv_iff_of_pos
            (div_nonneg (le_of_lt hs) (le_of_lt spf.hd)) (le_of_lt ht) sgn_σ ]
        rw [← _root_.mul_lt_mul_left spf.hd]
        rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
      · unfold_let ton inv; simp
        rw [← Real.rpow_inv_lt_iff_of_pos (le_of_lt ht)
            (div_nonneg (le_of_lt hs) (le_of_lt spf.hd)) sgn_σ ]
        rw [← _root_.mul_lt_mul_left spf.hd]
        rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
    · simp
      intro s hs t ht
      rcases spf.hσ with σ_pos | σ_neg
      · contradiction
      · constructor
        · unfold_let ton inv; simp
          rw [← Real.rpow_inv_lt_iff_of_neg ht (div_pos hs spf.hd) σ_neg]
          rw [← _root_.mul_lt_mul_left spf.hd]
          rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
        · unfold_let ton inv; simp
          rw [← Real.lt_rpow_inv_iff_of_neg (div_pos hs spf.hd) ht σ_neg]
          rw [← _root_.mul_lt_mul_left spf.hd]
          rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]

def res (j : Bool) (β : ℝ) : Set ℝ := if j then Ioo (0 : ℝ) β else Ioi β

lemma measurableSet_res {j : Bool} {β : ℝ} : MeasurableSet (res j β) := by
  unfold res
  split
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi

lemma res_subset_Ioi {j : Bool} {β : ℝ} (hβ : β > 0) : res j β ⊆ Ioi 0 := by
  unfold res
  split
  · exact Ioo_subset_Ioi_self
  · unfold Ioi
    simp
    intro s hs
    linarith

instance decidableMemRes {j : Bool} {β : ℝ} : Decidable (t ∈ res j β) := by
  exact Classical.propDecidable (t ∈ res j β)

def φ {j : Bool} {p' q' q : ℝ} [tc : ToneCouple] (s t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
  distribution f (ENNReal.ofReal t) μ *
  if t ∈ res j (tc.ton s) then 1 else 0

lemma switch_arguments_φ' {j : Bool} [tc : ToneCouple] {s t : ℝ} (hs : s ∈ Ioi 0)
    (ht : t ∈ Ioi 0) :
    (if t ∈ res j (tc.ton s) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1 else
    @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0) =
    if s ∈ res (xor j tc.mon) (tc.inv t) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1 else
    @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 := by
  -- Written out because otherwise it got quite slow
  unfold res Ioo Ioi
  have h₀ := tc.inv_pf
  split at h₀ <;> rename_i mon
  · have h₀₁ := (h₀ s hs t ht).1
    have h₀₂ := (h₀ s hs t ht).2
    split <;> rename_i hj
    · rw [mon, hj]
      simp only [mem_setOf_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i hc1
      · split <;> rename_i hc2
        · exact Eq.refl (OfNat.ofNat 1)
        · exact False.elim (hc2 (h₀₂.mp hc1.2))
      · split <;> rename_i hc2
        · exact False.elim (hc1 (And.intro ht (h₀₂.mpr hc2)))
        · exact Eq.refl (OfNat.ofNat 0)
    · rw [mon, eq_false_of_ne_true hj]
      simp only [mem_setOf_eq, Bool.bne_true, Bool.not_false, ↓reduceIte]
      split <;> rename_i hc1
      · split <;> rename_i hc2
        · exact Eq.refl (OfNat.ofNat 1)
        · exact False.elim (hc2 (And.intro hs (h₀₁.mp hc1)))
      · split <;> rename_i hc2
        · exact False.elim (hc1 (h₀₁.mpr hc2.2))
        · exact Eq.refl (OfNat.ofNat 0)
  · have h₀₁ := (h₀ s hs t ht).1
    have h₀₂ := (h₀ s hs t ht).2
    split <;> rename_i hj
    · rw [eq_false_of_ne_true mon, hj]
      simp only [mem_setOf_eq, Bool.bne_false, ↓reduceIte]
      · split <;> rename_i hc1
        · split <;> rename_i hc2
          · exact Eq.refl (OfNat.ofNat 1)
          · exact False.elim (hc2 (And.intro hs (h₀₂.mp hc1.2)))
        · split <;> rename_i hc2
          · exact False.elim (hc1 (And.intro ht (h₀₂.mpr hc2.2)))
          · exact Eq.refl (OfNat.ofNat 0)
    · rw [eq_false_of_ne_true mon, eq_false_of_ne_true hj]
      simp only [mem_setOf_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      · split <;> rename_i hc1
        · split <;> rename_i hc2
          · exact Eq.refl (OfNat.ofNat 1)
          · exact False.elim (hc2 (h₀₁.mp hc1))
        · split <;> rename_i hc2
          · exact False.elim (hc1 (h₀₁.mpr hc2))
          · exact Eq.refl (OfNat.ofNat 0)

-- lemma restrict_φ {j : Bool} {tc : ToneCouple} {s t : ℝ} (hs : s ∈ Ioi 0)
--     (ht : t ∈ Ioi 0):
--     (if j then (
--       if t < tc.ton s then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)
--     else (
--       if tc.ton s < t then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)) =
--     if t ∈ res j (tc.ton s) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 := by
--   unfold res
--   have h₀ := tc.inv_pf
--   split at h₀ <;> rename_i mon
--   · split <;> rename_i hj
--     · simp
--       split
--       · split <;> tauto
--       · split <;> tauto
--     · simp
--   · split
--     · simp
--       split
--       · split <;> tauto
--       · split <;> tauto
--     · simp

-- lemma switch_arguments_φ' {j : Bool} {tc : ToneCouple} {s t : ℝ} (hs : s ∈ Ioi 0)
--     (ht : t ∈ Ioi 0):
--     (if j then (
--       if t < tc.ton s then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)
--     else (
--       if tc.ton s < t then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)) =
--     if (xor j tc.mon) then (
--       if s < tc.inv t then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)
--     else (
--       if tc.inv t < s then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0) := by
--   have h₀ := tc.inv_pf
--   split at h₀ <;> rename_i mon
--   · have h₀₁ := (h₀ s hs t ht).1
--     have h₀₂ := (h₀ s hs t ht).2
--     split <;> rename_i hj
--     · rw [mon, hj]
--       simp
--       split <;> rename_i hts
--       · split <;> rename_i hinv <;> tauto
--       · split <;> rename_i hinv <;> tauto
--     · rw [mon, eq_false_of_ne_true hj]
--       simp
--       split
--       · split <;> tauto
--       · split <;> tauto
--   · have h₀₁ := (h₀ s hs t ht).1
--     have h₀₂ := (h₀ s hs t ht).2
--     split <;> rename_i hj
--     · rw [eq_false_of_ne_true mon, hj]
--       simp
--       split
--       · split <;> tauto
--       . split <;> tauto
--     · rw [eq_false_of_ne_true mon, eq_false_of_ne_true hj]
--       simp
--       split
--       · split <;> tauto
--       · split <;> tauto

-- lemma restrict_φ' {j : Bool} {tc : ToneCouple} {s t : ℝ} (hs : s ∈ Ioi 0)
--     (ht : t ∈ Ioi 0) :
--     (if (xor j tc.mon) then (
--       if s < tc.inv t then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)
--     else (
--       if tc.inv t < s then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0)
--      ) =
--     if s ∈ res (xor j tc.mon) (tc.inv t) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1
--       else @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 := by
--   unfold res
--   have h₀ := tc.inv_pf
--   split at h₀ <;> rename_i mon
--   · split
--     · simp
--       split
--       · split <;> tauto
--       · split <;> tauto
--     · simp
--   · split
--     · simp
--       split
--       · split <;> tauto
--       · split <;> tauto
--     · simp

lemma switch_arguments_φ {j : Bool} {p' q' q : ℝ} [tc : ToneCouple] (s t : ℝ) (hs : s ∈ Ioi 0)
    (ht : t ∈ Ioi 0) :
    @φ _ _ _ μ _ f j p' q' q tc s t
    = ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
      distribution f (ENNReal.ofReal t) μ *
      if s ∈ res (xor j tc.mon) (tc.inv t) then 1 else 0
     := by
  unfold φ
  rw [switch_arguments_φ' hs ht]



lemma test_ (a b : ℝ≥0∞) (c : ℝ) (hc : c > 0) :
  (a * b) ^ c = a ^ c * b ^ c := by refine mul_rpow_of_nonneg a b ?hz

lemma test__ (a b : ℝ≥0∞) (c d: ℝ) (hc : c > 0) (hd : d > 0):
  (a ^ c) ^ d = a ^ (c * d) := by exact Eq.symm (ENNReal.rpow_mul a c d)

lemma test___ (a : ℝ) (c : ℝ) (hc : c ≥ 0) :
  ENNReal.ofReal a ^ c = ENNReal.ofReal (a ^ c) := by
  refine ofReal_rpow_of_pos ?hx_pos

-- TODO: generalize tc.inv?
lemma value_integral_φ' {j : Bool} {p' q' q : ℝ} [tc : ToneCouple] {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0):
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t),
    (ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
        distribution f (ENNReal.ofReal t) μ) ^
      (q' / p')
    --
    -- (ENNReal.ofReal s ^ (q - q' - 1))) * ENNReal.ofReal t ^ ((p' - 1) * (q' / p')) * (distribution f (ENNReal.ofReal t) μ) ^ (q' / p')
    := by
  have h₀ : q' / p' ≥ 0 := by sorry
  --have h₁ : ((q - q' - 1) * p' / q') * (q' / p') = q - q' - 1 := by sorry
  -- rw [ofReal_rpow_of_pos ht]
  -- rw [ENNReal.rpow_mul]
  -- rw [← h₁]
  -- rw [funext fun _ ↦ ENNReal.rpow_mul _ _ _]
  -- rw [← lintegral_mul_const _ (Measurable.pow_const
  --     (Measurable.pow_const measurable_ofReal _) _)]
  -- rw [← funext fun f ↦ mul_rpow_of_nonneg _ _ h₀]
  -- rw [← lintegral_mul_const _ (Measurable.pow_const (Measurable.mul_const
  --     (Measurable.pow_const measurable_ofReal _) _) _)]
  -- rw [← funext fun f ↦ mul_rpow_of_nonneg _ _ h₀]
  rw [lintegral_double_restrict_set (B := res (xor j tc.mon) (tc.inv t))]
  · rw [inter_eq_right.mpr (res_subset_Ioi (tc.ran_inv t ht))]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_res]
    intro s hs
    have h₁ : s ∈ Ioi 0 := res_subset_Ioi (tc.ran_inv t ht) hs
    rw [switch_arguments_φ _ _ h₁ ht]
    split
    · rw [mul_one]
    · contradiction
  · exact measurableSet_Ioi
  · exact measurableSet_res
  · filter_upwards
    intro s hs
    have h₁ : s ∈ Ioi 0 := by exact mem_of_mem_diff hs
    rw [switch_arguments_φ _ _ h₁ ht]
    split <;> rename_i hs1
    · exact False.elim (hs.2 hs1)
    . rw [mul_zero]
      rw [zero_rpow_of_pos]
      exact div_pos hq' hp'





-- lemma value_integral_φ₀ {p₀ q₀ q σ t : ℝ} {μ : Measure α} {f : α → E₁} (ht : t > 0)
--     (hσ : σ > 0) :
--     ∫⁻ s : ℝ in Ioi 0, φ₀ μ f p₀ q₀ q (s ^ σ) s t ^ (q₀ / p₀) =
--     ∫⁻ s : ℝ in Ioo 0 (t ^ (σ⁻¹)),
--     (ENNReal.ofReal s ^ ((q - q₀ - 1) * p₀ / q₀) * ENNReal.ofReal t ^ (p₀ - 1) *
--         distribution f (ENNReal.ofReal t) μ) ^ (q₀ / p₀) := by
--   unfold φ₀
--   rw [lintegral_double_restrict_set (B := Ioo 0 (t ^ σ⁻¹)) _ measurableSet_Ioo]
--   · have h₀ : Ioi 0 ∩ Ioo 0 (t ^ σ⁻¹) = Ioo 0 (t ^ σ⁻¹) := by sorry
--     rw [h₀]
--     apply lintegral_congr_ae
--     filter_upwards [self_mem_ae_restrict measurableSet_Ioo]
--     simp
--     intro s hs1 hs2 hs3
--     contrapose! hs2
--     refine (Real.rpow_inv_le_iff_of_pos (le_of_lt ht) (le_of_lt hs1) hσ).mpr hs3
--   · apply ae_of_all
--     simp
--     intro s hs1 hs2
--     split <;> rename_i hs3
--     · contrapose! hs3
--       refine (Real.rpow_le_rpow_iff (z := σ⁻¹) (le_of_lt ht) ?hy (inv_pos_of_pos hσ)).mp ?_
--       · sorry
--       · rw [Real.rpow_rpow_inv (le_of_lt hs1) (ne_of_gt hσ)]
--         exact hs2 hs1
--     · refine zero_rpow_of_pos ?_
--       sorry
--   · exact measurableSet_Ioi

lemma test_sub (a b c: ℝ) (ha : a ≠ 0): (0 : ℝ) ^ a  = 0 := by
  exact Real.zero_rpow ha

#check φ

lemma estimate_trunc_comp_integral' (f : α → E₁) (q p₀ q₀ : ℝ) {tc : ToneCouple} (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀)
    (β : ℝ) (hβ : β ≥ 0) :
    ∫⁻ (s : ℝ) in (Ioi 0),
    ENNReal.ofReal s ^ (q - q₀ - 1) * (snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ) ^ q₀ ≤
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₀) * (@φ _ _ _ μ _ f false p₀ q₀ q tc s t )) ^ (q₀ / p₀) := by
  apply set_lintegral_mono' measurableSet_Ioi
  intro s hs
  refine Preorder.le_trans ?_
      (ENNReal.ofReal s ^ (q - q₀ - 1) *
      ((∫⁻ (s : ℝ) in (res false (tc.ton s)),
        ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) * distribution f (ENNReal.ofReal s) μ) ^
      p₀⁻¹) ^ q₀) ?_ ?_ ?_
  · apply mul_le_mul_left'
    have hq₀ : q₀ ≥ 0 := by linarith
    have h₀ : snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ≤
        (∫⁻ s : ℝ in res false (tc.ton s), ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
        distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
      apply estimate_snorm_trunc_compl hp₀
      sorry
    apply ENNReal.rpow_le_rpow
    · exact h₀
    · exact hq₀
  · have hq₀ : q₀ ≠ 0 := by linarith
    have hp₀inv : p₀⁻¹ ≠ 0 := by
      refine inv_ne_zero ?_
      linarith
    have hp₀ : (ENNReal.ofReal p₀).toReal = p₀ := by
      refine toReal_ofReal ?_
      linarith
    have h₁ : p₀⁻¹ * q₀ ≠ 0 := by sorry
    have h₂ : p₀⁻¹ * q₀ ≥ 0 := by sorry
    -- rw [hp₀]
    rw [← ENNReal.rpow_mul, div_eq_inv_mul]
    rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₀ - 1))]
    rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
    rw [← mul_rpow_of_nonneg (hz := h₂)]
    have h₃ : (ENNReal.ofReal s ^ (q - q₀ - q₀ / q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ≠ ⊤ := by sorry
    rw [← lintegral_const_mul' (hr := h₃)]
    refine ENNReal.rpow_le_rpow ?_ h₂
    unfold φ
    have h₃ : Ioi (0 : ℝ) ∩ res false (tc.ton s) = res false (tc.ton s) := by
      refine inter_eq_self_of_subset_right ?_
      refine res_subset_Ioi ?_
      sorry
    nth_rewrite 2 [lintegral_double_restrict_set (B := res false (tc.ton s)) _ measurableSet_res]
    · rw [h₃]
      apply set_lintegral_mono_ae' (measurableSet_Ioi)
      apply ae_of_all
      intro t ht; simp at ht
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₀)]
      split <;> rename_i t_res
      · rw [mul_one, ← mul_assoc]
        apply mul_le_mul_right'
        rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
        apply mul_le_mul_right'
        apply mul_le_mul_left'
        apply le_of_eq
        rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₀, ← mul_assoc]
        rfl
      · unfold res at t_res
        simp at t_res
        contrapose t_res; simp; exact ht
    · apply ae_of_all
      simp
      intro t ht ht2 ht3
      contrapose! ht3; exact ht2
    · exact measurableSet_Ioi

lemma test_3 (a: ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) :
  a = (a ^ (c) ) ^c⁻¹ := by
  exact Eq.symm (ENNReal.rpow_rpow_inv hc a)

lemma estimate_trunc' (p₁ : ℝ) (A : ℝ):
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution (trunc f A) (ENNReal.ofReal t) μ =
          ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution f (ENNReal.ofReal ↑t) μ := by
  rw [lintegral_double_restrict_set (B := Ioo 0 A) _ measurableSet_Ioo]
  rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo]; intro t ht; rw [distribution_trunc]
    split <;> rename_i h₀
    · rfl
    · exact False.elim (h₀ ((ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht.1)).mpr ht.2))
  · apply ae_of_all; intro t ht; rw [distribution_trunc]
    split <;> rename_i ht2
    · exact False.elim (ht.2 ⟨ht.1, (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht.1)).mp ht2⟩)
    · rw [mul_zero]
  · exact measurableSet_Ioi

-- TODO link this to the lemmas that are proven
lemma estimate_trunc (p₁ : ℝ) (hp₁ : p₁ ≥ 1) A :
  snorm (trunc f A) p₁.toNNReal μ =
  (∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution f (ENNReal.ofReal t) μ) ^ p₁⁻¹ := by
  have hp : p₁ ≠ 0 := sorry
  have hp2 : p₁ = (p₁.toNNReal).toReal := by
    refine Eq.symm (Real.coe_toNNReal p₁ ?hr)
    sorry
  rw [← ENNReal.rpow_rpow_inv (y := p₁) hp (snorm (trunc f A) p₁.toNNReal μ)]
  nth_rewrite 2 [hp2]
  rw [snorm_pow_eq_distribution]
  rw [← hp2]
  -- TODO : work towards using estimate_trunc'
  sorry

-- TODO: Combine this function with estimate_trunc_compl_integral'
lemma eq_trunc_integral' (f : α → E₁) (q p₁ q₁ : ℝ) (tc : ToneCouple) :
    ∫⁻ (s : ℝ) in Ioi 0,
    ENNReal.ofReal s ^ (q - q₁ - 1) *
    (snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ) ^ q₁ =
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁) * (@φ _ _ _ μ _ f true p₁ q₁ q tc s t )) ^ (q₁ / p₁)
    := by
  apply set_lintegral_congr_fun measurableSet_Ioi
  apply ae_of_all
  intro s hs
  rw [estimate_trunc]
  have hq₀ : q₁ ≠ 0 := by sorry
  have hp₀inv : p₁⁻¹ ≠ 0 := by sorry
  have hp₀ : (ENNReal.ofReal p₁).toReal = p₁ := by
    refine toReal_ofReal sorry
  have h₁ : p₁⁻¹ * q₁ ≠ 0 := by sorry
  have h₂ : p₁⁻¹ * q₁ ≥ 0 := by sorry
  rw [hp₀]
  rw [← ENNReal.rpow_mul, div_eq_inv_mul]
  rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₁ - 1))]
  rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
  rw [← mul_rpow_of_nonneg (hz := h₂)]
  have h₃ : (ENNReal.ofReal s ^ (q - q₁ - q₁ / q₁)) ^ (p₁⁻¹ * q₁)⁻¹ ≠ ⊤ := by sorry
  rw [← lintegral_const_mul' (hr := h₃)]
  refine congrFun (congrArg HPow.hPow ?_) (p₁⁻¹ * q₁)
  unfold φ
  nth_rewrite 2 [lintegral_double_restrict_set (B := res true (tc.ton s)) _ measurableSet_res]
  · have h₃ : Ioi (0 : ℝ) ∩ (res true (tc.ton s)) = res true (tc.ton s) := by
      refine inter_eq_self_of_subset_right ?_
      refine res_subset_Ioi ?_
      sorry
    rw [h₃]
    apply set_lintegral_congr_fun (measurableSet_Ioo)
    apply ae_of_all
    intro t ht; simp at ht
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₁)]
    split
    · rw [mul_one, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      apply congrArg
      rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₁, ← mul_assoc]
      rfl
    · tauto
  · apply ae_of_all
    simp
    intro t ht1 ht2 ht3
    contradiction
  · exact measurableSet_Ioi

lemma compute_integral' {β γ : ℝ} (hβ : β > 0) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  have hγ2 : γ + 1 > 0 := by linarith
  rw [set_lintegral_congr Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hβ]
    rw [integral_rpow]
    · rw [Real.zero_rpow (ne_of_gt hγ2), sub_zero]
      rw [abs_of_nonneg (le_of_lt hγ2)]
    · exact Or.inl hγ
  · apply (@intervalIntegral.intervalIntegrable_rpow' 0 β γ ?_).1
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt hs.1) γ

lemma compute_integral'' {β γ : ℝ} (hβ : β > 0) (hγ : γ > 0):
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ (γ - 1)) =
    ENNReal.ofReal (β ^ γ / |γ|) := by
  have hγ' : -1 < γ - 1 := by linarith
  rw [set_lintegral_congr Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hβ]
    rw [integral_rpow]
    · rw [Real.zero_rpow]
      · rw [abs_of_nonneg (le_of_lt hγ)]
        simp
      · simp
        exact (ne_of_gt hγ)
    · exact Or.inl hγ'
  · apply (@intervalIntegral.intervalIntegrable_rpow' 0 β (γ - 1) ?_).1
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt hs.1) (γ - 1)

lemma compute_integral''' {β σ : ℝ} (hβ : β > 0) (hσ : σ < -1):
    ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / |σ + 1|) := by
  have hσ2 : σ + 1 < 0 := by linarith
  rw [abs_of_neg hσ2]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt hσ hβ]
    rw [div_neg, neg_div]
  · apply integrableOn_Ioi_rpow_of_lt hσ hβ
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt (lt_trans hβ hs)) σ

-- lemma compute_integral'''' {β γ : ℝ} (hβ : β > 0) (hγ : γ < 0) :
--     ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ (γ - 1)) =
--     ENNReal.ofReal (β ^ γ / |γ|) := by
--   rw [compute_integral''' hβ ]
--   · simp
--     rw [abs_of_neg hγ, div_neg, neg_div]
--   · linarith

-- TODO : check if the tc.inv parameter can be generalized
lemma compute_integral''''' {j : Bool} {tc : ToneCouple} {γ : ℝ} {t : ℝ}
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) (ht : t > 0) :
  ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t), ENNReal.ofReal s ^ γ =
    ENNReal.ofReal ((tc.inv t) ^ (γ + 1) / |γ + 1|) := by
  rw [← lintegral_congr_ae (Filter.mp_mem (self_mem_ae_restrict measurableSet_res)
      (Filter.univ_mem'
      (fun s hs ↦ Eq.symm (ofReal_rpow_of_pos (res_subset_Ioi (tc.ran_inv t ht) hs)))))]
  unfold res
  split at hγ <;> rename_i xor_split
  · rw [xor_split]
    simp
    rw [compute_integral' (tc.ran_inv t ht) hγ]
  · rw [eq_false_of_ne_true xor_split]
    simp
    rw [compute_integral''' (tc.ran_inv t ht) hγ]

lemma value_integral_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0)
    (hγ : if xor j tc.mon = true then q - q' - 1 > -1 else q - q' - 1 < -1):
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') =
    ENNReal.ofReal (tc.inv t ^ (q - q') / |q - q'|) * ENNReal.ofReal t ^ ((p' - 1) * (q' / p')) *
    distribution f (ENNReal.ofReal t) μ ^ (q' / p')
    --
    -- (ENNReal.ofReal s ^ (q - q' - 1))) * ENNReal.ofReal t ^ ((p' - 1) * (q' / p')) * (distribution f (ENNReal.ofReal t) μ) ^ (q' / p')
    := by
  have h₀ : q' / p' ≥ 0 := by sorry
  have h₁ : ((q - q' - 1) * p' / q') * (q' / p') = q - q' - 1 := by sorry
  rw [value_integral_φ' ht hq' hp']
  rw [funext fun f ↦ mul_rpow_of_nonneg _ _ h₀]
  rw [lintegral_mul_const _ (Measurable.pow_const (Measurable.mul_const
      (Measurable.pow_const measurable_ofReal _) _) _)]
  rw [funext fun f ↦ mul_rpow_of_nonneg _ _ h₀]
  rw [lintegral_mul_const _ (Measurable.pow_const (Measurable.pow_const measurable_ofReal _) _)]
  rw [← ENNReal.rpow_mul, ← funext fun _ ↦ ENNReal.rpow_mul _ _ _]
  rw [h₁]
  rw [compute_integral''''' _ ht]
  · rw [sub_add_cancel]
  · exact hγ

lemma ennreal_div (a b : ℝ≥0∞) :
  (a / b) = a * b⁻¹ := by
  rw [@DivInvMonoid.div_eq_mul_inv]

lemma ennreal_div' (a b c : ℝ) (hc : c ≠ 0):
  (a *  b) ^ c = a ^ c * (b ^ c) := by
  sorry

lemma test________ (a c : ℝ) : ENNReal.ofReal (a ^ c) = ENNReal.ofReal a ^ c := by
  sorry


lemma value_integral_φ'' {j : Bool} {p' q' q : ℝ} {spf : ScaledPowerFunction} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0)
    (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p') =
    ENNReal.ofReal (spf.d ^ (q - q')) * ENNReal.ofReal |q - q'|⁻¹ *
    ENNReal.ofReal t ^ ((p' - 1) * (q' / p') + spf.σ⁻¹ * (q - q')) *
    distribution f (ENNReal.ofReal t) μ ^ (q' / p') := by
  rewrite [value_integral_φ ht hq' hp' hγ]
  unfold ToneCouple.inv spf_to_tc
  simp only
  have h₀ : |q - q'|⁻¹   ≥ 0 := sorry
  have h₁ : (t ^ spf.σ⁻¹) ≥ 0 := sorry
  have h₂ : 0 ≤ spf.d ^ (q - q') := sorry
  rw [div_eq_mul_inv, ofReal_mul' h₀, Real.mul_rpow (le_of_lt spf.hd) h₁,
      ← Real.rpow_mul (le_of_lt ht), ofReal_mul h₂, ← mul_comm _ (ENNReal.ofReal _),
        mul_comm _ (ENNReal.ofReal t ^ ((p' - 1) * (q' / p'))), ← mul_assoc, ← mul_assoc,
        ← ofReal_rpow_of_pos, ← ENNReal.rpow_add, mul_assoc _ _ (ENNReal.ofReal |q - q'|⁻¹),
        mul_comm _ ((ENNReal.ofReal (spf.d ^ (q - q')) * ENNReal.ofReal |q - q'|⁻¹))]
  · sorry
  · exact coe_ne_top
  · exact ht

lemma test (a : ℝ≥0∞) (c d : ℝ) : (a ^ c) ^ d = a ^ (c * d) := by
  apply?

lemma test_2 (a b: ℝ≥0∞) (c d : ℝ) : (a * b) ^ c = a ^ c * b ^ c := by
  apply?

lemma value_integral_φ''' {j : Bool} {p' q' q : ℝ} {spf : ScaledPowerFunction} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0) (hp : p' + spf.σ⁻¹ * (q - q') * (p' / q') > 1)
    (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :
    ∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p')) ^ (p' / q') =
    ENNReal.ofReal (spf.d ^ (q - q')) ^ (p' / q') * ENNReal.ofReal |q - q'|⁻¹ ^ (p' / q') *
    ENNReal.ofReal (p' + spf.σ⁻¹ * (q - q') * (p' / q') )⁻¹ *
    snorm f (p' + spf.σ⁻¹ * (q - q') * (p' / q')).toNNReal μ ^
    (p' + spf.σ⁻¹ * (q - q') * (p' / q'))
    := by
  have hp2 : p' + spf.σ⁻¹ * (q - q') * (p' / q') > 0 := by linarith
  nth_rewrite 3 [← Real.coe_toNNReal (p' + spf.σ⁻¹ * (q - q') * (p' / q')) (le_of_lt hp2)]
  rw [snorm_pow_eq_distribution sorry]
  rw [Real.coe_toNNReal (p' + spf.σ⁻¹ * (q - q') * (p' / q')) (le_of_lt hp2)]
  have h₀ : p' - 1 + spf.σ⁻¹ * (q - q') * (p' / q') =
      p' + spf.σ⁻¹ * (q - q') * (p' / q') - 1 := by linarith
  rw [← h₀]
  rw [← lintegral_const_mul']
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro t ht
    rw [value_integral_φ'' ht hq' hp' hγ]
    have hpq : p'/q' ≥ 0 := sorry
    have hpq2 : q' / p' * (p' / q') = 1 := sorry
    rw [mul_rpow_of_nonneg _ _ hpq, mul_rpow_of_nonneg _ _ hpq,
        mul_rpow_of_nonneg _ _ hpq, ← ENNReal.rpow_mul, add_mul, ← ENNReal.rpow_mul,
        mul_assoc (p' - 1), hpq2, mul_one, ENNReal.rpow_one, mul_assoc]
    · sorry
  · sorry

--- For Minkowski's inequality: first prove statement dual statement about the norm
lemma test_powers_2 (a : ℝ≥0∞) (c d : ℝ) :
  (a) * a ^ d = a ^ (1 + d) := by
  rw [← rpow_one a]

lemma minkowski_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in Ioi 0, ∫⁻ t : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') ≤
    (∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t) ^ (p' / q') ) ^ (q' / p') := sorry

lemma rpow_add_of_pos (a : ℝ≥0∞) (c d : ℝ) (hc : c > 0) (hd : d > 0):
    a ^ (c + d) = a ^ c * a ^ d := by
  have hcd : c + d  > 0 := by linarith
  rcases (eq_or_ne a 0) with a_eq_zero | a_ne_zero
  · rw [a_eq_zero]
    rw [zero_rpow_of_pos hcd, zero_rpow_of_pos hc, zero_rpow_of_pos hd, mul_zero]
  · rcases (eq_or_ne a ⊤) with a_eq_top | a_ne_top
    · rw [a_eq_top]
      rw [top_rpow_of_pos hcd, top_rpow_of_pos hc, top_rpow_of_pos hd, top_mul_top]
    · rw [ENNReal.rpow_add c d a_ne_zero a_ne_top]

lemma test_powers_4 (a : ℝ≥0∞) (c d : ℝ) (hc : c > 0) (hd : d > 0):
  (⊤ : ℝ≥0∞) ^ c = ⊤ := by
  exact top_rpow_of_pos hc

lemma exists_monotone_integrable {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∃ g : ℕ → α → ℝ≥0∞, Monotone g ∧ ∀ n : ℕ, ∫⁻ x, g n x ∂μ < ⊤ ∧
    ⨆ n : ℕ, g n = f := by
  sorry

lemma representationLp {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : Measurable f) {p q : ℝ} (hp : p > 1) (hq : q ≥ 1)
    (hpq : 1 / p + 1 / q = 1):
    ∫⁻ x : α, (f x) ^ p ∂μ =
    ⨆ g ∈ {g' : α → ℝ≥0∞ | ∫⁻ x : α, (g x) ^ q ∂μ ≤ 1},
    ∫⁻ x : α, (f x) * g x ∂μ := by
  let A := spanningSets μ
  have A_mon := monotone_spanningSets μ
  let g := fun n : ℕ ↦ (A n).indicator (fun x ↦ min (f x) n)
  have g_mon : Monotone g := by
    intro m n hmn x; unfold_let g; unfold indicator; simp only
    split <;> rename_i hx1
    · split <;> rename_i hx2
      · refine min_le_min_left (f x) (Nat.cast_le.mpr hmn)
      · exact (False.elim (hx2 (A_mon hmn hx1)))
    · exact zero_le _
  have f_mul : ∀ n : ℕ, (g n) ^ p ≤ f * (g n) ^ (p - 1) := by
    intro n x; unfold_let g; unfold indicator; simp; split <;> rename_i hx1
    · refine le_trans (b := (min (f x) ↑n) * min (f x) ↑n ^ (p - 1)) ?_ ?_
      · nth_rewrite 1 [← add_sub_cancel 1 p]
        rw [rpow_add_of_pos, ENNReal.rpow_one]; exact Real.zero_lt_one; linarith
      · exact mul_le_mul_right' (min_le_left (f x) ↑n) (min (f x) ↑n ^ (p - 1))
    · rw [zero_rpow_of_pos]; exact zero_le _; linarith
  have g_sup : ∀ x : α, ⨆ n : ℕ, g n x = f x := by
    intro x; refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?h₁ ?h₂
    · intro n; unfold_let g; unfold indicator; simp only
      split; exact min_le_left (f x) ↑n; exact zero_le (f x)
    · intro w hw
      rcases (exists_exists_eq_and.mp
          (Eq.mpr (id (congrArg (fun _a ↦ x ∈ _a) (MeasureTheory.iUnion_spanningSets μ))) True.intro)) with ⟨m, wm⟩
      rcases exists_nat_gt (w.toReal + (f x).toReal) with ⟨n, wn⟩
      use n + m
      unfold_let g; unfold indicator; simp only
      split <;> rename_i hx
      · rcases (eq_top_or_lt_top (f x)) with fx_eq_top | fx_lt_top
        · simp only [Nat.cast_add, lt_min_iff]; simp [fx_eq_top] at wn
          exact ⟨hw, lt_of_lt_of_le (b := (n : ℝ≥0∞))
              ((toNNReal_lt_toNNReal (LT.lt.ne_top hw) coe_ne_top).mp wn) le_self_add⟩
        · rw [min_eq_left]; exact hw
          rw [Nat.cast_add]
          refine le_trans (le_of_lt ?_) (le_self_add (a := (n : ℝ≥0∞)) (c := m))
          rw [← (ofReal_toReal_eq_iff.mpr (LT.lt.ne_top fx_lt_top))]
          exact (ofReal_lt_iff_lt_toReal toReal_nonneg coe_ne_top).mpr
              (lt_of_add_lt_of_nonneg_right wn (toReal_nonneg))
      · refine False.elim (hx (A_mon le_add_self wm))

-- lemma value_integral_φ₀''' {p₀ q₀ q β : ℝ} (hβ : β ≥ 0) (hqq₀ : 0 < q - q₀) :
--     ∫⁻ (s : ℝ) in Ioo 0 β, ENNReal.ofReal s ^ (((q - q₀ - 1) * p₀ / q₀) * (q₀ / p₀)) =
--     ENNReal.ofReal (β ^ (q - q₀) / (q - q₀))
--     := by
--   have h₀ : q - q₀ - 1 + 1 = q - q₀ := by linarith
--   have power_pos : - 1 < q - q₀ - 1 := by linarith
--   nth_rewrite 2 [← h₀]; nth_rewrite 3 [← h₀]
--   rw [← compute_integral'' hβ power_pos]
--   have eqqs : (q - q₀ - 1) * p₀ / q₀ * (q₀ / p₀) = q - q₀ - 1 := by
--     sorry
--   apply lintegral_congr_ae
--   filter_upwards [self_mem_ae_restrict measurableSet_Ioo]
--   intro s hs
--   rw [eqqs, ofReal_rpow_of_pos hs.1]

-- lemma value_integral_φ₀' {p₀ q₀ q σ : ℝ} {g : ℝ → ℝ} (ht : t > 0)
--     (hσ : σ > 0) (hp₀ : p₀ ≥ 1) (hqq₀ : 0 < q - q₀):
--     ∫⁻ s : ℝ in Ioi 0, φ₀ μ f p₀ q₀ q (g s) s t ^ (q₀ / p₀) =
--     ENNReal.ofReal ((t ^ σ⁻¹) ^ (q - q₀) / (q - q₀)) *
--     (ENNReal.ofReal t ^ (p₀ - 1)) ^ (q₀ / p₀) *
--     distribution f (ENNReal.ofReal t) μ ^ (q₀ / p₀) := by
--   have hβ : t ^ σ⁻¹ ≥ 0 := by sorry
--   rw [← value_integral_φ₀''' (p₀ := p₀) hβ hqq₀]
--   -- rw [value_integral_φ₀ ht hσ]
--   have h₀ : (q₀ / p₀) ≥ 0 := by sorry
--   rw [funext fun s : ℝ ↦ ENNReal.mul_rpow_of_nonneg _ (distribution f (ENNReal.ofReal t) μ) h₀]
--   rw [lintegral_mul_const']
--   · rw [funext fun s : ℝ ↦ ENNReal.mul_rpow_of_nonneg _ (ENNReal.ofReal t ^ (p₀ - 1)) h₀]
--     rw [lintegral_mul_const']
--     rw [← funext fun s ↦ ENNReal.rpow_mul (ENNReal.ofReal s) ((q - q₀ - 1) * p₀ / q₀) (q₀ / p₀)]
--     refine rpow_ne_top_of_nonneg h₀ (rpow_ne_top_of_nonneg ?_ coe_ne_top)
--     linarith
--   · sorry

-- lemma value_integral_φ₀'' {p₀ q₀ p q σ : ℝ} (hσ : σ > 0) (hp₀ : p₀ ≥ 1) (hqq₀ : 0 < q - q₀) :
--     ∫⁻ t : ℝ in Ioi 0, (∫⁻ s : ℝ in Ioi 0, φ₀ μ f p₀ q₀ q (s ^ σ) s t ^ (q₀ / p₀)) ^ (p₀ / q₀) =
--     ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal ((t ^ σ⁻¹) ^ (q - q₀) / (q - q₀)) *
--     (ENNReal.ofReal t ^ (p₀ - 1)) ^ (q₀ / p₀) *
--     distribution f (ENNReal.ofReal t) μ ^ (q₀ / p₀) := by
--   apply lintegral_congr_ae
--   filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
--   intro t ht
--   have h₀ : 0 < p₀ / q₀ := by sorry
--   #check mul_rpow_of_nonneg
--   rw [value_integral_φ₀' ht hσ hp₀ hqq₀]
--   #check mul_rpow_of_nonneg
--   rw [mul_rpow_of_nonneg (hz := le_of_lt h₀)]
--   rw [mul_rpow_of_nonneg (hz := le_of_lt h₀)]
--   rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← Real.rpow_mul (le_of_lt ht)]
--   rw [← ofReal_rpow_of_pos]
--   · sorry

--   sorry

lemma test (f : α → E) :
  ‖ ∫ x : α, f x ∂μ ‖₊ ≤ ∫⁻ x : α, ‖f x‖₊ ∂ μ := by
  exact ennnorm_integral_le_lintegral_ennnorm fun a ↦ f a

lemma test' (f g : α → E) :
    ‖ ∫ x : α, ‖g x‖₊ • f x ∂μ ‖₊ ≤ ∫⁻ x : α, ‖‖g x‖₊ • f x‖₊ ∂μ := by
  exact test _

lemma test_2 (z : E) : ‖‖z‖‖₊ = ‖z‖₊ := by
  exact nnnorm_norm z

lemma test'' (f g : α → E) :
    ∫⁻ x : α, ‖‖g x‖ • f x‖₊ ∂μ = ∫⁻ x : α, ‖g x‖₊ * ‖f x‖₊ ∂μ := by
  apply congr_arg
  ext x
  rw [nnnorm_smul (r := ‖g x‖)]
  rw [nnnorm_norm]
  rw [coe_mul]


/-- Marcinkiewicz real interpolation theorem. -
-- feel free to assume that T also respect a.e.-equality if needed. -/
/- For the proof, see
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.4, theorem 6.28.
You want to use `trunc f A` when the book uses `h_A`.
Minkowski's inequality is `ENNReal.lintegral_Lp_add_le` -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) :
    ∃ C > 0, HasStrongType T p q μ ν C := by
  exists ?_
  constructor
  · sorry
  · unfold HasStrongType
    intros f fMem
    constructor
    · exact h₂T f fMem
    · let A := (3 : ℝ).toNNReal
      have h₀ : ∫⁻ x, ‖trunc f A x‖₊ ^ p.toReal ∂μ =
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
          distribution (trunc f A) (ENNReal.ofReal t) μ := by
        apply lintegral_norm_pow_eq_distribution
        sorry
      -- #check distribution_trunc
      -- have h₁ := distribution_trunc (f := f) (s := ENNReal.ofReal t) (t := A.toReal) (μ := μ)
      -- rewrite [h₁] at h₀
      -- have h₁ : ∫⁻ t in Ioo 0 A, ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ =
      --     ∫⁻ x : ℝ, (Ioo 0 A).indicator (fun t : ℝ ↦ ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ) := by
      sorry
      -- have h₂ : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
      --     distribution (trunc f A) (ENNReal.ofReal t) μ =
      --     ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ := by
      --   rewrite [← lintegral_indicator (hs := measurableSet_Ioi)]
      --   rewrite [← lintegral_indicator (hs := measurableSet_Ioo)]
      --   apply congr_arg
      --   ext t
      --   unfold indicator
      --   simp
      --   rewrite [distribution_trunc]
      --   simp
      --   split <;> rename_i h₃
      --   · split <;> rename_i h₄
      --     · split <;> rename_i h₅
      --       · rfl
      --       · simp at h₅
      --         have h₆ := h₅ h₃
      --         have _ : t < ↑A := by
      --           rewrite [← ofReal_coe_nnreal] at h₄
      --           refine (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₃)).mp h₄
      --         linarith
      --     · split <;> rename_i h₅
      --       · have _ : A.toReal ≤ t := by
      --           simp at h₄
      --           rewrite [← ofReal_coe_nnreal] at h₄
      --           exact (ofReal_le_ofReal_iff (le_of_lt h₃)).mp h₄
      --         linarith
      --       · rfl
      --   · split <;> rename_i h₄
      --     · linarith
      --     · rfl
      -- unfold HasWeakType at h₀T
      -- unfold wnorm at h₀T
      -- unfold wnorm' at h₀T
      -- -- have h₃ : ∫⁻ x, ‖T f (x)‖₊ ^q.toReal ∂ν  =
      --     2^q.toReal * q * ∫⁻ s in Ioi (0 : ℝ),
      --     ENNReal.ofReal s^(q.toReal - 1) * distribution (T f) ((ENNReal.ofReal 2)*(ENNReal.ofReal s)) ν := by
      --   have one_le_q : (1 : ℝ) ≤ q.toReal := sorry
      --   rewrite [lintegral_norm_pow_eq_distribution one_le_q]
      --   · have two_gt_0 : (2 : ℝ) > 0 := by linarith
      --     nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := 2) two_gt_0]
      --     have h₄ : ENNReal.ofReal |2| ≠ ⊤ := coe_ne_top
      --     have h₅ : (2 ^ q.toReal) * q ≠ ⊤ := sorry
      --     rewrite [← lintegral_const_mul' (hr := h₄)]
      --     rewrite [← lintegral_const_mul' (hr := h₅)]
      --     apply set_lintegral_congr_fun (measurableSet_Ioi)
      --     apply ae_of_all
      --     simp
      --     intros t t_gt_0
      --     rw [ofReal_mul' (le_of_lt t_gt_0)]
      --     have h₈ : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
      --       exact ofReal_eq_ofNat.mpr rfl
      --     rw [h₈]
      --     rw [← mul_assoc]
      --     rw [← mul_assoc]
      --     -- TODO: rename!!!
      --     apply test_9
      --     sorry

/- State and prove Remark 1.2.7 -/

end MeasureTheory
