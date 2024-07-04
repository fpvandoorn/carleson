import Carleson.WeakType
import Mathlib.Analysis.SpecialFunctions.Integrals

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

#check snorm
#check MeasureTheory.lintegral_inter_add_diff

lemma split_integration_domain (f : α → ℝ≥0∞) (s u v : Set α) (hs : s = u ⊔ v):
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in u, f x ∂μ + ∫⁻ x in v, f x ∂μ := by
  apply?

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

set_option diagnostics true

lemma distribution_shift_trunc (t : ℝ) (s : ℝ≥0∞) :
    distribution (f - (trunc f t)) s μ = distribution f (s + t.toNNReal) μ := by
  -- TODO: clean up
  unfold distribution
  unfold trunc
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
          rewrite [← (sub_smul)]
          rewrite [norm_smul]
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
    if s < t.toNNReal then distribution f s μ else 0 := by
  split <;> rename_i h₀
  · unfold distribution
    apply congrArg μ
    ext x
    simp
    unfold trunc
    split <;> rename_i h₁
    · rfl
    · split <;> rename_i h₂
      have h₄ : ofNNReal ↑‖(t * ‖f x‖⁻¹) • f x‖₊ = ofNNReal t.toNNReal := by
        sorry
      rewrite [h₄]
      · constructor
        · intro h
          have h₅ : t < ‖f x‖ := by
            exact lt_of_not_ge h₁
          have h₆ : t.toNNReal < ‖f x‖.toNNReal := by
            refine (Real.toNNReal_lt_toNNReal_iff_of_nonneg ?hr).mpr h₅
            exact le_of_lt h₂
          sorry
        · intro h
          sorry
      · have h₃ : t.toNNReal = 0 := by
          apply Real.toNNReal_of_nonpos
          exact le_of_not_lt h₂
        rewrite [h₃] at h₀
        simp at h₀
  · unfold distribution
    unfold trunc
    have h₀ : {x | s < ↑‖if ‖f x‖ ≤ t then f x else if 0 < t then (t * ‖f x‖⁻¹) • f x else 0‖₊} =
        ∅ := by
      ext x
      simp
      split
      · sorry
      · split
        · sorry
        · sorry
    rewrite [h₀]
    exact OuterMeasureClass.measure_empty μ

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

-- lemma test_2 (a : ℝ):
--     MeasureTheory.Measure.map (fun x : ℝ ↦ a + x) MeasureTheory.volume = MeasureTheory.volume := by
--   exact Measure.IsAddLeftInvariant.map_add_left_eq_self a

-- lemma test_3 (a : ℝ) (f : ℝ → ENNReal) :
--   ∫⁻ x in Icc 1 2, f x = ∫⁻ x in Icc (1-a) (2-a), f (x + a) := by
--   refine Eq.symm (MeasurePreserving.lintegral_comp ?hg ?hf)
--   sorry

-- lemma test_4 (A : Set ℝ) (f : ℝ → ENNReal) :
--     ∫⁻ x in A, f x = ∫⁻ x, (A.indicator f) x := by
--   refine Eq.symm (lintegral_indicator f ?hs)
--   sorry

-- lemma test_5 (A: Set ℝ) (f g : ℝ → ENNReal):
--     g * A.indicator f = A.indicator (g * f) := by
--   ext x
--   unfold indicator
--   show_term {
--     change g x * @ite ℝ≥0∞ (x ∈ A) (Classical.decPred (fun x ↦ x ∈ A) x) (f x) 0 = @ite ℝ≥0∞ (x ∈ A) (Classical.decPred (fun x ↦ x ∈ A) x) ((g * f) x) 0
--     rewrite [mul_ite]
--     rewrite [mul_zero]
--     rfl
--   }

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
  rw [lintegral_scale_constant_halfspace f h]
  rw [← mul_assoc]
  rw [← ofReal_mul (abs_nonneg a)]
  rw [@abs_inv]
  rw [mul_inv_cancel (abs_ne_zero.mpr h)]
  simp

lemma lintegral_scale_constant' {f: ℝ → ENNReal} {a : ℝ} (h : a ≠ 0):
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h]
  rw [← mul_assoc]
  rw [← ofReal_mul (abs_nonneg a)]
  rw [@abs_inv]
  rw [mul_inv_cancel (abs_ne_zero.mpr h)]
  simp

-- lemma test_7 (A : Set ℝ) (f: ℝ → ENNReal):
--     ∫⁻ x in A, f x = ∫⁻ x, f x := by
--   apply MeasureTheory.setLIntegral_eq_of_support_subset

-- lemma test_8 (A: Set ℝ) (f : ℝ → ENNReal) (a : ENNReal) :
--   a * ∫⁻ x in A, f x = ∫⁻ x in A, a * f x := by
--   refine Eq.symm (lintegral_const_mul' a (fun a ↦ f a) ?hr)

lemma test_9 (a b c : ℝ≥0∞) :
  a = b → a * c = b * c := by
  exact fun a_1 ↦ congrFun (congrArg HMul.hMul a_1) c

-- lemma test_10 (a b c : ℝ) :
--   a ^ b * a ^c = a ^ (b + c) := by
--   refine Eq.symm (Real.rpow_add ?hx b c)

-- lemma test_11 (P : ℝ → Prop) (A : Set ℝ) (h : ∀ x ∈ A, P x) (μ : Measure ℝ):
--     ∀ᵐ x : ℝ, x ∈ A → P x := by
--   exact ae_of_all volume h

-- lemma test_12 (a b : ℝ) :
--   ENNReal.ofReal (a + b) = ENNReal.ofReal a + ENNReal.ofReal b := by
--   apply?

-- lemma test_13 (f g: ℝ → ENNReal) (h : ∀ x : ℝ, f x = g x):
--     ∫⁻ x : ℝ, f x = ∫⁻ x : ℝ, g x := by
--   rw [h]

-- lemma test_14 (f g: ℝ → ENNReal) (h : ∀ x : ℝ, f x = g x):
--     (fun x ↦ f x) = fun x ↦ g x := by
--   rw [h]

-- lemma test_15 (f g : ℝ → ENNReal) (s : Set ℝ) (h : ∀ x ∈ s, f x ≤ g x) (μ : Measure ℝ):
--     ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ := by
--   #check set_lintegral_mono'



lemma estimate_trunc' (p₁ : ℝ≥0∞) (A : ℝ):
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
          distribution (trunc f A) (ENNReal.ofReal t) μ =
          ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
          distribution f (ENNReal.ofReal ↑t) μ := by
  rewrite [← lintegral_indicator (hs := measurableSet_Ioi)]
  rewrite [← lintegral_indicator (hs := measurableSet_Ioo)]
  apply congr_arg
  ext t
  unfold indicator
  simp
  rewrite [distribution_trunc]
  simp
  split <;> rename_i h₃
  · split <;> rename_i h₄
    · split <;> rename_i h₅
      · rfl
      · simp at h₅
        have h₆ := h₅ h₃
        have _ : t < ↑A := by
          rewrite [← ofReal_coe_nnreal] at h₄
          refine (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₃)).mp h₄
        linarith
    · split <;> rename_i h₅
      · have _ : A ≤ t := by
          simp at h₄
          rewrite [← ofReal_coe_nnreal] at h₄
          exact (ofReal_le_ofReal_iff (le_of_lt h₃)).mp h₄
        linarith
      · rfl
  · split <;> rename_i h₄
    · linarith
    · rfl

lemma estimate_trunc (p₁ : ℝ≥0∞) (A : ℝ):
  snorm (trunc f A) p₁ μ =
  (∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, p₁ * ENNReal.ofReal t ^ (p₁.toReal - 1) *
          distribution f (ENNReal.ofReal t) μ) ^ p₁.toReal⁻¹ := by
  sorry

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

lemma estimate_trunc_compl'' {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (f : α → E) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ x, ‖(f - trunc f a) x‖₊ ^ p₀ ∂μ ≤
    ∫⁻ s : ℝ in Ioi a, ENNReal.ofReal p₀ * ENNReal.ofReal (s ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal s) μ := by
  rw [estimate_trunc_compl hp₀ ha]
  rw [estimate_trunc_compl']
  apply set_lintegral_mono' measurableSet_Ioi
  simp
  intros t t_gt_a
  apply mul_le_mul_three
  · exact le_of_eq rfl
  · apply ofReal_le_ofReal_iff'.mpr
    left
    apply Real.rpow_le_rpow
    · linarith
    · linarith
    · linarith
  · exact le_of_eq rfl

lemma estimate_snorm_trunc_compl {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (f : α → E) {a : ℝ} (ha : 0 ≤ a) :
  snorm (f - trunc f a) (ENNReal.ofReal p₀) μ ≤
  (∫⁻ s : ℝ in Ioi a, ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
    distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
  refine (ENNReal.rpow_one_div_le_iff ?hz).mp ?_
  · sorry
  · unfold snorm
    split <;> rename_i h₁
    · contrapose! h₁
      sorry
    · split <;> rename_i h₂
      · sorry
      · unfold snorm'
        simp

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
    -- TODO: rename!!!
    apply test_9
    rw [Real.mul_rpow (le_of_lt two_gt_0) (le_of_lt zero_lt_t), ← mul_assoc]
    rw [ofReal_mul]
    · rw [← mul_assoc]
      apply test_9
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

lemma test_power (a b : ℝ) (q : ℝ) (h : a ^ q ≤ b ^ q) :
  a ≤ b := by
  refine (Real.rpow_le_rpow_iff (z := q) ?hx ?hy ?hz).mp h
  · sorry
  · sorry
  · sorry

lemma test_power_1 (a b : ℝ) (q : ℝ) (h : a ^ (q⁻¹) ≤ b) :
  a  ≤ b ^ q := by
  refine (Real.rpow_le_rpow_iff (z := q) ?hx ?hy ?hz).mp ?_
  sorry

lemma test_power_2 (a b : ℝ≥0∞) (q : ℝ) (h : a ^ (q⁻¹) ≤ b) :
  a  ≤ b ^ q := by
  refine (ENNReal.rpow_one_div_le_iff ?hz).mp ?_
  sorry

lemma test_of_NNREAL {a b : ℝ≥0} : ENNReal.ofNNReal a * ENNReal.ofNNReal b = ENNReal.ofNNReal (a * b) :=
  by
  show_term {
    exact rfl
  }

lemma test_of_NNReal' {a b : ℝ} : a.toNNReal * b.toNNReal = (a*b).toNNReal :=
  by
  show_term {
    refine Eq.symm (Real.toNNReal_mul ?hp)
  }

lemma test_mul_inv (t : ℝ) (ht : t ≠ 0) : t * t⁻¹ = 1 := by
  exact CommGroupWithZero.mul_inv_cancel t ht

lemma lintegral_const_mul_set' {r : ℝ≥0∞} (hr : r ≠ ⊤) (s : Set α) (f : α → ℝ≥0∞):
    r * ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, r * f x ∂μ :=
  Eq.symm (lintegral_const_mul' r (fun a ↦ f a) hr)

lemma lintegral_double_restrict_set {A B: Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := set_lintegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]

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

lemma test_ (a b : ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) :
    (a * b) ^ c=  a ^ c * b ^ c := by
  refine mul_rpow_of_nonneg a b ?hz

lemma test__ (a : ℝ≥0∞) (b c : ℝ) (hc : c ≠ 0) :
    (a ^ b) ^ c=  a ^ (b * c) := by
  apply?

lemma test___ (a b c: ℝ≥0∞) (h : b = c) : b * a = c * a := by
  exact congrFun (congrArg HMul.hMul h) a

lemma test_2 (a b: ℝ≥0∞) (c : ℝ) (hc : c ≥ 0) (hineq : a = b) :
    a ^ c = b ^ c := by
  exact congrFun (congrArg HPow.hPow hineq) c

lemma test_3 (a b : ℝ) (ha : a ≠ 0) : a⁻¹ * b = b / a := by apply?

-- lemma estimate_trunc_integral (f : α → E₁) (q p₁ q₁ : ℝ) (a σ : ℝ) :
--     ∫⁻ (s : ℝ) in Ioi 0,
--     ENNReal.ofReal s ^ (q - q₁ - 1) * (snorm (trunc f (s ^ σ)) (ENNReal.ofReal p₁) μ) ^ q₁ =
--     ∫⁻ s : ℝ in Ioi 0,
--     ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁ ) * (φ₁ μ f p₁ q₁ q σ s t )) ^ (q₁ / p₁) := by
--   apply set_lintegral_congr_fun measurableSet_Ioi
--   apply ae_of_all
--   intro s hs
--   rw [estimate_trunc]
--   have hq₀ : q₁ ≠ 0 := by sorry
--   have hp₀inv : p₁⁻¹ ≠ 0 := by sorry
--   have hp₀ : (ENNReal.ofReal p₁).toReal = p₁ := by
--     refine toReal_ofReal sorry
--   have h₁ : p₁⁻¹ * q₁ ≠ 0 := by sorry
--   have h₂ : p₁⁻¹ * q₁ ≥ 0 := by sorry
--   rw [hp₀]
--   rw [← ENNReal.rpow_mul, div_eq_inv_mul]
--   rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₁ - 1))]
--   rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
--   rw [← mul_rpow_of_nonneg (hz := h₂)]
--   rw [← lintegral_const_mul']
--   apply ENNReal.rpow_le_rpow
--   unfold φ₁
--   nth_rewrite 2 [lintegral_double_restrict_set (B := Ioo (0 : ℝ) (s ^ σ))]
--   have h₃ : Ioi (0 : ℝ) ∩ Ioo (0 : ℝ) (s ^ σ) = Ioo (0 : ℝ) (s ^ σ) := by
--     unfold Ioi Ioo
--     simp
--     tauto
--   rw [h₃]
--   apply set_lintegral_mono_ae' (measurableSet_Ioo)
--   apply ae_of_all
--   intro t ht; simp at ht
--   rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₁)]
--   sorry

lemma estimate_trunc_comp_integral (f : α → E₁) (q p₀ q₀ : ℝ) (hp₀ : 1 ≤ p₀) (β : ℝ) :
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
    have hq₀ : q₀ ≥ 0 := by sorry
    have h₀ : snorm (f - trunc f β) (ENNReal.ofReal p₀) μ ≤
        (∫⁻ s : ℝ in Ioi β, ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
        distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
      apply estimate_snorm_trunc_compl hp₀
      sorry
    exact ENNReal.rpow_le_rpow h₀ hq₀
  · have hq₀ : q₀ ≠ 0 := by sorry
    have hp₀inv : p₀⁻¹ ≠ 0 := by sorry
    have hp₀ : (ENNReal.ofReal p₀).toReal = p₀ := by
      refine toReal_ofReal sorry
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

lemma test_powers (a b c : ℝ) (hc : c ≠ 0) : (a ^ c) ^ c⁻¹ = a := by
  refine Real.rpow_rpow_inv ?hx hc


lemma value_integral_φ₀ {p₀ q₀ q σ t : ℝ} {μ : Measure α} {f : α → E₁} (ht : t > 0)
    (hσ : σ > 0) :
    ∫⁻ s : ℝ in Ioi 0, φ₀ μ f p₀ q₀ q (s ^ σ) s t ^ (q₀ / p₀) =
    ∫⁻ s : ℝ in Ioo 0 (t ^ (σ⁻¹)),
    (ENNReal.ofReal s ^ ((q - q₀ - 1) * p₀ / q₀) * ENNReal.ofReal t ^ (p₀ - 1) *
        distribution f (ENNReal.ofReal t) μ) ^ (q₀ / p₀) := by
  unfold φ₀
  rw [lintegral_double_restrict_set (B := Ioo 0 (t ^ σ⁻¹)) _ measurableSet_Ioo]
  · have h₀ : Ioi 0 ∩ Ioo 0 (t ^ σ⁻¹) = Ioo 0 (t ^ σ⁻¹) := by sorry
    rw [h₀]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo]
    simp
    intro s hs1 hs2 hs3
    contrapose! hs2
    refine (Real.rpow_inv_le_iff_of_pos (le_of_lt ht) (le_of_lt hs1) hσ).mpr hs3
  · apply ae_of_all
    simp
    intro s hs1 hs2
    split <;> rename_i hs3
    · contrapose! hs3
      refine (Real.rpow_le_rpow_iff (z := σ⁻¹) (le_of_lt ht) ?hy (inv_pos_of_pos hσ)).mp ?_
      · sorry
      · rw [Real.rpow_rpow_inv (le_of_lt hs1) (ne_of_gt hσ)]
        exact hs2 hs1
    · refine zero_rpow_of_pos ?_
      sorry
  · exact measurableSet_Ioi


-- lemma equality_integrals (g : ℝ → ℝ≥0∞) :
--   ∫ x : ℝ in Icc 0 1, g x = ∫⁻ x : ℝ, f x := by
--   apply?

-- lemma compute_integral (β σ : ℝ) (hσ : -1 < σ):
--     ∫ (s : ℝ) in Ioc 0 β, s ^ σ =  (β ^ (σ + 1) - 0 ^ (σ + 1)) / (σ + 1) := by


-- lemma compute_integral (β σ : ℝ) (hσ : -1 < σ):
--     ∫ (s : ℝ) in (0)..β, s ^ σ =  (β ^ (σ + 1) - 0 ^ (σ + 1)) / (σ + 1) := by
--   exact integral_rpow (Or.inl hσ)

-- lemma compute_integral' (β σ : ℝ) (hσ : -1 < σ):
--     ∫⁻ s : ℝ in Ioc 0 β, ENNReal.ofReal (s ^ σ) =
--     ENNReal.ofReal (∫ (s : ℝ) in Ioc 0 β, s ^ σ) := by
--   rw [ofReal_integral_eq_lintegral_ofReal]
--   exact (@intervalIntegral.intervalIntegrable_rpow' 0 β σ hσ).1

lemma test_zero_pow (σ : ℝ) : (0 : ℝ) ^ σ = 0  := by
  apply?

lemma compute_integral'' {β σ : ℝ} (hβ : β ≥ 0) (hσ : -1 < σ):
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / (σ + 1)) := by
  rw [set_lintegral_congr Ioo_ae_eq_Ioc, ← sub_zero (β ^ (σ + 1))]
  have h₀ : σ + 1 ≠ 0 := by sorry
  nth_rewrite 2 [← Real.zero_rpow h₀]
  rw [← integral_rpow (Or.inl hσ)]
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  split
  · unfold uIoc
    rw [smul_eq_mul, one_mul, min_eq_left hβ, max_eq_right hβ, ofReal_integral_eq_lintegral_ofReal
        (@intervalIntegral.intervalIntegrable_rpow' 0 β σ hσ).1]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
    exact fun a ha ↦ Real.rpow_nonneg (le_of_lt ha.1) σ
  · contradiction

lemma compute_integral''' {p₀ q₀ p q γ: ℝ} (hqq₀ : q₀ < q) (hγ : γ ):
    ∫⁻ (s : ℝ) in Ioo 0 (t ^ σ⁻¹), ENNReal.ofReal s ^ (((q - q₀ - 1) * p₀ / q₀) * (q₀ / p₀)) =
    ENNReal.ofReal (β ^ (σ + 1) / (σ + 1)) := by

lemma test_integral_right (f : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
  ∫⁻ s : ℝ in Ioi 0, f s * c = (∫⁻ s : ℝ in Ioi 0, f s) * c := by
  exact lintegral_mul_const' c (fun a ↦ f a) hc

lemma test_power_3 (a c : ℝ) : ENNReal.ofReal (a ^ c) = ENNReal.ofReal a ^ c := by
  apply?

lemma test_integral (f g : ℝ → ℝ≥0∞) (hfg : ∀ x : ℝ, f x = g x) :
    ∫⁻ x : ℝ in Ioc 0 1, f x = ∫⁻ x : ℝ in Ioo 0 1, f x := by
  exact set_lintegral_congr (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)

lemma value_integral_φ₀''' {p₀ q₀ q β : ℝ} (hβ : β ≥ 0) (hqq₀ : 0 < q - q₀) :
    ∫⁻ (s : ℝ) in Ioo 0 β, ENNReal.ofReal s ^ (((q - q₀ - 1) * p₀ / q₀) * (q₀ / p₀)) =
    ENNReal.ofReal (β ^ (q - q₀) / (q - q₀))
    := by
  have h₀ : q - q₀ - 1 + 1 = q - q₀ := by linarith
  have power_pos : - 1 < q - q₀ - 1 := by linarith
  nth_rewrite 2 [← h₀]; nth_rewrite 3 [← h₀]
  rw [← compute_integral'' hβ power_pos]
  have eqqs : (q - q₀ - 1) * p₀ / q₀ * (q₀ / p₀) = q - q₀ - 1 := by
    sorry
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo]
  intro s hs
  rw [eqqs, ofReal_rpow_of_pos hs.1]

lemma value_integral_φ₀' {p₀ q₀ p q σ : ℝ} (ht : t > 0)
    (hσ : σ > 0) (hp₀ : p₀ ≥ 1) (hqq₀ : 0 < q - q₀):
    ∫⁻ s : ℝ in Ioi 0, φ₀ μ f p₀ q₀ q (s ^ σ) s t ^ (q₀ / p₀) =
    ENNReal.ofReal ((t ^ σ⁻¹) ^ (q - q₀) / (q - q₀)) *
    (ENNReal.ofReal t ^ (p₀ - 1)) ^ (q₀ / p₀) *
    distribution f (ENNReal.ofReal t) μ ^ (q₀ / p₀) := by
  have hβ : t ^ σ⁻¹ ≥ 0 := by sorry
  rw [← value_integral_φ₀''' (p₀ := p₀) hβ hqq₀]
  rw [value_integral_φ₀ ht hσ]
  have h₀ : (q₀ / p₀) ≥ 0 := by sorry
  rw [funext fun s : ℝ ↦ ENNReal.mul_rpow_of_nonneg _ (distribution f (ENNReal.ofReal t) μ) h₀]
  rw [lintegral_mul_const']
  · rw [funext fun s : ℝ ↦ ENNReal.mul_rpow_of_nonneg _ (ENNReal.ofReal t ^ (p₀ - 1)) h₀]
    rw [lintegral_mul_const']
    rw [← funext fun s ↦ ENNReal.rpow_mul (ENNReal.ofReal s) ((q - q₀ - 1) * p₀ / q₀) (q₀ / p₀)]
    refine rpow_ne_top_of_nonneg h₀ (rpow_ne_top_of_nonneg ?_ coe_ne_top)
    linarith
  · sorry

lemma value_integral_φ₀'' (p₀ q₀ p q σ : ℝ) :
    ∫⁻ t : ℝ in Ioi 0, (∫⁻ s : ℝ in Ioi 0, φ₀ μ f p₀ q₀ q σ s t ) ^ (p₀ / q₀) =
    (ENNReal.ofReal |q - q₀|) ^ (- p₀ / q₀) *
    ENNReal.ofReal p⁻¹ * snorm f (ENNReal.ofReal q) μ := by
  unfold φ₀
  sorry


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

      have h₂ : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
          distribution (trunc f A) (ENNReal.ofReal t) μ =
          ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
          distribution f (ENNReal.ofReal ↑t) μ := by
        rewrite [← lintegral_indicator (hs := measurableSet_Ioi)]
        rewrite [← lintegral_indicator (hs := measurableSet_Ioo)]
        apply congr_arg
        ext t
        unfold indicator
        simp
        rewrite [distribution_trunc]
        simp
        split <;> rename_i h₃
        · split <;> rename_i h₄
          · split <;> rename_i h₅
            · rfl
            · simp at h₅
              have h₆ := h₅ h₃
              have _ : t < ↑A := by
                rewrite [← ofReal_coe_nnreal] at h₄
                refine (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₃)).mp h₄
              linarith
          · split <;> rename_i h₅
            · have _ : A.toReal ≤ t := by
                simp at h₄
                rewrite [← ofReal_coe_nnreal] at h₄
                exact (ofReal_le_ofReal_iff (le_of_lt h₃)).mp h₄
              linarith
            · rfl
        · split <;> rename_i h₄
          · linarith
          · rfl
      unfold HasWeakType at h₀T
      unfold wnorm at h₀T
      unfold wnorm' at h₀T
      -- have h₃ : ∫⁻ x, ‖T f (x)‖₊ ^q.toReal ∂ν  =
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
