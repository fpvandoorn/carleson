import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Carleson.Defs
import Carleson.ToMathlib.Data.ENNReal
import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.MeasureTheory.Measure.AEMeasurable
import Carleson.ToMathlib.MeasureTheory.Function.SimpleFunc
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.ToMathlib.Rearrangement
import Carleson.ToMathlib.RealInterpolation.Misc

-- Upstreaming status: this file is actively being worked on; not ready yet

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

namespace MeasureTheory

variable {α α' ε₁ ε₂ : Type*} {m0 : MeasurableSpace α} {m : MeasurableSpace α'}
  {μ : Measure α} {ν : Measure α'} [TopologicalSpace ε₁] [TopologicalSpace ε₂] {p q : ℝ≥0∞}

/-- An operator has Lorentz type `(p, r, q, s)` if it is bounded as a map
from `L^{q, s}` to `L^{p, r}`. `HasLorentzType T p r q s μ ν c` means that
`T` has Lorentz type `(p, r, q, s)` w.r.t. measures `μ`, `ν` and constant `c`. -/
def HasLorentzType [ENorm ε₁] [ENorm ε₂] (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧
    eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ

lemma hasStrongType_iff_hasLorentzType [ESeminormedAddMonoid ε₁] [ESeminormedAddMonoid ε₂]
  {T : (α → ε₁) → (α' → ε₂)} {c : ℝ≥0∞} :
    HasStrongType T p q μ ν c ↔ HasLorentzType T p p q q μ ν c := by
  unfold HasStrongType HasLorentzType
  constructor
  · intro h f hf
    unfold MemLp MemLorentz at *
    rw [eLorentzNorm_eq_eLpNorm hf.1] at *
    have := h f hf
    rwa [eLorentzNorm_eq_eLpNorm this.1]
  · intro h f hf
    unfold MemLp MemLorentz at *
    rw [← eLorentzNorm_eq_eLpNorm hf.1] at *
    have := h f hf
    rwa [← eLorentzNorm_eq_eLpNorm this.1]


variable {β : Type*} [Zero β] [One β]

/-- Defines when an operator "has restricted weak type". This is an even weaker version
of `HasBoundedWeakType`. -/
def HasRestrictedWeakType [ENorm ε₂] (T : (α → β) → (α' → ε₂)) (p q : ℝ≥0∞)
  (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ q⁻¹.toReal

lemma HasRestrictedWeakType.without_finiteness [ESeminormedAddMonoid ε₂] {T : (α → β) → (α' → ε₂)}
    (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤)
    {c : ℝ≥0} (c_pos : 0 < c) (hT : HasRestrictedWeakType T p q μ ν c)
    (T_zero_of_ae_zero : ∀ {f : α → β} (_ : f =ᶠ[ae μ] 0), enorm ∘ T f =ᶠ[ae ν] 0) :
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (MeasurableSet G) →
    eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
      ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ q⁻¹.toReal := by
  intro F G hF hG
  have p_inv_pos : 0 < p⁻¹.toReal := by
    simp only [ENNReal.toReal_inv, inv_pos, ENNReal.toReal_pos p_ne_zero p_ne_top]
  have q_inv_pos : 0 < q⁻¹.toReal := by
    simp only [ENNReal.toReal_inv, inv_pos, ENNReal.toReal_pos q_ne_zero q_ne_top]
  by_cases hFG : μ F < ∞ ∧ ν G < ∞
  · exact (hT F G hF hFG.1 hG hFG.2).2
  · rw [not_and_or] at hFG
    rcases hFG with hF | hG
    · by_cases G_zero : ν G = 0
      · rw [G_zero, ENNReal.zero_rpow_of_pos q_inv_pos]
        simp only [ENNReal.toReal_inv, mul_zero, nonpos_iff_eq_zero]
        convert eLpNorm_measure_zero
        simpa
      simp only [not_lt, top_le_iff] at hF
      rw [hF]
      convert le_top
      rw [ENNReal.mul_eq_top]
      right
      constructor
      · rw [ENNReal.top_rpow_of_pos p_inv_pos, ENNReal.mul_top (by simp [c_pos.ne'])]
      simp only [ENNReal.toReal_inv, ne_eq, ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', not_or,
        not_and, not_lt, ENNReal.toReal_nonneg, implies_true, and_true]
      intro h
      exfalso
      exact G_zero h
    · by_cases F_zero : μ F = 0
      · rw [F_zero, ENNReal.zero_rpow_of_pos p_inv_pos]
        simp only [mul_zero, ENNReal.toReal_inv, zero_mul, nonpos_iff_eq_zero]
        rw [← nonpos_iff_eq_zero]
        apply (eLpNorm_restrict_le _ _ _ _).trans
        simp only [nonpos_iff_eq_zero]
        apply eLpNorm_zero_of_ae_zero' (T_zero_of_ae_zero (indicator_meas_zero F_zero))
      simp only [not_lt, top_le_iff] at hG
      rw [hG]
      convert le_top
      rw [ENNReal.mul_eq_top]
      left
      constructor
      · simp only [ENNReal.toReal_inv, ne_eq, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_pos,
          inv_neg'', not_or, not_and, not_lt, ENNReal.toReal_nonneg, implies_true, and_true]
        use (by simp [c_pos.ne'])
        intro h
        exfalso
        exact F_zero h
      rw [ENNReal.top_rpow_of_pos q_inv_pos]

/-- An enhanced version of `HasRestrictedWeakType` -/
def HasRestrictedWeakType' [TopologicalSpace β] [ENorm β] [ENorm ε₂] (T : (α → β) → (α' → ε₂)) (p q : ℝ≥0∞)
  (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (f : α → β) (_ : MemLorentz f p 1 μ) (G : Set α') (_ : MeasurableSet G),
    AEStronglyMeasurable (T f) ν ∧
      eLpNorm (T f) 1 (ν.restrict G)
        ≤ c * eLorentzNorm f p 1 μ * (ν G) ^ q⁻¹.toReal

-- TODO: move
-- TODO: Could probably weaken assumption to (h : ∀ᶠ (x : β) in f, u x ≤ v x)
theorem Filter.mono_limsup {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u v : β → α} (h : ∀ (x : β), u x ≤ v x) : Filter.limsup u f ≤ Filter.limsup v f := by
  refine Filter.limsup_le_limsup ?_
  apply Filter.Eventually.of_forall h

-- TODO: move?
theorem Filter.limsup_le_of_le' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u : β → α} {a : α} (h : ∀ᶠ (n : β) in f, u n ≤ a) :
  Filter.limsup u f ≤ a := sInf_le h

-- TODO: move?
theorem ENNReal.rpow_add_rpow_le_add' {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  calc
    _ = ((a ^ p + b ^ p) ^ (1 / p)) ^ p := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      linarith
    _ ≤ (a + b) ^ p := by
      gcongr
      exact ENNReal.rpow_add_rpow_le_add _ _ hp1

-- TODO: move
theorem ENNReal.limsup_mul_const_of_ne_top {α : Type*} {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    Filter.limsup (fun x ↦ u x * a) f = Filter.limsup u f * a := by
  simp_rw [mul_comm]
  exact ENNReal.limsup_const_mul_of_ne_top ha_top

-- TODO: move
theorem ENNReal.limsup_mul_const {α : Type u_1} {f : Filter α} [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    limsup (fun x ↦ u x * a) f = limsup u f * a := by
  simp_rw [mul_comm, limsup_const_mul]

/-
def WeaklyContinuous [TopologicalSpace ε] (T : (α → ε) → (α' → ε')) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {f : α → ε} {fs : ℕ → SimpleFunc α ε}
  (hfs : ∀ (x : α), Filter.Tendsto (fun (n : ℕ) => (fs n) x) Filter.atTop (nhds (f x))) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop
-/

variable {ε ε' : Type*}

/-- The weak continuity assumption needed for `HasRestrictedWeakType.hasLorentzType_helper`. -/
def WeaklyContinuous [TopologicalSpace ε] [ENorm ε] [SupSet ε]
  [Preorder ε] [ENorm ε'] (T : (α → ε) → (α' → ε')) (p : ℝ≥0∞) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {fs : ℕ → SimpleFunc α ε} (_ : Monotone fs) (_ : BddAbove (range (fun n ↦ ⇑(fs n)))),
  let f := fun x ↦ ⨆ n, (fs n) x;
  ∀ (_ : MemLorentz f p 1 μ) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T ⇑(fs n)) 1 (ν.restrict G)) Filter.atTop


theorem HasRestrictedWeakType.hasRestrictedWeakType'_nnreal [TopologicalSpace ε'] [ENormedSpace ε']
    {c : ℝ≥0} (c_pos : 0 < c) {T : (α → ℝ≥0) → α' → ε'} (p_ne_top : p ≠ ⊤) (q_ne_top : q ≠ ⊤)
    (hpq : p.HolderConjugate q)
    (T_meas : ∀ {f : α → ℝ≥0}, (MemLorentz f p 1 μ) → AEStronglyMeasurable (T f) ν)
    (T_subadd : ∀ {f g : α → ℝ≥0}, (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
      ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (T_submul : ∀ (a : ℝ≥0) (f : α → ℝ≥0), ∀ᵐ x ∂ν, ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ * ‖T f x‖ₑ)
    (T_ae_eq_of_ae_eq : ∀ {f g : α → ℝ≥0}, (f =ᶠ[ae μ] g) → T f =ᶠ[ae ν] T g)
    (T_zero : T 0 =ᶠ[ae ν] 0)
    (hT : HasRestrictedWeakType T p q μ ν c)
    (weakly_cont_T : WeaklyContinuous T p μ ν) :
      HasRestrictedWeakType' T p q μ ν (c / p) := by
  have T_zero_of_ae_zero : ∀ {f : α → ℝ≥0} (_ : f =ᶠ[ae μ] 0), enorm ∘ T f =ᶠ[ae ν] 0 := by
    intro f hf
    filter_upwards [T_ae_eq_of_ae_eq hf, T_zero]
    intro a h h'
    simp only [comp_apply, Pi.zero_apply, enorm_eq_zero]
    rwa [h]
  have hcp : 0 < ↑c / p := by
    simp only [ENNReal.div_pos_iff, ne_eq, ENNReal.coe_eq_zero]
    use c_pos.ne', p_ne_top
  intro f hf' G hG
  use T_meas hf'
  wlog hf : Measurable f generalizing f
  · rcases hf'.1 with ⟨g, stronglyMeasurable_g, hfg⟩
    have hg' : MemLorentz g p 1 μ := by
      use StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_g
      convert hf'.2 using 1
      symm
      exact eLorentzNorm_congr_ae hfg
    have hg : Measurable g := stronglyMeasurable_g.measurable
    convert this g hg' hg using 1
    · apply eLpNorm_congr_ae
      apply ae_restrict_le
      exact T_ae_eq_of_ae_eq hfg
    · congr 2
      exact eLorentzNorm_congr_ae hfg
  have hp : 1 ≤ p := hpq.one_le
  have p_ne_zero : p ≠ 0 := hpq.ne_zero
  rw [eLorentzNorm_eq_eLorentzNorm' p_ne_zero p_ne_top]
  revert hf'
  revert f
  apply @Measurable.nnreal_induction _ m0
  · intro f
    induction f using SimpleFunc.induction''
    · rename_i a s hs
      rw [SimpleFunc.coe_restrict _ hs]
      have : s.indicator (Function.const α a) = a • (s.indicator (fun _ ↦ 1)) := by
        ext x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Set.indicator_const_mul]
        congr
        simp
      intro hf'
      calc _
        _ = eLpNorm (T (a • (s.indicator (fun _ ↦ 1)))) 1 (ν.restrict G) := by
          congr 1
          ext x
          congr
        _ ≤ ‖a‖ₑ * eLpNorm (T ((s.indicator (fun _ ↦ 1)))) 1 (ν.restrict G) := by
          rw [← eLpNorm_const_smul']
          apply eLpNorm_mono_enorm_ae
          apply ae_restrict_le
          simp only [Pi.smul_apply, enorm_smul_eq_smul]
          apply T_submul
        _ ≤ ‖a‖ₑ * (c * (μ s) ^ p⁻¹.toReal * (ν G) ^ q⁻¹.toReal) := by
          gcongr
          apply hT.without_finiteness p_ne_zero p_ne_top hpq.symm.ne_zero q_ne_top c_pos T_zero_of_ae_zero s G hs hG
        _ = c * (‖a‖ₑ * μ s ^ p⁻¹.toReal) * (ν G) ^ q⁻¹.toReal := by ring
        _ = (c / p) * eLorentzNorm' (s.indicator (Function.const α a)) p 1 μ * ν G ^ q⁻¹.toReal := by
          rw [eLorentzNorm'_indicator_const (by simp) p_ne_zero p_ne_top]
          rw [← mul_assoc (c / p), ENNReal.div_mul_cancel p_ne_zero p_ne_top]
    · rename_i f a s hs hfs hf hg
      rw [SimpleFunc.coe_add]
      set g := (SimpleFunc.const α a).restrict s with g_def
      intro hfg'
      have hf' : MemLorentz f p 1 μ :=
        ⟨by fun_prop, hfg'.2.trans_le' <| eLorentzNorm_mono_enorm_ae (by simp)⟩
      have hg' : MemLorentz g p 1 μ := ⟨by fun_prop, hfg'.2.trans_le' <| eLorentzNorm_mono_enorm_ae (by simp)⟩
      calc _
        _ ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G) := by
          nth_rw 2 [← eLpNorm_enorm]
          nth_rw 3 [← eLpNorm_enorm]
          apply (eLpNorm_add_le _ _ (by rfl)).trans'
          · apply eLpNorm_mono_enorm_ae
            simp only [Pi.add_apply, enorm_eq_self]
            exact ae_restrict_le (T_subadd hf' hg')
          · exact (T_meas hf').enorm.aestronglyMeasurable.restrict
          · exact (T_meas hg').enorm.aestronglyMeasurable.restrict
        _ ≤ c / p * eLorentzNorm' f p 1 μ * ν G ^ q⁻¹.toReal + c / p *  eLorentzNorm' g p 1 μ * ν G ^ q⁻¹.toReal := by
          gcongr
          · exact hf hf'
          · exact hg hg'
        _ = c / p * eLorentzNorm' (f + g) p 1 μ * ν G ^ q⁻¹.toReal := by
          rw [← add_mul, ← mul_add]
          congr
          rw [eLorentzNorm'_eq_integral_distribution_rpow,
            eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_eq_integral_distribution_rpow]
          rw [← mul_add]
          congr 1
          rw [SimpleFunc.coe_add, g_def, SimpleFunc.coe_restrict _ hs, SimpleFunc.coe_const]
          symm
          calc _
            _ = ∫⁻ (t : ℝ≥0), (if t < a then μ s else distribution f (t - a) μ) ^ p.toReal⁻¹ := by
              congr with t
              congr
              rw [distribution_indicator_add_of_support_subset_nnreal (μ := μ) hfs]
              simp only [ENNReal.coe_lt_coe]
            _ = ∫⁻ (t : ℝ≥0), if t < a then μ s ^ p.toReal⁻¹ else distribution f (t - a) μ ^ p.toReal⁻¹ := by
              simp only [ite_pow]
            _ = ∫⁻ (t : ℝ≥0), (Set.Iio a).indicator (fun _ ↦ μ s ^ p.toReal⁻¹) t
                  + (Set.Ici a).indicator (fun t ↦ distribution f (t - a) μ ^ p.toReal⁻¹) t := by
              congr with t
              rw [← Set.compl_Iio, ← Pi.add_apply, Set.indicator_add_compl_eq_piecewise]
              unfold Set.piecewise
              simp
            _ = a * μ s ^ p.toReal⁻¹ + ∫⁻ (t : ℝ≥0), distribution f t μ ^ p.toReal⁻¹ := by
              rw [lintegral_add_left (by measurability)]
              congr 1
              · rw [lintegral_indicator_const measurableSet_Iio, NNReal.volume_Iio, mul_comm]
              · rw [lintegral_indicator measurableSet_Ici, setLIntegral_nnreal_Ici]
                simp
          rw [add_comm]
          congr
          apply (ENNReal.mul_right_inj p_ne_zero p_ne_top).mp
          rw [← eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_indicator_const (by simp) p_ne_zero p_ne_top]
          simp
  · intro f hf h hf'
    by_cases f_zero : f =ᶠ[ae μ] 0
    · have := T_zero_of_ae_zero f_zero
      rw [← eLorentzNorm_eq_eLorentzNorm' hpq.ne_zero p_ne_top, eLorentzNorm_congr_ae f_zero,
          eLpNorm_zero_of_ae_zero' (T_zero_of_ae_zero f_zero).restrict]
      simp only [eLorentzNorm_zero, mul_zero, toReal_inv, zero_mul, nonpos_iff_eq_zero]
    by_cases hG' : ν G = ∞
    · rw [hG', ENNReal.top_rpow_of_pos, ENNReal.mul_top]
      · exact le_top
      · apply mul_ne_zero hcp.ne'
        contrapose! f_zero
        rwa [eLorentzNorm'_eq_zero_iff p_ne_zero p_ne_top (by simp)] at f_zero
      · simp only [toReal_inv, inv_pos]
        exact ENNReal.toReal_pos hpq.symm.ne_zero q_ne_top
    rw [← SimpleFunc.iSup_nnapprox hf] at hf'
    calc _
      _ ≤ Filter.limsup (fun n ↦ eLpNorm (T (SimpleFunc.nnapprox f n)) 1 (ν.restrict G)) Filter.atTop := by
        nth_rw 1 [← SimpleFunc.iSup_nnapprox hf]
        apply weakly_cont_T SimpleFunc.monotone_nnapprox _ hf' G
        use f
        rw [mem_upperBounds]
        intro g hg
        rcases hg with ⟨n, hn⟩
        rw [← hn]
        intro x
        apply SimpleFunc.nnapprox_le hf
      _ ≤ Filter.limsup (fun n ↦ (c / p) * eLorentzNorm' (SimpleFunc.nnapprox f n) p 1 μ * ν G ^ q⁻¹.toReal) Filter.atTop := by
        apply Filter.mono_limsup
        intro n
        apply h n _
        use (by fun_prop)
        apply hf'.2.trans_le'
        apply eLorentzNorm_mono_enorm_ae
        apply Filter.Eventually.of_forall
        intro x
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        rw [SimpleFunc.iSup_nnapprox_apply hf]
        apply SimpleFunc.nnapprox_le hf
      _ ≤ (c / p) * eLorentzNorm' f p 1 μ * ν G ^ q⁻¹.toReal := by
        simp_rw [mul_assoc]
        rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.div_ne_top (by simp) p_ne_zero)]
        gcongr
        rw [ENNReal.limsup_mul_const_of_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) hG')]
        gcongr
        apply Filter.limsup_le_of_le'
        filter_upwards with n
        apply eLorentzNorm'_mono_enorm_ae
        filter_upwards with x
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        exact SimpleFunc.approx_le hf bot_eq_zero'


lemma HasRestrictedWeakType'.hasLorentzType [SigmaFinite ν]
  {𝕂 : Type*} [RCLike 𝕂] [TopologicalSpace ε'] [ENormedSpace ε']
  {T : (α → 𝕂) → (α' → ε')} (hpq : p.HolderConjugate q) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
  {c : ℝ≥0∞} (hc : c ≠ ⊤) (hT : HasRestrictedWeakType' T p q μ ν c) :
    HasLorentzType T p 1 p ∞ μ ν c := by
  intro f hf
  have hf' : AEStronglyMeasurable (T f) ν := (hT f hf ∅ MeasurableSet.empty).1
  use (hT f hf ∅ MeasurableSet.empty).1
  rw [eLorentzNorm_eq_wnorm hpq.ne_zero, wnorm_ne_top hp, wnorm']
  apply iSup_le
  intro l
  by_cases l_zero : l = 0
  · simp [l_zero]
  set G := {x | ↑l < ‖T f x‖ₑ}
  have hG : NullMeasurableSet G ν := by
    unfold G
    exact nullMeasurableSet_lt aemeasurable_const (by fun_prop)
  rcases hG.exists_measurable_superset_ae_eq  with ⟨G', _, hG', G'G⟩
  have measure_G'G := measure_congr G'G
  have measure_G : ν G = distribution (T f) l ν := by rfl
  rw [← measure_G]
  have p_toReal_pos : 0 < p.toReal := toReal_pos hpq.ne_zero hp
  have q_toReal_pos : 0 < q.toReal := toReal_pos hpq.symm.ne_zero hq
  by_cases G_finite : ν G = ⊤
  · exfalso
    rw [← measure_G'G] at G_finite
    set r := (c * eLorentzNorm f p 1 μ / ↑l) ^ p.toReal with r_def
    have : r < ν G' := by
      rw [G_finite]
      unfold r
      apply (ENNReal.rpow_lt_top_iff_of_pos p_toReal_pos).mpr
      have := hf.2.ne
      exact ENNReal.div_lt_top (by finiteness) (by simpa)
    rcases ν.exists_subset_measure_lt_top hG' this with ⟨H, hH, H_subset_G', H_gt, H_finite⟩
    have H_pos := (zero_le _).trans_lt H_gt
    apply (hT f hf H hH).2.not_gt
    calc _
      _ < l * ν H := by
        rw [← ENNReal.lt_div_iff_mul_lt
            (by left; rw [ne_eq, ENNReal.rpow_eq_zero_iff_of_pos (by simpa)]; exact H_pos.ne.symm)
            (by left; apply ENNReal.rpow_ne_top_of_nonneg (by simp) H_finite.ne), mul_div_assoc]
        nth_rw 1 [← ENNReal.rpow_one (ν H)]
        have : 1 - q⁻¹.toReal = p⁻¹.toReal := by
          have hpq' := ENNReal.holderConjugate_iff.mp hpq
          have : 1 = ENNReal.toReal 1 := by simp
          rw [this, ← hpq', toReal_add, add_sub_cancel_right]
          · simp only [ne_eq, inv_eq_top]
            exact hpq.ne_zero
          · simp only [ne_eq, inv_eq_top]
            exact hpq.symm.ne_zero
        rw [← ENNReal.rpow_sub _ _ H_pos.ne.symm H_finite.ne, this, mul_comm (ofNNReal l),
            ← ENNReal.div_lt_iff (by left; simpa) (by left; simp),
            ← ENNReal.rpow_rpow_inv (toReal_ne_zero.mpr ⟨hpq.ne_zero, hp⟩) (c * _ / ↑l),
            ← r_def, toReal_inv]
        apply ENNReal.rpow_lt_rpow H_gt (inv_pos.mpr p_toReal_pos)
      _ = ∫⁻ (x : α') in H, l ∂ν := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ (x : α') in H, ‖T f x‖ₑ ∂ν := by
        apply setLIntegral_mono_ae' hH
        filter_upwards [G'G]
        intro x h hx
        have : G x := by
          rw [← h]
          exact H_subset_G' hx
        exact this.le
      _ = eLpNorm (T f) 1 (ν.restrict H) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
  rw [← Ne, ← lt_top_iff_ne_top] at G_finite
  have G'_finite : ν G' < ∞ := by
    convert G_finite
  by_cases G_zero : ν G = 0
  · rw [G_zero, zero_rpow_of_pos]
    · simp
    simp only [inv_pos]
    exact toReal_pos hpq.ne_zero hp
  calc _
    _ = ↑l * ν G / ν G ^ q⁻¹.toReal := by
      rw [mul_div_assoc]
      congr
      rw [ENNReal.eq_div_iff,
          ← ENNReal.rpow_add, ← ENNReal.toReal_inv, ← ENNReal.toReal_add, add_comm, ENNReal.holderConjugate_iff.mp hpq]
      · simp only [ENNReal.toReal_one, ENNReal.rpow_one]
      · rw [ne_eq, ENNReal.inv_eq_top]
        exact hpq.symm.ne_zero
      · rw [ne_eq, ENNReal.inv_eq_top]
        exact hpq.ne_zero
      · exact G_zero
      · exact G_finite.ne
      · simp only [toReal_inv, ne_eq, ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', not_or,
        not_and, not_lt, toReal_nonneg, implies_true, and_true]
        intro
        contradiction
      · simp only [toReal_inv, ne_eq, rpow_eq_top_iff, inv_neg'', inv_pos, not_or, not_and,
        not_lt, toReal_nonneg, implies_true, true_and]
        intro h
        exfalso
        exact G_finite.ne h
    _ ≤ (∫⁻ (x : α') in G, ‖T f x‖ₑ ∂ν) / ν G ^ q⁻¹.toReal := by
      gcongr
      rw [← Measure.restrict_eq_self _ (subset_refl G)]
      calc _
        _ ≤ ↑l * (ν.restrict G) {x | ↑l ≤ ‖T f x‖ₑ} := by
          gcongr
          intro x hx
          unfold G at hx
          rw [Set.mem_setOf_eq] at hx ⊢; exact hx.le
      apply mul_meas_ge_le_lintegral₀ hf'.enorm.restrict
    _ ≤ (c * _ * ν G ^ q⁻¹.toReal) / ν G ^ q⁻¹.toReal := by
      gcongr
      convert (hT f hf G' hG').2 using 2
      · rw [eLpNorm_one_eq_lintegral_enorm]
        apply setLIntegral_congr G'G.symm
      · congr 1
        exact measure_G'G.symm
    _ = c * _  := by
      apply ENNReal.mul_div_cancel_right
      · contrapose! G_zero
        rwa [ENNReal.rpow_eq_zero_iff_of_pos] at G_zero
        simp only [toReal_inv, inv_pos]
        apply toReal_pos hpq.symm.ne_zero hq
      · exact ENNReal.rpow_ne_top' G_zero G_finite.ne

theorem RCLike.norm_I {K : Type u_1} [RCLike K] : ‖(RCLike.I : K)‖ = if RCLike.I ≠ (0 : K) then 1 else 0 := by
  split_ifs with h
  · apply RCLike.norm_I_of_ne_zero h
  · push Not at h
    simpa

/-
theorem weakly_cont_implies_ae_eq [TopologicalSpace α] {𝕂 : Type*} [TopologicalSpace ε'] [RCLike 𝕂]
  [ENormedSpace ε'] {T : (α → 𝕂) → α' → ε'} {p q : ℝ≥0∞}
  {μ : Measure α} [IsLocallyFiniteMeasure μ] {ν : Measure α'}
  (weakly_cont_T : ∀ {f : α → 𝕂} {fs : ℕ → α → 𝕂}
                     (f_locInt : LocallyIntegrable f μ)
                     (hF_meas : ∀ (n : ℕ), AEStronglyMeasurable (fs n) μ)
                     (h_norm_monotone : ∀ (a : α), Monotone (fun n ↦ ‖fs n a‖))
                     (h_lim : ∀ (a : α), Filter.Tendsto (fun (n : ℕ) => fs n a) Filter.atTop (nhds (f a)))
                     (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop)
  (G : Set α') ⦃f g : α → 𝕂⦄ (hfg : f =ᶠ[ae μ] g) (f_locInt : LocallyIntegrable f μ) :
  eLpNorm (T g) 1 (ν.restrict G) = eLpNorm (T f) 1 (ν.restrict G) := by
  have g_locInt : LocallyIntegrable g μ := f_locInt.congr hfg
  apply le_antisymm
  · have : eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun (n : ℕ) ↦ eLpNorm (T g) 1 (ν.restrict G)) Filter.atTop := by
      apply weakly_cont_T f_locInt
      · intro n
        --exact g_locInt.aestronglyMeasurable
        sorry
      · intro a
        exact monotone_const

      · intro a
        rw [hfg]
        apply Filter.Tendsto.congr' (by apply Filter.Eventually.of_forall; intro x; rw [hfg])
        exact Filter.tendsto_nhds_nhds
  --  := @weakly_cont_T _ (fun n ↦ g) f_locInt
  sorry
-/

/-- TODO: check whether this is the right approach -/
def RCLike.Components {𝕂 : Type*} [RCLike 𝕂] : Finset 𝕂 := {1, -1, RCLike.I, -RCLike.I}

lemma RCLike.Components.norm_eq_one {𝕂 : Type*} [RCLike 𝕂] {c : 𝕂} (hc : c ∈ Components) (hc' : c ≠ 0) :
    ‖c‖ = 1 := by
  unfold Components at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc <;> rw [hc]
  · simp
  · simp
  · rw [RCLike.norm_I_of_ne_zero]
    rwa [← hc]
  · rw [norm_neg, RCLike.norm_I_of_ne_zero]
    rwa [← neg_ne_zero, ← hc]

lemma RCLike.Components.norm_le_one {𝕂 : Type*} [RCLike 𝕂] {c : 𝕂} (hc : c ∈ Components) : ‖c‖ ≤ 1 := by
  by_cases h : c = 0
  · rw [h]
    simp
  rw [norm_eq_one hc h]

open ComplexConjugate

/-- TODO: check whether this is the right approach -/
def RCLike.component {𝕂 : Type*} [RCLike 𝕂] (c : 𝕂) (a : 𝕂) : ℝ≥0 :=
  Real.toNNReal (RCLike.re (a * conj c))

lemma RCLike.component_le_norm {𝕂 : Type*} [RCLike 𝕂] {c a : 𝕂} (hc : c ∈ Components) :
    component c a ≤ ‖a‖ := by
  unfold component
  rw [Real.coe_toNNReal']
  apply max_le _ (by simp)
  apply (RCLike.re_le_norm (a * (starRingEnd 𝕂) c)).trans
  simp only [norm_mul, RCLike.norm_conj]
  nth_rw 2 [← mul_one ‖a‖]
  gcongr
  exact Components.norm_le_one hc

lemma RCLike.component_le_nnnorm {𝕂 : Type*} [RCLike 𝕂] {c a : 𝕂} (hc : c ∈ Components) :
    component c a ≤ ‖a‖₊ := by
  rw [← norm_toNNReal]
  apply NNReal.le_toNNReal_of_coe_le
  exact component_le_norm hc

lemma RCLike.decomposition {𝕂 : Type*} [RCLike 𝕂] {a : 𝕂} :
  1 * ((algebraMap ℝ 𝕂) (component 1 a).toReal)
  + -1 * ((algebraMap ℝ 𝕂) (component (-1) a).toReal)
  + RCLike.I * ((algebraMap ℝ 𝕂) (component RCLike.I a).toReal)
  + -RCLike.I * ((algebraMap ℝ 𝕂) (component (-RCLike.I) a).toReal) = a := by
  unfold component
  simp only [map_one, mul_one, Real.coe_toNNReal', one_mul, map_neg, mul_neg, neg_mul,
    RCLike.conj_I, RCLike.mul_re, RCLike.I_re, mul_zero, RCLike.I_im, zero_sub, neg_neg]
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← map_sub, add_sub_assoc, ← mul_sub, ← map_sub]
  rw [max_zero_sub_eq_self, max_zero_sub_eq_self, mul_comm]
  exact RCLike.re_add_im_ax a

/-
--TODO: is this needed?
@[simp]
lemma RCLike.decomposition' {𝕂 : Type*} [RCLike 𝕂] {a : 𝕂} :
  ∑ c ∈ RCLike.Components, c * ((algebraMap ℝ 𝕂) (RCLike.component c a).toReal) = a := by
  unfold Components
  rw [Finset.sum_insert sorry, Finset.sum_insert sorry, Finset.sum_insert sorry, Finset.sum_singleton,
      ← add_assoc, ← add_assoc]
  exact RCLike.decomposition
-/


theorem RCLike.nnnorm_ofReal
  {𝕂 : Type*} [RCLike 𝕂] {a : ℝ≥0} :
  a = ‖(@RCLike.ofReal 𝕂 _) (NNReal.toReal a)‖₊ := by
  apply NNReal.eq
  simp

theorem RCLike.enorm_ofReal
  {𝕂 : Type*} [RCLike 𝕂] {a : ℝ≥0} :
    ‖a‖ₑ = ‖(@RCLike.ofReal 𝕂 _) (NNReal.toReal a)‖ₑ := by
  simp only [enorm_NNReal]
  rw [enorm_eq_nnnorm]
  simp


/-
--TODO: move / generalize or find existing version
theorem add_induction {β γ} [AddCommMonoid β] [AddCommMonoid γ]
  {g : α → β} {f : β → γ} {motive : γ → γ → Prop}
  (motive_trans : IsTrans γ motive)
  (motive_add_left : ∀ {x y z : γ}, motive y z → motive (x + y) (x + z))
  (zero : motive (f 0) 0)
  (add : ∀ {x y : β}, motive (f (x + y)) (f x + f y))
  {s : Finset α} :
    motive (f (∑ x ∈ s, g x)) (∑ x ∈ s, f (g x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have : motive (f (g a + ∑ x ∈ s, g x)) (f (g a) + f (∑ x ∈ s, g x)) := add
    apply motive_trans.trans _ _ _ this
    apply motive_add_left ih


--TODO: move / generalize or find existing version
theorem vector_valued_induction {β γ} [AddCommMonoid β] [AddCommMonoid γ]
  {M : Type*} [AddCommMonoid M] [Module ℝ M]
  {Q : (α → M) → Prop} {motive : ℕ → (α → M) → Prop}
  {f : α → M} (hf : Q f)
  :
  motive 1 f := sorry
-/

/-! ### Helper lemmas for the RCLike component decomposition norm bounds -/

section RCLikeComponentHelpers

open _root_.RCLike RCLike in
private lemma component_one_add_neg_one {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    algebraMap ℝ 𝕂 (component 1 a).toReal +
      (-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal = algebraMap ℝ 𝕂 (re a) := by
  unfold component
  simp only [map_one, mul_one, map_neg, mul_neg, neg_mul, one_mul]
  rw [← map_neg, ← map_add]; congr 1
  simp only [Real.coe_toNNReal']
  linarith [max_zero_sub_eq_self (re a)]

open _root_.RCLike RCLike in
private lemma component_I_add_neg_I {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    (I : 𝕂) * algebraMap ℝ 𝕂 (component I a).toReal +
      (-I : 𝕂) * algebraMap ℝ 𝕂 (component (-I) a).toReal = algebraMap ℝ 𝕂 (im a) * I := by
  unfold component
  simp only [conj_I, mul_neg, Real.coe_toNNReal', map_neg]
  ring_nf
  rw [← mul_sub, ← map_sub,
    show max (-re (I * a)) 0 - max (re (I * a)) 0 = im a from by
      rw [show re (I * a) = -im a from by simp [mul_re, I_re], neg_neg]
      exact max_zero_sub_eq_self _]

open _root_.RCLike RCLike in
/-- Norm of the real component part is at most `‖a‖`. -/
private lemma norm_realPart_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖algebraMap ℝ 𝕂 (component 1 a).toReal +
      (-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal‖ ≤ ‖a‖ := by
  rw [component_one_add_neg_one, norm_ofReal]
  exact abs_re_le_norm a

open _root_.RCLike RCLike in
/-- Norm of the imaginary component part is at most `‖a‖`. -/
private lemma norm_imPart_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖(I : 𝕂) * algebraMap ℝ 𝕂 (component I a).toReal +
      (-I : 𝕂) * algebraMap ℝ 𝕂 (component (-I) a).toReal‖ ≤ ‖a‖ := by
  rw [component_I_add_neg_I]
  calc ‖algebraMap ℝ 𝕂 (im a) * I‖
      ≤ ‖algebraMap ℝ 𝕂 (im a)‖ * ‖(I : 𝕂)‖ := norm_mul_le _ _
    _ ≤ |im a| * 1 := by
        gcongr
        · exact (norm_ofReal _).le
        · rw [RCLike.norm_I]; split_ifs <;> simp
    _ = |im a| := mul_one _
    _ ≤ ‖a‖ := abs_im_le_norm a

open _root_.RCLike RCLike in
/-- `max(re a, 0)` embedded in 𝕂 has norm at most `|re a|`. -/
private lemma norm_posReal_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖(algebraMap ℝ 𝕂 (component 1 a).toReal : 𝕂)‖ ≤
      ‖algebraMap ℝ 𝕂 (component 1 a).toReal +
        (-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal‖ := by
  rw [component_one_add_neg_one, norm_ofReal, norm_ofReal]
  unfold component
  simp only [map_one, mul_one, Real.coe_toNNReal']
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

open _root_.RCLike RCLike in
/-- `max(-re a, 0)` negated and embedded in 𝕂 has norm at most `|re a|`. -/
private lemma norm_negReal_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖(-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal‖ ≤
      ‖algebraMap ℝ 𝕂 (component 1 a).toReal +
        (-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal‖ := by
  rw [component_one_add_neg_one, norm_ofReal]
  simp only [neg_mul, one_mul, norm_neg, norm_ofReal]
  unfold component
  simp only [map_neg, map_one, mul_neg, mul_one, Real.coe_toNNReal']
  rw [abs_of_nonneg (le_max_right _ _)]
  simp [abs_nonneg, neg_le_abs]

open _root_.RCLike RCLike in
/-- `I * max(im a, 0)` has norm at most `‖I * im⁺ - I * im⁻‖`. -/
private lemma norm_posIm_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖(I : 𝕂) * algebraMap ℝ 𝕂 (component I a).toReal‖ ≤
      ‖(I : 𝕂) * algebraMap ℝ 𝕂 (component I a).toReal +
        (-I : 𝕂) * algebraMap ℝ 𝕂 (component (-I) a).toReal‖ := by
  rw [component_I_add_neg_I, norm_mul, norm_mul, norm_ofReal, norm_ofReal,
    mul_comm (‖(I : 𝕂)‖)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold component
  simp only [conj_I, mul_neg, Real.coe_toNNReal']
  change |max (re (-(a * I))) 0| ≤ |im a|
  rw [show re (-(a * I)) = im a from by simp [mul_re, I_re, I_im]]
  simp [abs_of_nonneg, le_abs_self]

open _root_.RCLike RCLike in
/-- `-I * max(-im a, 0)` has norm at most `‖I * im⁺ - I * im⁻‖`. -/
private lemma norm_negIm_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖(-I : 𝕂) * algebraMap ℝ 𝕂 (component (-I) a).toReal‖ ≤
      ‖(I : 𝕂) * algebraMap ℝ 𝕂 (component I a).toReal +
        (-I : 𝕂) * algebraMap ℝ 𝕂 (component (-I) a).toReal‖ := by
  rw [component_I_add_neg_I]
  simp only [norm_neg, norm_mul, norm_ofReal, mul_comm (‖(I : 𝕂)‖)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold component
  simp only [map_neg, conj_I, neg_neg, Real.coe_toNNReal']
  rw [show re (a * I) = -im a from by simp [mul_re, I_re, I_im]]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (neg_le_abs _) (abs_nonneg _)

end RCLikeComponentHelpers

--TODO: clean up the proof
theorem RCLike.induction {𝕂 : Type*} [RCLike 𝕂]
  {β : Type*} [Mul β] {a b}
  {P : (α → 𝕂) → Prop}
  (P_add : ∀ {f g : α → 𝕂}, P f → P g → P (f + g))
  (P_components : ∀ {f : α → 𝕂} {c : 𝕂} (_ : c ∈ RCLike.Components),
    P f → P (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ RCLike.component c ∘ f))
  (P_mul_unit : ∀ {f : α → 𝕂} {c : 𝕂} (_ : c ∈ RCLike.Components), P f → P (c • f))
  {motive : (α → 𝕂) → β → Prop}
  (motive_nnreal : ∀ {f : α → ℝ≥0} (_ : P (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ f)),
    motive (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ f) a)
  (motive_add' : ∀ {n : β} {f g : α → 𝕂} (_ : ∀ {x}, ‖f x‖ ≤ ‖f x + g x‖) (_ : ∀ {x}, ‖g x‖ ≤ ‖f x + g x‖) (_ : P f) (_ : P g), motive f n → motive g n → motive (f + g) (n * b))
  (motive_mul_unit : ∀ {f : α → 𝕂} {c : 𝕂} {n : β} (_ : c ∈ RCLike.Components) (_ : P f),
    motive f n → motive (c • f) n)
  ⦃f : α → 𝕂⦄ (hf : P f) :
    motive f (a * b * b) := by
  have f_decomposition :
    (1 : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component 1 ∘ f)
    + (-1 : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component (-1) ∘ f)
    + (RCLike.I : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component RCLike.I ∘ f)
    + (-RCLike.I : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component (-RCLike.I) ∘ f) = f := by
    ext x
    simp only [Pi.add_apply, comp_apply, Pi.smul_apply, smul_eq_mul]
    exact RCLike.decomposition
  -- Decompose f into real and imaginary parts, each further split into positive/negative parts
  rw [← f_decomposition, add_assoc]
  have hP_comp : ∀ {c : 𝕂} (_ : c ∈ Components),
      P (c • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component c ∘ f)) := fun hc =>
    P_mul_unit hc (P_components hc hf)
  -- Pointwise version of the decomposition
  have f_decomp_pt : ∀ x, (algebraMap ℝ 𝕂) ((component 1 (f x)).toReal)
      + (-1) * (algebraMap ℝ 𝕂) ((component (-1) (f x)).toReal)
      + (RCLike.I * (algebraMap ℝ 𝕂) ((component RCLike.I (f x)).toReal)
        + -RCLike.I * (algebraMap ℝ 𝕂) ((component (-RCLike.I) (f x)).toReal)) = f x := by
    intro x
    have := congr_fun f_decomposition x
    simp only [Pi.add_apply, comp_apply, Pi.smul_apply, smul_eq_mul, one_mul] at this
    rw [add_assoc] at this; exact this
  -- Outer split: real part vs imaginary part
  apply motive_add'
  · -- ‖real_part x‖ ≤ ‖(real_part + imag_part) x‖
    intro x
    simp only [Pi.add_apply, comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [f_decomp_pt]
    exact norm_realPart_le (f x)
  · -- ‖imag_part x‖ ≤ ‖(real_part + imag_part) x‖
    intro x
    simp only [Pi.add_apply, comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [f_decomp_pt]
    exact norm_imPart_le (f x)
  · exact P_add (hP_comp (by unfold Components; simp)) (hP_comp (by unfold Components; simp))
  · exact P_add (hP_comp (by unfold Components; simp)) (hP_comp (by unfold Components; simp))
  · -- Inner split: positive real vs negative real
    apply motive_add'
    · -- ‖1 * pos_re x‖ ≤ ‖(1 * pos_re + (-1) * neg_re) x‖
      intro x
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact norm_posReal_le (f x)
    · -- ‖(-1) * neg_re x‖ ≤ ‖(1 * pos_re + (-1) * neg_re) x‖
      intro x
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact norm_negReal_le (f x)
    · exact hP_comp (by unfold Components; simp)
    · exact hP_comp (by unfold Components; simp)
    · exact motive_mul_unit (by unfold Components; simp) (P_components (by unfold Components; simp) hf)
        (motive_nnreal (P_components (by unfold Components; simp) hf))
    · exact motive_mul_unit (by unfold Components; simp) (P_components (by unfold Components; simp) hf)
        (motive_nnreal (P_components (by unfold Components; simp) hf))
  · -- Inner split: positive imaginary vs negative imaginary
    apply motive_add'
    · -- ‖I * pos_im x‖ ≤ ‖(I * pos_im + (-I) * neg_im) x‖
      intro x
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul]
      exact norm_posIm_le (f x)
    · -- ‖(-I) * neg_im x‖ ≤ ‖(I * pos_im + (-I) * neg_im) x‖
      intro x
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul]
      exact norm_negIm_le (f x)
    · exact hP_comp (by unfold Components; simp)
    · exact hP_comp (by unfold Components; simp)
    · exact motive_mul_unit (by unfold Components; simp) (P_components (by unfold Components; simp) hf)
        (motive_nnreal (P_components (by unfold Components; simp) hf))
    · exact motive_mul_unit (by unfold Components; simp) (P_components (by unfold Components; simp) hf)
        (motive_nnreal (P_components (by unfold Components; simp) hf))

theorem enorm_eq_enorm_embedRCLike {𝕂 : Type*} [RCLike 𝕂] {f : α → ℝ≥0} (x : α) :
    ‖(⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) x‖ₑ = ‖f x‖ₑ := by
  rw [← ofReal_norm]
  simp

theorem aestronglyMeasurable_iff_aestronglyMeasurable_embedRCLike {𝕂 : Type*} [RCLike 𝕂]
  {f : α → ℝ≥0} :
    AEStronglyMeasurable (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) μ ↔ AEStronglyMeasurable f μ := by
  constructor
  · intro hf
    have comp_eq : (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) = fun x ↦ ⇑(algebraMap ℝ 𝕂) (f x).toReal := by
      ext x
      simp
    rw [comp_eq] at hf
    rwa [IsEmbedding.aestronglyMeasurable_comp_iff, IsEmbedding.aestronglyMeasurable_comp_iff] at hf
    · exact (Isometry.isEmbedding fun _ ↦ congrFun rfl)
    · exact (algebraMap_isometry ℝ 𝕂).isEmbedding
  · intro hf
    fun_prop

theorem memLorentz_iff_memLorentz_embedRCLike {𝕂 : Type*} [RCLike 𝕂]
  {f : α → ℝ≥0} :
    MemLorentz (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) p q μ ↔ MemLorentz f p q μ := by
  constructor
  · intro hf
    constructor
    · have := hf.1
      rwa [aestronglyMeasurable_iff_aestronglyMeasurable_embedRCLike] at this
    · convert hf.2 using 1
      apply eLorentzNorm_congr_enorm_ae
      apply Eventually.of_forall
      intro x
      symm
      apply enorm_eq_enorm_embedRCLike
  · intro hf
    constructor
    · have := hf.1
      rwa [aestronglyMeasurable_iff_aestronglyMeasurable_embedRCLike]
    · convert hf.2 using 1
      apply eLorentzNorm_congr_enorm_ae
      apply Eventually.of_forall enorm_eq_enorm_embedRCLike

lemma HasRestrictedWeakType'.of_hasRestrictedWeakType'_nnreal [NoAtoms μ]
  {𝕂 : Type*} [RCLike 𝕂] [TopologicalSpace ε'] [ENormedSpace ε']
  {T : (α → 𝕂) → (α' → ε')}
  (T_meas : ∀ {f : α → 𝕂}, (MemLorentz f p 1 μ) → AEStronglyMeasurable (T f) ν)
  (T_zero : T 0 =ᶠ[ae ν] 0)
  (T_subadd : ∀ {f g : α → 𝕂}, (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
  (T_submul : ∀ (a : 𝕂) (f : α → 𝕂), ∀ᵐ x ∂ν, ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ * ‖T f x‖ₑ)
  {c : ℝ≥0∞} (hT_nnreal : HasRestrictedWeakType' (fun f ↦ T (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f)) p q μ ν c) :
    HasRestrictedWeakType' T p q μ ν (4 * c) := by
  intro f hf G hG
  use T_meas hf
  have : (4 : ℝ≥0∞) = 1 * 2 * 2 := by norm_num
  rw [this]
  revert f
  apply RCLike.induction (motive := fun f n ↦ eLpNorm (T f) 1 (ν.restrict G) ≤ (n : ℝ≥0∞) * c * eLorentzNorm f p 1 μ * (ν G) ^ q⁻¹.toReal)
  · exact MemLorentz.add
  · intro f c hc hf
    constructor
    · have := hf.1
      rw [aestronglyMeasurable_iff_aemeasurable]
      apply AEMeasurable.comp_aemeasurable (by fun_prop)
      apply AEMeasurable.comp_aemeasurable (by fun_prop)
      unfold RCLike.component
      apply AEMeasurable.comp_aemeasurable (by fun_prop) hf.1.aemeasurable
    · apply hf.2.trans_le'
      apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      have : NNNorm 𝕂 := by infer_instance
      rw [← ofReal_norm, ← ofReal_norm]
      simp only [comp_apply, norm_algebraMap', Real.norm_eq_abs, NNReal.abs_eq,
        ofReal_coe_nnreal, ofReal_norm, coe_le_enorm, ge_iff_le]
      exact RCLike.component_le_nnnorm hc
  · intro f c hc hf
    constructor
    · apply AEStronglyMeasurable.const_smul hf.1
    · apply hf.2.trans_le'
      apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
      nth_rw 2 [← one_mul ‖f x‖ₑ]
      gcongr
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_of_le_toReal
      simp only [toReal_one]
      exact RCLike.Components.norm_le_one hc
  · rw [one_mul]
    intro f hf
    rw [memLorentz_iff_memLorentz_embedRCLike] at hf
    rw [eLorentzNorm_congr_enorm_ae (Eventually.of_forall enorm_eq_enorm_embedRCLike)]
    apply (hT_nnreal f hf G hG).2
  · intro n f g hf_add hg_add hf hg hf' hg'
    calc _
      _ ≤ eLpNorm ((fun x ↦ ‖T f x‖ₑ) + (fun x ↦ ‖T g x‖ₑ)) 1 (ν.restrict G) := by
        apply eLpNorm_mono_enorm_ae
        simp only [enorm_eq_self]
        apply ae_restrict_le
        exact T_subadd hf hg
    apply (eLpNorm_add_le (T_meas hf).enorm.aestronglyMeasurable.restrict
                          (T_meas hg).enorm.aestronglyMeasurable.restrict
                          (by simp)).trans
    rw [mul_comm n, mul_assoc 2, mul_assoc 2, mul_assoc 2, two_mul]
    rw [eLpNorm_enorm, eLpNorm_enorm]
    apply (add_le_add hf' hg').trans
    gcongr
    · apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      rw [← ofReal_norm, ← ofReal_norm, Pi.add_apply]
      apply ENNReal.ofReal_le_ofReal hf_add
    · apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal hg_add
  · intro f b n hb hf
    by_cases h : b = 0
    · intro _
      rw [h]
      simp only [zero_smul, eLorentzNorm_zero, mul_zero, toReal_inv, zero_mul, nonpos_iff_eq_zero]
      apply eLpNorm_zero_of_ae_zero
      exact ae_restrict_le T_zero
    gcongr
    · apply eLpNorm_mono_enorm_ae
      apply ae_restrict_le
      filter_upwards [T_submul b f]
      intro x hx
      rw [← one_mul ‖T f x‖ₑ]
      apply hx.trans
      gcongr
      rw [enorm_eq_nnnorm]
      simp only [coe_le_one_iff]
      apply RCLike.Components.norm_le_one hb
    · apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
      rw [← ofReal_norm, ← ofReal_norm, RCLike.Components.norm_eq_one hb h]
      simp

lemma HasRestrictedWeakType.hasLorentzType {𝕂 : Type*}
  [RCLike 𝕂] [TopologicalSpace ε'] [ENormedSpace ε']
  {T : (α → 𝕂) → (α' → ε')} {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) (p_ne_top : p ≠ ⊤) (q_ne_top : q ≠ ⊤)
  [NoAtoms μ] [SigmaFinite ν] {c : ℝ≥0} (c_pos : 0 < c)
  (hT : HasRestrictedWeakType T p q μ ν c)
  (T_meas : ∀ {f : α → 𝕂}, (MemLorentz f p 1 μ) → AEStronglyMeasurable (T f) ν)
  (T_subadd : ∀ {f g : α → 𝕂}, (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
  (T_submul : ∀ (a : 𝕂) (f : α → 𝕂), ∀ᵐ (x : α') ∂ν, ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ * ‖T f x‖ₑ)
  (weakly_cont_T : ∀ {f : α → 𝕂} {fs : ℕ → α → 𝕂},
                     (MemLorentz f p 1 μ) →
                     (∀ (n : ℕ), AEStronglyMeasurable (fs n) μ) →
                     (∀ (a : α), Monotone (fun n ↦ ‖fs n a‖)) →
                     (∀ (a : α), Filter.Tendsto (fun (n : ℕ) => fs n a) Filter.atTop (nhds (f a))) →
                     (G : Set α') →
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop)
  (T_zero : T 0 =ᶠ[ae ν] 0)
  (T_ae_eq_of_ae_eq : ∀ {f g : α → 𝕂} (_ : f =ᶠ[ae μ] g), T f =ᶠ[ae ν] T g) --TODO: incorporate into weakly_cont_T?
    :
    HasLorentzType T p 1 p ∞ μ ν (4 * c / p) := by
  /-
  by_cases p_ne_top : p = ⊤
  · rw [p_ne_top] at hT
    unfold HasRestrictedWeakType at hT
    simp at hT
    sorry
  by_cases q_ne_top : q = ⊤
  · sorry
  -/
  rw [mul_div_assoc]
  apply HasRestrictedWeakType'.hasLorentzType hpq p_ne_top q_ne_top (by finiteness [hpq.ne_zero])
  apply HasRestrictedWeakType'.of_hasRestrictedWeakType'_nnreal T_meas T_zero T_subadd T_submul
  apply hasRestrictedWeakType'_nnreal c_pos p_ne_top q_ne_top hpq
  · intro f hf
    apply T_meas
    rwa [memLorentz_iff_memLorentz_embedRCLike]
  · intro f g hf hg
    rw [← memLorentz_iff_memLorentz_embedRCLike (𝕂 := 𝕂)] at hf
    rw [← memLorentz_iff_memLorentz_embedRCLike (𝕂 := 𝕂)] at hg
    filter_upwards [T_subadd hf hg]
    intro x h
    apply h.trans_eq'
    congr with x
    simp
  · intro a f
    filter_upwards [T_submul (NNReal.toReal a) (RCLike.ofReal ∘ NNReal.toReal ∘ f)]
    intro x h
    convert h
    · ext x
      simp
    · rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      simp
  · intro f g hfg
    apply T_ae_eq_of_ae_eq
    filter_upwards [hfg]
    simp
  /-
  · intro F hF F_finite
    have := hT F hF F_finite
    unfold T'
    constructor
    · apply T_meas
      rw [memLorentz_iff_memLorentz_embedRCLike]
      have : (1 : α → ℝ≥0) = fun _ ↦ 1 := rfl
      constructor
      · apply Measurable.aestronglyMeasurable
        rwa [this, measurable_indicator_const_iff]
      · rw [this, const_def, eLorentzNorm_indicator_const]
        simp only [one_ne_zero, ↓reduceIte, one_ne_top, enorm_NNReal, ENNReal.coe_one, mul_one,
          div_one, toReal_one, inv_one, ENNReal.rpow_one]
        split_ifs
        apply mul_lt_top (Ne.lt_top p_top)
        exact rpow_lt_top_of_nonneg (by simp) F_finite.ne
    · apply this.2.trans_eq'
      congr
      ext x
      simp only [comp_apply, NNReal.coe_indicator, Pi.one_apply, NNReal.coe_one]
      unfold indicator
      split_ifs <;> simp
  -/
  · simpa
  · intro F G hF F_finite hG G_finite
    have := hT F G hF F_finite hG G_finite
    constructor
    · apply T_meas
      rw [memLorentz_iff_memLorentz_embedRCLike]
      constructor
      · apply Measurable.aestronglyMeasurable
        apply Measurable.indicator measurable_const hF
      · rw [const_def, eLorentzNorm_indicator_const]
        simp only [one_ne_zero, ↓reduceIte, one_ne_top, enorm_NNReal, ENNReal.coe_one, mul_one,
          div_one, toReal_one, inv_one, ENNReal.rpow_one]
        split_ifs
        · simp
        apply mul_lt_top (Ne.lt_top p_ne_top)
        exact rpow_lt_top_of_nonneg (by simp) F_finite.ne
    · simp only
      convert this.2
      ext x
      simp only [comp_apply, NNReal.coe_indicator, NNReal.coe_one]
      unfold indicator
      split_ifs <;> simp
  · intro fs hfs bddAbove_fs f hf G
    apply weakly_cont_T
    · rwa [memLorentz_iff_memLorentz_embedRCLike]
    · intro n
      apply Measurable.aestronglyMeasurable
      apply RCLike.measurable_ofReal.comp
      apply measurable_coe_nnreal_real.comp (SimpleFunc.measurable (fs n))
    · intro x
      simp only [Function.comp_apply, norm_algebraMap', Real.norm_eq_abs, NNReal.abs_eq]
      exact fun ⦃a b⦄ a_1 ↦ hfs a_1 x
    · intro x
      have : Tendsto (fun n ↦ (fs n) x) atTop (𝓝 (f x)) := by
        apply tendsto_atTop_ciSup
        · intro n m hmn
          apply hfs hmn
        · rw [bddAbove_def] at *
          rcases bddAbove_fs with ⟨g, hg⟩
          use g x
          intro y hy
          rcases hy with ⟨n, hn⟩
          rw [← hn]
          apply hg
          use n
      apply Filter.Tendsto.comp (y := (𝓝 ((toReal ∘ f) x)))
      · apply Continuous.tendsto'
        · continuity
        · simp
      apply Filter.Tendsto.comp (z := 𝓝 (toReal (f x))) _ this
      apply NNReal.continuous_coe.tendsto'
      rfl



end MeasureTheory
