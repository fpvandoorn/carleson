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
import Carleson.ToMathlib.Topology.Order.Basic


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

/-
-- TODO: find better name
lemma HasLorentzType_p_infty_qs {T : (α → ε₁) → (α' → ε₂)} {p q s : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞} (h : 0 < c) (hT : AEStronglyMeasurable (T f) ν) :
  HasLorentzType T p ∞ q s μ ν c := by
  intro f hf
-/

--TODO: what exactly should be the requirements on 𝕂? Actually, we only need a 1 here.
--TODO: This could be more general, it currently assumes T f ≥ 0
variable {β : Type*} [Zero β] [One β] --[NormedField 𝕂] --[ENormedAddMonoid 𝕂] [Field 𝕂] --[TopologicalSpace 𝕂]
  --[TopologicalSpace 𝕂] [ContinuousENorm 𝕂] [NormedField 𝕂]
  --[TopologicalSpace 𝕂] [ENormedAddMonoid 𝕂] --TODO: Actually, these last arguments should probably be infered

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
    (T_zero_of_ae_zero : ∀ {f : α → β} (_ : f =ᶠ[ae μ] 0), eLpNorm (T f) 1 ν = 0) :
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
        rw [← le_zero_iff]
        exact (eLpNorm_restrict_le _ _ _ _).trans (T_zero_of_ae_zero (indicator_meas_zero F_zero)).le
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


--TODO: Could probably weaken assumption to (h : ∀ᶠ (x : β) in f, u x ≤ v x)
theorem Filter.mono_limsup {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u v : β → α} (h : ∀ (x : β), u x ≤ v x) : Filter.limsup u f ≤ Filter.limsup v f := by
  refine Filter.limsup_le_limsup ?_
  apply Filter.Eventually.of_forall h

--TODO: move?
theorem Filter.limsup_le_of_le' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u : β → α} {a : α} (h : ∀ᶠ (n : β) in f, u n ≤ a) :
  Filter.limsup u f ≤ a := sInf_le h

--TODO: move?
theorem ENNReal.rpow_add_rpow_le_add' {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  calc
    _ = ((a ^ p + b ^ p) ^ (1 / p)) ^ p := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      linarith
    _ ≤ (a + b) ^ p := by
      gcongr
      apply ENNReal.rpow_add_rpow_le_add _ _ hp1


--variable [ENorm ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

--TODO: move
theorem ENNReal.limsup_mul_const_of_ne_top {α : Type*} {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    Filter.limsup (fun x ↦ u x * a) f = Filter.limsup u f * a := by
  simp_rw [mul_comm]
  apply ENNReal.limsup_const_mul_of_ne_top ha_top

/-
def WeaklyContinuous [TopologicalSpace ε] (T : (α → ε) → (α' → ε')) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {f : α → ε} {fs : ℕ → SimpleFunc α ε}
  (hfs : ∀ (x : α), Filter.Tendsto (fun (n : ℕ) => (fs n) x) Filter.atTop (nhds (f x))) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop
-/

variable {ε ε' : Type*}

/-- The weak continuity assumption neede for `HasRestrictedWeakType.hasLorentzType_helper`. -/
def WeaklyContinuous [TopologicalSpace ε] [ENorm ε] [SupSet ε]
  [Preorder ε] [ENorm ε'] (T : (α → ε) → (α' → ε')) (p : ℝ≥0∞) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {fs : ℕ → SimpleFunc α ε} (_ : Monotone fs),
  let f := fun x ↦ ⨆ n, (fs n) x;
  ∀ (_ : MemLorentz f p 1 μ) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T ⇑(fs n)) 1 (ν.restrict G)) Filter.atTop
--TODO: Show that the Carleson operator is weakly continuous in this sense via Fatou's lemma

--lemma carlesonOperator_weaklyContinuous : WeaklyContinuous carlesonOperator

theorem HasRestrictedWeakType.hasLorentzType_helper [TopologicalSpace ε'] [ENormedSpace ε']
  {c : ℝ≥0} (c_pos : 0 < c) {T : (α → ℝ≥0) → α' → ε'}
  (hT : HasRestrictedWeakType T p q μ ν c) --(T_zero : eLpNorm (T 0) 1 ν = 0)
  (hpq : p.HolderConjugate q)
  (weakly_cont_T : WeaklyContinuous T p μ ν)
  {G : Set α'} (hG : MeasurableSet G) (hG' : ν G < ⊤)
  (T_subadditive : ∀ (f g : α → ℝ≥0), (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    eLpNorm (T (f + g)) 1 (ν.restrict G) ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G))
  (T_submult : ∀ (f : α → ℝ≥0) (a : ℝ≥0), eLpNorm (T (a • f)) 1 (ν.restrict G) ≤ eLpNorm (a • T f) 1 (ν.restrict G))
  (T_zero_of_ae_zero : ∀ {f : α → ℝ≥0} (_ : f =ᶠ[ae μ] 0), eLpNorm (T f) 1 ν = 0)
  {f : α → ℝ≥0} (hf : Measurable f) (hf' : MemLorentz f p 1 μ) :
      eLpNorm (T f) 1 (ν.restrict G) ≤ (c / p) * eLorentzNorm f p 1 μ * ν G ^ q⁻¹.toReal := by
  by_cases p_ne_top : p = ∞
  · sorry --TODO: check whether this works or whether it should be excluded
  by_cases q_ne_top : q = ∞
  · sorry --TODO: check whether this works or whether it should be excluded
  have hp : 1 ≤ p := hpq.one_le --use: should follow from hpq
  have p_ne_zero : p ≠ 0 := hpq.ne_zero --TODO: easy
  rw [eLorentzNorm_eq_eLorentzNorm' p_ne_zero p_ne_top] --TODO: assumptions on p
  revert f
  apply @Measurable.nnreal_induction _ m0
  · intro f
    induction f using SimpleFunc.induction''
    · rename_i a s hs
      /-
      by_cases a_ne_top : a = ⊤
      · sorry --TODO: add new lemma what eLorentzNorm does with indicator functions; could also be used for the other part
        --alternative: use that f is bounded in the eLorentzNorm
      -/
      --simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      --  SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
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
          --apply eLpNorm_mono_enorm_ae
          apply T_submult
        _ ≤ ‖a‖ₑ * (c * (μ s) ^ p⁻¹.toReal * (ν G) ^ q⁻¹.toReal) := by
          gcongr
          apply hT.without_finiteness p_ne_zero p_ne_top hpq.symm.ne_zero q_ne_top c_pos T_zero_of_ae_zero s G hs hG
        _ = c * (‖a‖ₑ * μ s ^ p⁻¹.toReal) * (ν G) ^ q⁻¹.toReal := by ring
        _ = (c / p) * eLorentzNorm' (s.indicator (Function.const α a)) p 1 μ * ν G ^ q⁻¹.toReal := by
          rw [eLorentzNorm'_indicator (by simp) p_ne_zero p_ne_top]
          rw [← mul_assoc (c / p), ENNReal.div_mul_cancel p_ne_zero p_ne_top]
    · rename_i f a s hs hfs hf hg
      /-
      by_cases a_ne_top : a = ⊤
      · sorry --TODO: add new lemma what eLorentzNorm does with indicator functions; could also be used for the other part
      --have hf' : MemLorentz f p 1 μ := by sorry --TODO: get this from hfg' and measurability of f and g
      --have hg' : MemLorentz g p 1 μ := by sorry
      -/
      rw [SimpleFunc.coe_add]
      set g := (SimpleFunc.const α a).restrict s with g_def
      intro hfg'
      have hf' : MemLorentz f p 1 μ := by sorry --TODO: get this from hfg' and measurability of f and g
      have hg' : MemLorentz g p 1 μ := by sorry --TODO: use that g is an indicator function with finite value
      calc _
        _ ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G) := by
          apply T_subadditive f g hf' hg'
        _ ≤ c / p * eLorentzNorm' f p 1 μ * ν G ^ q⁻¹.toReal + c / p *  eLorentzNorm' g p 1 μ * ν G ^ q⁻¹.toReal := by
          gcongr
          · exact hf hf'
          · exact hg hg'
        _ = c / p * eLorentzNorm' (f + g) p 1 μ * ν G ^ q⁻¹.toReal := by
          rw [← add_mul, ← mul_add]
          congr
          rw [eLorentzNorm'_eq_integral_distribution_rpow,
            eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_eq_integral_distribution_rpow]
          rw [← mul_add] --TODO: measurability --← lintegral_add_left sorry
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
          rw [← eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_indicator (by simp) p_ne_zero p_ne_top]
          simp
  · intro f hf h hf'
    rw [← SimpleFunc.iSup_nnapprox hf] at hf'
    --have
    calc _
      _ ≤ Filter.limsup (fun n ↦ eLpNorm (T (SimpleFunc.nnapprox f n)) 1 (ν.restrict G)) Filter.atTop := by
        nth_rw 1 [← SimpleFunc.iSup_nnapprox hf]
        apply weakly_cont_T SimpleFunc.monotone_nnapprox hf' G
      _ ≤ Filter.limsup (fun n ↦ (c / p) * eLorentzNorm' (SimpleFunc.nnapprox f n) p 1 μ * ν G ^ q⁻¹.toReal) Filter.atTop := by
        apply Filter.mono_limsup
        intro n
        apply h n _
        sorry --use : all of these functions are bounded (by a constant / by f and this is MemLorentz)
      _ ≤ (c / p) * eLorentzNorm' f p 1 μ * ν G ^ q⁻¹.toReal := by
        simp_rw [mul_assoc]
        rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.div_ne_top (by simp) p_ne_zero)]
        gcongr
        --simp_rw [mul_comm]
        rw [ENNReal.limsup_mul_const_of_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) hG'.ne)]
        gcongr
        apply Filter.limsup_le_of_le'
        apply Filter.Eventually.of_forall
        intro n
        apply eLorentzNorm'_mono_enorm_ae
        apply Filter.Eventually.of_forall
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        intro x
        exact SimpleFunc.approx_le hf bot_eq_zero'
    /-
    intro fs monotone_fs hfs hf
    set f := (fun x ↦ ⨆ n, (fs n) x)
    calc _
      _ ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop := by
        apply weakly_cont_T monotone_fs hf
      _ ≤ Filter.limsup (fun n ↦ (c / p) * eLorentzNorm' (fs n) p 1 μ * ν G ^ q⁻¹.toReal) Filter.atTop := by
        apply Filter.mono_limsup
        intro n
        apply hfs n _
        sorry --use : every (fs n) is bounded by f and this is MemLorentz
      _ ≤ (c / p) * eLorentzNorm' f p 1 μ * ν G ^ q⁻¹.toReal := by
        simp_rw [mul_assoc]
        rw [ENNReal.limsup_const_mul_of_ne_top sorry] --use : c_ne_top
        gcongr
        --simp_rw [mul_comm]
        rw [ENNReal.limsup_mul_const_of_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) hG'.ne)]
        gcongr
        sorry --use: monotonicity of fs / def. of f
    -/

theorem RCLike.norm_I {K : Type u_1} [RCLike K] : ‖(RCLike.I : K)‖ = if RCLike.I ≠ (0 : K) then 1 else 0 := by
  split_ifs with h
  · apply RCLike.norm_I_of_ne_zero h
  · push_neg at h
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
/-
inductive RCLike.Component
  | pos_re
  | neg_re
  | pos_im
  | neg_im


instance : Fintype RCLike.Component where
  elems := sorry
  /-
  {RCLike.Component.pos_re,
    RCLike.Component.neg_re,
    RCLike.Component.pos_im,
    RCLike.Component.neg_im}
  -/
  complete := sorry
-/

/-- TODO: check whether this is the right approach -/
def RCLike.Components {𝕂 : Type*} [RCLike 𝕂] : Finset 𝕂 := {1, -1, RCLike.I, -RCLike.I}

open ComplexConjugate

/-- TODO: check whether this is the right approach -/
def RCLike.component {𝕂 : Type*} [RCLike 𝕂] (c : 𝕂) (a : 𝕂) : ℝ≥0 :=
  Real.toNNReal (RCLike.re (a * conj c))

  /-
  (match c with
  | Component.pos_re => RCLike.re a
  | Component.neg_re => - RCLike.re a
  | Component.pos_im => RCLike.im a
  | Component.neg_im => - RCLike.im a)
  -/

/-
def RCLike.coeff {𝕂 : Type*} [RCLike 𝕂] (c : Component) : 𝕂 :=
  match c with
  | Component.pos_re => 1
  | Component.neg_re => -1
  | Component.pos_im => RCLike.I
  | Component.neg_im => -RCLike.I
-/

--TODO: move
@[simp]
lemma RCLike.decomposition {𝕂 : Type*} [RCLike 𝕂] {a : 𝕂} :
  ∑ c ∈ RCLike.Components, (RCLike.component c a).toReal • c = a := by
  unfold RCLike.Components component
  rw [Finset.sum_insert sorry, Finset.sum_insert sorry, Finset.sum_insert sorry, Finset.sum_singleton]
  simp only [map_one, mul_one, Real.coe_toNNReal', map_neg, mul_neg, smul_neg, RCLike.conj_I,
    RCLike.mul_re, RCLike.I_re, mul_zero, RCLike.I_im, zero_sub, neg_neg]
  rw [← sub_eq_add_neg, ← sub_smul, ← add_assoc, ← sub_eq_add_neg, ← sub_smul]
  rw [max_zero_sub_eq_self, max_zero_sub_eq_self]
  rw [RCLike.real_smul_eq_coe_mul, mul_one, RCLike.real_smul_eq_coe_mul]
  exact RCLike.re_add_im_ax a

@[simp]
lemma RCLike.decomposition' {𝕂 : Type*} [RCLike 𝕂] {a : 𝕂} :
  ∑ c ∈ RCLike.Components, c * ((RCLike.component c a).toReal : 𝕂) = a := by
  nth_rw 2 [← @RCLike.decomposition _ _ a]
  congr with c
  rw [RCLike.real_smul_eq_coe_mul, mul_comm]


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


lemma HasRestrictedWeakType.hasLorentzType [TopologicalSpace α] {𝕂 : Type*} /- [MeasurableSpace ε'] [BorelSpace ε'] -/
  --[ENormedAddMonoid ε']
  [RCLike 𝕂] [TopologicalSpace ε'] [ENormedSpace ε']
  {T : (α → 𝕂) → (α' → ε')} (hp : 1 ≤ p)
  [IsLocallyFiniteMeasure μ] {c : ℝ≥0} (c_pos : 0 < c)
  (hT : HasRestrictedWeakType T p q μ ν c) (hpq : p.HolderConjugate q)
  (T_meas : ∀ {f : α → 𝕂}, (MemLorentz f p 1 μ) → AEStronglyMeasurable (T f) ν)
  (T_subadditive : ∀ {G : Set α'} (hG : MeasurableSet G) (hG' : ν G < ⊤) {f g : α → 𝕂}, (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    eLpNorm (T (f + g)) 1 (ν.restrict G) ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G))
  /-
  (T_subadd : ∀ (f g : α → 𝕂) (x : α'), (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    --‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    ‖T (f + g) x‖ₑ ≤ ‖T f x + T g x‖ₑ)
  -/
  (T_submul : ∀ (a : 𝕂) (f : α → 𝕂) (x : α'), ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ • ‖T f x‖ₑ)
  (weakly_cont_T : ∀ {f : α → 𝕂} {fs : ℕ → α → 𝕂}
                     (f_locInt : LocallyIntegrable f μ)
                     (hF_meas : ∀ (n : ℕ), AEStronglyMeasurable (fs n) μ)
                     (h_norm_monotone : ∀ (a : α), Monotone (fun n ↦ ‖fs n a‖))
                     (h_lim : ∀ (a : α), Filter.Tendsto (fun (n : ℕ) => fs n a) Filter.atTop (nhds (f a)))
                     (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop)
  (T_zero_of_ae_zero : ∀ {f : α → 𝕂} (_ : f =ᶠ[ae μ] 0), eLpNorm (T f) 1 ν = 0) --TODO: incorporate into weakly_cont_T?
    :

  --(weakly_cont_T : WeaklyContinuous T μ ν) : --TODO: correct assumption with modified T
    --TODO: might have to adjust the constant
    HasLorentzType T p 1 p ∞ μ ν (4 * c / p) := by
  have T_eq_of_ae_eq : ∀ {f g : α → 𝕂} (hfg : f =ᶠ[ae μ] g) {G : Set α'},
    eLpNorm (T f) 1 (ν.restrict G) = eLpNorm (T g) 1 (ν.restrict G) := by
    sorry --use T_submul and T_zero_of_ae_zero
    --TODO: have this as an external lemma?

  intro f hf
  --have hp : 1 ≤ p := by sorry --use: should follow from hpq
  have claim : ∀ (G : Set α'), (MeasurableSet G) → (ν G < ∞) → eLpNorm (T f) 1 (ν.restrict G)
    ≤ (4 * c / p) * eLorentzNorm f p 1 μ * (ν G) ^ q⁻¹.toReal := by
      intro G measurable_G G_finite
      rcases hf with ⟨aemeasurable_f, hf⟩
      revert f --TODO: go on here
      apply AEStronglyMeasurable.induction
      · intro f g stronglyMeasurable_f hfg hf hg
        have : eLorentzNorm f p 1 μ < ⊤ := by
          rwa [eLorentzNorm_congr_ae hfg]
        have hf := hf this
        rw [← eLorentzNorm_congr_ae hfg]
        convert hf using 1
        rw [T_eq_of_ae_eq hfg]
      intro g stronglyMeasurable_g hg

      --TODO: decompose g into 4 nonnegative parts with constant coefficients
      /-
      set g₁ := fun x ↦ Real.toNNReal (RCLike.re (g x))
      set g₂ := fun x ↦ Real.toNNReal (- RCLike.re (g x))
      set g₃ := fun x ↦ Real.toNNReal (RCLike.im (g x))
      set g₄ := fun x ↦ Real.toNNReal (- RCLike.im (g x))
      have g_decomposition : g = (1 : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₁)
                                + (-1 : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₂)
                                + (RCLike.I : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₃)
                                + (-RCLike.I : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₄) := by
        unfold g₁ g₂ g₃ g₄
        ext x
        simp only [one_smul, neg_smul, Pi.add_apply, Function.comp_apply, Real.coe_toNNReal',
          Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
        rw [algebraMap]
        sorry --TODO: simple algebra
      -/
      set T' := T ∘ (fun f ↦ (@RCLike.ofReal 𝕂 _) ∘ NNReal.toReal ∘ f)
      --TODO: use properties for T to get those for T'
      have hT' : HasRestrictedWeakType T' p q μ ν c := sorry
      have weaklyCont_T' : WeaklyContinuous T' p μ ν := by
        unfold WeaklyContinuous T'
        intro fs hfs f hf G
        simp only [Function.comp_apply]
        apply weakly_cont_T
        · apply ((hf.memLp (by simpa)).locallyIntegrable hp).congr'_enorm
          · apply AEMeasurable.aestronglyMeasurable
            apply RCLike.measurable_ofReal.comp_aemeasurable
            apply measurable_coe_nnreal_real.comp_aemeasurable
            exact hf.1.aemeasurable
          · simp only [Function.comp_apply]
            simp_rw [← RCLike.enorm_ofReal]
            simp
        · --apply Filter.Eventually.of_forall
          intro n
          apply Measurable.aestronglyMeasurable
          apply RCLike.measurable_ofReal.comp
          apply measurable_coe_nnreal_real.comp (SimpleFunc.measurable (fs n))
        · intro x
          simp only [Function.comp_apply, norm_algebraMap', Real.norm_eq_abs, NNReal.abs_eq]
          exact fun ⦃a b⦄ a_1 ↦ hfs a_1 x
        · --apply Filter.Eventually.of_forall
          intro x
          --apply Filter.Tendsto.algebraMap
          --apply Filter.Tendsto.comp _
          --apply Filter.Tendsto.comp _
          sorry --TODO: use that f is the supremum; maybe need to add a condition implying that
          -- the (fs n) are really converging to f


      have T'_subadd : ∀ (f g : α → ℝ≥0),
        MemLorentz f p 1 μ →
          MemLorentz g p 1 μ →
            eLpNorm (T' (f + g)) 1 (ν.restrict G)
              ≤ eLpNorm (T' f) 1 (ν.restrict G) + eLpNorm (T' g) 1 (ν.restrict G) := by
        intro f g hf hg
        unfold T'
        simp only [Function.comp_apply]
        have hf' : MemLorentz ((@RCLike.ofReal 𝕂 _) ∘ NNReal.toReal ∘ f) p 1 μ := by
          constructor
          · apply RCLike.measurable_ofReal.aestronglyMeasurable.comp_aemeasurable
            refine aestronglyMeasurable_iff_aemeasurable.mp ?_
            apply measurable_coe_nnreal_real.aestronglyMeasurable.comp_aemeasurable hf.1.aemeasurable
          · convert hf.2 using 1
            apply eLorentzNorm_congr_enorm_ae
            simp only [Function.comp_apply]
            simp_rw [← RCLike.enorm_ofReal]
            simp
        have hg' : MemLorentz ((@RCLike.ofReal 𝕂 _) ∘ NNReal.toReal ∘ g) p 1 μ := by
          constructor
          · apply RCLike.measurable_ofReal.aestronglyMeasurable.comp_aemeasurable
            refine aestronglyMeasurable_iff_aemeasurable.mp ?_
            apply measurable_coe_nnreal_real.aestronglyMeasurable.comp_aemeasurable hg.1.aemeasurable
          · convert hg.2 using 1
            apply eLorentzNorm_congr_enorm_ae
            simp only [Function.comp_apply]
            simp_rw [← RCLike.enorm_ofReal]
            simp
        apply le_trans _ (eLpNorm_add_le _ _ le_rfl)
        · /-
          apply eLpNorm_mono_enorm
          intro x
          simp only [Pi.add_apply]
          apply le_of_eq_of_le _ (T_subadd _ _ _ hf' hg')
          congr with x
          simp
          -/
          sorry
        · apply AEStronglyMeasurable.restrict
          apply T_meas hf'
        · apply AEStronglyMeasurable.restrict
          apply T_meas hg'
      have T'_submul : ∀ (f : α → ℝ≥0) (a : ℝ≥0), eLpNorm (T' (a • f)) 1 (ν.restrict G)
          ≤ eLpNorm (a • T' f) 1 (ν.restrict G) := by
        intro f a
        apply eLpNorm_mono_enorm
        intro x
        unfold T'
        simp only [Function.comp_apply, Pi.smul_apply, enorm_smul_eq_smul]
        have : a • ‖T (RCLike.ofReal ∘ NNReal.toReal ∘ f) x‖ₑ
          = ‖a‖ₑ • ‖T (RCLike.ofReal ∘ NNReal.toReal ∘ f) x‖ₑ := by
          congr
        rw [this]
        convert T_submul (NNReal.toReal a) _ x
        · ext x
          simp
        congr
        simp
      have helper : ∀ {f : α → ℝ≥0} (hf : Measurable f) (hf' : MemLorentz f p 1 μ),
          eLpNorm (T' f) 1 (ν.restrict G) ≤ (c / p) * eLorentzNorm f p 1 μ * ν G ^ q⁻¹.toReal := by
        intro f hf hf'
        apply HasRestrictedWeakType.hasLorentzType_helper c_pos hT' hpq weaklyCont_T' measurable_G G_finite
          T'_subadd T'_submul _ hf hf'
        intro f hf
        unfold T'
        simp only [Function.comp_apply]
        apply T_zero_of_ae_zero
        have : RCLike.ofReal ∘ NNReal.toReal ∘ (0 : α → ℝ≥0) = (0 : α → 𝕂) := by simp
        rw [← this]
        apply Filter.EventuallyEq.fun_comp
        apply Filter.EventuallyEq.fun_comp hf

      have g_decomposition : g = ∑ c ∈ RCLike.Components, c • (fun x ↦ (RCLike.ofReal (RCLike.component c (g x)).toReal : 𝕂)) := by
        ext x
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact Eq.symm RCLike.decomposition'
      calc _
        _ ≤ ∑ c ∈ RCLike.Components, eLpNorm (T (c • (fun x ↦ (RCLike.ofReal (RCLike.component c (g x)).toReal : 𝕂)))) 1 (ν.restrict G) := by
          nth_rw 1 [g_decomposition]
          classical
          apply add_induction (f := fun h ↦ eLpNorm (T h) 1 (ν.restrict G)) --(motive := T_subadditive measurable_G G_finite)
          · exact instIsTransLe
          · exact fun {x y z} a ↦ add_le_add_right a x
          · sorry
          · --apply T_subadditive measurable_G G_finite
            sorry


        /-
        _ ≤ eLpNorm (∑ c ∈ RCLike.Components, enorm ∘ T' (RCLike.component c ∘ g)) 1 (ν.restrict G) := by
          apply eLpNorm_mono_enorm
          intro x
          nth_rw 1 [g_decomposition]
          simp only [Finset.sum_apply, Function.comp_apply, enorm_eq_self]
          unfold T'
        -/
        /-
        eLpNorm (enorm ∘ T' g₁ + enorm ∘ T' g₂ + enorm ∘ T' g₃ + enorm ∘ T' g₄) 1 (ν.restrict G) := by
          have T_subadd' : ∀ (f₁ f₂ f₃ f₄ : α → 𝕂) (x : α'),
            (MemLorentz f₁ p 1 μ) → (MemLorentz f₂ p 1 μ) → (MemLorentz f₃ p 1 μ) → (MemLorentz f₄ p 1 μ) →
              ‖T (f₁ + f₂ + f₃ + f₄) x‖ₑ ≤ ‖T f₁ x‖ₑ + ‖T f₂ x‖ₑ + ‖T f₃ x‖ₑ + ‖T f₄ x‖ₑ := by
            sorry --use: iterate T_subadd
          apply eLpNorm_mono_enorm
          intro x
          rw [g_decomposition]
          simp only [Pi.add_apply, Function.comp_apply, enorm_eq_self]
          apply (T_subadd' _ _ _ _ _ _ _ _ _).trans
          · gcongr
            · apply (T_submul _ _ _).trans
              unfold T'
              simp
            · apply (T_submul _ _ _).trans
              unfold T'
              simp
            · apply (T_submul _ _ _).trans
              rw [← ofReal_norm_eq_enorm]
              rw [RCLike.norm_I]
              unfold T'
              split_ifs <;> simp
            · apply (T_submul _ _ _).trans
              rw [← ofReal_norm_eq_enorm, norm_neg]
              rw [RCLike.norm_I]
              unfold T'
              split_ifs <;> simp
          · sorry --TODO: Do these later when sure that this is the right condition in T_subadd
          · sorry
          · sorry
          · sorry
        -/
        _ ≤ ∑ c ∈ RCLike.Components, eLpNorm (T' (RCLike.component c ∘ g)) 1 (ν.restrict G) := by
          sorry
          /-
          eLpNorm (T' g₁) 1 (ν.restrict G) + eLpNorm (T' g₂) 1 (ν.restrict G)
          + eLpNorm (T' g₃) 1 (ν.restrict G) + eLpNorm (T' g₄) 1 (ν.restrict G) := by
          apply (eLpNorm_add_le sorry sorry le_rfl).trans
          gcongr
          · apply (eLpNorm_add_le sorry sorry le_rfl).trans
            gcongr
            · apply (eLpNorm_add_le sorry sorry le_rfl).trans
              gcongr <;> rw [Function.comp_def, eLpNorm_enorm]
            rw [Function.comp_def, eLpNorm_enorm]
          · rw [Function.comp_def, eLpNorm_enorm]
          -/
        _ ≤ (c / p) * ∑ c ∈ RCLike.Components, eLorentzNorm (RCLike.component c ∘ g) p 1 μ * ν G ^ q⁻¹.toReal := by
          sorry
          /-
          (c / p) * eLorentzNorm g₁ p 1 μ * ν G ^ q⁻¹.toReal
           +(c / p) * eLorentzNorm g₂ p 1 μ * ν G ^ q⁻¹.toReal
           +(c / p) * eLorentzNorm g₃ p 1 μ * ν G ^ q⁻¹.toReal
           +(c / p) * eLorentzNorm g₄ p 1 μ * ν G ^ q⁻¹.toReal := by
          gcongr
          · apply helper
            · apply measurable_real_toNNReal.comp (RCLike.measurable_re.comp stronglyMeasurable_g.measurable)
            · sorry
          · sorry --TODO: analogous to the first one, fill in once everything is finalized there
          · sorry
          · sorry
          -/
        _ ≤ (4 * c / p) * eLorentzNorm g p 1 μ * ν G ^ q⁻¹.toReal := by
          have : (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 := by ring
          rw [mul_div_assoc 4, mul_assoc 4, mul_assoc 4, this, add_mul, add_mul, add_mul]
          simp only [one_mul]
          sorry
          --unfold g₁ g₂ g₃ g₄
          --TODO: unify cases below
          /-
          gcongr
          · apply eLorentzNorm_mono_enorm_ae
            apply Filter.Eventually.of_forall
            intro x
            simp only [enorm_NNReal, coe_le_enorm]
            rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm]
            apply RCLike.re_le_norm
          · --analogous to the first case
            apply eLorentzNorm_mono_enorm_ae
            apply Filter.Eventually.of_forall
            intro x
            rw [← map_neg]
            simp only [enorm_NNReal, coe_le_enorm]
            rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm, ← norm_neg]
            apply RCLike.re_le_norm
          · --analogous to the first case
            apply eLorentzNorm_mono_enorm_ae
            apply Filter.Eventually.of_forall
            intro x
            simp only [enorm_NNReal, coe_le_enorm]
            rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm]
            apply RCLike.im_le_norm
          · --analogous to the first case
            apply eLorentzNorm_mono_enorm_ae
            apply Filter.Eventually.of_forall
            intro x
            rw [← map_neg]
            simp only [enorm_NNReal, coe_le_enorm]
            rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm, ← norm_neg]
            apply RCLike.im_le_norm
          -/
  -- Apply claim to a special G
  --let G := {x | ‖T x‖ₑ > }
  --constructor
  use T_meas hf
  by_cases h : p = ⊤
  · rw [h]
    rw [eLorentzNorm_eq_eLpNorm sorry]
    by_cases h' : f =ᵐ[μ] 0
    · sorry
    · sorry
  · rw [eLorentzNorm_eq_wnorm hpq.ne_zero, wnorm_ne_top h]
    unfold wnorm'
    apply iSup_le
    intro l
    unfold distribution
    set G := {x | ↑l < ‖T f x‖ₑ}
--      set G'
    --rw [div_le_div__right]
    calc _
      _ = ↑l * ν G / ν G ^ q⁻¹.toReal := by
        rw [mul_div_assoc]
        congr
        rw [ENNReal.holderConjugate_iff] at hpq
        rw [ENNReal.eq_div_iff sorry sorry, ← ENNReal.rpow_add, ← ENNReal.toReal_inv, ← ENNReal.toReal_add, add_comm, hpq]
        · simp only [ENNReal.toReal_one, ENNReal.rpow_one]
        · rw [ne_eq, ENNReal.inv_eq_top]
          sorry
        · rw [ne_eq, ENNReal.inv_eq_top]
          sorry
        · sorry
        · sorry
      _ ≤ (∫⁻ (x : α') in G, ‖T f x‖ₑ ∂ν) / ν G ^ q⁻¹.toReal := by
        gcongr
        --rw [setLIntegral]
        rw [← Measure.restrict_eq_self _ (subset_refl G)]
        calc _
          _ ≤ ↑l * (ν.restrict G) {x | ↑l ≤ ‖T f x‖ₑ} := by
            gcongr
            intro x hx
            unfold G at hx
            rw [Set.mem_setOf_eq] at hx ⊢; exact hx.le
        apply mul_meas_ge_le_lintegral₀
        sorry
      _ = eLpNorm (T f) 1 (ν.restrict G) / ν G ^ q⁻¹.toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ((4 * c / p) * eLorentzNorm f p 1 μ * ν G ^ q⁻¹.toReal) / ν G ^ q⁻¹.toReal := by
        gcongr
        apply claim
        · sorry
        · sorry
      _ ≤ (4 * c / p) * eLorentzNorm f p 1 μ * 1 := by
        rw [mul_div_assoc]
        gcongr
        exact ENNReal.div_self_le_one
      _ = (4 * c / p) * eLorentzNorm f p 1 μ := by ring

--end Lorentz

end MeasureTheory
