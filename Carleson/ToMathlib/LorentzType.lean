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
  {μ : Measure α} {ν : Measure α'} [TopologicalSpace ε₁] [TopologicalSpace ε₂] {p p' q : ℝ≥0∞}

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

/-
def HasRestrictedWeakType' [ENorm ε₂] (T : (α → β) → (α' → ε₂)) (p q : ℝ≥0∞)
  (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator 1)) 1 (ν.restrict G)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ q⁻¹.toReal
-/

/-- Defines when an operator "has restricted weak type". This is an even weaker version
of `HasBoundedWeakType`. -/
def HasRestrictedWeakType [ENorm ε₂] (T : (α → β) → (α' → ε₂)) (p p' : ℝ≥0∞)
  (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α), (MeasurableSet F) → (μ F < ∞) →
    AEStronglyMeasurable (T (F.indicator 1)) ν ∧
      wnorm (T (F.indicator 1)) p' ν ≤ c * (μ F) ^ p⁻¹.toReal

lemma HasRestrictedWeakType.of_lintegral_le [SigmaFinite ν] [ContinuousENorm ε₂] {T : (α → β) → (α' → ε₂)}
  (hpq : p.HolderConjugate q) (hp : p ≠ ⊤) (hq : q ≠ ⊤) {c : ℝ≥0}
  (hT : ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator 1)) ν ∧
      (∫⁻ (x : α') in G, ‖T (F.indicator 1) x‖ₑ ∂ν)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ q⁻¹.toReal) :
    HasRestrictedWeakType T p p μ ν c := by
  intro F hF F_finite
  have hf : AEStronglyMeasurable (T (F.indicator fun x ↦ 1)) ν := by
    apply (hT F ∅ hF F_finite MeasurableSet.empty (by simp)).1
  use hf
  rw [wnorm_ne_top hp, wnorm']
  apply iSup_le
  intro l
  by_cases l_zero : l = 0
  · simp [l_zero]
  set G := {x | ↑l < ‖T (F.indicator 1) x‖ₑ}
  set f := (F.indicator (1 : α → β))
  have hG : NullMeasurableSet G ν := by
    unfold G
    apply nullMeasurableSet_lt aemeasurable_const hf.enorm
  rcases hG.exists_measurable_superset_ae_eq  with ⟨G', _, hG', G'G⟩
  have measure_G'G := measure_congr G'G
  have measure_G : ν G = distribution (T f) l ν := by rfl
  rw [← measure_G]
  have p_toReal_pos : 0 < p.toReal := toReal_pos hpq.ne_zero hp
  have q_toReal_pos : 0 < q.toReal := toReal_pos hpq.symm.ne_zero hq
  by_cases G_finite : ν G = ⊤
  · exfalso
    rw [← measure_G'G] at G_finite
    set r := (c * μ F ^ p⁻¹.toReal / ↑l) ^ p.toReal with r_def
    have : r < ν G' := by
      rw [G_finite]
      unfold r
      apply (ENNReal.rpow_lt_top_iff_of_pos p_toReal_pos).mpr
      apply ENNReal.div_lt_top _ (by simpa)
      apply ENNReal.mul_ne_top (by simp)
      apply ENNReal.rpow_ne_top_of_nonneg (by simp) F_finite.ne
    rcases ν.exists_subset_measure_lt_top hG' this with ⟨H, hH, H_subset_G', H_gt, H_finite⟩
    have H_pos := (zero_le _).trans_lt H_gt
    have := (hT F H hF F_finite hH H_finite).2
    apply this.not_gt
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
            ← ENNReal.rpow_rpow_inv (toReal_ne_zero.mpr ⟨hpq.ne_zero, hp⟩) (c * μ F ^ p⁻¹.toReal / ↑l),
            ← r_def, toReal_inv]
        apply ENNReal.rpow_lt_rpow H_gt (inv_pos.mpr p_toReal_pos)
      _ = ∫⁻ (x : α') in H, l ∂ν := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ (x : α') in H, ‖T (F.indicator 1) x‖ₑ ∂ν := by
        apply setLIntegral_mono_ae' hH
        filter_upwards [G'G]
        intro x h hx
        have : G x := by
          rw [← h]
          exact H_subset_G' hx
        exact this.le
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
      apply mul_meas_ge_le_lintegral₀
      apply AEMeasurable.restrict
      exact AEStronglyMeasurable.enorm hf
    _ ≤ (c * μ F ^ p⁻¹.toReal * ν G ^ q⁻¹.toReal) / ν G ^ q⁻¹.toReal := by
      gcongr
      convert (hT F G' hF F_finite hG' G'_finite).2 using 2
      · exact Measure.restrict_congr_set G'G.symm
      · congr 1
        exact measure_G'G.symm
    _ = c * μ F ^ p⁻¹.toReal := by
      apply ENNReal.mul_div_cancel_right
      · contrapose! G_zero
        rwa [ENNReal.rpow_eq_zero_iff_of_pos] at G_zero
        simp only [toReal_inv, inv_pos]
        apply toReal_pos hpq.symm.ne_zero hq
      · exact ENNReal.rpow_ne_top' G_zero G_finite.ne


lemma HasRestrictedWeakType.without_finiteness [ESeminormedAddMonoid ε₂] {T : (α → β) → (α' → ε₂)}
    (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
    {c : ℝ≥0} (c_pos : 0 < c) (hT : HasRestrictedWeakType T p p' μ ν c) :
  ∀ (F : Set α), (MeasurableSet F) →
      wnorm (T (F.indicator 1)) p' ν ≤ c * (μ F) ^ p⁻¹.toReal := by
  intro F hF
  by_cases F_finite : μ F < ∞
  · exact (hT F hF F_finite).2
  · simp only [not_lt, top_le_iff] at F_finite
    rw [F_finite, ENNReal.top_rpow_of_pos, mul_top]
    · exact le_top
    · simp only [ne_eq, ENNReal.coe_eq_zero]
      exact c_pos.ne.symm
    · simp only [toReal_inv, inv_pos]
      exact ENNReal.toReal_pos p_ne_zero p_ne_top

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
def WeaklyContinuous' [TopologicalSpace ε] [ENorm ε] [SupSet ε]
  [Preorder ε] [ENorm ε'] (T : (α → ε) → (α' → ε')) (p : ℝ≥0∞) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {fs : ℕ → SimpleFunc α ε} (_ : Monotone fs) (_ : BddAbove (range (fun n ↦ ⇑(fs n)))),
  let f := fun x ↦ ⨆ n, (fs n) x;
  ∀ (_ : MemLorentz f p 1 μ) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T ⇑(fs n)) 1 (ν.restrict G)) Filter.atTop
--TODO: Show that the Carleson operator is weakly continuous in this sense via Fatou's lemma

--wnorm (T fun a ↦ ⨆ n, (SimpleFunc.nnapprox f n) a) p ν ≤ limsup (fun n ↦ wnorm (T ⇑(SimpleFunc.nnapprox f n)) p ν) atTop
def WeaklyContinuous [TopologicalSpace ε] [ENorm ε] [SupSet ε]
  [Preorder ε] [ENorm ε'] (T : (α → ε) → (α' → ε')) (p : ℝ≥0∞) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {fs : ℕ → SimpleFunc α ε} (_ : Monotone fs) (_ : BddAbove (range (fun n ↦ ⇑(fs n)))),
  let f := fun x ↦ ⨆ n, (fs n) x;
  ∀ (_ : MemLorentz f p 1 μ),
    wnorm (T f) p ν ≤ Filter.limsup (fun n ↦ wnorm (T (fs n)) p ν) Filter.atTop

--lemma carlesonOperator_weaklyContinuous : WeaklyContinuous carlesonOperator

/-
theorem HasRestrictedWeakType.hasLorentzType_helper [TopologicalSpace ε'] [ENormedSpace ε']
  {c : ℝ≥0} (c_pos : 0 < c) {T : (α → ℝ≥0) → α' → ε'}
  (hT : HasRestrictedWeakType T p q μ ν c) --(T_zero : eLpNorm (T 0) 1 ν = 0)
  (hpq : p.HolderConjugate q)
  (weakly_cont_T : WeaklyContinuous' T p μ ν)
  {G : Set α'} (hG : MeasurableSet G)
  (T_subadd : ∀ (f g : α → ℝ≥0), (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    eLpNorm (T (f + g)) 1 (ν.restrict G) ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G))
  (T_submult : ∀ (f : α → ℝ≥0) (a : ℝ≥0), eLpNorm (T (a • f)) 1 (ν.restrict G) ≤ eLpNorm (a • T f) 1 (ν.restrict G))
  (T_zero_of_ae_zero : ∀ {f : α → ℝ≥0} (_ : f =ᶠ[ae μ] 0), eLpNorm (T f) 1 ν = 0)
  (T_ae_eq_of_ae_eq : ∀ {f g : α → ℝ≥0} (hfg : f =ᶠ[ae μ] g), T f =ᶠ[ae ν] T g)
  {f : α → ℝ≥0} (hf' : MemLorentz f p 1 μ) :
      eLpNorm (T f) 1 (ν.restrict G) ≤ (c / p) * eLorentzNorm f p 1 μ * ν G ^ q⁻¹.toReal := by
  wlog hf : Measurable f generalizing f
  · rcases hf'.1 with ⟨g, stronglyMeasurable_g, hfg⟩
    have hg' : MemLorentz g p 1 μ := by
      use StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_g
      convert hf'.2 using 1
      symm
      exact eLorentzNorm_congr_ae hfg
    have hg : Measurable g := stronglyMeasurable_g.measurable
    convert this hg' hg using 1
    · apply eLpNorm_congr_ae
      apply ae_restrict_le
      exact T_ae_eq_of_ae_eq hfg
    · congr 2
      exact eLorentzNorm_congr_ae hfg
  by_cases p_ne_top : p = ∞
  · sorry --TODO: check whether this works or whether it should be excluded
  by_cases q_ne_top : q = ∞
  · sorry --TODO: check whether this works or whether it should be excluded
  by_cases hG' : ν G = ∞
  · by_cases f_zero : f =ᶠ[ae μ] 0
    · sorry
    rw [hG', top_rpow_of_pos, mul_top]
    · exact le_top
    · apply mul_ne_zero
      · simp only [ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, not_or]
        use c_pos.ne.symm, p_ne_top
      · sorry --TODO: get this from f_zero (maybe need one more lemma)
    · simp only [toReal_inv, inv_pos]
      apply toReal_pos hpq.symm.ne_zero q_ne_top
  have hp : 1 ≤ p := hpq.one_le --use: should follow from hpq
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
          apply T_submult
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
      have hf' : MemLorentz f p 1 μ := by
        use (by fun_prop)
        apply hfg'.2.trans_le'
        apply eLorentzNorm_mono_enorm_ae
        simp
      have hg' : MemLorentz g p 1 μ := by
        use (by fun_prop)
        apply hfg'.2.trans_le'
        apply eLorentzNorm_mono_enorm_ae
        simp
      calc _
        _ ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G) := by
          apply T_subadd f g hf' hg'
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
        apply Filter.Eventually.of_forall
        intro n
        apply eLorentzNorm'_mono_enorm_ae
        apply Filter.Eventually.of_forall
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        intro x
        exact SimpleFunc.approx_le hf bot_eq_zero'
-/

theorem HasRestrictedWeakType.hasLorentzType_nnreal [TopologicalSpace ε'] [ENormedSpace ε']
  {c : ℝ≥0} (c_pos : 0 < c) {T : (α → ℝ≥0) → α' → ε'} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  {f : α → ℝ≥0} (hf' : MemLorentz f p 1 μ)
  (weakly_cont_T : WeaklyContinuous T p μ ν)
  (T_subadd : ∀ {f g : α → ℝ≥0}, (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
  (T_submul : ∀ (a : ℝ≥0) (f : α → ℝ≥0) (x : α'), ‖T (a • f) x‖ₑ ≤ a * ‖T f x‖ₑ)
  --(T_zero_of_ae_zero : ∀ {f : α → ℝ≥0} (_ : f =ᶠ[ae μ] 0), eLpNorm (T f) 1 ν = 0)
  (T_ae_eq_of_ae_eq : ∀ {f g : α → ℝ≥0}, (f =ᶠ[ae μ] g) → T f =ᶠ[ae ν] T g)
  (hT : HasRestrictedWeakType T p p μ ν c)
   :
      eLorentzNorm (T f) p ⊤ ν ≤ c / p * eLorentzNorm f p 1 μ := by
  wlog hf : Measurable f generalizing f
  · rcases hf'.1 with ⟨g, stronglyMeasurable_g, hfg⟩
    have hg' : MemLorentz g p 1 μ := by
      use StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_g
      convert hf'.2 using 1
      symm
      exact eLorentzNorm_congr_ae hfg
    have hg : Measurable g := stronglyMeasurable_g.measurable
    convert this hg' hg using 1
    · exact eLorentzNorm_congr_ae (T_ae_eq_of_ae_eq hfg)
    · congr 1
      exact eLorentzNorm_congr_ae hfg
  rw [eLorentzNorm_eq_wnorm p_ne_zero, eLorentzNorm_eq_eLorentzNorm' p_ne_zero p_ne_top]
  revert hf'
  revert f
  apply @Measurable.nnreal_induction _ m0
  · intro f
    induction f using SimpleFunc.induction''
    · rename_i a s hs
      rw [SimpleFunc.coe_restrict _ hs]
      simp only [SimpleFunc.coe_const]
      have smul_indicator : s.indicator (Function.const α a) = a • (s.indicator 1) := by
        ext x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Set.indicator_const_mul]
        congr with x
        simp
      nth_rw 1 2 [smul_indicator]
      intro hf'
      rw [eLorentzNorm'_indicator_const (by simp) p_ne_zero p_ne_top,
          ← mul_assoc, ENNReal.div_mul_cancel p_ne_zero p_ne_top]
      calc _
        _ ≤ wnorm (‖a‖ₑ • enorm ∘ (T (s.indicator 1))) p ν := by
          apply wnorm_mono_enorm_ae
          apply Eventually.of_forall
          intro x
          simp only [enorm_NNReal, Pi.smul_apply, comp_apply, smul_eq_mul, enorm_eq_self]
          apply T_submul
        _ ≤ ‖a‖ₑ * wnorm (enorm ∘ (T (s.indicator 1))) p ν := by
          apply wnorm_const_smul_le p_ne_zero
        _ = ‖a‖ₑ * wnorm (T (s.indicator 1)) p ν := by
          congr
        _ ≤ ‖a‖ₑ * (c * (μ s) ^ p⁻¹.toReal) := by
          gcongr
          exact hT.without_finiteness p_ne_zero p_ne_top c_pos s hs
      apply le_of_eq
      ring
    · rename_i f a s hs hfs hf hg
      rw [SimpleFunc.coe_add]
      set g := (SimpleFunc.const α a).restrict s with g_def
      intro hfg'
      have hf' : MemLorentz f p 1 μ := by
        use (by fun_prop)
        apply hfg'.2.trans_le'
        apply eLorentzNorm_mono_enorm_ae
        simp
      have hg' : MemLorentz g p 1 μ := by
        use (by fun_prop)
        apply hfg'.2.trans_le'
        apply eLorentzNorm_mono_enorm_ae
        simp
      calc _
        _ ≤ wnorm (T ⇑f) p ν + wnorm (T ⇑g) p ν := sorry --T_subadd hf' hg' --TODO: find a (non-general) triangle ineq for wnorm
        _ ≤ ↑c / p * eLorentzNorm' (⇑f) p 1 μ + ↑c / p * eLorentzNorm' (⇑g) p 1 μ := by
          gcongr
          · exact hf hf'
          · exact hg hg'
        _ = ↑c / p * (eLorentzNorm' (⇑f) p 1 μ + eLorentzNorm' (⇑g) p 1 μ) := by ring
      gcongr
      apply le_of_eq
      rw [eLorentzNorm'_eq_integral_distribution_rpow,
        eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_eq_integral_distribution_rpow]
      rw [← mul_add]
      congr 1
      rw [g_def, SimpleFunc.coe_restrict _ hs, SimpleFunc.coe_const]
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
  · intro f meas_f hfn hf
    rw [← SimpleFunc.iSup_nnapprox meas_f] at hf
    calc _
      _ ≤ Filter.limsup (fun n ↦ wnorm (T (SimpleFunc.nnapprox f n)) p ν) Filter.atTop := by
        nth_rw 1 [← SimpleFunc.iSup_nnapprox meas_f]
        apply weakly_cont_T SimpleFunc.monotone_nnapprox _ hf
        use f
        rw [mem_upperBounds]
        intro g hg
        rcases hg with ⟨n, hn⟩
        rw [← hn]
        intro x
        apply SimpleFunc.nnapprox_le meas_f
      _ ≤ Filter.limsup (fun n ↦ c / p * eLorentzNorm' (SimpleFunc.nnapprox f n) p 1 μ) Filter.atTop := by
        apply Filter.mono_limsup
        intro n
        apply hfn n
        use (by fun_prop)
        apply hf.2.trans_le'
        apply eLorentzNorm_mono_enorm_ae
        apply Filter.Eventually.of_forall
        intro x
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        rw [SimpleFunc.iSup_nnapprox_apply meas_f]
        apply SimpleFunc.nnapprox_le meas_f
      _ ≤ (c / p) * eLorentzNorm' f p 1 μ := by
        rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.div_ne_top (by simp) p_ne_zero)]
        gcongr
        apply Filter.limsup_le_of_le'
        apply Filter.Eventually.of_forall
        intro n
        apply eLorentzNorm'_mono_enorm_ae
        apply Filter.Eventually.of_forall
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        intro x
        exact SimpleFunc.approx_le meas_f bot_eq_zero'

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

@[simp]
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

--TODO: clean up the proof
theorem RCLike.induction {𝕂 : Type*} [RCLike 𝕂]
  {P : (α → 𝕂) → Prop}
  (P_add : ∀ {f g : α → 𝕂}, P f → P g → P (f + g))
  (P_components : ∀ {f : α → 𝕂} {c : 𝕂} (_ : c ∈ RCLike.Components),
    P f → P (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ RCLike.component c ∘ f))
  (P_mul_unit : ∀ {f : α → 𝕂} {c : 𝕂} (_ : c ∈ RCLike.Components), P f → P (c • f))
  {motive : (α → 𝕂) → ℕ → Prop}
  (motive_nnreal : ∀ {f : α → ℝ≥0} (_ : P (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ f)),
    motive (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ f) 1)
  (motive_add : ∀ {f g : α → 𝕂} {n m : ℕ} (_ : ∀ {a : α}, ‖f a‖ ≤ ‖(f + g) a‖) (_ : ∀ {a : α}, ‖g a‖ ≤ ‖(f + g) a‖)
    (_ : P f) (_ : P g), motive f n → motive g m → motive (f + g) (n + m))
  --(motive_mono_norm : ∀ {f g : α → 𝕂} {n : ℕ} (_ : ∀ {a : α}, ‖f a‖ ≤ ‖g a‖) (_ : P g), motive g n → motive f n)
  (motive_mul_unit : ∀ {f : α → 𝕂} {c : 𝕂} {n : ℕ} (_ : c ∈ RCLike.Components) (_ : P f),
    motive f n → motive (c • f) n)
  ⦃f : α → 𝕂⦄ (hf : P f) :
    motive f 4 := by
  have f_decomposition :
    (1 : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component 1 ∘ f)
    + (-1 : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component (-1) ∘ f)
    + (RCLike.I : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component RCLike.I ∘ f)
    + (-RCLike.I : 𝕂) • ((algebraMap ℝ 𝕂) ∘ toReal ∘ component (-RCLike.I) ∘ f) = f := by
    ext x
    simp only [Pi.add_apply, comp_apply, Pi.smul_apply, smul_eq_mul]
    exact RCLike.decomposition
  rw [← f_decomposition]
  have : 4 = 1 + 1 + 1 + 1 := by norm_num
  rw [this]
  apply motive_add
  · sorry
  · sorry
  · apply P_add
    · apply P_add
      · apply P_mul_unit (by unfold Components; simp)
        apply P_components (by unfold Components; simp) hf
      · apply P_mul_unit (by unfold Components; simp)
        apply P_components (by unfold Components; simp) hf
    · apply P_mul_unit (by unfold Components; simp)
      apply P_components (by unfold Components; simp) hf
  · apply P_mul_unit (by unfold Components; simp)
    apply P_components (by unfold Components; simp) hf
  · apply motive_add
    · sorry
    · sorry
    · apply P_add
      · apply P_mul_unit (by unfold Components; simp)
        apply P_components (by unfold Components; simp) hf
      · apply P_mul_unit (by unfold Components; simp)
        apply P_components (by unfold Components; simp) hf
    · apply P_mul_unit (by unfold Components; simp)
      apply P_components (by unfold Components; simp) hf
    · apply motive_add
      · sorry
      · sorry
      · apply P_mul_unit (by unfold Components; simp)
        apply P_components (by unfold Components; simp) hf
      · apply P_mul_unit (by unfold Components; simp)
        apply P_components (by unfold Components; simp) hf
      · apply motive_mul_unit (by unfold Components; simp)
        · apply P_components (by unfold Components; simp) hf
        apply motive_nnreal (f := component _ ∘ f)
        apply P_components (by unfold Components; simp) hf
      · apply motive_mul_unit (by unfold Components; simp)
        · apply P_components (by unfold Components; simp) hf
        apply motive_nnreal (f := component _ ∘ f)
        apply P_components (by unfold Components; simp) hf
    · apply motive_mul_unit (by unfold Components; simp)
      · apply P_components (by unfold Components; simp) hf
      apply motive_nnreal (f := component _ ∘ f)
      apply P_components (by unfold Components; simp) hf
  · apply motive_mul_unit (by unfold Components; simp)
    · apply P_components (by unfold Components; simp) hf
    apply motive_nnreal (f := component _ ∘ f)
    apply P_components (by unfold Components; simp) hf

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

theorem memLorentz_iff_memLorentz_embedRCLike [TopologicalSpace α] {𝕂 : Type*} [RCLike 𝕂]
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

lemma HasRestrictedWeakType.hasLorentzType [TopologicalSpace α] {𝕂 : Type*}
  [RCLike 𝕂] [TopologicalSpace ε'] [ENormedSpace ε']
  {T : (α → 𝕂) → (α' → ε')}
  [IsLocallyFiniteMeasure μ] [NoAtoms μ] {c : ℝ≥0} (c_pos : 0 < c)
  (hT : HasRestrictedWeakType T p p μ ν c) --(hpq : p.HolderConjugate q)
  (T_meas : ∀ {f : α → 𝕂}, (MemLorentz f p 1 μ) → AEStronglyMeasurable (T f) ν)
  (T_subadd : ∀ {f g : α → 𝕂}, (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    --wnorm (T (f + g)) p ν ≤ wnorm (T f) p ν + wnorm (T g) p ν) --TODO: replace by pointwise estimate?
  (T_submul : ∀ (a : 𝕂) (f : α → 𝕂) (x : α'), ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ * ‖T f x‖ₑ)
  (weakly_cont_T : ∀ {f : α → 𝕂} {fs : ℕ → α → 𝕂},
                     (MemLorentz f p 1 μ) →
                     (∀ (n : ℕ), AEStronglyMeasurable (fs n) μ) →
                     (∀ (a : α), Monotone (fun n ↦ ‖fs n a‖)) →
                     (∀ (a : α), Filter.Tendsto (fun (n : ℕ) => fs n a) Filter.atTop (nhds (f a))) →
    wnorm (T f) p ν ≤ Filter.limsup (fun n ↦ wnorm (T (fs n)) p ν) Filter.atTop)
  (T_zero : T 0 =ᶠ[ae ν] 0)
  (T_ae_eq_of_ae_eq : ∀ {f g : α → 𝕂} (_ : f =ᶠ[ae μ] g), T f =ᶠ[ae ν] T g) --TODO: incorporate into weakly_cont_T?
    :
    HasLorentzType T p 1 p ∞ μ ν (4 * c / p) := by
  have T_zero_of_ae_zero : ∀ {f : α → 𝕂} (_ : f =ᶠ[ae μ] 0), T f =ᶠ[ae ν] 0 := by
    intro f hf
    filter_upwards [T_ae_eq_of_ae_eq hf, T_zero]
    intro a h h'
    rwa [h]
  intro f hf
  use T_meas hf
  by_cases p_zero : p = 0
  · rw [p_zero]
    simp
  by_cases p_top : p = ⊤
  · rw [p_top]
    rw [eLorentzNorm_eq_eLpNorm (T_meas hf)]
    by_cases h' : f =ᵐ[μ] 0
    · rw [eLpNorm_zero_of_ae_zero (T_zero_of_ae_zero h'),
          eLorentzNorm_zero_of_ae_zero h']
      simp
    · have := hf.2
      rw [p_top, eLorentzNorm_exponent_top (by simp) (by simp) h'] at this
      contradiction
  revert f
  apply RCLike.induction (motive := fun f n ↦ eLorentzNorm (T f) p ⊤ ν ≤ n * ↑c / p * eLorentzNorm f p 1 μ)
  · exact MemLorentz.add
  · intro f c hc hf
    rw [memLorentz_iff_memLorentz_embedRCLike]
    constructor
    · have := hf.1
      rw [aestronglyMeasurable_iff_aemeasurable]
      unfold RCLike.component
      apply AEMeasurable.comp_aemeasurable (by fun_prop) hf.1.aemeasurable
    · apply hf.2.trans_le'
      apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      simp only [comp_apply, enorm_NNReal, coe_le_enorm]
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
  · --main case
    intro f hf
    simp only [Nat.cast_one, one_mul]
    set T' := T ∘ (fun f ↦ ⇑(algebraMap ℝ 𝕂) ∘ NNReal.toReal ∘ f)
    -- T' inherits properties of T
    have T'f_eq : T' f = T (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) := by
      unfold T'
      simp
    rw [← T'f_eq]
    rw [eLorentzNorm_congr_enorm_ae (Eventually.of_forall enorm_eq_enorm_embedRCLike)]
    rw [memLorentz_iff_memLorentz_embedRCLike] at hf
    apply HasRestrictedWeakType.hasLorentzType_nnreal c_pos p_zero p_top hf
    · unfold WeaklyContinuous T'
      intro fs hfs bddAbove_fs f hf
      simp only [Function.comp_apply]
      apply weakly_cont_T
      · rwa [memLorentz_iff_memLorentz_embedRCLike]
        /-
        apply ((hf.memLp (by simpa)).locallyIntegrable hp).congr'_enorm
        · apply AEMeasurable.aestronglyMeasurable
          apply RCLike.measurable_ofReal.comp_aemeasurable
          apply measurable_coe_nnreal_real.comp_aemeasurable
          exact hf.1.aemeasurable
        -/
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
    · intro f g hf hg
      unfold T'
      simp only [comp_apply]
      rw [← memLorentz_iff_memLorentz_embedRCLike (𝕂 := 𝕂)] at hf
      rw [← memLorentz_iff_memLorentz_embedRCLike (𝕂 := 𝕂)] at hg
      filter_upwards [T_subadd hf hg]
      intro x h
      apply h.trans_eq'
      congr with x
      simp
    · intro a f x
      unfold T'
      simp only [comp_apply]
      have : a * ‖T (RCLike.ofReal ∘ NNReal.toReal ∘ f) x‖ₑ
        = ‖a‖ₑ * ‖T (RCLike.ofReal ∘ NNReal.toReal ∘ f) x‖ₑ := by
        congr
      rw [this]
      convert T_submul (NNReal.toReal a) _ x
      · ext x
        simp
      congr
      simp
    · intro f g hfg
      unfold T'
      simp only [comp_apply]
      apply T_ae_eq_of_ae_eq
      filter_upwards [hfg]
      simp
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
  · intro f g n m hf_add hg_add hf hg hf' hg'
    rw [eLorentzNorm_eq_wnorm p_zero] at *
    --apply eLpNorm_add
    /-
    apply (T_subadd hf hg).trans
    rw [Nat.cast_add, add_mul, ENNReal.add_div, add_mul]
    gcongr
    · apply hf'.trans
      gcongr
      apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal hf_add
    · apply hg'.trans
      gcongr
      apply eLorentzNorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal hg_add
    -/
    sorry
  · intro f b n hb hf
    by_cases h : b = 0
    · intro _
      rw [h]
      simp only [zero_smul, eLorentzNorm_zero, mul_zero,
        nonpos_iff_eq_zero]
      apply eLorentzNorm_zero_of_ae_zero
      apply T_zero_of_ae_zero
      trivial
    gcongr
    · rw [eLorentzNorm_eq_wnorm p_zero, eLorentzNorm_eq_wnorm p_zero]
      apply wnorm_mono_enorm_ae
      apply Eventually.of_forall
      intro x
      apply (T_submul _ _ _).trans
      nth_rw 2 [← one_mul ‖T f x‖ₑ]
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
  /-
  have T_zero_of_ae_zero' : ∀ {f : α → 𝕂} (_ : f =ᶠ[ae μ] 0), eLpNorm (T f) 1 ν = 0 := by
    intro f hf
    exact eLpNorm_zero_of_ae_zero (T_zero_of_ae_zero hf)
  have T_ae_eq_of_ae_eq : ∀ {f g : α → 𝕂} (hfg : f =ᶠ[ae μ] g), T f =ᶠ[ae ν] T g := by
    intro f g hfg
    --have : f = g + (f - g) := by simp
    --apply le_antisymm
    sorry

    --sorry --use T_submul and T_zero_of_ae_zero
    --TODO: have this as an external lemma?

  have claim : ∀ (G : Set α'), (MeasurableSet G) → eLpNorm (T f) 1 (ν.restrict G)
    ≤ (4 * c / p) * eLorentzNorm f p 1 μ * (ν G) ^ q⁻¹.toReal := by
      intro G measurable_G
      revert f
      apply RCLike.induction (motive := fun f n ↦
        eLpNorm (T f) 1 (ν.restrict G)
          ≤ (n : ℝ≥0∞) * c / p * eLorentzNorm f p 1 μ * (ν G) ^ q⁻¹.toReal)
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
      · --main case
        set T' := T ∘ (fun f ↦ ⇑(algebraMap ℝ 𝕂) ∘ NNReal.toReal ∘ f)
        -- T' inherits properties of T
        have hT' : HasRestrictedWeakType T' p q μ ν c := by
          intro F G measurable_F hF measurable_G hG
          unfold T'
          have fun_eq : (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ F.indicator fun x ↦ 1) = F.indicator fun x ↦ 1 := by
            ext x
            unfold indicator
            split_ifs <;> simpa
          simp only [comp_apply]
          rw [fun_eq]
          exact hT F G measurable_F hF measurable_G hG
        have weaklyCont_T' : WeaklyContinuous T' p μ ν := by
          unfold WeaklyContinuous T'
          intro fs hfs bddAbove_fs f hf G
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
          apply (T_subadd measurable_G hf' hg').trans_eq'
          congr
          ext x
          simp
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
        have helper : ∀ {f : α → ℝ≥0} (hf : MemLorentz f p 1 μ),
            eLpNorm (T' f) 1 (ν.restrict G) ≤ (c / p) * eLorentzNorm f p 1 μ * ν G ^ q⁻¹.toReal := by
          intro f hf
          apply HasRestrictedWeakType.hasLorentzType_helper c_pos hT' hpq weaklyCont_T' measurable_G
            T'_subadd T'_submul _ _ hf
          · intro f hf
            unfold T'
            simp only [Function.comp_apply]
            apply T_zero_of_ae_zero'
            have : RCLike.ofReal ∘ NNReal.toReal ∘ (0 : α → ℝ≥0) = (0 : α → 𝕂) := by simp
            rw [← this]
            apply Filter.EventuallyEq.fun_comp
            apply Filter.EventuallyEq.fun_comp hf
          · intro f g hfg
            unfold T'
            simp only [comp_apply]
            apply T_ae_eq_of_ae_eq
            filter_upwards [hfg]
            intro a hfg
            simpa
        unfold T' at helper
        simp only [comp_apply] at helper
        intro f hf
        simp only [Nat.cast_one, one_mul]
        have : eLorentzNorm (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) p 1 μ = eLorentzNorm f p 1 μ := by
          apply eLorentzNorm_congr_enorm_ae
          apply Eventually.of_forall
          intro x
          rw [← ofReal_norm]
          simp
        rw [this]
        apply helper
        constructor
        · have comp_eq : (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) = fun x ↦ ⇑(algebraMap ℝ 𝕂) (f x).toReal := by
            ext x
            simp
          have := hf.1
          rw [comp_eq] at this
          rwa [IsEmbedding.aestronglyMeasurable_comp_iff, IsEmbedding.aestronglyMeasurable_comp_iff] at this
          · exact (Isometry.isEmbedding fun _ ↦ congrFun rfl)
          · exact (algebraMap_isometry ℝ 𝕂).isEmbedding
        · rw [← this]
          exact hf.2
      · intro f g n m hf_add hg_add hf hg hf' hg'
        apply (T_subadd measurable_G hf hg).trans
        rw [Nat.cast_add, add_mul, ENNReal.add_div, add_mul, add_mul]
        gcongr
        · apply hf'.trans
          gcongr
          apply eLorentzNorm_mono_enorm_ae
          apply Eventually.of_forall
          intro x
          rw [← ofReal_norm, ← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal hf_add
        · apply hg'.trans
          gcongr
          apply eLorentzNorm_mono_enorm_ae
          apply Eventually.of_forall
          intro x
          rw [← ofReal_norm, ← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal hg_add
      · intro f b n hb hf
        by_cases h : b = 0
        · intro _
          rw [h]
          simp only [zero_smul, eLorentzNorm_zero, mul_zero, toReal_inv, zero_mul,
            nonpos_iff_eq_zero]
          apply eLpNorm_eq_zero_of_ae_zero
          apply ae_restrict_le
          apply T_zero_of_ae_zero
          trivial
        gcongr
        · apply eLpNorm_mono_enorm
          intro x
          apply (T_submul _ _ _).trans
          nth_rw 2 [← one_mul ‖T f x‖ₑ]
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
  by_cases p_top : p = ⊤
  · rw [p_top]
    rw [eLorentzNorm_eq_eLpNorm (T_meas hf)]
    by_cases h' : f =ᵐ[μ] 0
    · rw [eLpNorm_zero_of_ae_zero (T_zero_of_ae_zero h'),
          eLorentzNorm_zero_of_ae_zero h']
      simp
    · have := hf.2
      rw [p_top, eLorentzNorm_exponent_top (by simp) (by simp) h'] at this
      contradiction
  · have p_zero : p ≠ 0 := hpq.ne_zero
    have q_zero : q ≠ 0 := hpq.symm.ne_zero
    have hp : 0 < p.toReal := by
      apply toReal_pos p_zero p_top
    rw [eLorentzNorm_eq_wnorm hpq.ne_zero, wnorm_ne_top p_top]
    unfold wnorm'
    apply iSup_le
    intro l
    unfold distribution
    set G := {x | ↑l < ‖T f x‖ₑ}
    have measurable_G : MeasurableSet G := by
      sorry
    have measure_G : ν G = distribution (T f) l ν := by rfl
    have G_finite : ν G < ∞ := by
      sorry --TODO: might need another case distinction
    by_cases G_zero : ν G = 0
    · rw [G_zero, zero_rpow_of_pos (by simpa)]
      simp
    calc _
      _ = ↑l * ν G / ν G ^ q⁻¹.toReal := by
        rw [mul_div_assoc]
        congr
        rw [ENNReal.holderConjugate_iff] at hpq
        rw [ENNReal.eq_div_iff,
            ← ENNReal.rpow_add, ← ENNReal.toReal_inv, ← ENNReal.toReal_add, add_comm, hpq]
        · simp only [ENNReal.toReal_one, ENNReal.rpow_one]
        · rwa [ne_eq, ENNReal.inv_eq_top]
        · rwa [ne_eq, ENNReal.inv_eq_top]
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
        apply mul_meas_ge_le_lintegral₀
        apply AEMeasurable.restrict
        exact AEStronglyMeasurable.enorm (T_meas hf)
      _ = eLpNorm (T f) 1 (ν.restrict G) / ν G ^ q⁻¹.toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ((4 * c / p) * eLorentzNorm f p 1 μ * ν G ^ q⁻¹.toReal) / ν G ^ q⁻¹.toReal := by
        gcongr
        apply claim _ measurable_G
      _ ≤ (4 * c / p) * eLorentzNorm f p 1 μ * 1 := by
        rw [mul_div_assoc]
        gcongr
        exact ENNReal.div_self_le_one
      _ = (4 * c / p) * eLorentzNorm f p 1 μ := by ring
  -/

end MeasureTheory
