import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.WeakType
import Carleson.ToMathlib.MeasureTheory.Measure.NNReal


noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α}

namespace MeasureTheory

/-
section decreasing_rearrangement
variable [ENorm ε] [ENorm ε']

def decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0) : ℝ≥0 :=
  sInf {σ | distribution f σ μ ≤ t}

lemma decreasing_rearrangement_antitone {f : α → ε} {μ : Measure α} :
    Antitone (decreasing_rearrangement f μ) := sorry

lemma distribution_decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0):
  distribution f t μ = distribution (decreasing_rearrangement f μ) t volume := sorry

end decreasing_rearrangement
-/

section Lorentz
variable [ENorm ε] [ENorm ε'] {p : ℝ≥0∞} {q : ℝ}


/-- The Lorentz norm of a function, for `p < ∞` -/
def eLorentzNorm' (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  p ^ r⁻¹.toReal * eLpNorm (fun (t : ℝ≥0) ↦ t * distribution f t μ ^ p⁻¹.toReal) r
    (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

/-- The Lorentz norm of a function -/
def eLorentzNorm (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then (if r = 0 then 0 else if r = ∞ then eLpNormEssSup f μ else ∞ * eLpNormEssSup f μ)
  else eLorentzNorm' f p r μ

@[simp]
lemma eLorentzNorm_eq_eLorentzNorm' {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLorentzNorm f p r μ = eLorentzNorm' f p r μ := by
  unfold eLorentzNorm
  simp [hp_ne_zero, hp_ne_top]

@[simp]
lemma eLorentzNorm_zero {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} (hp : p = 0) :
    eLorentzNorm f p r μ = 0 := by
  unfold eLorentzNorm
  simp [hp]

@[simp]
lemma eLorentzNorm_zero' {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} (hr : r = 0) :
    eLorentzNorm f p r μ = 0 := by
  unfold eLorentzNorm eLorentzNorm'
  simp [hr]


--TODO: make this an iff, for p, r ≠ 0?
lemma eLorentzNorm_zero_of_ae_zero {E : Type*} [TopologicalSpace E] [ENormedAddMonoid E] {p r : ℝ≥0∞} {μ : Measure α} {f : α → E} (h : f =ᵐ[μ] 0) : eLorentzNorm f p r μ = 0 := by
  unfold eLorentzNorm
  simp only [ite_eq_left_iff]
  intro p_ne_zero
  rw [eLpNormEssSup_eq_zero_iff.mpr h]
  simp only [mul_zero, ite_self, ite_eq_left_iff]
  intro p_ne_top
  unfold eLorentzNorm'
  conv in ↑t * distribution f _ μ ^ p⁻¹.toReal =>
    rw [distribution_zero h,
    ENNReal.zero_rpow_of_pos (by simp only [ENNReal.toReal_inv, inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top),
    mul_zero]
  simp

/-
/- Alternative definition. Not used at the moment. -/
lemma eLorentzNorm_eq {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} :
    eLorentzNorm f p r μ
      = eLpNorm (fun t ↦ t ^ p⁻¹.toReal * decreasing_rearrangement f μ t) r
          (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := sorry
-/

@[simp]
lemma eLorentzNorm_top_top {E : Type*} [ENorm E] --[NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} :
    eLorentzNorm f ∞ ∞ μ = eLpNormEssSup f μ := by
  unfold eLorentzNorm
  simp

lemma eLorentzNorm_eq_Lp {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    {μ : Measure α} {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0∞}  :
  eLorentzNorm f p p μ = eLpNorm f p μ := by
  unfold eLorentzNorm
  by_cases p_zero : p = 0
  · simp [p_zero]
  by_cases p_eq_top : p = ∞
  · simp [p_eq_top]
  have p_eq : p = .ofReal p.toReal := by simp [p_eq_top]
  simp only [p_zero, ↓reduceIte, p_eq_top]
  unfold eLorentzNorm'
  calc _
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal t ^ (p.toReal - 1) ) ^ p⁻¹.toReal := by
        rw [← p_eq, eLpNorm_eq_eLpNorm' p_zero p_eq_top, eLpNorm'_eq_lintegral_enorm,
          ENNReal.mul_rpow_of_nonneg, lintegral_withDensity_eq_lintegral_mul_non_measurable]
        · simp only [ENNReal.toReal_inv, enorm_eq_self, one_div]
          congr 2
          simp only [Pi.mul_apply]
          rw [@integral_nnreal' (fun x ↦ x⁻¹ * (x * distribution f x μ ^ p.toReal⁻¹)^ p.toReal)]
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht
          simp only
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← mul_assoc, ← ENNReal.rpow_neg_one,
              ← ENNReal.rpow_add _ _ (by simpa) (by simp), mul_comm]
          congr 2
          · rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨p_zero,p_eq_top⟩), ENNReal.rpow_one]
          · exact neg_add_eq_sub 1 p.toReal
        · exact Measurable.inv measurable_coe_nnreal_ennreal
        · rw[Filter.eventually_iff_exists_mem]
          use {x | x ≠ 0}
          constructor
          · refine mem_ae_iff.mpr ?_
            rw [NNReal.volume_val]
            simp
          · intro x hx
            rw[ENNReal.inv_lt_top, ENNReal.coe_pos]
            exact pos_of_ne_zero hx
        · simp
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal (t ^ (p.toReal - 1)) ) ^ p.toReal⁻¹ := by
        rw [ENNReal.toReal_inv]
        congr 2
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [Pi.mul_apply, ENNReal.ofReal_rpow_of_pos ht]
    _ = eLpNorm f (.ofReal p.toReal) μ := (eLpNorm_eq_distribution hf (ENNReal.toReal_pos p_zero p_eq_top)).symm
    _ = eLpNorm f p μ := by congr; exact p_eq.symm




lemma eLorentzNorm_eq_wnorm {E : Type*} [ENorm E] --[NormedAddCommGroup E]
    {f : α → E} {p : ℝ≥0∞} (hp : p ≠ 0) {μ : Measure α} : eLorentzNorm f p ∞ μ = wnorm f p μ := by
  by_cases p_eq_top : p = ∞
  · rw [p_eq_top]
    simp
  rw [eLorentzNorm_eq_eLorentzNorm' hp p_eq_top, wnorm_ne_top p_eq_top]
  unfold eLorentzNorm' wnorm'
  simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, ENNReal.toReal_inv,
    eLpNorm_exponent_top, one_mul]
  unfold eLpNormEssSup
  --rw [Continuous.essSup]
  simp only [enorm_eq_self]
  --TODO: somehow use continuity properties of the distribution function here
  sorry

variable [TopologicalSpace ε] [ContinuousENorm ε]
/-- A function is in the Lorentz space L_{pr} if it is (strongly a.e.)-measurable and has finite Lorentz norm. -/
def MemLorentz (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ eLorentzNorm f p r μ < ∞

-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_nested {f : α → ε} {p r₁ r₂ : ℝ≥0∞} {μ : Measure α}
  (h : r₁ ≤ r₂) (hf : MemLorentz f p r₁ μ) :
    MemLorentz f p r₂ μ := sorry


variable {α' ε₁ ε₂ : Type*} {m : MeasurableSpace α'} [TopologicalSpace ε₁] [ContinuousENorm ε₁]
    [TopologicalSpace ε₂] [ContinuousENorm ε₂] --[TopologicalSpace ε₃] [ContinuousENorm ε₃]
    {f : α → ε} {f₁ : α → ε₁}

/-- An operator has Lorentz type `(p, r, q, s)` if it is bounded as a map
from `L^{q, s}` to `L^{p, r}`. `HasLorentzType T p r q s μ ν c` means that
`T` has Lorentz type `(p, r, q, s)` w.r.t. measures `μ`, `ν` and constant `c`. -/
def HasLorentzType (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧
    eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ

/-
-- TODO: find better name
lemma HasLorentzType_p_infty_qs {T : (α → ε₁) → (α' → ε₂)} {p q s : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞} (h : 0 < c) (hT : AEStronglyMeasurable (T f) ν) :
  HasLorentzType T p ∞ q s μ ν c := by
  intro f hf
-/

--TODO: what exactly should be the requirements on 𝕂? Actually, we only need a 1 here.
--TODO: This could be more general, it currently assumes T f ≥ 0
variable {𝕂 : Type*} [TopologicalSpace 𝕂] [ContinuousENorm 𝕂] [NormedField 𝕂]

/-- Defines when an operator "has restricted weak type". This is an even weaker version
of `HasBoundedWeakType`. -/
def HasRestrictedWeakType (T : (α → 𝕂) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal

lemma HasRestrictedWeakType.HasLorentzType {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] {T : (α → 𝕂) → (α' → E)} {p p' : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞}
  (hT : HasRestrictedWeakType T p p' μ ν c) (hpp' : p.HolderConjugate p') :
    --TODO: might have to adjust the constant
    HasLorentzType T p 1 p ∞ μ ν c := by
  intro f hf
  have claim : ∀ (G : Set α'), (MeasurableSet G) → (ν G < ∞) → eLpNorm (T f) 1 (ν.restrict G)
    ≤ c * eLorentzNorm f p 1 μ * (ν G) ^ p'⁻¹.toReal := by
      -- Get this for simple functions first?
      sorry
  -- Apply claim to a special G
  --let G := {x | ‖T x‖ₑ > }
  constructor
  · sorry
  · by_cases h : p = ⊤
    · rw [h]
      rw [eLorentzNorm_eq_Lp sorry]
      by_cases h' : f =ᵐ[μ] 0
      · sorry
      · sorry
    · rw [eLorentzNorm_eq_wnorm sorry, wnorm_ne_top h]
      unfold wnorm'
      apply iSup_le
      intro l
      unfold distribution
      set G := {x | ↑l < ‖T f x‖ₑ}
--      set G'
      --rw [div_le_div__right]
      calc _
        _ = ↑l * ν G / ν G ^ p'⁻¹.toReal := by
          rw [mul_div_assoc]
          congr
          rw [ENNReal.holderConjugate_iff] at hpp'
          rw [ENNReal.eq_div_iff sorry sorry, ← ENNReal.rpow_add, ← ENNReal.toReal_inv, ← ENNReal.toReal_add, add_comm, hpp']
          · simp only [ENNReal.toReal_one, ENNReal.rpow_one]
          · rw [ne_eq, ENNReal.inv_eq_top]
            sorry
          · rw [ne_eq, ENNReal.inv_eq_top]
            sorry
          · sorry
          · sorry
        _ ≤ (∫⁻ (x : α') in G, ‖T f x‖ₑ ∂ν) / ν G ^ p'⁻¹.toReal := by
          gcongr
          --rw [setLIntegral]
          rw [← Measure.restrict_eq_self _ (subset_refl G)]
          calc _
            _ ≤ ↑l * (ν.restrict G) {x | ↑l ≤ ‖T f x‖ₑ} := by
              gcongr
              intro x hx
              unfold G at hx
              simp only [coe_lt_enorm, Set.mem_setOf_eq] at hx
              simp only [coe_le_enorm, Set.mem_setOf_eq, hx.le]
          apply mul_meas_ge_le_lintegral₀
          sorry
        _ = eLpNorm (T f) 1 (ν.restrict G) / ν G ^ p'⁻¹.toReal := by
          rw [eLpNorm_one_eq_lintegral_enorm]
        _ ≤ (c * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal) / ν G ^ p'⁻¹.toReal := by
          gcongr
          apply claim
          · sorry
          · sorry
        _ ≤ c * eLorentzNorm f p 1 μ * 1 := by
          rw [mul_div_assoc]
          gcongr
          exact ENNReal.div_self_le_one
        _ = c * eLorentzNorm f p 1 μ := by ring

end Lorentz

end MeasureTheory
