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

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']


namespace MeasureTheory

def decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0) : ℝ≥0 :=
  sInf {σ | distribution f σ μ ≤ t}

lemma decreasing_rearrangement_antitone {f : α → ε} {μ : Measure α} :
    Antitone (decreasing_rearrangement f μ) := sorry

#check NNReal.measurableSpace


lemma distribution_decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0):
  distribution f t μ = distribution (decreasing_rearrangement f μ) t volume := sorry

section Lorentz

/-
/-- The Lorentz norm of a function, for `r < ∞` -/
def eLorentzNorm' (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0) (μ : Measure α) : ℝ≥0∞ :=
  eLpNorm (fun t ↦ t ^ p⁻¹.toReal * decreasing_rearrangement f μ t) r
    (Measure.Subtype.measureSpace.volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

/-- The Lorentz norm of a function, for `r = ∞` -/
def eLorentzNormSup (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :=
  ⨆ t : ℝ≥0, t ^ p⁻¹.toReal * decreasing_rearrangement f μ t
-/


/-- The Lorentz norm of a function -/
/-
def eLorentzNorm (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if r = 0 then 0 else if r = ∞ then eLorentzNormSup f p μ else eLorentzNorm' f p r.toNNReal μ
-/
def eLorentzNorm (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  p ^ r⁻¹.toReal * eLpNorm (fun (t : ℝ≥0) ↦ t * distribution f t μ) r
    (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

/- Alternative definition. Not used at the moment. -/
lemma eLorentzNorm_eq {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} :
    eLorentzNorm f p r μ
      = eLpNorm (fun t ↦ t ^ p⁻¹.toReal * decreasing_rearrangement f μ t) r
          (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := sorry

lemma eLorentzNorm_eq_Lp {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
  eLorentzNorm f p p μ = eLpNorm f p μ := sorry

lemma eLorentzNorm_eq_wnorm {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
  eLorentzNorm f p ∞ μ = wnorm f p μ := sorry

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


def HasLorentzType (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧ eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ


--TODO: what exactly should be the requirements on 𝕂? Actually, we only need a 1 here.
--TODO: This could be more general, it currently assumes T f ≥ 0
variable {𝕂 : Type*} [TopologicalSpace 𝕂] [ContinuousENorm 𝕂] [NormedField 𝕂]
def HasRestrictedWeakType (T : (α → 𝕂) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G) ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal

lemma HasRestrictedWeakType.HasLorentzType {T : (α → 𝕂) → (α' → ε₂)} {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'}
  {c : ℝ≥0∞} (hT : HasRestrictedWeakType T p p' μ ν c) (hpp' : p.HolderConjugate p') :
    --TODO: might have to adjust the constant
    HasLorentzType T p 1 p ∞ μ ν c := by
  intro f hf
  have claim : ∀ (G : Set α'), (MeasurableSet G) → (ν G < ∞) → eLpNorm (T f) 1 (ν.restrict G)
    ≤ c * eLorentzNorm f p 1 μ * (ν G) ^ p'⁻¹.toReal := by
      -- Get this for simple functions first?
      sorry
  -- Apply claim to a special G
  sorry
