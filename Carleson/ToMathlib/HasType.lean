module

public import Carleson.ToMathlib.BoundedFiniteSupport
public import Carleson.ToMathlib.WNorm

@[expose] public section

/-!
# Weak, strong and Lorentz type of operators

The predicates `HasWeakType`, `HasBoundedWeakType`, `HasStrongType`, `HasBoundedStrongType` and
`HasLorentzType` for operators between function spaces, and their basic properties.
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

section Defs

variable [ENorm ε₁] [ENorm ε₂] [TopologicalSpace ε₁] [TopologicalSpace ε₂]
/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from `L^p` to weak `L^q`.
`HasWeakType T p p' μ ν c` means that `T` has weak type `(p, p')` w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A weaker version of `HasWeakType`. -/
def HasBoundedWeakType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, BoundedFiniteSupport f μ →
  AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- An operator has strong type `(p, q)` if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`. -/
def HasStrongType {α α' : Type*}
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

-- `HasBoundedStrongType` has moved to `Defs.lean`

/-- An operator has Lorentz type `(p, r, q, s)` if it is bounded as a map
from `L^{q, s}` to `L^{p, r}`. `HasLorentzType T p r q s μ ν c` means that
`T` has Lorentz type `(p, r, q, s)` w.r.t. measures `μ`, `ν` and constant `c`. -/
def HasLorentzType (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧
    eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ

end Defs

/-! ### Lemmas about `HasWeakType` -/

section HasWeakType

variable [TopologicalSpace ε₁] [ContinuousENorm ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {f₁ : α → ε₁}

lemma HasWeakType.memWLp (h : HasWeakType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemWLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasWeakType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasWeakType T p p' μ ν c) :
    HasWeakType (T · · |>.toReal) p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, wnorm_toReal_le.trans (h f hf).2 ⟩

lemma hasWeakType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
    HasWeakType (T · · |>.toReal) p p' μ ν c ↔ HasWeakType T p p' μ ν c := by
  refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
  obtain ⟨h1, h2⟩ := h f hf
  refine ⟨?_, by rwa [← wnorm_toReal_eq (hT f hf)]⟩
  rwa [← aestronglyMeasurable_ennreal_toReal_iff]
  refine .of_null <| measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [hT f hf] with x hx
  simp [hx]

lemma hasWeakType_iSup_of_monotone {f : ℕ → (α → ε₁) → (α' → ℝ≥0∞)} (hf : Monotone f)
    (hp' : p' ≠ 0) (hwtf : ∀ n, HasWeakType (f n) p p' μ ν c) :
    HasWeakType (fun u x => ⨆ n, f n u x) p p' μ ν c := by
  intro v mlpv
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    -- should StronglyMeasurable.iSup exist?
    apply AEMeasurable.iSup
    exact (hwtf · v mlpv |>.left.aemeasurable)
  · rw [wnorm_iSup_of_monotone hp' _ (hf.apply₂ v) _ (hwtf · v mlpv |>.left.aemeasurable)]
    exact iSup_le fun n => hwtf n v mlpv |>.right

-- lemma comp_left [MeasurableSpace ε₂] {ν' : Measure ε₂} {f : ε₂ → ε₃} (h : HasWeakType T p p' μ ν c)
--     (hf : MemLp f p' ν') :
--     HasWeakType (f ∘ T ·) p p' μ ν c := by
--   intro u hu
--   refine ⟨h u hu |>.1.comp_measurable hf.1, ?_⟩

end HasWeakType

/-! ### Lemmas about `HasBoundedWeakType` -/

section HasBoundedWeakType

variable [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ENorm ε₂]
    {f₁ : α → ε₁}

lemma HasBoundedWeakType.memWLp (h : HasBoundedWeakType T p p' μ ν c)
    (hf₁ : BoundedFiniteSupport f₁ μ) (hc : c < ⊤ := by finiteness) :
    MemWLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc (hf₁.memLp p).2⟩

lemma HasWeakType.hasBoundedWeakType (h : HasWeakType T p p' μ ν c) :
    HasBoundedWeakType T p p' μ ν c :=
  fun f hf ↦ h f (hf.memLp _)

end HasBoundedWeakType

/-! ### Lemmas about `HasStrongType` -/

section HasStrongType

variable [TopologicalSpace ε₁] [ContinuousENorm ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {f₁ : α → ε₁}

lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩

lemma HasStrongType.hasWeakType (hp' : 0 < p')
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
  refine .of_null <| measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [hT f hf] with x hx
  simp [hx]

lemma hasStrongType_iSup_of_monotone {f : ℕ → (α → ε₁) → (α' → ℝ≥0∞)} (hf : Monotone f)
    (hstf : ∀ n, HasStrongType (f n) p p' μ ν c) :
    HasStrongType (fun u x => ⨆ n, f n u x) p p' μ ν c := by
  intro v mlpv
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    -- should StronglyMeasurable.iSup exist?
    apply AEMeasurable.iSup
    exact (hstf · v mlpv |>.left.aemeasurable)
  · rw [eLpNorm_iSup']
    · exact iSup_le fun n => hstf n v mlpv |>.right
    · exact fun n => hstf n v mlpv |>.left.aemeasurable
    · apply ae_of_all
      intro a
      exact (hf.apply₂ _).apply₂ _

end HasStrongType

/-! ### Lemmas about `HasBoundedStrongType` -/

section HasBoundedStrongType

variable [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ContinuousENorm ε₂]
    {f₁ : α → ε₁}

lemma HasBoundedStrongType.memLp (h : HasBoundedStrongType T p p' μ ν c)
    (hf₁ : BoundedFiniteSupport f₁ μ) (hc : c < ⊤ := by finiteness) :
    MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc (hf₁.memLp _).2⟩

lemma HasStrongType.hasBoundedStrongType (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c :=
  fun f hf ↦ h f (hf.memLp _)

lemma HasBoundedStrongType.hasBoundedWeakType (hp' : 0 < p')
    (h : HasBoundedStrongType T p p' μ ν c) :
    HasBoundedWeakType T p p' μ ν c :=
  fun f hf ↦
    ⟨(h f hf).1, wnorm_le_eLpNorm (h f hf).1 hp' |>.trans (h f hf).2⟩

set_option backward.isDefEq.respectTransparency false in
lemma HasBoundedStrongType.const_smul {T : (α → ε₁) → α' → ℝ≥0∞}
    (h : HasBoundedStrongType T p p' μ ν c) (r : ℝ≥0) :
    HasBoundedStrongType (r • T) p p' μ ν (r • c) := by
  intro f hf
  rw [Pi.smul_apply, MeasureTheory.eLpNorm_const_smul' (ε' := ℝ≥0∞)]
  exact ⟨(h f hf).1.const_smul _, le_of_le_of_eq (mul_le_mul_right (h f hf).2 ‖r‖ₑ) (by simp; rfl)⟩

end HasBoundedStrongType

/-! ### Comparison with `HasLorentzType` -/

section HasLorentzType

variable [TopologicalSpace ε₁] [TopologicalSpace ε₂]

lemma hasStrongType_iff_hasLorentzType [ESeminormedAddMonoid ε₁] [ESeminormedAddMonoid ε₂]
  {T : (α → ε₁) → (α' → ε₂)} {c : ℝ≥0∞} :
    HasStrongType T p q μ ν c ↔ HasLorentzType T p p q q μ ν c := by
  unfold HasStrongType HasLorentzType
  constructor
  · intro h f hf
    have hf' := MemLorentz_iff_MemLp.mp hf
    have := h f hf'
    rwa [eLorentzNorm_eq_eLpNorm this.1, eLorentzNorm_eq_eLpNorm hf'.1]
  · intro h f hf
    have := h f (MemLorentz_iff_MemLp.mpr hf)
    rwa [← eLorentzNorm_eq_eLpNorm this.1, ← eLorentzNorm_eq_eLpNorm hf.1]

lemma hasWeakType_iff_hasLorentzType [ESeminormedAddMonoid ε₁] [ESeminormedAddMonoid ε₂]
  {T : (α → ε₁) → (α' → ε₂)} {c : ℝ≥0∞} :
    HasWeakType T p q μ ν c ↔ HasLorentzType T p p q ∞ μ ν c := by
  constructor
  · intro h f hf
    have hf' := MemLorentz_iff_MemLp.mp hf
    rw [eLorentzNorm_eq_eLpNorm hf'.1]
    exact h f hf'
  · intro h f hf
    rw [← eLorentzNorm_eq_eLpNorm hf.1]
    exact h f (MemLorentz_iff_MemLp.mpr hf)

end HasLorentzType

variable {f g : α → ε}

section

variable {ε ε' : Type*} [TopologicalSpace ε] [ENorm ε]
variable [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε'] [SMul ℝ≥0 ε']
  [ENormSMulClass ℝ≥0 ε']

variable [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [NormSMulClass 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [NormSMulClass 𝕜 E']

lemma HasStrongType.const_smul [ContinuousConstSMul ℝ≥0 ε']
    {T : (α → ε) → (α' → ε')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (k : ℝ≥0) :
    HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  refine fun f hf ↦
    ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_nnreal_smul_le.trans ?_⟩
  rw [mul_assoc]
  gcongr
  exact (h f hf).2

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
variable {𝕜 E' : Type*} [NormedRing 𝕜] [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E'] in
lemma HasStrongType.const_smul'
    {T : (α → ε) → (α' → E')} {c : ℝ≥0∞} (h : HasStrongType T p p' μ ν c) (k : 𝕜) :
    HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le.trans ?_⟩
  rw [mul_assoc]
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

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  [Module ℝ≥0 ε'] [ENormSMulClass ℝ≥0 ε'] in
lemma HasWeakType.const_smul [ContinuousConstSMul ℝ≥0 ε']
    {T : (α → ε) → (α' → ε')} (hp' : p' ≠ 0) {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (k : ℝ≥0) :
    HasWeakType (k • T) p p' μ ν (k * c) := by
  intro f hf
  refine ⟨(h f hf).1.const_smul k, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ k * wnorm (T f) p' ν := by simpa using wnorm_const_smul_le hp' (h f hf).1 _ (ε' := ε')
    _ ≤ k * (c * eLpNorm f p μ) := by
      gcongr
      apply (h f hf).2
    _ = (k * c) * eLpNorm f p μ := by rw [mul_assoc]

-- TODO: do we want to unify this lemma with its unprimed version, perhaps using an
-- `ENormedSemiring` class?
lemma HasWeakType.const_smul' [IsBoundedSMul 𝕜 E'] {T : (α → ε) → (α' → E')} (hp' : p' ≠ 0)
    {c : ℝ≥0∞} (h : HasWeakType T p p' μ ν c) (k : 𝕜) :
    HasWeakType (k • T) p p' μ ν (‖k‖ₑ * c) := by
  intro f hf
  refine ⟨aestronglyMeasurable_const.smul (h f hf).1, ?_⟩
  calc wnorm ((k • T) f) p' ν
    _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le' hp' (h f hf).1]
    _ ≤ ‖k‖ₑ * (c * eLpNorm f p μ) := by
      gcongr
      apply (h f hf).2
    _ = (‖k‖ₑ * c) * eLpNorm f p μ := by rw [mul_assoc]

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

end MeasureTheory
