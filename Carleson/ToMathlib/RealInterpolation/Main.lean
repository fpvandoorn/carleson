module

public import Carleson.ToMathlib.RealInterpolation.Minkowski

/-!
# The Marcinkiewisz real interpolation theorem

This file contains a proof of the Marcinkiewisz real interpolation theorem.
The proof roughly follows Folland, Real Analysis. Modern Techniques and Their Applications,
section 6.4, theorem 6.28, but a different truncation is used, and some estimates instead
follow the technique as e.g. described in [Duoandikoetxea, Fourier Analysis, 2000].

This file has the definitions for the main proof, and the final proof of the theorem.
A few other files contain the necessary pre-requisites:
- (in `InterpolateExponents.lean`) Convenience results for working with (interpolated) exponents
- (in `InterpolateExponents.lean`) Results about the particular choice of exponent
- (in `Misc.lean`) Interface for using cutoff functions
- (in `Misc.lean`) Results about the particular choice of scale
- (in `Misc.lean`) Some tools for measure theory computations
- (in `Misc.lean`) Results about truncations of a function
- (in `Misc.lean`) Measurability properties of truncations
- (in `Misc.lean`) Truncations and Lp spaces
- (in `Misc.lean`) Some results about the integrals of truncations
- (in `Minkowski.lean`) Minkowski's integral inequality
- (in `Minkowski.lean`) Apply Minkowski's integral inequality to truncations
- (in `Minkowski.lean`) Weaktype estimates applied to truncations

Upstreaming status: the result is highly desirable; the ideal proof strategy is not yet clear.
It may be nicer to generalise this to Lorentz spaces first, and then upstream the proof there.
(Useful ingredients for this proof also belong into mathlib.)
Prioritise other files first (e.g., about weak type or the prerequisites files).

-/

@[expose] public section

noncomputable section

open NNReal ENNReal MeasureTheory Set Pointwise

variable {α α' ε E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  [TopologicalSpace E] [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace E₃]
  [ESeminormedAddCommMonoid E]
  [ESeminormedAddCommMonoid E₁] [ESeminormedAddCommMonoid E₂] [ESeminormedAddCommMonoid E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₃] [BorelSpace E₃]
  {f : α → E₁} {t : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}

/-! # The real interpolation theorem

## Definitions -/
namespace MeasureTheory

variable {ε₁ ε₂ : Type*} [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ESeminormedAddMonoid ε₂]

def Subadditive [ENorm ε] (T : (α → ε₁) → α' → ε) : Prop :=
  ∃ A ≠ ⊤, ∀ (f g : α → ε₁) (x : α'), ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

def Subadditive_trunc [ENorm ε] (T : (α → ε₁) → α' → ε) (A : ℝ≥0∞) (f : α → ε₁) (ν : Measure α') :
    Prop :=
  ∀ a : ℝ≥0∞, 0 < a → ∀ᵐ y ∂ν,
  ‖T (trunc f a + truncCompl f a) y‖ₑ ≤ A * (‖T (trunc f a) y‖ₑ + ‖T (truncCompl f a) y‖ₑ)

/-- The operator is subadditive on functions satisfying `P` with constant `A`
(this is almost vacuous if `A = ⊤`). -/
def AESubadditiveOn [ENorm ε] (T : (α → ε₁) → α' → ε) (P : (α → ε₁) → Prop) (A : ℝ≥0∞)
    (ν : Measure α') : Prop :=
  ∀ (f g : α → ε₁), P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

namespace AESubadditiveOn

variable [TopologicalSpace ε] [ESeminormedAddMonoid ε] {ν : Measure α'}
  {u : α → ε₁} {T : (α → ε₁) → α' → ε₂}

lemma antitone {T : (α → ε₁) → α' → ε} {P P' : (α → ε₁) → Prop}
    (h : ∀ {u : α → ε₁}, P u → P' u) {A : ℝ≥0∞} (sa : AESubadditiveOn T P' A ν) :
    AESubadditiveOn T P A ν :=
  fun f g hf hg ↦ sa f g (h hf) (h hg)

lemma zero {P : (α → ε₁) → Prop} (hP : ∀ {f g : α → ε₁}, P f → P g → P (f + g))
    (A : ℝ≥0∞) (h : ∀ u, P u → T u =ᵐ[ν] 0) : AESubadditiveOn T P A ν := by
  intro f g hf hg
  filter_upwards [h f hf, h g hg, h (f + g) (hP hf hg)] with x hx1 hx2 hx3
  simp [hx1, hx2, hx3]

lemma forall_le {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → ε₁) → α' → ε}
    {P : (α → ε₁) → Prop} {A : ℝ≥0∞}
    (h : ∀ i ∈ 𝓑, AESubadditiveOn (T i) P A ν)
    {f g : α → ε₁} (hf : P f) (hg : P g) :
    ∀ᵐ x ∂ν, ∀ i ∈ 𝓑, ‖T i (f + g) x‖ₑ ≤ A * (‖T i f x‖ₑ + ‖T i g x‖ₑ) :=
  eventually_countable_ball h𝓑 |>.mpr fun i hi ↦ h i hi f g hf hg

lemma biSup {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → ε₁) → α' → ℝ≥0∞}
    {P : (α → ε₁) → Prop} (hT : ∀ (u : α → ε₁), P u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (hP : ∀ {f g : α → ε₁}, P f → P g → P (f + g))
    {A : ℝ≥0∞} (h : ∀ i ∈ 𝓑, AESubadditiveOn (T i) P A ν) :
    AESubadditiveOn (fun u x ↦ ⨆ i ∈ 𝓑, T i u x) P A ν := by
  have hT' : ∀ i ∈ 𝓑, ∀ (u : α → ε₁), P u → ∀ᵐ x ∂ν, T i u x ≠ ∞ := by
    intro i hi f hf
    filter_upwards [hT f hf] with x hx
    rw [ne_eq, eq_top_iff] at hx ⊢
    exact fun h ↦ hx <| h.trans (le_biSup (fun i ↦ T i f x) hi)
  -- rcases lt_or_le A 0 with A0 | A0
  -- · refine AESubadditiveOn.zero hP A (fun f hf ↦ ?_)
  --   have h (i : ι) (hi : i ∈ 𝓑) := (h i hi).neg _ A0
  --   simp_rw [Set.forall_in_swap, imp.swap, ← imp_forall_iff] at h hT'
  --   filter_upwards [(ae_ball_iff h𝓑).mpr (h f hf), (ae_ball_iff h𝓑).mpr (hT' f hf)] with x hx hx'
  --   simp only [Pi.zero_apply, toReal_eq_zero_iff, ENNReal.iSup_eq_zero]
  --   refine Or.inl fun i hi ↦ ?_
  --   have := (ENNReal.toReal_eq_zero_iff _).mp (hx i hi)
  --   tauto
  intro f g hf hg
  simp_rw [AESubadditiveOn] at h
  conv at hT' => enter [i]; rw [forall_comm]
  rw [forall_comm] at hT'; rw [forall₂_comm] at h
  simp_rw [imp.swap, ← imp_forall_iff] at h hT'
  specialize h f hf g hg
  simp_rw [enorm_eq_self] at h ⊢
  filter_upwards [hT f hf, hT g hg, (ae_ball_iff h𝓑).mpr h, (ae_ball_iff h𝓑).mpr (hT' f hf),
    (ae_ball_iff h𝓑).mpr (hT' g hg), (ae_ball_iff h𝓑).mpr (hT' (f + g) (hP hf hg))] with x hTfx hTgx hx hT'fx hT'gx hT'fgx
  simp_rw [iSup_le_iff]
  intro i hi
  specialize hx i hi
  apply hx.trans
  gcongr <;> apply le_biSup _ hi

lemma indicator {T : (α → ε₁) → α' → ε} {P : (α → ε₁) → Prop} {A : ℝ≥0∞}
    (sa : AESubadditiveOn T P A ν) (S : Set α') :
    AESubadditiveOn (fun u x ↦ (S.indicator (fun y ↦ T u y) x)) P A ν := by
  intro f g hf hg
  filter_upwards [sa f g hf hg] with x hx
  by_cases h : x ∈ S <;> simp [hx, h]

-- If `T` is constant in the second argument (but not necessarily the first) and satisfies
-- a subadditivity criterion, then `AESubadditiveOn T P 1`
lemma const (T : (α → ε₁) → ε) (P : (α → ε₁) → Prop)
    (h_add : ∀ {f g}, P f → P g → ‖T (f + g)‖ₑ ≤ ‖T f‖ₑ + ‖T g‖ₑ) :
    AESubadditiveOn (fun u (_ : α') ↦ T u) P 1 ν :=
  fun f g hf hg ↦ ae_of_all _ fun _ ↦ (by simpa using h_add hf hg)

end AESubadditiveOn

--[NormedSpace ℝ E₁] [NormedSpace ℝ E₂]
variable [TopologicalSpace ε] [ENormedSpace ε]

variable {ε₁ ε₂ : Type*} [TopologicalSpace ε₁] [ENormedSpace ε₁]

/-- The operator is sublinear on functions satisfying `P` with constant `A`. -/
def AESublinearOn (T : (α → ε₁) → α' → ε) (P : (α → ε₁) → Prop) (A : ℝ≥0∞) (ν : Measure α') :
    Prop :=
  AESubadditiveOn T P A ν ∧ ∀ (f : α → ε₁) (c : ℝ≥0), P f → T (c • f) =ᵐ[ν] c • T f

namespace AESublinearOn

variable {ν : Measure α'}

lemma antitone {T : (α → ε₁) → α' → ε} {P P' : (α → ε₁) → Prop}
    (h : ∀ {u : α → ε₁}, P u → P' u) {A : ℝ≥0∞} (sl : AESublinearOn T P' A ν) :
    AESublinearOn T P A ν :=
  ⟨sl.1.antitone (fun hu ↦ h hu), fun u c hu ↦ sl.2 u c (h hu)⟩

lemma biSup {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → ε₁) → α' → ℝ≥0∞}
    {P : (α → ε₁) → Prop} (hT : ∀ (u : α → ε₁), P u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (h_add : ∀ {f g : α → ε₁}, P f → P g → P (f + g))
    (h_smul : ∀ {f : α → ε₁} {c : ℝ≥0}, P f → P (c • f))
    {A : ℝ≥0∞} (h : ∀ i ∈ 𝓑, AESublinearOn (T i) P A ν) :
    AESublinearOn (fun u x ↦ ⨆ i ∈ 𝓑, T i u x) P A ν := by
  have hT' : ∀ i ∈ 𝓑, ∀ (u : α → ε₁), P u → ∀ᵐ x ∂ν, T i u x ≠ ∞ := by
    intro i hi f hf
    filter_upwards [hT f hf] with x hx
    rw [ne_eq, eq_top_iff] at hx ⊢
    exact fun h ↦ hx <| h.trans (le_biSup (fun i ↦ T i f x) hi)
  refine ⟨AESubadditiveOn.biSup h𝓑 hT h_add (fun i hi ↦ (h i hi).1), fun f c hf ↦ ?_⟩
  conv at hT' => enter [i]; rw [forall_comm]
  rw [forall_comm] at hT'; simp_rw [imp.swap, ← imp_forall_iff] at hT'
  filter_upwards [(ae_ball_iff h𝓑).mpr (fun i hi ↦ (h i hi).2 f c hf),
    (ae_ball_iff h𝓑).mpr (hT' f hf), (ae_ball_iff h𝓑).mpr (hT' (c • f) (h_smul hf))] with x hx hT'fx hT'cfx
  simp_rw [Pi.smul_apply, ENNReal.smul_iSup]
  refine biSup_congr (fun i hi ↦ ?_)
  specialize hx i hi
  simpa only [Pi.smul_apply, smul_eq_mul] using hx

lemma biSup2 {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → ε₁) → α' → ℝ≥0∞}
    {P : (α → ε₁) → Prop} {Q : (α → ε₁) → Prop}
    (hPT : ∀ (u : α → ε₁), P u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (hQT : ∀ (u : α → ε₁), Q u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (P0 : P 0)
    (Q0 : Q 0)
    (haP : ∀ {f g : α → ε₁}, P f → P g → P (f + g))
    (haQ : ∀ {f g : α → ε₁}, Q f → Q g → Q (f + g))
    (hsP : ∀ {f : α → ε₁} {c : ℝ≥0}, P f → P (c • f))
    (hsQ : ∀ {f : α → ε₁} {c : ℝ≥0}, Q f → Q (c • f))
    {A : ℝ≥0} -- todo, here and elsewhere: probably better to have {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hAP : ∀ i ∈ 𝓑,
      AESublinearOn (T i) (fun g ↦ g ∈ {f | P f} + {f | Q f}) A ν) :
    AESublinearOn (fun u x ↦ ⨆ i ∈ 𝓑, T i u x) (fun f ↦ P f ∨ Q f) A ν := by
  set R := fun g ↦ g ∈ {f | P f} + {f | Q f}
  have hPR : ∀ {f}, P f → R f := fun hu ↦ ⟨_, hu, 0, Q0, by simp⟩
  have hQR : ∀ {f}, Q f → R f := fun hu ↦ ⟨0, P0, _, hu, by simp⟩
  apply AESublinearOn.antitone (P' := R) (fun hu ↦ hu.elim hPR hQR)
  refine AESublinearOn.biSup (P := R) h𝓑 ?_ ?_ ?_ hAP
  · rintro _ ⟨f, hf, g, hg, rfl⟩
    filter_upwards [hPT f hf, hQT g hg,
      AESubadditiveOn.forall_le h𝓑 (fun i hi ↦ hAP i hi |>.1) (hPR hf) (hQR hg)] with x hfx hgx hTx
    simp_rw [← lt_top_iff_ne_top] at hfx hgx ⊢
    simp_rw [enorm_eq_self] at hTx
    calc
      _ ≤ ⨆ i ∈ 𝓑, A * (T i f x + T i g x) := by gcongr; exact hTx _ ‹_›
      _ ≤ A * ((⨆ i ∈ 𝓑, T i f x) + (⨆ i ∈ 𝓑, T i g x)) := by
          simp_rw [← ENNReal.mul_iSup]
          gcongr
          -- todo: make lemma
          simp_rw [iSup_le_iff]
          intro i hi
          gcongr <;> apply le_biSup _ hi
      _ < ⊤ := mul_lt_top coe_lt_top <| add_lt_top.mpr ⟨hfx, hgx⟩
  · rintro _ _ ⟨f₁, hf₁, g₁, hg₁, rfl⟩ ⟨f₂, hf₂, g₂, hg₂, rfl⟩
    exact ⟨f₁ + f₂, haP hf₁ hf₂, g₁ + g₂, haQ hg₁ hg₂, by dsimp only; abel_nf⟩
  · rintro _ c ⟨f, hf, g, hg, rfl⟩
    exact ⟨c • f, hsP hf, c • g, hsQ hg, by module⟩

lemma indicator {T : (α → ε₁) → α' → ε} {P : (α → ε₁) → Prop} {A : ℝ≥0∞} (S : Set α')
    (sl : AESublinearOn T P A ν) :
    AESublinearOn (fun u x ↦ (S.indicator (fun y ↦ T u y) x)) P A ν := by
  refine ⟨AESubadditiveOn.indicator sl.1 S, fun f c hf ↦ ?_⟩
  filter_upwards [sl.2 f c hf] with x hx
  by_cases h : x ∈ S <;> simp [h, hx]

-- If `T` is constant in the second argument (but not necessarily the first) and satisfies
-- certain requirements, then `AESublinearOn T P 1`
lemma const (T : (α → ε₁) → ε) (P : (α → ε₁) → Prop)
    (h_add : ∀ {f g}, P f → P g → ‖T (f + g)‖ₑ ≤ ‖T f‖ₑ + ‖T g‖ₑ)
    (h_smul : ∀ f {c : ℝ≥0}, P f → T (c • f) = c • T f) :
    AESublinearOn (fun u (_ : α') ↦ T u) P 1 ν := by
  refine ⟨AESubadditiveOn.const T P h_add, fun f c hf ↦ ae_of_all _ fun _ ↦ ?_⟩
  simpa using h_smul f hf

lemma toReal {T : (α → ε₁) → α' → ℝ≥0∞}
    {P : (α → ε₁) → Prop}
    {A : ℝ≥0∞} (h : AESublinearOn T P A ν)
    (hP : ∀ (u : α → ε₁), P u → ∀ᵐ x ∂ν, T u x ≠ ∞) :
    AESublinearOn (T · · |>.toReal) P A ν := by
  refine ⟨fun f g hf hg ↦ ?_, fun f c hf ↦ ?_⟩
  · filter_upwards [h.1 f g hf hg, hP f hf, hP g hg] with x hx hfx hgx
    simp only [ne_eq, hfx, not_false_eq_true, enorm_toReal, hgx] at hx ⊢
    exact enorm_toReal_le.trans hx
  · filter_upwards [h.2 f c hf, hP f hf] with x hx hfx
    rw [hx, Pi.smul_apply, toReal_smul]
    rfl

end AESublinearOn

end MeasureTheory

end


noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsChoiceExponent
    ComputationsInterpolatedExponents ChoiceScale

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {f : α → E₁} {t : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}

/-! ## Proof of the real interpolation theorem

    In this section the estimates are combined to finally give a proof of the
    real interpolation theorem.
-/
namespace MeasureTheory

variable {ε₁ ε₂ : Type*} [TopologicalSpace ε₁] [ESeminormedAddMonoid ε₁] [TopologicalSpace ε₂] [ESeminormedAddMonoid ε₂]

/-- Proposition that expresses that the map `T` map between function spaces preserves
    AE strong measurability on L^p. -/
def PreservesAEStrongMeasurability (T : (α → ε₁) → α' → ε₂) (p : ℝ≥0∞) : Prop :=
    ∀ ⦃f : α → ε₁⦄, MemLp f p μ → AEStronglyMeasurable (T f) ν

lemma estimate_distribution_Subadditive_trunc {f : α → ε₁} {T : (α → ε₁) → (α' → ε₂)}
    {a : ℝ≥0∞} (ha : 0 < a) {A : ℝ≥0∞} (h : Subadditive_trunc T A f ν) :
    distribution (T f) (2 * A * t) ν ≤
    distribution (T (trunc f a)) t ν +
    distribution (T (truncCompl f a)) t ν := by
  nth_rw 2 [mul_comm]
  rw [mul_assoc, two_mul]
  apply distribution_add_le'
  nth_rw 1 [← trunc_add_truncCompl (f := f) (t := a)]
  exact h a ha

lemma rewrite_norm_func {q : ℝ} {g : α' → E}
    [TopologicalSpace E] [ESeminormedAddCommMonoid E] (hq : 0 < q) {A : ℝ≥0} (hA : 0 < A)
    (hg : AEStronglyMeasurable g ν) :
    ∫⁻ x, ‖g x‖ₑ ^ q ∂ν =
    ENNReal.ofReal ((2 * A) ^ q * q) * ∫⁻ s,
    distribution g ((ENNReal.ofReal (2 * A) * s))  ν * s ^ (q - 1) := by
  calc
  _ = ENNReal.ofReal ((2 * A) ^ q * q) * ∫⁻ s in Ioi (0 : ℝ),
      distribution g ((ENNReal.ofReal (2 * A * s)))  ν * ENNReal.ofReal (s ^ (q - 1)) := by
    have : 0 < (A : ℝ) := hA
    rw [lintegral_norm_pow_eq_distribution hg (by linarith)]
    nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := (2 * A)) (by linarith)]
    rw [← lintegral_const_mul' _ _ (by finiteness), ← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (zero_lt_t : 0 < t)
    nth_rw 12 [mul_comm]
    rw [Real.mul_rpow, ← mul_assoc, ← ofReal_mul', ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← ofReal_mul']
        <;> try positivity
    congr 3
    rw [mul_assoc, mul_comm q, ← mul_assoc]
    congr 1
    rw [abs_of_nonneg] <;> try positivity
    nth_rw 1 [← Real.rpow_one (2 * A), ← Real.rpow_add (by linarith), add_sub_cancel]
  _ = _ := by
    congr 1
    rw [lintegral_ennreal_eq_lintegral_Ioi_ofReal]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    rw [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_mul (by positivity)]

lemma estimate_norm_rpow_range_operator {q : ℝ} {f : α → E₁}
    [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] [TopologicalSpace E₂] [ESeminormedAddCommMonoid E₂]
    (hq : 0 < q) (tc : StrictRangeToneCouple) {A : ℝ≥0} (hA : 0 < A)
    (ht : Subadditive_trunc T A f ν) (hTf : AEStronglyMeasurable (T f) ν) :
  ∫⁻ x : α', ‖T f x‖ₑ ^ q ∂ν ≤
  ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s, distribution (T (trunc f (tc.ton s))) s ν * s^(q - 1) +
  distribution (T (truncCompl f (tc.ton s))) s ν * s ^ (q - 1) := by
  rw [rewrite_norm_func hq hA hTf]
  refine mul_le_mul' (le_refl _) (lintegral_mono_ae ?_)
  filter_upwards [ae_in_Ioo_zero_top] with a ha
  rw [ENNReal.ofReal_mul (by simp), ← add_mul]
  gcongr ?_ * _
  convert estimate_distribution_Subadditive_trunc (tc.ran_ton a ha).1 ht <;> simp

-- TODO: the infrastructure can perhaps be improved here
@[measurability, fun_prop]
theorem ton_measurable_eLpNorm_trunc [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (tc : ToneCouple) :
    Measurable (fun x ↦ eLpNorm (trunc f (tc.ton x)) p₁ μ) := by
  change Measurable ((fun t : ℝ≥0∞ ↦ eLpNorm (trunc f t) p₁ μ) ∘ (tc.ton))
  have tone := tc.ton_is_ton
  split_ifs at tone
  · exact (eLpNorm_trunc_mono.comp tone.monotone).measurable
  · exact (eLpNorm_trunc_mono.comp_antitone tone.antitone).measurable

lemma estimate_norm_rpow_range_operator'
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hp₁p : p < p₁) (hp₀p : p₀ < p)
    (tc : StrictRangeToneCouple)
    (hq₀' : q₀ = ⊤ → ∀ s > 0, distribution (T (truncCompl f (tc.ton s))) s ν = 0)
    (hq₁' : q₁ = ⊤ → ∀ s > 0, distribution (T (trunc f (tc.ton s))) s ν = 0)
    (hf : MemLp f p μ) (hT₁ : HasWeakType T p₁ q₁ μ ν C₁) (hT₀ : HasWeakType T p₀ q₀ μ ν C₀) :
    ∫⁻ s : ℝ≥0∞, distribution (T (trunc f (tc.ton s))) s ν *
    s ^ (q.toReal - 1) +
    distribution (T (truncCompl f (tc.ton s))) s ν *
    s ^ (q.toReal - 1) ≤
    (if q₁ < ⊤ then 1 else 0) * (C₁ ^ q₁.toReal * (∫⁻ s : ℝ≥0∞,
        eLpNorm (trunc f (tc.ton s)) p₁ μ ^ q₁.toReal *
        s ^ (q.toReal - q₁.toReal - 1))) +
    (if q₀ < ⊤ then 1 else 0) * (C₀ ^ q₀.toReal * ∫⁻ s : ℝ≥0∞,
        eLpNorm (truncCompl f (tc.ton s)) (p₀) μ ^ q₀.toReal *
        s ^ (q.toReal - q₀.toReal - 1)) := by
  have : ∀ q' q : ℝ, -q' + (q - 1) = q - q' - 1 := by intro q' q; group
  repeat rw [← this]
  have := hp₁p.le
  have := hp₀p.le
  have := hp₁p.ne_top
  have p_pos : 0 < p := lt_trans hp₀ hp₀p
  repeat rw [lintegral_rw₂ (Filter.EventuallyEq.refl _ _) power_aux_3]
  nth_rw 2 [← lintegral_const_mul' _ _ (by finiteness)]
  nth_rw 1 [← lintegral_const_mul' _ _ (by finiteness)]
  simp_rw [← mul_assoc]
  split_ifs with is_q₁top is_q₀top
  · rw [one_mul, one_mul, ← lintegral_add_left']
    · apply lintegral_mono_ae
      filter_upwards [ae_in_Ioo_zero_top] with s ⟨s_pos, s_lt_top⟩
      gcongr
      · have : tc.ton s ≠ ⊤ := (tc.ran_ton s ⟨s_pos, s_lt_top⟩).2.ne
        apply weaktype_estimate_trunc p_pos hq₁ _ hp₁p.le <;> assumption
      · have : 0 < tc.ton s := (tc.ran_ton s ⟨s_pos, s_lt_top⟩).1
        apply weaktype_estimate_truncCompl (p₀ := p₀) hp₀ <;> assumption
    · fun_prop
  · rw [one_mul, zero_mul, add_zero]
    apply lintegral_mono_ae
    filter_upwards [ae_in_Ioo_zero_top] with s ⟨s_pos, s_lt_top⟩
    have : q₀ = ⊤ := not_lt_top.mp is_q₀top
    rw [hq₀' this s s_pos, zero_mul, add_zero]
    gcongr
    have : tc.ton s ≠ ⊤ := (tc.ran_ton s ⟨s_pos, s_lt_top⟩).2.ne
    apply weaktype_estimate_trunc p_pos <;> assumption
  · rw [one_mul, zero_mul, zero_add]
    apply lintegral_mono_ae
    filter_upwards [ae_in_Ioo_zero_top] with s ⟨s_pos, s_lt_top⟩
    have : q₁ = ⊤ := not_lt_top.mp is_q₁top
    rw [hq₁' this s s_pos, zero_mul, zero_add]
    have : 0 < tc.ton s := (tc.ran_ton s ⟨s_pos, s_lt_top⟩).1
    gcongr
    apply weaktype_estimate_truncCompl (p₀ := p₀) _ hp₁p.ne_top <;> assumption
  · simp only [zero_mul, add_zero, nonpos_iff_eq_zero]
    have : ∫⁻ _ : ℝ≥0∞, 0 = 0 := lintegral_zero
    rw [← this]
    apply lintegral_congr_ae
    filter_upwards [ae_in_Ioo_zero_top] with s ⟨s_pos, s_lt_top⟩
    have is_q₀top : ¬ q₀ < ⊤ := by assumption
    rw [hq₀' (not_lt_top.mp is_q₀top) s s_pos, hq₁' (not_lt_top.mp is_q₁top) s s_pos, zero_mul, add_zero]

lemma simplify_factor_rw_aux₀ (a b c d e f : ℝ≥0∞) :
    a * b * c * d * e * f = a * c * e * (b * d * f) := by ring
lemma simplify_factor_rw_aux₁ (a b c d e f : ℝ≥0∞) :
    a * b * c * d * e * f = c * (a * e) * (b * f * d) := by ring_nf

lemma simplify_factor₀ {D : ℝ≥0∞}
    [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (hq₀' : q₀ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    (ht : t ∈ Ioo 0 1)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    C₀ ^ q₀.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
    (D ^ (q.toReal - q₀.toReal)) =
    C₀ ^ ((1 - t).toReal * q.toReal) * C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₀pos : 0 < p₀ := hp₀.1
  have q₀pos : 0 < q₀ := lt_of_lt_of_le hp₀.1 hp₀.2
  have p₁pos : 0 < p₁ := hp₁.1
  have q₁pos : 0 < q₁ := lt_of_lt_of_le hp₁.1 hp₁.2
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀' hp₀.2
  have hp' : p ∈ Ioo 0 ⊤ := interp_exp_in_Ioo_zero_top ht p₀pos p₁pos (by left; exact p₀ne_top) hp
  have p_toReal_pos : 0 < p.toReal := toReal_pos_of_Ioo hp'
  rw [hD]
  unfold d
  nth_rw 2 [div_eq_mul_inv]
  rw [ENNReal.mul_inv]
  · repeat rw [ENNReal.mul_rpow_of_ne_zero _ _ (q.toReal - q₀.toReal)]
    · rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
      repeat rw [← ENNReal.rpow_mul]
      repeat rw [← mul_assoc]
      rw [simplify_factor_rw_aux₀ (a := C₀ ^ q₀.toReal)]
      repeat rw [← ENNReal.rpow_add] <;> try positivity
      · congr 1
        · congr 1
          · rw [eq_exponents₀] <;> try assumption
          · rw [neg_mul, eq_exponents₁ (t := t)] <;> try assumption
            ring_nf
        · congr 1
          rw [mul_assoc, ← mul_add, eq_exponents₂ (t := t)] <;> try assumption
          rw [mul_assoc, mul_assoc, ← mul_add, neg_mul, eq_exponents₃ (t := t)] <;> try assumption
          simp only [neg_mul, neg_neg]
          rw [← mul_assoc, ← add_mul, ← preservation_interpolation ht hp₀.1 hp₁.1 hp, toReal_inv]
          field_simp
      · exact ne_zero_of_Ioo hF
      · exact ne_top_of_Ioo hF
      · exact ne_zero_of_Ioo hF
      · exact ne_top_of_Ioo hF
      · exact coe_ne_top
    · exact ENNReal.inv_ne_zero.mpr (d_ne_top_aux₁ hC₁)
    · exact ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF)
    · exact d_ne_zero_aux₁ hC₀
    · exact d_ne_zero_aux₀ hF
    · exact d_ne_zero_aux₂ hC₀ hF
    · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₁ hC₁))
        (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF))
  · exact Or.inr (d_ne_top_aux₂ hF)
  · exact Or.inr (d_ne_zero_aux₀ hF)

lemma simplify_factor₁ {D : ℝ≥0∞}
    [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (hq₁' : q₁ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    (ht : t ∈ Ioo 0 1)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    C₁ ^ q₁.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
    (D ^ (q.toReal - q₁.toReal)) =
    C₀ ^ ((1 - t).toReal * q.toReal) * C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₀pos : 0 < p₀ := hp₀.1
  have q₀pos : 0 < q₀ := lt_of_lt_of_le hp₀.1 hp₀.2
  have p₁pos : 0 < p₁ := hp₁.1
  have q₁pos : 0 < q₁ := lt_of_lt_of_le hp₁.1 hp₁.2
  have p₁ne_top : p₁ ≠ ⊤ := ne_top_of_le_ne_top hq₁' hp₁.2
  have hp' : p ∈ Ioo 0 ⊤ := interp_exp_in_Ioo_zero_top ht p₀pos p₁pos
    (Decidable.not_or_of_imp fun _ ↦ p₁ne_top) hp
  have p_toReal_pos : 0 < p.toReal := toReal_pos_of_Ioo hp'
  rw [hD]
  unfold d
  nth_rw 2 [div_eq_mul_inv]
  rw [ENNReal.mul_inv]
  · repeat rw [ENNReal.mul_rpow_of_ne_zero _ _ (q.toReal - q₁.toReal)]
    · rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
      repeat rw [← ENNReal.rpow_mul]
      repeat rw [← mul_assoc]
      rw [simplify_factor_rw_aux₁ (a := C₁ ^ q₁.toReal)]
      repeat rw [← ENNReal.rpow_add]
      · rw [neg_mul]
        congr 3
        · rw [eq_exponents₆] <;> try assumption
        · rw [eq_exponents₅] <;> try assumption
        · rw [mul_assoc, mul_assoc, ← mul_add, eq_exponents₈, neg_mul,
            eq_exponents₇ (ht := ht)] <;> try assumption
          rw [← mul_add, ← add_mul, add_comm, ← preservation_interpolation ht hp₀.1 hp₁.1 hp,
            toReal_inv]
          field_simp
      · exact ne_zero_of_Ioo hF
      · exact ne_top_of_Ioo hF
      · exact ne_zero_of_Ioo hF
      · exact ne_top_of_Ioo hF
      · exact (ENNReal.coe_pos.mpr hC₁).ne'
      · exact coe_ne_top
    · exact ENNReal.inv_ne_zero.mpr (rpow_ne_top' ((ENNReal.coe_pos.mpr hC₁).ne') coe_ne_top)
    · exact ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF)
    · exact d_ne_zero_aux₁ hC₀
    · exact d_ne_zero_aux₀ hF
    · exact d_ne_zero_aux₂ hC₀ hF
    · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₁ hC₁))
        (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF))
  · exact Or.inr (d_ne_top_aux₂ hF)
  · exact Or.inr (d_ne_zero_aux₀ hF)


def finite_spanning_sets_from_lintegrable {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hg_int : ∫⁻ x, g x ∂μ < ⊤) : Measure.FiniteSpanningSetsIn
      (μ.restrict g.support) Set.univ where
  set := fun n ↦ if n = 0 then {x | g x = 0} else { x | 1 / (n + 1) ≤ g x }
  set_mem := fun _ ↦ trivial
  finite := by
    intro n
    split_ifs
    · rw [Measure.restrict_apply₀']
      · rw [measure_mono_null _ measure_empty]
        · exact zero_lt_top
        · intro x; simp
      · exact (aestronglyMeasurable_iff_aemeasurable.mpr hg).nullMeasurableSet_support
    · have one_div_ne_zero : (1 : ℝ≥0∞) / (n + 1) ≠ 0 := by
        apply ne_of_gt
        rw [one_div]
        exact ENNReal.inv_pos.mpr (by finiteness)
      calc
      _ ≤ (∫⁻ x : α in g.support, g x ∂μ) / (1 / (n + 1)) :=
        meas_ge_le_lintegral_div hg.restrict one_div_ne_zero (by finiteness)
      _ ≤ (∫⁻ x : α, g x ∂μ) / (1 / (n + 1)) := by
        gcongr
        exact Measure.restrict_le_self
      _ < ⊤ := by finiteness
  spanning := by
    ext x
    constructor
    · simp
    · intro _
      rcases (eq_zero_or_pos (g x)) with gx_zero | gx_pos
      · simp only [mem_iUnion]; use 0; simpa
      · simp only [mem_iUnion]
        have : ∃ n : ℕ, (g x)⁻¹ < n := ENNReal.exists_nat_gt (inv_lt_top.mpr gx_pos).ne
        obtain ⟨n, wn⟩ := ENNReal.exists_nat_gt (inv_lt_top.mpr gx_pos).ne
        use n
        simp only [one_div]
        split_ifs with is_n_zero
        · simp [is_n_zero] at wn
        · simp only [mem_setOf_eq]
          refine inv_le_iff_inv_le.mpr ?_
          apply le_of_lt
          refine lt_trans wn ?_
          nth_rw 1 [← add_zero (n : ℝ≥0∞)]
          exact (ENNReal.add_lt_add_iff_left coe_ne_top).mpr zero_lt_one

lemma support_sigma_finite_of_lintegrable {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hg_int : ∫⁻ x, g x ∂μ < ⊤) :
    SigmaFinite (μ.restrict g.support) where
  out' := by
    apply Exists.nonempty
    use (finite_spanning_sets_from_lintegrable hg hg_int)

lemma support_sigma_finite_from_MemLp
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
    (hf : MemLp f p μ) (hp : p ≠ ⊤) (hp' : p ≠ 0) :
    SigmaFinite (μ.restrict f.support) := by
  let g : α → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ p.toReal
  have : g.support = f.support := by
    unfold Function.support g
    ext x
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, enorm_eq_zero, not_or, not_and, not_lt,
      toReal_nonneg, implies_true, and_true, mem_setOf_eq]
    constructor
    · contrapose
      simp [Classical.not_imp, not_le, toReal_pos hp' hp]
    · intro h h'
      contradiction
  rw [← this]
  apply support_sigma_finite_of_lintegrable
  · exact hf.1.enorm.pow_const _
  · unfold g
    have obs := hf.2
    unfold eLpNorm eLpNorm' at obs
    split_ifs at obs
    · contradiction
    · exact lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top (toReal_pos hp' hp) obs

-- lemma support_sfinite_from_MemLp
--     [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁] (hf : MemLp f p μ)
--     (hp : p ≠ ⊤) (hp' : p ≠ 0) :
--     SFinite (μ.restrict f.support) := by
--   have : SigmaFinite (μ.restrict f.support) := support_sigma_finite_from_MemLp hf hp hp'
--   exact instSFiniteOfSigmaFinite

lemma combine_estimates₀ {A : ℝ≥0} (hA : 0 < A)
  [TopologicalSpace E₁] [ENormedAddCommMonoid E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [TopologicalSpace.PseudoMetrizableSpace E₁]
  [TopologicalSpace E₂] [ENormedAddCommMonoid E₂] --[BorelSpace E₂]
  {spf : ScaledPowerFunction}
  (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
  (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁)
  (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
  (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
  (hf : MemLp f p μ) (hT : Subadditive_trunc T A f ν)
  (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
  (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
  (hspf : spf = spf_ch (toReal_mem_Ioo ht) hq₀q₁ hp₀.1 (lt_of_lt_of_le hp₀.1 hp₀.2) hp₁.1
      (lt_of_lt_of_le hp₁.1 hp₁.2) hp₀p₁.ne hC₀ hC₁ hF)
  (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
  (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
  (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ)) :
    ∫⁻ x , ‖T f x‖ₑ ^ q.toReal ∂ν ≤
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) *
    C₀ ^ ((1 - t).toReal * q.toReal) * C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have one_le_p₀ := hp₀.1
  have one_le_p1 := hp₁.1
  have p₀pos : 0 < p₀ := hp₀.1
  have q₀pos : 0 < q₀ := lt_of_lt_of_le hp₀.1 hp₀.2
  have p₁pos : 0 < p₁ := hp₁.1
  have q₁pos : 0 < q₁ := lt_of_lt_of_le hp₁.1 hp₁.2
  have p_pos : 0 < p := interpolated_pos' one_le_p₀ one_le_p1 (ne_top_of_Ioo ht) hp
  have : SigmaFinite (μ.restrict f.support) :=
    support_sigma_finite_from_MemLp hf (interp_exp_ne_top hp₀p₁.ne ht hp) p_pos.ne'
  let tc := spf_to_tc spf
  calc
  ∫⁻ x , ‖T f x‖ₑ ^ q.toReal ∂ν
    ≤ ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * ∫⁻ s,
      distribution (T (trunc f (tc.ton s))) s ν *
      s^(q.toReal - 1) +
      distribution (T (truncCompl f (tc.ton s))) s ν *
      s^(q.toReal - 1) :=
    estimate_norm_rpow_range_operator
      (interp_exp_toReal_pos ht q₀pos q₁pos hq₀q₁ hq) _ hA hT (h₂T hf)
  _ ≤ ENNReal.ofReal ((2 * A)^q.toReal * q.toReal) *
      ((if q₁ < ⊤ then 1 else 0) * (C₁ ^ q₁.toReal * (∫⁻ s,
        eLpNorm (trunc f (tc.ton s)) p₁ μ ^ q₁.toReal *
        s ^ (q.toReal - q₁.toReal - 1))) +
      (if q₀ < ⊤ then 1 else 0) * (C₀ ^ q₀.toReal * ∫⁻ s,
        eLpNorm (truncCompl f (tc.ton s)) p₀ μ ^ q₀.toReal *
        s ^ (q.toReal - q₀.toReal - 1))) := by
    gcongr
    apply estimate_norm_rpow_range_operator' (p := p) (tc := tc) p₀pos q₀pos q₁pos <;> try assumption
    · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).2
    · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).1
    · intro q₀top s (hs : 0 < s)
      apply weaktype_estimate_truncCompl_top (d := spf.d) hC₀ hp₀.1 q₀top _ _ hf h₀T hs _
      · rw [hspf]
        exact d_eq_top₀ one_le_p₀ q₁pos hp₀p₁.ne_top q₀top hq₀q₁
      · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).1
      · exact interp_exp_ne_top hp₀p₁.ne ht hp
      · dsimp only [tc, spf_to_tc]
        congr
        rw [hspf]
        dsimp only [spf_ch]
        exact ζ_equality₇ ht one_le_p₀ q₀pos one_le_p1 q₁pos hp₀p₁.ne hq₀q₁ hp hq hp₀p₁.ne_top q₀top
    · intro q₁top s (hs : 0 < s)
      rcases (eq_or_ne p₁ ⊤) with p₁eq_top | p₁ne_top
      · apply weaktype_estimate_trunc_top_top hC₁ _ p₁eq_top q₁top _ hf h₁T
        · dsimp only [tc, spf_to_tc]
          rw [hspf]
          dsimp only [spf_ch]
          rw [d_eq_top_top] <;> try assumption
          rw [ζ_eq_top_top, ENNReal.rpow_one] <;> try assumption
          exact hp₀p₁.ne
        · exact p_pos
        · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).2.le
      · apply weaktype_estimate_trunc_top (p₁ := p₁) (p := p) (hd := spf.hd) hC₁ <;> try assumption
        · unfold tc
          rw [hspf]
          dsimp only [spf_to_tc, spf_ch]
          congr
          apply ζ_equality₈ ht (hp₀p₁ := hp₀p₁.ne) <;> assumption
        · rw [hspf]
          dsimp only [spf_ch]
          apply d_eq_top₁ <;> assumption
        · exact p₁ne_top.lt_top
        · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).2
  _ ≤ ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
      ((if q₁ < ⊤ then 1 else 0) * (C₁ ^ q₁.toReal *
      ((spf.d ^ (q.toReal - q₁.toReal)) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ *
        ((eLpNorm f p μ) ^ p.toReal) ^ ((sel ⊤ p₀ p₁).toReal ⁻¹ * (sel ⊤ q₀ q₁).toReal)))
        +
      (if q₀ < ⊤ then 1 else 0) * (C₀ ^ q₀.toReal *
      ((spf.d ^ (q.toReal - q₀.toReal)) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ *
        (((eLpNorm f p μ) ^ p.toReal) ^ ((sel ⊥ p₀ p₁).toReal ⁻¹ * (sel ⊥ q₀ q₁).toReal))))) := by
      apply mul_le_mul_right
      apply add_le_add
      · split_ifs with is_q₁top
        · gcongr
          rw [lintegral_ennreal_eq_lintegral_Ioi_ofReal, ← lintegral_rw_aux power_aux_4]
          apply estimate_trnc₁ (j := ⊤) ht <;> try assumption
          · exact hp₁.2
          · exact ne_top_of_Ioc hp₁ is_q₁top
          · exact is_q₁top.ne_top
          · exact hf.1
          · rw [hspf]; rfl
        · simp
      · split_ifs with is_q₀top
        · gcongr
          rw [lintegral_ennreal_eq_lintegral_Ioi_ofReal, ← lintegral_rw_aux power_aux_4]
          apply estimate_trnc₁ (j := ⊥) ht <;> try assumption
          · exact hp₀.2
          · exact ne_top_of_Ioc hp₀ is_q₀top
          · exact is_q₀top.ne_top
          · exact hf.1
          · rw [hspf]; rfl
        · simp
  _ = (if q₁ < ⊤ then 1 else 0) *
      (↑C₁ ^ q₁.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
          spf.d ^ (q.toReal - q₁.toReal) * ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹) +
      (if q₀ < ⊤ then 1 else 0) *
      (↑C₀ ^ q₀.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
          spf.d ^ (q.toReal - q₀.toReal) * ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
    dsimp only [sel]
    ring_nf
  _ = (if q₁ < ⊤ then 1 else 0) *
      (↑C₀ ^ ((1 - t).toReal * q.toReal) * ↑C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal *
          ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹) +
    (if q₀ < ⊤ then 1 else 0) *
      (↑C₀ ^ ((1 - t).toReal * q.toReal) * ↑C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal *
          ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
    congr 1
    · split_ifs with is_q₁top
      · congr 3
        apply simplify_factor₁ _ hp₀ <;> try assumption
        · rw [hspf]; rfl
        · exact is_q₁top.ne_top
      · simp
    · split_ifs with is_q₀top
      · congr 3
        apply simplify_factor₀ _ hp₀ hp₁ <;> try assumption
        · rw [hspf]; rfl
        · exact is_q₀top.ne_top
      · simp
  _ = _ := by split_ifs <;> ring

lemma combine_estimates₁ {A : ℝ≥0} (hA : 0 < A)
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [TopologicalSpace.PseudoMetrizableSpace E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    {spf : ScaledPowerFunction}
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
    (hf : MemLp f p μ) (hT : Subadditive_trunc T A f ν)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ))
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch (toReal_mem_Ioo ht) hq₀q₁ hp₀.1 (lt_of_lt_of_le hp₀.1 hp₀.2) hp₁.1
        (lt_of_lt_of_le hp₁.1 hp₁.2) hp₀p₁.ne hC₀ hC₁ hF) :
    eLpNorm (T f) q ν ≤
    ENNReal.ofReal (2 * A) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t).toReal * C₁ ^ t.toReal * eLpNorm f p μ := by
  have q_ne_zero : q ≠ 0 := (interpolated_pos' (lt_of_lt_of_le hp₀.1 hp₀.2)
    (lt_of_lt_of_le hp₁.1 hp₁.2) (ne_top_of_Ioo ht) hq).ne'
  have q_ne_top : q ≠ ⊤ := interp_exp_ne_top hq₀q₁ ht hq
  have q'pos : 0 < q.toReal := toReal_pos q_ne_zero q_ne_top
  refine le_of_rpow_le q'pos ?_
  calc
  _ = ∫⁻ x , ‖T f x‖ₑ ^ q.toReal ∂ν := by
    unfold eLpNorm eLpNorm'
    split_ifs <;> [contradiction; rw [one_div, ENNReal.rpow_inv_rpow q'pos.ne']]
  _ ≤ _ := by
    apply combine_estimates₀ (hT := hT) (p := p) <;> try assumption
  _ = _ := by
    repeat rw [ENNReal.mul_rpow_of_nonneg _ _ q'pos.le]
    rw [ENNReal.ofReal_mul' q'pos.le]
    repeat rw [ENNReal.rpow_mul]
    congr
    · rw [ofReal_rpow_of_nonneg] <;> positivity
    · rw [toReal_inv, ENNReal.rpow_inv_rpow q'pos.ne']
      exact ofReal_toReal_eq_iff.mpr q_ne_top
    · rw [toReal_inv, ENNReal.rpow_inv_rpow q'pos.ne']

lemma simplify_factor₃ [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (hp₀ : 0 < p₀) (hp₀' : p₀ ≠ ⊤) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hp₀p₁ : p₀ = p₁) :
    C₀ ^ q₀.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) =
    (↑C₀ * eLpNorm f p μ) ^ q₀.toReal := by
  rw [← interp_exp_eq hp₀p₁ ht hp, ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul, ← mul_div_assoc,
    mul_div_cancel_left₀]
  · exact (toReal_pos hp₀.ne' hp₀').ne'
  positivity

lemma simplify_factor_aux₄ [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (hq₀' : q₀ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ = p₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    ↑C₀ ^ ((1 - t).toReal * q.toReal) * (eLpNorm f p μ ^ p.toReal) ^ ((1 - t).toReal * p₀⁻¹.toReal * q.toReal) *
      ↑C₁ ^ (t.toReal * q.toReal) *
    (eLpNorm f p μ ^ p.toReal) ^ (t.toReal * p₁⁻¹.toReal * q.toReal) = C₀ ^ ((1 - t).toReal * q.toReal) *
    C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have hp' : p₀ = p := (interp_exp_eq hp₀p₁ ht hp)
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀' hp₀.2
  have p₀toReal_pos : 0 < p₀.toReal := toReal_pos hp₀.1.ne' p₀ne_top
  rw [← hp', ← hp₀p₁]
  have (a b c d : ℝ≥0∞): a * b * c * d = a * c * (b * d) := by ring
  rw [this, ← ENNReal.rpow_add]
  · rw [← ENNReal.rpow_mul]
    congr
    rw [toReal_inv]
    ring_nf
    field_simp
    have : (1 - t + t).toReal = 1 := by
      rw [toReal_eq_one_iff, add_comm, add_tsub_cancel_iff_le]
      exact ht.2.le
    rw [mul_comm, ← toReal_add, this, one_mul]
    · finiteness
    · finiteness
  · exact hp' ▸ d_pos_aux₀ hF |>.ne'
  · exact hp' ▸ d_ne_top_aux₀ hF

lemma simplify_factor₄ {D : ℝ≥0∞} [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (hq₀' : q₀ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ = p₁)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    (↑C₀ * eLpNorm f p μ) ^ q₀.toReal * (D ^ (q.toReal - q₀.toReal)) =
    C₀ ^ ((1 - t).toReal * q.toReal) * C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₀pos : 0 < p₀ := hp₀.1
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀' hp₀.2
  rw [← simplify_factor₃] <;> try assumption
  rw [simplify_factor₀ (ht := ht) (hD := hD)] <;> assumption


lemma simplify_factor₅ {D : ℝ≥0∞} [TopologicalSpace E₁] [ESeminormedAddCommMonoid E₁] (hq₁' : q₁ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ = p₁)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    (↑C₁ * eLpNorm f p μ) ^ q₁.toReal * (D ^ (q.toReal - q₁.toReal)) =
    C₀ ^ ((1 - t).toReal * q.toReal) * C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₁pos : 0 < p₁ := hp₁.1
  have p₁ne_top : p₁ ≠ ⊤ := ne_top_of_le_ne_top hq₁' hp₁.2
  rw [← simplify_factor₃ p₁pos p₁ne_top (mem_sub_Ioo one_ne_top ht) (switch_exponents ht hp) hp₀p₁.symm,
    simplify_factor₁ hq₁' hp₀ hp₁ ht hq₀q₁ hp hq hC₀ hC₁ hF hD]

/-- The trivial case for the estimate in the real interpolation theorem
    when the function `Lp` norm of `f` vanishes. -/
lemma exists_hasStrongType_real_interpolation_aux₀ {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁] [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
    {C₀ : ℝ≥0}
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) (hf : MemLp f p μ)
    (hF : eLpNorm f p μ = 0) :
    eLpNorm (T f) q ν = 0 := by
  unfold HasWeakType at h₀T
  have p_pos : 0 < p := interpolated_pos' hp₀.1 hp₁.1 (ne_top_of_Ioo ht) hp
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  have q_pos : 0 < q := interpolated_pos' q₀pos q₁pos (ne_top_of_Ioo ht) hq
  have f_ae_0 : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hf.1 p_pos.ne').mp hF
  have hf₂ : eLpNorm f p₀ μ = 0 := (eLpNorm_eq_zero_iff hf.1 hp₀.1.ne').mpr f_ae_0
  have hf₁ : MemLp f p₀ μ := ⟨hf.1, by rw [hf₂]; exact zero_lt_top⟩
  have := (h₀T f hf₁).2
  rw [hf₂, mul_zero] at this
  have wnorm_0 : wnorm (T f) q₀ ν = 0 := nonpos_iff_eq_zero.mp this
  have : (T f) =ᵐ[ν] 0 := (wnorm_eq_zero_iff q₀pos.ne').mp wnorm_0
  exact (eLpNorm_eq_zero_iff (h₂T hf) q_pos.ne').mpr this

/-- The estimate for the real interpolation theorem in case `p₀ < p₁`. -/
lemma exists_hasStrongType_real_interpolation_aux {p₀ p₁ q₀ q₁ p q : ℝ≥0∞} {A : ℝ≥0}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [TopologicalSpace.PseudoMetrizableSpace E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂] (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Subadditive_trunc T A f ν) (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    ENNReal.ofReal (2 * A) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t).toReal * C₁ ^ t.toReal * eLpNorm f p μ := by
  have hq₀ : 0 < q₀ := pos_of_rb_Ioc hp₀
  have hq₁ : 0 < q₁ := pos_of_rb_Ioc hp₁
  rcases (eq_zero_or_pos (eLpNorm f p μ)) with hF | hF
  · refine le_of_eq_of_le ?_ zero_le
    apply exists_hasStrongType_real_interpolation_aux₀ (hp := hp) (hq := hq) <;> try assumption
  · let spf := spf_ch (toReal_mem_Ioo ht) hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ hp₀p₁.ne hC₀ hC₁ ⟨hF, hf.2⟩
    apply combine_estimates₁ <;> try assumption
    on_goal 1 => unfold spf
    rfl

-- TODO: the below lemmas were split because otherwise the lean server would crash
-- (seems to be related to the linter?) (after the merge)
lemma exists_hasStrongType_real_interpolation_aux₁ {f : α → E₁}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ = p₁) (hq₀q₁ : q₀ < q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (ENNReal.ofReal q.toReal *
        ((C₀ * eLpNorm f p μ )^ q₀.toReal *
        (∫⁻ (t : ℝ) in Ioo 0 (@d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f).toReal,
        ENNReal.ofReal (t ^ (q.toReal - q₀.toReal - 1))) * (if q₀ = ⊤ then 0 else 1) +
        ((C₁ * eLpNorm f p μ) ^ q₁.toReal *
        ∫⁻ (t : ℝ) in Ici (@d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f).toReal,
        ENNReal.ofReal (t ^ (q.toReal - q₁.toReal - 1))) * if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ =
    q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
    ↑C₀ ^ ((1 - t).toReal) * ↑C₁ ^ t.toReal * eLpNorm f p μ := by
    let M := @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f
    have hq₀q₁' : q₀ ≠ q₁ := hq₀q₁.ne
    have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
    have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
    have q₀lt_q_toReal : q₀.toReal < q.toReal :=
      preservation_inequality_of_lt₀ ht q₀pos q₁pos hq hq₀q₁
    have q_toReal_ne_zero : q.toReal ≠ 0 :=
      (interp_exp_toReal_pos' ht q₀pos q₁pos hq (Or.inl hq₀q₁.ne_top)).ne'
    -- lemma below proves the same, but for M.toReal
    have M_pos : 0 < M := by
      apply d_pos <;> assumption
    have M_ne_top : M ≠ ∞ := by finiteness
    have : 0 < M.toReal := toReal_pos M_pos.ne' M_ne_top
    have : ENNReal.ofReal M.toReal = M := by rw [ofReal_toReal M_ne_top]
    have coe_q : ENNReal.ofReal q.toReal = q :=
    ofReal_toReal_eq_iff.mpr (interp_exp_ne_top hq₀q₁.ne ht hq)
    -- type mismatches, ℝ vs ℝ≥0∞
    have eq :
        (ENNReal.ofReal q.toReal *
        ((((↑C₀ * eLpNorm f p μ) ^ q₀.toReal * ∫⁻ (t : ℝ) in Ioo 0 M.toReal,
            ENNReal.ofReal (t ^ (q.toReal - q₀.toReal - 1))) *
            if q₀ = ⊤ then 0 else 1) +
          ((↑C₁ * eLpNorm f p μ) ^ q₁.toReal * ∫⁻ (t : ℝ) in Ici M.toReal,
            ENNReal.ofReal (t ^ (q.toReal - q₁.toReal - 1))) *
            if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ = (ENNReal.ofReal q.toReal *
            (↑C₀ ^ ((1 - t).toReal * q.toReal) * ↑C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal *
              ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
            ↑C₀ ^ ((1 - t).toReal * q.toReal) * ↑C₁ ^ (t.toReal * q.toReal) * eLpNorm f p μ ^ q.toReal *
                ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * if q₁ = ⊤ then 0 else 1)) ^
            q.toReal⁻¹ := by
      congr 3
      · rw [lintegral_rpow_of_gt_abs, sub_add_cancel, ENNReal.ofReal_div_of_pos,
            div_eq_mul_inv, ← ofReal_inv_of_pos, ← ENNReal.ofReal_rpow_of_pos] <;> try positivity
        rw [← mul_assoc, simplify_factor₄ (ht := ht) (hC₁ := hC₁) (hq₀' := hq₀q₁.ne_top)]
            <;> try assumption
        · rw [abs_of_pos] <;> linarith
        · rw [abs_of_pos] <;> linarith
        · linarith
      · split_ifs with is_q₁top
        · rw [mul_zero, mul_zero]
        · have q_lt_q₁toReal : q.toReal < q₁.toReal :=
            preservation_inequality_of_lt₁ ht q₀pos q₁pos hq hq₀q₁ is_q₁top
          rw [mul_one, mul_one, setLIntegral_congr (Filter.EventuallyEq.symm Ioi_ae_eq_Ici),
          lintegral_Ioi_rpow_of_lt_abs, sub_add_cancel, ENNReal.ofReal_div_of_pos,
            div_eq_mul_inv, ← ofReal_inv_of_pos, ← ENNReal.ofReal_rpow_of_pos] <;> try positivity
          rw [← mul_assoc, simplify_factor₅ (hC₀ := hC₀) (ht := ht) (q₀ := q₀) (q₁ := q₁) (p₀ := p₀)
              (p₁ := p₁)] <;> try assumption
          · rw [abs_of_neg] <;> linarith
          · rw [abs_of_neg] <;> linarith
          · linarith
    rw [eq, coe_q]
    nth_rw 1 [mul_assoc]
    nth_rw 3 [mul_assoc]
    rw [← mul_add]
    have obs : q.toReal⁻¹ ≥ 0 := by positivity
    repeat rw [ENNReal.mul_rpow_of_nonneg _ _ obs]
    rw [ENNReal.rpow_rpow_inv, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_assoc (1 - t).toReal,
        mul_inv_cancel₀, mul_assoc t.toReal, mul_inv_cancel₀, mul_one, mul_one] <;> try positivity
    ring

/-- The main estimate in the real interpolation theorem for `p₀ = p₁`, before taking roots,
    for the case `q₀ < q₁`. -/
lemma exists_hasStrongType_real_interpolation_aux₂ {f : α → E₁}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ = p₁) (hq₀q₁ : q₀ < q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
    ↑C₀ ^ ((1 - t).toReal) * ↑C₁ ^ t.toReal * eLpNorm f p μ := by
  let M := (@d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f).toReal
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀q₁.ne_top hp₀.2
  have q_toReal_ne_zero : q.toReal ≠ 0 :=
    (interp_exp_toReal_pos' ht q₀pos q₁pos hq (Or.inl hq₀q₁.ne_top)).ne'
  have p_eq_p₀ : p = p₀ := (interp_exp_eq hp₀p₁ ht hp).symm
  rcases (eq_zero_or_pos (eLpNorm f p μ)) with hF | snorm_pos
  · refine le_of_eq_of_le ?_ zero_le
    apply exists_hasStrongType_real_interpolation_aux₀ (hp := hp) (hq := hq) <;> try assumption
  · have hF : eLpNorm f p μ ∈ Ioo 0 ⊤ := ⟨snorm_pos, hf.2⟩
    have M_pos : 0 < M := toReal_pos (d_pos hC₀ hC₁ hF).ne' (d_ne_top hC₀ hC₁ hF)
    have coe_q : ENNReal.ofReal q.toReal = q :=
    ofReal_toReal_eq_iff.mpr (interp_exp_ne_top hq₀q₁.ne ht hq)
    nth_rw 1 [← coe_q]
    rw [eLpNorm_eq_distribution (h₂T hf)
        (interp_exp_toReal_pos ht q₀pos q₁pos hq₀q₁.ne hq)]
    calc
    (ENNReal.ofReal q.toReal *
    ∫⁻ (t : ℝ) in Ioi 0, distribution (T f) (ENNReal.ofReal t) ν * ENNReal.ofReal (t ^ (q.toReal - 1))) ^ q.toReal⁻¹
      ≤ (ENNReal.ofReal q.toReal * (
        (∫⁻ (t : ℝ) in Ioo 0 M, distribution (T f) (ENNReal.ofReal t) ν * ENNReal.ofReal (t ^ (q.toReal - 1))) +
        (∫⁻ (t : ℝ) in Ici M, distribution (T f) (ENNReal.ofReal t) ν * ENNReal.ofReal (t ^ (q.toReal - 1))))
        ) ^ q.toReal⁻¹ := by
      gcongr
      rw [← Ioo_union_Ici_eq_Ioi (M_pos)]
      apply lintegral_union_le _ (Ioo (0 : ℝ) (M : ℝ)) (Ici (M : ℝ))
    _ ≤ (ENNReal.ofReal q.toReal *
        ((∫⁻ (t : ℝ) in Ioo 0 M, C₀ ^ q₀.toReal *
        eLpNorm f p μ ^ q₀.toReal * ENNReal.ofReal (t ^ (-q₀.toReal)) *
        ENNReal.ofReal (t ^ (q.toReal - 1))) * (if q₀ = ⊤ then 0 else 1)+
        (∫⁻ (t : ℝ) in Ici M, C₁ ^ q₁.toReal *
        eLpNorm f p μ ^ q₁.toReal * ENNReal.ofReal (t ^ (-q₁.toReal)) *
        ENNReal.ofReal (t ^ (q.toReal - 1))) * if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ := by
      apply ENNReal.rpow_le_rpow <;> try positivity
      apply mul_le_mul_right
      apply add_le_add
      · split_ifs with is_q₀top
        · contrapose! is_q₀top; exact hq₀q₁.ne_top
        · rw [mul_one]
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ⟨(ht₁ : 0 < t), _⟩
          gcongr
          rw [← ofReal_rpow_of_pos ht₁]
          apply weaktype_estimate <;> try assumption
          · exact (hq₀q₁.ne_top).lt_top
          · rw [p_eq_p₀]; exact h₀T
          · exact ofReal_pos.mpr ht₁
      · split_ifs with is_q₁_top
        · simp only [mul_zero, nonpos_iff_eq_zero]
          have hf_0 : EqOn (fun t ↦ distribution (T f) (ENNReal.ofReal t) ν *
              ENNReal.ofReal (t ^ (q.toReal - 1))) (fun x ↦ 0) (Ici M) := by
            intro t ht
            dsimp only
            rw [weaktype_estimate_top] <;> try assumption
            · simp
            · rw [p_eq_p₀, hp₀p₁]; exact h₁T
            · have p₀pos : 0 < p₀ := hp₀.1
              have p₁pos : 0 < p₁ := hp₁.1
              have q₀ne_top : q₀ ≠ ⊤ := hq₀q₁.ne_top
              unfold M at ht
              rw [d_eq_top_of_eq] at ht <;> try assumption
              have : ENNReal.ofReal (C₁ * eLpNorm f p μ).toReal = C₁ * eLpNorm f p μ :=
                ofReal_toReal_eq_iff.mpr (by finiteness)
              rw [← this]
              exact ofReal_le_ofReal ht
          rw [setLIntegral_congr_fun measurableSet_Ici hf_0, lintegral_zero]
        · rw [mul_one]
          apply setLIntegral_mono' measurableSet_Ici
          intro t ht
          have ht' := lt_of_lt_of_le M_pos ht
          gcongr
          rw [← ofReal_rpow_of_pos ht']
          apply weaktype_estimate <;> try assumption
          · exact Ne.lt_top is_q₁_top
          · rw [p_eq_p₀, hp₀p₁]; exact h₁T
          · positivity
    _ = (ENNReal.ofReal q.toReal *
        ((C₀ * eLpNorm f p μ )^ q₀.toReal *
        (∫⁻ (t : ℝ) in Ioo 0 M, ENNReal.ofReal (t ^ (q.toReal - q₀.toReal - 1))) *
        (if q₀ = ⊤ then 0 else 1) +
        ((C₁ * eLpNorm f p μ) ^ q₁.toReal *
        ∫⁻ (t : ℝ) in Ici M,  ENNReal.ofReal (t ^ (q.toReal - q₁.toReal - 1))) *
        if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ := by
      congr
      · rw [← lintegral_const_mul]
        · apply setLIntegral_congr_fun measurableSet_Ioo
          intro t ⟨(ht₁ : 0 < t), _⟩
          dsimp
          rw [ENNReal.mul_rpow_of_nonneg] <;> try positivity
          rw [mul_assoc, ← ofReal_mul] <;> try positivity
          congr
          rw [← Real.rpow_add ht₁]
          congr 1; linarith
        · refine Measurable.ennreal_ofReal ?_
          exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) (q.toReal - q₀.toReal - 1)
      · rw [← lintegral_const_mul]
        · apply setLIntegral_congr_fun measurableSet_Ici
          intro t ht
          dsimp only
          have t_pos : 0 < t := lt_of_lt_of_le M_pos ht
          rw [ENNReal.mul_rpow_of_nonneg] <;> try positivity
          rw [mul_assoc, ← ofReal_mul] <;> try positivity
          congr
          rw [← Real.rpow_add] <;> try positivity
          congr 1; linarith
        · refine Measurable.ennreal_ofReal ?_
          exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) (q.toReal - q₁.toReal - 1)
    _ = _ := by
      apply exists_hasStrongType_real_interpolation_aux₁ <;> assumption

/-- The main estimate for the real interpolation theorem for `p₀ = p₁`, requiring `q₀ ≠ q₁`,
before taking roots. -/
lemma exists_hasStrongType_real_interpolation_aux₃ {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ = p₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
    ↑C₀ ^ ((1 - t).toReal) * ↑C₁ ^ t.toReal * eLpNorm f p μ := by
  rcases lt_or_gt_of_ne hq₀q₁ with q₀lt_q₁ | q₁lt_q₀
  · apply exists_hasStrongType_real_interpolation_aux₂ <;> assumption
  · have (a b c d : ℝ≥0∞) : a * b * c * d = a * c * b * d := by ring
    rw [this, add_comm]
    have hp' := switch_exponents ht hp
    have hq' := switch_exponents ht hq
    nth_rw 1 [← one_sub_one_sub_eq ht]
    apply exists_hasStrongType_real_interpolation_aux₂ (ht := mem_sub_Ioo one_ne_top ht)
        (hp₀p₁ := hp₀p₁.symm) (hq₀q₁ := q₁lt_q₀) <;> assumption

/-- The main estimate for the real interpolation theorem, before taking roots, combining
the cases `p₀ ≠ p₁` and `p₀ = p₁`. -/
lemma exists_hasStrongType_real_interpolation_aux₄ {p₀ p₁ q₀ q₁ p q : ℝ≥0∞} {A : ℝ≥0} (hA : 0 < A)
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [TopologicalSpace.PseudoMetrizableSpace E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Subadditive_trunc T A f ν) (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    (if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A)) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t).toReal * C₁ ^ t.toReal * eLpNorm f p μ := by
  let M := if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A)
  have hM : M = if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A) := rfl
  rw [← hM]
  split_ifs at hM with are_ps_eq
  · rw [hM, one_mul]
    have p_eq_p₀ : p = p₀ := (interp_exp_eq are_ps_eq ht hp).symm
    calc
    _ ≤ q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
        ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
        ↑C₀ ^ ((1 - t).toReal) * ↑C₁ ^ t.toReal * eLpNorm f p μ := by
      apply exists_hasStrongType_real_interpolation_aux₃ <;> try assumption
    _ = _ := by
      rw [p_eq_p₀]
      congr 4
      · rw [toReal_inv]
      · rw [add_comm]
        congr 2
        · rw [mul_comm]
          have : (q₁ < ⊤) ↔ (q₁ ≠ ⊤):= lt_top_iff_ne_top
          split_ifs <;> tauto
        · rw [mul_comm]
          have : (q₀ < ⊤) ↔ (q₀ ≠ ⊤):= lt_top_iff_ne_top
          split_ifs <;> tauto
        · rw [toReal_inv]
  · rcases (lt_or_gt_of_ne are_ps_eq) with p₀lt_p₁ | p₁lt_p₀
    · rw [hM]
      apply exists_hasStrongType_real_interpolation_aux <;> try assumption
    · have (a b c d e f : ℝ≥0∞) : a * b * c * d * e * f = a * b * c * e * d * f := by ring
      rw [hM, this, add_comm]
      have hp' := switch_exponents ht hp
      have hq' := switch_exponents ht hq
      nth_rw 1 [← one_sub_one_sub_eq ht]
      apply exists_hasStrongType_real_interpolation_aux (ht := mem_sub_Ioo one_ne_top ht)
          (hq₀q₁ := hq₀q₁.symm) <;> assumption

/-- The definition of the constant in the real interpolation theorem, when viewed as
    an element of `ℝ≥0∞`. -/
def C_realInterpolation_ENNReal (p₀ p₁ q₀ q₁ q : ℝ≥0∞) (C₀ C₁ : ℝ≥0) (A : ℝ≥0) (t : ℝ≥0∞) :=
    (if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A)) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t).toReal * C₁ ^ t.toReal

lemma C_realInterpolation_ENNReal_ne_top {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0}
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) :
    C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t ≠ ⊤ := by
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  unfold C_realInterpolation_ENNReal
  apply mul_ne_top
  · apply mul_ne_top
    · apply mul_ne_top
      · finiteness [interpolated_pos' q₀pos q₁pos (ne_top_of_Ioo ht) hq |>.ne',
          interp_exp_ne_top hq₀q₁ ht hq]
      · apply rpow_ne_top'
        · split_ifs
          · rw [one_mul, one_mul]
            apply ne_of_gt
            apply add_pos'
            · exact ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq
            · exact ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq
          · simp [ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq |>.ne']
          · simp [ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq |>.ne']
          · simp_all
        · split_ifs <;> exact (ne_of_beq_false rfl).symm
    · finiteness
  · finiteness

lemma C_realInterpolation_ENNReal_pos {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0} (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) :
    0 < C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t := by
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  unfold C_realInterpolation_ENNReal
  apply ENNReal.mul_pos
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · split_ifs <;> positivity
        · apply ne_of_gt
          apply ENNReal.rpow_pos
          · exact interpolated_pos' q₀pos q₁pos (ne_top_of_Ioo ht) hq
          · exact interp_exp_ne_top hq₀q₁ ht hq
      · apply ne_of_gt
        apply ENNReal.rpow_pos ?_ (by finiteness)
        split_ifs
        · rw [one_mul, one_mul]
          apply add_pos'
          · exact ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq
          · exact ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq
        · simp [ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq]
        · simp [ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq]
        · simp_all
    · exact (ENNReal.rpow_pos (by positivity) coe_ne_top).ne'
  · exact (ENNReal.rpow_pos (by positivity) coe_ne_top).ne'

/-- The constant occurring in the real interpolation theorem -/
-- todo: check order of arguments
def C_realInterpolation (p₀ p₁ q₀ q₁ q : ℝ≥0∞) (C₀ C₁ A : ℝ≥0) (t : ℝ≥0∞) : ℝ≥0 :=
    C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t |>.toNNReal

lemma C_realInterpolation_pos {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0} (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) :
    0 < C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t := by
  unfold C_realInterpolation
  refine toNNReal_pos ?_ ?_
  · apply ne_of_gt
    apply C_realInterpolation_ENNReal_pos <;> assumption
  · apply C_realInterpolation_ENNReal_ne_top (A := A) <;> assumption

lemma coe_C_realInterpolation {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0}
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) :
  ENNReal.ofNNReal (C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t) =
     C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t := by
  refine coe_toNNReal ?_
  apply C_realInterpolation_ENNReal_ne_top (A := A) <;> assumption

lemma Subadditive_trunc_from_SubadditiveOn_Lp₀p₁ {p₀ p₁ p : ℝ≥0∞}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    {A : ℝ≥0} (hA : 1 ≤ A) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁)
    (hT : AESubadditiveOn T (fun f ↦ MemLp f p₀ μ ∨ MemLp f p₁ μ) A ν)
    (hf : MemLp f p μ) :
    Subadditive_trunc T A f ν := by
  intro a a_pos
  by_cases ha : a = ∞
  · rw [ha]
    simp only [trunc_top, truncCompl_top]
    filter_upwards with x
    nth_rw 1 [← one_mul ‖T (f + fun x ↦ 0) x‖ₑ]
    gcongr
    · exact one_le_coe_iff.mpr hA
    · apply le_trans (add_zero _).symm.le
      gcongr
      · apply le_of_eq
        congr
        · ext x; simp
      · simp
  apply hT
  · rcases lt_trichotomy p₀ p₁ with p₀lt_p₁ | (p₀eq_p₁ | p₁lt_p₀)
    · refine Or.inr (trunc_Lp_Lq_higher (p := p) ?_ hf ha)
      exact ⟨interpolated_pos' hp₀ hp₁ (ne_top_of_Ioo ht) hp, (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).2.le⟩
    · exact Or.inl <| interp_exp_eq p₀eq_p₁ ht hp ▸ hf.trunc
    · refine Or.inl (trunc_Lp_Lq_higher (p := p) ?_ hf ha)
      exact ⟨interpolated_pos' hp₀ hp₁ (ne_top_of_Ioo ht) hp,
        (interp_exp_between hp₁ hp₀ p₁lt_p₀ (mem_sub_Ioo one_ne_top ht)
          (switch_exponents ht hp)).2.le⟩
  · rcases lt_trichotomy p₀ p₁ with p₀lt_p₁ | (p₀eq_p₁ | p₁lt_p₀)
    · refine Or.inl (truncCompl_Lp_Lq_lower (p := p) (interp_exp_ne_top p₀lt_p₁.ne ht hp)
        ⟨hp₀, (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1.le⟩ a_pos hf)
    · exact Or.inl <| interp_exp_eq p₀eq_p₁ ht hp ▸ hf.truncCompl
    · refine Or.inr <| truncCompl_Lp_Lq_lower (p := p) ?_ ?_ a_pos hf
      · exact interp_exp_ne_top p₁lt_p₀.ne (mem_sub_Ioo one_ne_top ht) (switch_exponents ht hp)
      · exact ⟨hp₁, (interp_exp_between hp₁ hp₀ p₁lt_p₀ (mem_sub_Ioo one_ne_top ht)
          (switch_exponents ht hp)).1.le⟩

/-- Marcinkiewicz real interpolation theorem -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    [TopologicalSpace E₁] [ENormedAddCommMonoid E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [TopologicalSpace.PseudoMetrizableSpace E₁]
    [TopologicalSpace E₂] [ENormedAddCommMonoid E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ A : ℝ≥0} (hA : 1 ≤ A) (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hmT : ∀ f, MemLp f p μ → AEStronglyMeasurable (T f) ν)
    (hT : AESubadditiveOn T (fun f ↦ MemLp f p₀ μ ∨ MemLp f p₁ μ) A ν)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁) :
    HasStrongType T p q μ ν (C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t) := by
  intro f hf
  refine ⟨hmT f hf, ?_⟩
  have hp' : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹ := by rw [hp]; congr
  have hq' : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹ := by rw [hq]; congr
  have obs : Subadditive_trunc T A f ν :=
    Subadditive_trunc_from_SubadditiveOn_Lp₀p₁ hp₀.1 hp₁.1 hA ht hp' hT hf
  rw [coe_C_realInterpolation hp₀ hp₁ hq₀q₁] <;> try assumption
  have : 0 < A := lt_of_lt_of_le (by norm_num) hA
  apply exists_hasStrongType_real_interpolation_aux₄ <;> assumption

end MeasureTheory

end
