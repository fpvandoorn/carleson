module

public import Carleson.Defs
public import Carleson.LipschitzNorm
public import Carleson.ToMathlib.Data.ENNReal

@[expose] public section

open MeasureTheory Measure Metric Complex Set Bornology Function
open ENNReal hiding one_lt_two
open scoped NNReal

noncomputable section

/-! # Basic definitions and lemmas

This file contains definitions from Section 2 of the blueprint and used throughout the proof
of metric Carleson, as well as results about structures defined in sections 1 and 2
(`DoublingMeasure` `KernelProofData`, `IsCancellative`, `FunctionDistances`, ...).
The constants `D`, `κ`, `Z` from the blueprint are introduce here, and useful inequalities are
provided for them (as well as for the constants `a` and `tau`).

-/

lemma seven_le_c : 7 ≤ 𝕔 := by simp [𝕔]

lemma c_le_100 : 𝕔 ≤ 100 := by simp [𝕔]

/- To check that the value of `c` is irrelevant, you can take `𝕔 = 7` above, or you can comment
the previous lines and uncomment the next ones.

lemma exists_c : ∃ (c : ℕ), 7 ≤ c ∧ c ≤ 100 := ⟨7, le_rfl, by norm_num⟩
def 𝕔 : ℕ := exists_c.choose
lemma seven_le_c : 7 ≤ 𝕔 := exists_c.choose_spec.1
lemma c_le_100 : 𝕔 ≤ 100 := exists_c.choose_spec.2
-/

/-- The constant `D` from (2.0.1). -/
@[simp] def defaultD (a : ℕ) : ℕ := 2 ^ (𝕔 * a ^ 2)

/-- `D` as an element of `ℝ≥0`. -/
def nnD (a : ℕ) : ℝ≥0 := ⟨defaultD a, by simp⟩

/-- The constant `κ` from (2.0.2). -/
@[simp] def defaultκ (a : ℕ) : ℝ := 2 ^ (-10 * (a : ℝ))

/-- The constant `Z` from (2.0.3). -/
@[simp] def defaultZ (a : ℕ) : ℕ := 2 ^ (12 * a)

section ConstantBounds

variable (a : ℕ)

lemma defaultD_pos : 0 < defaultD a := by rw [defaultD]; positivity

lemma realD_pos : 0 < (defaultD a : ℝ) := mod_cast defaultD_pos a

lemma realD_nonneg : 0 ≤ (defaultD a : ℝ) := le_of_lt (realD_pos a)

lemma one_le_realD : 1 ≤ (defaultD a : ℝ) := by
  rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_zero 2]
  exact pow_le_pow_right₀ (one_le_two) (by lia)

lemma defaultD_pow_pos (z : ℤ) : 0 < (defaultD a : ℝ) ^ z := by
  positivity [realD_pos a]

lemma mul_defaultD_pow_pos {r : ℝ} (hr : 0 < r) (z : ℤ) : 0 < r * (defaultD a : ℝ) ^ z :=
  mul_pos hr (defaultD_pow_pos a z)

section KernelProofData

variable (X) [PseudoMetricSpace X] {a} {K : X → X → ℂ} [hK : KernelProofData a K]

include hK

-- used in 7.5.6 (`limited_scale_impact`)
lemma hundred_lt_D : 100 < defaultD a := by
  have : 100 < 2 ^ 7 := by norm_num
  apply this.trans_le
  have : 16 ≤ a ^ 2 := by nlinarith [four_le_a X]
  simp only [defaultD]
  gcongr
  · norm_num
  · nlinarith [seven_le_c]

-- used in 7.5.6 (`limited_scale_impact`)
lemma hundred_lt_realD : (100 : ℝ) < defaultD a := mod_cast hundred_lt_D X

-- used in 4.1.7 (`small_boundary`)
lemma twentyfive_le_realD : (25 : ℝ) ≤ defaultD a := by linarith [hundred_lt_realD X]

-- used in 4.1.3 (`I3_prop_3_1`)
lemma eight_le_realD : (8 : ℝ) ≤ defaultD a := by linarith [twentyfive_le_realD X]

-- used in 4.1.6 (`transitive_boundary`)
lemma five_le_realD : (5 : ℝ) ≤ defaultD a := by linarith [twentyfive_le_realD X]

-- used in various places in `Carleson.TileExistence`
lemma four_le_realD : (4 : ℝ) ≤ defaultD a := by linarith [twentyfive_le_realD X]

lemma one_lt_realD : 1 < (defaultD a : ℝ) := by linarith [twentyfive_le_realD X]

lemma a_pos : 0 < a := by linarith [four_le_a X]

lemma cast_a_pos : 0 < (a : ℝ) := by norm_cast; exact a_pos X

lemma τ_pos : 0 < defaultτ a := inv_pos.mpr (cast_a_pos X)

lemma τ_nonneg : 0 ≤ defaultτ a := (τ_pos X).le

lemma τ_le_one : defaultτ a ≤ 1 := by
  rw [defaultτ, inv_le_one_iff₀]; right; norm_cast; linarith [four_le_a X]

/-- `τ` as an element of `ℝ≥0`. -/
def nnτ : ℝ≥0 := ⟨defaultτ a, τ_nonneg X⟩
lemma nnτ_pos : 0 < nnτ X := τ_pos X
@[simp]
lemma nnτ_def : nnτ X = (defaultτ a).toNNReal := Real.toNNReal_of_nonneg (τ_nonneg X) |>.symm

end KernelProofData

namespace ShortVariables
-- open this section to get shorter 1-letter names for a bunch of variables

set_option hygiene false
scoped notation "D" => defaultD a
scoped notation "κ" => defaultκ a
scoped notation "Z" => defaultZ a
scoped notation "τ" => defaultτ a
scoped notation "o" => cancelPt X
scoped notation "S" => defaultS X
scoped notation "nnτ" => nnτ X
scoped notation "nnD" => nnD a

end ShortVariables

open scoped ShortVariables

variable {a : ℕ}

lemma κ_nonneg : 0 ≤ κ :=
  Real.rpow_nonneg (by norm_num) _

lemma κ_le_one : κ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)

end ConstantBounds

section DoublingMeasure

universe u

namespace MeasureTheory

/- # Doubling metric measure spaces -/

variable {X : Type*} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

instance : ProperSpace X := by
  constructor
  intro x r
  refine TotallyBounded.isCompact_of_isClosed ?_ isClosed_closedBall
  obtain ⟨r', hr'⟩ := exists_gt r
  apply TotallyBounded.subset (closedBall_subset_ball hr')
  refine Metric.totallyBounded_iff.mpr fun ε hε ↦ ?_
  obtain ⟨s, _, h2s⟩ := IsDoubling.allBallsCoverBalls volume |>.ballsCoverBalls (by norm_num) hε x
  use s, s.finite_toSet, by simpa using h2s

instance : IsOpenPosMeasure (volume : Measure X) := isOpenPosMeasure_of_isDoubling _

/-- Monotonicity of doubling measure metric spaces in `A`. -/
@[reducible]
def DoublingMeasure.mono {A'} (h : A ≤ A') : DoublingMeasure X A' where
  toIsDoubling := IsDoubling.mono h

open Module

instance InnerProductSpace.DoublingMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    DoublingMeasure E (2 ^ finrank ℝ E) where

end MeasureTheory

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

lemma fact_isCompact_ball (x : X) (r : ℝ) : Fact (IsBounded (ball x r)) :=
  ⟨isBounded_ball⟩
attribute [local instance] fact_isCompact_ball

section FunctionDistances

variable [FunctionDistances 𝕜 X]

instance : ContinuousMapClass (Θ X) X 𝕜 := ⟨fun f ↦ (f : C(X, 𝕜)).2⟩

def toWithFunctionDistance {x : X} {r : ℝ} [FunctionDistances 𝕜 X] :
    Θ X ≃ WithFunctionDistance x r := .refl _

end FunctionDistances

/-- The `ℝ≥0`-valued distance function on `WithFunctionDistance x r`. Preferably use `edist` -/
notation3 "nndist_{" x ", " r "}" => @nndist (WithFunctionDistance x r) _
/-- The ball with center `x` and radius `r` in `WithFunctionDistance x r`. -/
notation3 "ball_{" x ", " r "}" => @ball (WithFunctionDistance x r) _ in
instance nonempty_Space [CompatibleFunctions 𝕜 X A] : Nonempty X := by
  obtain ⟨x,_⟩ := ‹CompatibleFunctions 𝕜 X A›.eq_zero
  use x

instance inhabited_Space [CompatibleFunctions 𝕜 X A] : Inhabited X :=
  ⟨nonempty_Space.some⟩

lemma le_localOscillation [CompatibleFunctions 𝕜 X A] (x : X) (r : ℝ) (f g : Θ X) {y z : X}
    (hy : y ∈ ball x r) (hz : z ∈ ball x r) : ‖coeΘ f y - coeΘ g y - coeΘ f z + coeΘ g z‖ ≤
    ENNReal.toReal (localOscillation (ball x r) (coeΘ f) (coeΘ g)) := by
  rw [(ENNReal.toReal_ofReal (norm_nonneg _)).symm]
  let f (z) := ⨆ (_ : z ∈ ball x r ×ˢ ball x r), ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖
  apply ENNReal.toReal_mono
  · exact lt_of_le_of_lt CompatibleFunctions.localOscillation_le_cdist ENNReal.ofReal_lt_top |>.ne
  · exact le_of_eq_of_le (Eq.symm (iSup_pos ⟨hy, hz⟩)) (le_iSup f ⟨y, z⟩)

lemma oscillation_le_cdist [CompatibleFunctions 𝕜 X A] (x : X) (r : ℝ) (f g : Θ X) {y z : X}
    (hy : y ∈ ball x r) (hz : z ∈ ball x r) :
    ‖coeΘ f y - coeΘ g y - coeΘ f z + coeΘ g z‖ ≤ dist_{x, r} f g := by
  apply le_trans <| le_localOscillation x r f g hy hz
  rw [← ENNReal.toReal_ofReal dist_nonneg]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top CompatibleFunctions.localOscillation_le_cdist

export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)

lemma dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
    (e₁ : x₁ = x₂) (e₂ : r₁ = r₂) : dist_{x₁, r₁} f g = dist_{x₂, r₂} f g := by congr

variable (X) in
/-- The point `o` in the blueprint -/
def cancelPt [CompatibleFunctions 𝕜 X A] : X :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose

lemma cancelPt_eq_zero [CompatibleFunctions 𝕜 X A] {f : Θ X} : f (cancelPt X) = 0 :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose_spec f

variable [hXA : DoublingMeasure X A]

lemma enorm_integral_exp_le [CompatibleFunctions ℝ X A] {τ : ℝ} [IsCancellative X τ]
    {x : X} {r : ℝ} {φ : X → ℂ} (h2 : support φ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * φ x‖ₑ ≤
    (A : ℝ≥0∞) * volume (ball x r) * iLipENorm φ x r * (1 + edist_{x, r} f g) ^ (- τ) := by
  rcases le_or_gt r 0 with hr | hr
  · simp only [ball_eq_empty.2 hr, subset_empty_iff, support_eq_empty_iff] at h2
    simp [h2]
  rcases eq_or_ne A 0 with rfl | hA
  · have : (volume : Measure X) = 0 := by
      have := hXA.toIsDoubling
      simp at this
      apply eq_zero_of_isDoubling_zero
    simp [this]
  rcases eq_or_ne (iLipENorm φ x r) ∞ with h1 | h1
  · apply le_top.trans_eq
    symm
    simp [h1, edist_ne_top, hA, (measure_ball_pos volume x hr).ne']
  exact IsCancellative.enorm_integral_exp_le' hr h1 h2

/-- Constructor of `IsCancellative` in terms of real norms instead of extended reals. -/
lemma isCancellative_of_norm_integral_exp_le (τ : ℝ) [CompatibleFunctions ℝ X A]
    (h : ∀ {x : X} {r : ℝ} {φ : X → ℂ} (_hr : 0 < r) (_h1 : iLipENorm φ x r ≠ ∞)
    (_h2 : support φ ⊆ ball x r) {f g : Θ X},
      ‖∫ x in ball x r, exp (I * (f x - g x)) * φ x‖ ≤
      A * volume.real (ball x r) * iLipNNNorm φ x r * (1 + dist_{x, r} f g) ^ (-τ)) :
    IsCancellative X τ := by
  constructor
  intro x r φ hr h1 h2 f g
  convert ENNReal.ofReal_le_ofReal (h (x := x) (r := r) (φ := φ) hr h1 h2 (f := f) (g := g))
  · rw [ofReal_norm_eq_enorm]
    congr 1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)]
    have : φ y = 0 := by
      apply notMem_support.1
      contrapose! hy
      exact h2 hy
    simp [this]
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    congr
    · simp
    · simp only [Measure.real, ofReal_toReal measure_ball_ne_top]
    · simp [iLipNNNorm, coe_toNNReal h1]
    · rw [← ENNReal.ofReal_rpow_of_pos (by positivity)]
      congr
      rw [ENNReal.ofReal_add zero_le_one dist_nonneg]
      simp [edist_dist]

/-- The "volume function" `V`. We will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ≥0∞ :=
  volume (ball x (dist x y))

@[fun_prop]
lemma measurable_vol {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasureSpace X] [OpensMeasurableSpace X] [SFinite (volume : Measure X)] :
    Measurable (uncurry vol : X × X → ℝ≥0∞) := by
  let f : X × X → X × ℝ := fun (x, y) ↦ (x, dist x y)
  let g : X × ℝ → ℝ≥0∞ := fun (x, a) ↦ volume (ball x a)
  apply Measurable.comp (f := f) (g := g)
  · apply measurable_measure_ball
  · fun_prop

@[fun_prop]
lemma measurable_vol₁ {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasureSpace X] [OpensMeasurableSpace X] [SFinite (volume : Measure X)] {y : X} :
    Measurable (vol · y) := by
  change Measurable (uncurry vol ∘ fun x : X ↦ (x, y))
  apply Measurable.comp <;> fun_prop

lemma Real.vol_def {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] {x y : X} :
  Real.vol x y = (vol x y).toReal := rfl

lemma ofReal_vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] [ProperSpace X]
  [IsFiniteMeasureOnCompacts (volume : Measure X)] {x y : X} :
    ENNReal.ofReal (Real.vol x y) = vol x y := by
  simp_rw [Real.vol_def, ENNReal.ofReal_toReal_eq_iff, vol]
  apply measure_ball_ne_top

lemma le_upperRadius [FunctionDistances ℝ X] {Q : X → Θ X} {θ : Θ X} {x : X} {r : ℝ}
    (hr : dist_{x, r} θ (Q x) < 1) : ENNReal.ofReal r ≤ upperRadius Q θ x := by
  apply le_iSup₂ (f := fun r _ ↦ ENNReal.ofReal r) r hr

set_option backward.isDefEq.respectTransparency false in
private lemma carlesonOperatorIntegrand_const_smul [FunctionDistances ℝ X] (K : X → X → ℂ)
    (θ : Θ X) (R₁ R₂ : ℝ) (f : X → ℂ) (z : ℂ) :
    carlesonOperatorIntegrand (z • K) θ R₁ R₂ f = z • carlesonOperatorIntegrand K θ R₁ R₂ f := by
  unfold carlesonOperatorIntegrand
  ext x
  simp_rw [Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr with y
  ring

private lemma linearizedCarlesonOperator_const_smul [FunctionDistances ℝ X] (Q : X → Θ X)
    (K : X → X → ℂ) (f : X → ℂ) (z : ℂ) :
    linearizedCarlesonOperator Q (z • K) f = ‖z‖ₑ • linearizedCarlesonOperator Q K f := by
  unfold linearizedCarlesonOperator
  simp_rw [carlesonOperatorIntegrand_const_smul, Pi.smul_apply, smul_eq_mul, enorm_mul, ← mul_iSup]
  rfl

lemma carlesonOperator_const_smul [FunctionDistances ℝ X] (K : X → X → ℂ) (f : X → ℂ) (z : ℂ) :
    carlesonOperator (z • K) f = ‖z‖ₑ • carlesonOperator K f := by
  unfold carlesonOperator
  simp_rw [linearizedCarlesonOperator_const_smul, Pi.smul_apply, ← smul_iSup]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma nontangentialOperator_const_smul (z : ℂ) {K : X → X → ℂ} :
    nontangentialOperator (z • K) = ‖z‖ₑ • nontangentialOperator K := by
  unfold nontangentialOperator
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, enorm_mul, ← ENNReal.mul_iSup]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma carlesonOperatorIntegrand_const_smul' [FunctionDistances ℝ X] (K : X → X → ℂ)
    (θ : Θ X) (R₁ R₂ : ℝ) (f : X → ℂ) (z : ℂ) :
    carlesonOperatorIntegrand K θ R₁ R₂ (z • f) = z • carlesonOperatorIntegrand K θ R₁ R₂ f := by
  unfold carlesonOperatorIntegrand
  ext x
  simp_rw [Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr with y
  ring

private lemma linearizedCarlesonOperator_const_smul' [FunctionDistances ℝ X] (Q : X → Θ X)
    (K : X → X → ℂ) (f : X → ℂ) (z : ℂ) :
    linearizedCarlesonOperator Q K (z • f) = ‖z‖ₑ • linearizedCarlesonOperator Q K f := by
  unfold linearizedCarlesonOperator
  simp_rw [carlesonOperatorIntegrand_const_smul', Pi.smul_apply, smul_eq_mul, enorm_mul, ← mul_iSup]
  rfl

lemma carlesonOperator_const_smul' [FunctionDistances ℝ X] (K : X → X → ℂ) (f : X → ℂ) (z : ℂ) :
    carlesonOperator K (z • f) = ‖z‖ₑ • carlesonOperator K f := by
  unfold carlesonOperator
  simp_rw [linearizedCarlesonOperator_const_smul', Pi.smul_apply, ← smul_iSup]
  rfl


end DoublingMeasure

section Kernel

variable {X : Type*} {a : ℕ} {K : X → X → ℂ} [PseudoMetricSpace X] [MeasureSpace X]

open Function

lemma C_K_pos {a : ℝ} : 0 < C_K a := NNReal.rpow_pos (by norm_num)
lemma C_K_pos_real {a : ℝ} : 0 < (C_K a : ℝ) := C_K_pos

export IsOneSidedKernel (measurable_K norm_K_le_vol_inv norm_K_sub_le)

lemma isOneSidedKernel_const_smul {a : ℕ} {K : X → X → ℂ} [IsOneSidedKernel a K] {r : ℝ}
    (hr : |r| ≤ 1) :
    IsOneSidedKernel a (r • K) where
  measurable_K := measurable_K.const_smul r
  norm_K_le_vol_inv x y := by
    convert mul_le_mul hr (norm_K_le_vol_inv (K := K) x y) (norm_nonneg _) (zero_le_one' ℝ) using 1
    all_goals simp
  norm_K_sub_le h := by
    simp only [Pi.smul_apply, real_smul]
    rw [← one_mul (_ ^ _ * _), ← mul_sub, Complex.norm_mul, norm_real, Real.norm_eq_abs]
    gcongr
    exact norm_K_sub_le h

lemma MeasureTheory.stronglyMeasurable_K [IsOneSidedKernel a K] :
    StronglyMeasurable (uncurry K) :=
  measurable_K.stronglyMeasurable

lemma MeasureTheory.aestronglyMeasurable_K [IsOneSidedKernel a K] :
    AEStronglyMeasurable (uncurry K) :=
  measurable_K.aestronglyMeasurable

lemma measurable_K_left [IsOneSidedKernel a K] (y : X) : Measurable (K · y) :=
  measurable_K.of_uncurry_right

lemma measurable_K_right [IsOneSidedKernel a K] (x : X) : Measurable (K x) :=
  measurable_K.of_uncurry_left

lemma enorm_K_le_vol_inv [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOneSidedKernel a K] (x y : X) : ‖K x y‖ₑ ≤ (C_K a : ℝ≥0∞) / vol x y := by
  rw [← ofReal_norm, ← ofReal_vol, ← ofReal_coe_nnreal]
  refine le_trans ?_ (ofReal_div_le measureReal_nonneg)
  gcongr
  apply norm_K_le_vol_inv

lemma enorm_K_le_ball_complement [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOneSidedKernel a K] {r : ℝ} {x : X} {y : X} (hy : y ∈ (ball x r)ᶜ) :
    ‖K x y‖ₑ ≤ C_K a / volume (ball x r) := by
  apply le_trans (enorm_K_le_vol_inv x y)
  apply ENNReal.div_le_div_left (measure_mono (ball_subset_ball (by simpa [dist_comm] using hy)))

lemma enorm_K_le_ball_complement' [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOpenPosMeasure (volume : Measure X)] [IsOneSidedKernel a K] {r : ℝ} (hr : 0 < r)
    {x : X} {y : X} (hy : y ∈ (ball x r)ᶜ) :
    ‖K x y‖ₑ ≤ (C_K a / volume (ball x r)).toNNReal := by
  rw [ENNReal.coe_toNNReal ?ne_top]
  case ne_top =>
    rw [Ne, ENNReal.div_eq_top]
    push Not
    simp [ne_of_gt (measure_ball_pos volume x hr)]
  exact enorm_K_le_ball_complement hy

lemma enorm_K_sub_le [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOneSidedKernel a K] {x y y' : X} (h : 2 * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ₑ ≤ (edist y y' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y) := by
  simp_rw [← ofReal_norm, ← ofReal_vol, ← ofReal_coe_nnreal, edist_dist]
  calc
    _ ≤ ENNReal.ofReal ((dist y y' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / Real.vol x y)) := by
      gcongr; apply norm_K_sub_le h
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul']; swap
      · exact div_nonneg NNReal.zero_le_coe measureReal_nonneg
      gcongr
      · rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        gcongr
        apply ofReal_div_le (by positivity)
      · exact ofReal_div_le measureReal_nonneg

lemma integrableOn_K_mul [IsOpenPosMeasure (volume : Measure X)]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] [ProperSpace X] [IsOneSidedKernel a K]
    {f : X → ℂ} {s : Set X} (hf : IntegrableOn f s) (x : X) {r : ℝ} (hr : 0 < r)
    (hs : s ⊆ (ball x r)ᶜ) : IntegrableOn (K x * f) s := by
  use (measurable_K_right x).aemeasurable.restrict.mul hf.aemeasurable |>.aestronglyMeasurable
  exact (hasFiniteIntegral_def _ _).mpr <| calc
    _ = ∫⁻ y in s, ‖K x y‖ₑ * ‖f y‖ₑ := by simp
    _ ≤ ∫⁻ y in s, C_K a / volume (ball x r) * ‖f y‖ₑ := by
      exact setLIntegral_mono_ae (hf.aemeasurable.enorm.const_mul _) <| Filter.Eventually.of_forall
        fun y hy ↦ mul_le_mul_left (enorm_K_le_ball_complement (hs hy)) _
    _ = _ * ∫⁻ y in s, ‖f y‖ₑ := by exact lintegral_const_mul'' _ hf.aemeasurable.enorm
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.div_lt_top coe_ne_top (measure_ball_pos _ x hr).ne') hf.2

lemma integrableOn_K_Icc [IsOpenPosMeasure (volume : Measure X)]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] [ProperSpace X]
    [IsOneSidedKernel a K] {x : X} {r R : ℝ} (hr : r > 0) :
    IntegrableOn (K x) {y | dist x y ∈ Icc r R} volume := by
  rw [← mul_one (K x)]
  refine integrableOn_K_mul ?_ x hr ?_
  · have : {y | dist x y ∈ Icc r R} ⊆ closedBall x R := Annulus.cc_subset_closedBall
    exact integrableOn_const ((measure_mono this).trans_lt measure_closedBall_lt_top).ne
  · intro y hy; simp [hy.1, dist_comm y x]

end Kernel


section PseudoMetricSpace

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X]

section Iterate

variable [CompatibleFunctions ℝ X (defaultA a)]

lemma le_cdist_iterate {x : X} {r : ℝ} (hr : 0 ≤ r) (f g : Θ X) (k : ℕ) :
    2 ^ k * dist_{x, r} f g ≤ dist_{x, (defaultA a) ^ k * r} f g := by
  induction k with
  | zero => rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans 2 * dist_{x, (defaultA a) ^ k * r} f g
    · rw [pow_succ', mul_assoc]
      exact (mul_le_mul_iff_right₀ zero_lt_two).mpr ih
    · convert le_cdist (ball_subset_ball _) using 1
      · exact dist_congr rfl (by rw [← mul_assoc, pow_succ'])
      · nth_rw 1 [← one_mul ((defaultA a) ^ k * r)]; gcongr
        rw [← Nat.cast_one, Nat.cast_le]; exact Nat.one_le_two_pow

lemma cdist_le_iterate {x : X} {r : ℝ} (hr : 0 < r) (f g : Θ X) (k : ℕ) :
    dist_{x, 2 ^ k * r} f g ≤ (defaultA a) ^ k * dist_{x, r} f g := by
  induction k with
  | zero => simp_rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans defaultA a * dist_{x, 2 ^ k * r} f g
    · convert cdist_le _ using 1
      · exact dist_congr rfl (by ring)
      · rw [dist_self]; positivity
    · replace ih := (mul_le_mul_iff_right₀ (show 0 < (defaultA a : ℝ) by positivity)).mpr ih
      rwa [← mul_assoc, ← pow_succ'] at ih

lemma cdist_le_mul_cdist {x x' : X} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (f g : Θ X) :
    dist_{x', r'} f g ≤ As (defaultA a) ((r' + dist x' x) / r) * dist_{x, r} f g := by
  calc
    dist_{x', r'} f g ≤ dist_{x, 2 ^ _ * r} f g := ?e
    _ ≤ _ := cdist_le_iterate hr f g _
  case e =>
    apply cdist_mono
    apply ball_subset_ball'
    calc
      r' + dist x' x = (r' + dist x' x) / r * r := div_mul_cancel₀ _ hr.ne' |>.symm
      _ ≤ 2 ^ ⌈Real.logb 2 ((r' + dist x' x) / r)⌉₊ * r := by
        gcongr
        apply Real.le_pow_natCeil_logb (by norm_num) (by positivity)

lemma ballsCoverBalls_iterate_nat {x : X} {d r : ℝ} {n : ℕ} :
    BallsCoverBalls (WithFunctionDistance x d) (2 ^ n * r) r (defaultA a ^ n) :=
  CompatibleFunctions.allBallsCoverBalls.pow r

lemma ballsCoverBalls_iterate {x : X} {d R r : ℝ} (hr : 0 < r) :
    BallsCoverBalls (WithFunctionDistance x d) R r (defaultA a ^ ⌈Real.logb 2 (R / r)⌉₊) :=
  CompatibleFunctions.allBallsCoverBalls.ballsCoverBalls one_lt_two hr

end Iterate

section MeasQ

variable [KernelProofData a K] {Q : SimpleFunc X (Θ X)}

@[fun_prop]
lemma measurable_Q₂ : Measurable fun p : X × X ↦ Q p.1 p.2 := fun s meass ↦ by
  have : (fun p : X × X ↦ (Q p.1) p.2) ⁻¹' s = ⋃ θ ∈ Q.range, (Q ⁻¹' {θ}) ×ˢ (θ ⁻¹' s) := by
    ext ⟨x, y⟩
    push _ ∈ _
    simp
  rw [this]
  exact Q.range.measurableSet_biUnion fun θ _ ↦
    (Q.measurableSet_fiber θ).prod (meass.preimage (map_continuous θ).measurable)

lemma stronglyMeasurable_Q₂ : StronglyMeasurable fun p : X × X ↦ Q p.1 p.2 :=
  measurable_Q₂.stronglyMeasurable

@[fun_prop]
lemma aestronglyMeasurable_Q₂ : AEStronglyMeasurable fun p : X × X ↦ Q p.1 p.2 :=
  measurable_Q₂.aestronglyMeasurable

@[fun_prop]
lemma measurable_Q₁ (x : X) : Measurable (Q x) :=
  let Q' : X → X → ℝ := fun x' y ↦ Q x' y
  have : (fun y ↦ Q' x y) = Q x := rfl
  this ▸ measurable_Q₂.of_uncurry_left

end MeasQ

end PseudoMetricSpace
