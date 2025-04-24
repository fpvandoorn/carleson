import Carleson.ToMathlib.RealInterpolation.InterpolatedExponents
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! This file contains a proof of the Marcinkiewisz real interpolation theorem.
    The proof roughly follows Folland, Real Analysis. Modern Techniques and Their Applications,
    section 6.4, theorem 6.28, but a different truncation is used, and some estimates instead
    follow the technique as e.g. described in [Duoandikoetxea, Fourier Analysis, 2000].

    The file consists of the following sections:
    - (in `InterpolateExponents.lean`) Convenience results for working with (interpolated) exponents
    - (in `InterpolateExponents.lean`) Results about the particular choice of exponent
    - Interface for using cutoff functions
    - Results about the particular choice of scale
    - Some tools for measure theory computations
    - Results about truncations of a function
    - Measurability properties of truncations
    - Truncations and Lp spaces
    - Some results about the integrals of truncations
    - (in `Minkowski.lean`) Minkowski's integral inequality
    - (in `Minkowski.lean`) Apply Minkowski's integral inequality to truncations
    - (in `Minkowski.lean`) Weaktype estimates applied to truncations
    - (in `Final.lean`) Definitions for the main proof
    - (in `Final.lean`) Proof of the real interpolation theorem
-/

noncomputable section

open ENNReal Real Set MeasureTheory

-- Note (F): can we make `t : ℝ≥0∞` for a large part of the proof?
variable {p₀ q₀ p₁ q₁ p q : ℝ≥0∞} {t : ℝ}

/-! ## Interface for using cutoff functions -/
section

open Real Set

/-- A ScaledPowerFunction is meant to represent a function of the form `t ↦ (t / d)^σ`,
    where `d` is strictly positive and either `σ > 0` or `σ < 0`. -/
structure ScaledPowerFunction where
  σ : ℝ
  d : ℝ
  hd : 0 < d
  hσ : (0 < σ) ∨ (σ < 0)

/-- A ToneCouple is an couple of two monotone functions that are practically inverses of each
    other. It is used in the proof of the real interpolation theorem.

    Note: originally it seemed useful to make the possible choice of this function general
    in the proof of the real inteprolation theorem. However, in the end really only one
    function works for all the different cases. This infrastructure, however, could potentially
    still be useful, if one would like to try to improve the constant. -/
structure ToneCouple where
  ton : ℝ → ℝ
  inv : ℝ → ℝ
  mon : Bool
  ton_is_ton : if mon then StrictMonoOn ton (Ioi 0) else StrictAntiOn ton (Ioi 0)
  ran_ton : ∀ t ∈ Ioi (0 : ℝ), ton t ∈ Ioi 0
  ran_inv : ∀ t ∈ Ioi (0 : ℝ), inv t ∈ Ioi 0
  inv_pf : if mon
      then ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ s < inv t) ∧ (t < ton s ↔ inv t < s)
      else ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ inv t < s) ∧ (t < ton s ↔ s < inv t)

/-- A scaled power function gives rise to a ToneCouple. -/
def spf_to_tc (spf : ScaledPowerFunction) : ToneCouple where
  ton := fun s : ℝ ↦ (s / spf.d) ^ spf.σ
  inv := fun t : ℝ ↦ spf.d * t ^ spf.σ⁻¹
  mon := if 0 < spf.σ then true else false
  ran_ton := fun t ht ↦ rpow_pos_of_pos (div_pos ht spf.hd) _
  ran_inv := fun t ht ↦ mul_pos spf.hd (rpow_pos_of_pos ht spf.σ⁻¹)
  ton_is_ton := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte]
      intro s (hs : 0 < s) t (ht : 0 < t) hst
      refine (rpow_lt_rpow_iff ?_ ?_ sgn_σ).mpr ?_
      · exact (div_pos hs spf.hd).le
      · exact (div_pos ht spf.hd).le
      · exact div_lt_div_of_pos_right hst spf.hd
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro s (hs : 0 < s) t (ht : 0 < t) hst
      rcases spf.hσ with σ_pos | σ_neg
      · exact (sgn_σ σ_pos).elim
      · simp only
        exact (Real.rpow_lt_rpow_iff_of_neg (div_pos ht spf.hd)
          (div_pos hs spf.hd) σ_neg).mpr (div_lt_div_of_pos_right hst spf.hd)
  inv_pf := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte, mem_Ioi]
      refine fun s hs t ht => ⟨?_, ?_⟩
      · rw [← Real.lt_rpow_inv_iff_of_pos (div_nonneg hs.le spf.hd.le) ht.le sgn_σ,
        ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']
      · rw [← Real.rpow_inv_lt_iff_of_pos ht.le (div_nonneg hs.le spf.hd.le)
          sgn_σ, ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']
    · simp only [↓reduceIte, mem_Ioi]
      intro s hs t ht
      rcases spf.hσ with σ_pos | σ_neg
      · contradiction
      · constructor
        · rw [← Real.rpow_inv_lt_iff_of_neg ht (div_pos hs spf.hd) σ_neg,
            ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']
        · rw [← Real.lt_rpow_inv_iff_of_neg (div_pos hs spf.hd) ht σ_neg,
            ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']

end

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents
    ComputationsChoiceExponent

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  [TopologicalSpace E₁] [ENormedAddCommMonoid E₁]
  {f : α → E₁} {t : ℝ}

/-! ## Results about the particular choice of scale

    The proof of the real interpolation theorem will estimate
    `distribution (trunc f A(t)) t` and `distribution (truncCompl f A(t)) t` for a
    function `A`. The function `A` can be given a closed-form expression that works for
    _all_ cases in the real interpolation theorem, because of the computation rules available
    for elements in `ℝ≥0∞` that avoid the need for a limiting procedure, e.g. `⊤⁻¹ = 0`.

    The function `A` will be of the form `A(t) = (t / d) ^ σ` for particular choices of `d` and
    `σ`. This section contatins results about the scale `d`.
-/
namespace ChoiceScale

def d := ENNReal.toReal
    (C₀ ^ (q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (eLpNorm f p μ ^ p.toReal) ^
      (p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (C₁ ^ (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (eLpNorm f p μ ^ p.toReal) ^
      (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal))))

lemma d_pos_aux₀ (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    0 < eLpNorm f p μ ^ p.toReal :=
  ENNReal.rpow_pos (pos_of_Ioo hF) (ne_top_of_Ioo hF)

lemma d_ne_top_aux₀ {b : ℝ} {F : ℝ≥0∞} (hF : F ∈ Ioo 0 ⊤) : F ^ b ≠ ⊤ :=
  rpow_ne_top' hF.1.ne' hF.2.ne

lemma d_ne_zero_aux₀ {b : ℝ} (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (eLpNorm f p μ ^ p.toReal) ^ b ≠ 0 :=
  (ENNReal.rpow_pos (d_pos_aux₀ hF) (d_ne_top_aux₀ hF)).ne'

lemma d_ne_zero_aux₁ {C : ℝ≥0} {c : ℝ} (hC : 0 < C) :
    (ENNReal.ofNNReal C) ^ c ≠ 0 :=
  (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hC) coe_ne_top).ne'

lemma d_ne_zero_aux₂ {C : ℝ≥0} {b c : ℝ} (hC : 0 < C)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    C ^ c * (eLpNorm f p μ ^ p.toReal) ^ b ≠ 0 :=
  (ENNReal.mul_pos (d_ne_zero_aux₁ hC) (d_ne_zero_aux₀ hF)).ne'

lemma d_ne_top_aux₁ {C : ℝ≥0} {c : ℝ} (hC : 0 < C) :
    (ENNReal.ofNNReal C) ^ c ≠ ⊤ :=
  rpow_ne_top' (ENNReal.coe_pos.mpr hC).ne' coe_ne_top

lemma d_ne_top_aux₂ {b : ℝ} (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (eLpNorm f p μ ^ p.toReal) ^ b ≠ ⊤ :=
  rpow_ne_top' (d_pos_aux₀ hF).ne' (d_ne_top_aux₀ hF)

lemma d_ne_top_aux₃ {C : ℝ≥0} {b c : ℝ} (hC : 0 < C)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    C ^ c * (eLpNorm f p μ ^ p.toReal) ^ b ≠ ⊤ :=
  mul_ne_top (d_ne_top_aux₁ hC) (d_ne_top_aux₂ hF)

lemma d_ne_zero_aux₃ {b₀ c₀ b₁ c₁ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (C₀ ^ c₀ * (eLpNorm f p μ ^ p.toReal) ^ b₀) /
    (C₁ ^ c₁ * (eLpNorm f p μ ^ p.toReal) ^ b₁) ≠ 0 := by
  refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
  · apply d_ne_zero_aux₂ <;> try assumption
  · apply d_ne_top_aux₃ <;> try assumption

lemma d_ne_top_aux₄ {b₀ c₀ b₁ c₁ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (C₀ ^ c₀ * (eLpNorm f p μ ^ p.toReal) ^ b₀) /
    (C₁ ^ c₁ * (eLpNorm f p μ ^ p.toReal) ^ b₁) ≠ ⊤ := by
  refine (div_lt_top ?_ ?_).ne
  · apply d_ne_top_aux₃ <;> assumption
  · apply d_ne_zero_aux₂ <;> assumption

-- If the `p`-norm of `f` is positive and finite, then `d` is positive
lemma d_pos (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
  @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f > 0 :=
toReal_pos (d_ne_zero_aux₃ hC₀ hC₁ hF) (d_ne_top_aux₄ hC₀ hC₁ hF)

lemma d_eq_top₀ (hp₀ : 0 < p₀) (hq₁ : 0 < q₁) (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ = ⊤) (hq₀q₁ : q₀ ≠ q₁):
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f =
    (↑C₀ ^ p₀.toReal * eLpNorm f p μ ^ p.toReal).toReal ^ p₀.toReal⁻¹ := by
  unfold d
  rw [hq₀']
  simp only [inv_top, toReal_zero, sub_zero, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    div_one]
  rw [mul_div_cancel_right₀]
  · rw [div_eq_mul_inv, mul_inv_cancel₀, ENNReal.rpow_one]
    · rw [toReal_rpow, ENNReal.mul_rpow_of_nonneg]
      · rw [ENNReal.rpow_rpow_inv, toReal_inv]
        exact (exp_toReal_pos hp₀ hp₀').ne'
      · positivity
    · exact (inv_toReal_pos_of_ne_top hq₁ ((hq₀' ▸ hq₀q₁).symm)).ne'
  · exact (inv_toReal_pos_of_ne_top hq₁ ((hq₀' ▸ hq₀q₁).symm)).ne'

lemma d_eq_top₁ (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ = ⊤)
    (hq₀q₁ : q₀ ≠ q₁) (hC₁ : 0 < C₁) :
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f =
    (↑C₁ ^ p₁.toReal * eLpNorm f p μ ^ p.toReal).toReal ^ p₁.toReal⁻¹ := by
  unfold d
  rw [hq₁']
  simp only [inv_top, toReal_zero, zero_sub, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    one_div]
  rw [div_neg, div_neg]
  rw [mul_div_cancel_right₀]
  · rw [div_eq_mul_inv, mul_inv_cancel₀, ENNReal.rpow_neg_one]
    · rw [toReal_rpow, ENNReal.mul_rpow_of_nonneg]
      · rw [ENNReal.rpow_rpow_inv, ← toReal_inv, ENNReal.mul_inv, inv_inv]
        · rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, toReal_inv, mul_neg, mul_one, neg_neg,
            toReal_mul, coe_toReal]
        · left; exact ENNReal.inv_ne_zero.mpr coe_ne_top
        · left; exact inv_ne_top.mpr <| (ENNReal.coe_pos.mpr hC₁).ne'
        · exact (exp_toReal_pos hp₁ hp₁').ne'
      · positivity
    · exact (inv_toReal_pos_of_ne_top hq₀ (hq₁' ▸ hq₀q₁)).ne'
  · exact (inv_toReal_pos_of_ne_top hq₀ (hq₁' ▸ hq₀q₁)).ne'

lemma d_eq_top_of_eq (hC₁ : 0 < C₁) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hq₀' : q₀ ≠ ⊤)
(hp₀': p₀ ≠ ⊤) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ = p₁) (hpp₀: p = p₀) (hq₁' : q₁ = ⊤) :
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f = (C₁ * eLpNorm f p μ).toReal := by
  rw [d_eq_top₁, ← hp₀p₁, hpp₀] <;> try assumption
  on_goal 1 => rw [toReal_rpow, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_rpow_inv, ENNReal.rpow_rpow_inv]
  · exact exp_toReal_ne_zero' hp₀ hp₀'
  · exact exp_toReal_ne_zero' hp₀ hp₀'
  · positivity
  · exact hp₀p₁ ▸ hp₀'
  · exact hq₁' ▸ hq₀'

lemma d_eq_top_top (hq₀ : 0 < q₀) (hq₀q₁ : q₀ ≠ q₁) (hp₁' : p₁ = ⊤) (hq₁' : q₁ = ⊤) :
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f = C₁ := by
  unfold d
  rw [hp₁', hq₁']
  simp only [inv_top, toReal_zero, zero_sub, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    zero_mul, one_div]
  rw [div_neg, div_eq_mul_inv, mul_inv_cancel₀]
  · rw [ENNReal.rpow_neg, ENNReal.rpow_one, inv_inv, coe_toReal]
  · exact (toReal_pos (ENNReal.inv_ne_zero.mpr (hq₁' ▸ hq₀q₁)) (ENNReal.inv_ne_top.mpr hq₀.ne')).ne'

/-- The particular choice of scaled power function that works in the proof of the
    real interpolation theorem. -/
def spf_ch (ht : t ∈ Ioo 0 1) (hq₀q₁ : q₀ ≠ q₁) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    ScaledPowerFunction where
  σ := ζ p₀ q₀ p₁ q₁ t
  d := @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f
  hσ := lt_or_gt_of_ne <| Ne.symm <| (ζ_ne_zero ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁)
  hd := d_pos hC₀ hC₁ hF

end ChoiceScale

end

noncomputable section

open NNReal ENNReal MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'}
  {f : α → E₁} {t : ℝ}

/-! ## Some tools for measure theory computations
    A collection of small lemmas to help with integral manipulations.
-/
namespace MeasureTheory

-- TODO: change lhs and rhs?
-- TODO: rewrite the condition in filter form?
lemma lintegral_double_restrict_set {A B: Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := setLIntegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]

lemma measure_preserving_shift {a : ℝ} :
    MeasurePreserving (fun x ↦ a + x) volume volume :=
  measurePreserving_add_left volume a

lemma measureable_embedding_shift {a : ℝ} : MeasurableEmbedding (fun x ↦ a + x) :=
  measurableEmbedding_addLeft a

lemma measure_preserving_scaling {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun x ↦ a * x) volume ((ENNReal.ofReal |a⁻¹|) • volume) :=
  { measurable := measurable_const_mul a, map_eq := Real.map_volume_mul_left ha }

lemma lintegral_shift (f : ℝ → ENNReal) {a : ℝ} :
    ∫⁻ x : ℝ, (f (x + a)) = ∫⁻ x : ℝ, f x :=
  lintegral_add_right_eq_self f a

lemma lintegral_shift' (f : ℝ → ENNReal) {a : ℝ} {s : Set ℝ}:
    ∫⁻ (x : ℝ) in (fun z : ℝ ↦ z + a)⁻¹' s, f (x + a) = ∫⁻ (x : ℝ) in s, f x := by
  rw [(measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight a)]

lemma lintegral_add_right_Ioi (f : ℝ → ENNReal) {a b : ℝ} :
    ∫⁻ (x : ℝ) in Ioi (b - a), f (x + a) = ∫⁻ (x : ℝ) in Ioi b, f x := by
  nth_rewrite 2 [← lintegral_shift' (a := a)]
  simp

lemma lintegral_scale_constant (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0):
    ∫⁻ x : ℝ, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x := by
  rw [← smul_eq_mul, ← @lintegral_smul_measure, MeasurePreserving.lintegral_comp_emb]
  · exact measure_preserving_scaling h
  · exact measurableEmbedding_mulLeft₀ h

lemma lintegral_scale_constant_preimage (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0) {s : Set ℝ} :
    ∫⁻ x : ℝ in (fun z : ℝ ↦ a * z)⁻¹' s, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in s, f x := by
  rw [← smul_eq_mul, ← lintegral_smul_measure,
    (measure_preserving_scaling h).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft₀ h),
    Measure.restrict_smul]

lemma lintegral_scale_constant_halfspace (f: ℝ → ENNReal) {a : ℝ} (h : 0 < a) :
    ∫⁻ x : ℝ in Ioi 0, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [← lintegral_scale_constant_preimage f h.ne']
  have h₀ : (fun z ↦ a * z) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp [mul_pos_iff_of_pos_left h]
  rw [h₀]

lemma lintegral_scale_constant_halfspace' {f: ℝ → ENNReal} {a : ℝ} (h : 0 < a) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ in Ioi 0, f (a*x) = ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [lintegral_scale_constant_halfspace f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a),
    abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h.ne')]
  simp

lemma lintegral_scale_constant' {f: ℝ → ENNReal} {a : ℝ} (h : a ≠ 0):
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a), abs_inv,
      mul_inv_cancel₀ (abs_ne_zero.mpr h)]
  simp

-- local convenience function
lemma lintegral_rw_aux {g : ℝ → ℝ≥0∞} {f₁ f₂ : ℝ → ℝ≥0∞} {A : Set ℝ}
    (heq : f₁ =ᶠ[ae (volume.restrict A)] f₂) :
    ∫⁻ s in A, g s * f₁ s = ∫⁻ s in A, g s * f₂ s :=
  (lintegral_rw₂ (Filter.EventuallyEq.refl (ae (volume.restrict A)) g) heq HMul.hMul)

lemma power_aux {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ (p + q)) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal s ^ p * ENNReal.ofReal s ^ q ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : 0 < s)
  rw [ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs,
    ← ofReal_mul (by positivity), ← Real.rpow_add hs]

lemma power_aux_2 {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal (s ^ (p + q))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p) * ENNReal.ofReal (s ^ q) ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : 0 < s)
  rw [← ofReal_mul (by positivity), ← Real.rpow_add hs]

lemma ofReal_rpow_of_pos_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    with s (hs : 0 < s) using ofReal_rpow_of_pos hs

lemma extract_constant_double_integral_rpow {f : ℝ → ℝ → ℝ≥0∞} {q : ℝ} (hq : q ≥ 0) {a : ℝ≥0∞}
    (ha : a ≠ ⊤):
    ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, a * f s t) ^ q =
    a ^ q * ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, f s t) ^ q := by
  simp_rw [← lintegral_const_mul' _ _ (rpow_ne_top_of_nonneg hq ha),
    ← ENNReal.mul_rpow_of_nonneg _ _ hq, lintegral_const_mul' a _ ha]

lemma ofReal_rpow_rpow_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    with s (hs : 0 < s) using ofReal_rpow_of_pos hs

lemma lintegral_rpow_of_gt {β γ : ℝ} (hβ : 0 < β) (hγ : -1 < γ) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / (γ + 1)) := by
  have hγ2 : 0 < γ + 1 := by linarith
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hβ.le, integral_rpow]
    · rw [Real.zero_rpow hγ2.ne', sub_zero]
    · exact Or.inl hγ
  · apply (@intervalIntegral.intervalIntegrable_rpow' 0 β γ ?_).1
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
      with s hs using Real.rpow_nonneg hs.1.le γ

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0} {a : ℝ}
  {μ : Measure α} {ν : Measure α'}
  [NormedAddCommGroup E₁]
  {f : α → E₁} {s t : ℝ}

/-! ## Results about truncations of a function
-/
namespace MeasureTheory

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E₁) (t : ℝ) (x : α) : E₁ := if ‖f x‖ ≤ t then f x else 0

/-- The complement of a `t`-truncation of a function `f`. -/
def truncCompl (f : α → E₁) (t : ℝ) : α → E₁ := f - trunc f t

lemma truncCompl_eq {f : α → E₁} :
    truncCompl f t = fun x ↦ if t < ‖f x‖ then f x else 0 := by
  ext x
  simp_rw [truncCompl, Pi.sub_apply, trunc, ← not_lt, ite_not, apply_ite (f x - ·), sub_zero, sub_self]

/-- A function to deal with truncations and complement of truncations in one go. -/
def trnc (j : Bool) (f : α → E₁) (t : ℝ) : α → E₁ :=
  match j with
  | false => f - trunc f t
  | true => trunc f t

/-- A function is the complement if its truncation and the complement of the truncation. -/
lemma trunc_buildup : f = trunc f t + truncCompl f t := by
  ext x; simp [trunc, truncCompl]

/-- If the truncation parameter is non-positive, the truncation vanishes. -/
lemma trunc_of_nonpos {f : α → E₁} {a : ℝ} (ha : a ≤ 0) :
    trunc f a = 0 := by
  unfold trunc
  ext x
  split_ifs
  · dsimp only [Pi.zero_apply]
    apply norm_eq_zero.mp
    · have : ‖f x‖ ≥ 0 := norm_nonneg _
      linarith []
  · rfl

/-- If the truncation parameter is non-positive, the complement of the truncation is the
    function itself. -/
lemma truncCompl_of_nonpos {f : α → E₁} {a : ℝ} (ha : a ≤ 0) :
    truncCompl f a = f := by
  rw [truncCompl_eq]
  ext x
  dsimp only [Pi.zero_apply]
  split_ifs
  · rfl
  · apply (norm_eq_zero.mp ?_).symm
    have : ‖f x‖ ≥ 0 := norm_nonneg _
    linarith

/-! ## Measurability properties of truncations -/

-- @[measurability, fun_prop]
-- lemma _root_.Measurable.trunc [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : Measurable f) : Measurable (trunc f t) := by
--   refine hf.ite (measurableSet_le ?_ ?_) measurable_const <;> fun_prop

-- @[measurability, fun_prop]
-- lemma _root_.Measurable.truncCompl [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : Measurable f) :
--     Measurable (truncCompl f t) := by
--   rw [truncCompl_eq]
--   apply Measurable.ite ?_ hf measurable_const
--   exact measurableSet_lt measurable_const hf.norm

@[measurability]
protected lemma StronglyMeasurable.trunc
    (hf : StronglyMeasurable f) : StronglyMeasurable (trunc f t) :=
  StronglyMeasurable.ite (measurableSet_le hf.norm stronglyMeasurable_const) hf
    stronglyMeasurable_const

@[measurability]
protected lemma StronglyMeasurable.truncCompl
    (hf : StronglyMeasurable f) : StronglyMeasurable (truncCompl f t) := by
  rw [truncCompl_eq]
  exact hf.ite (measurableSet_lt stronglyMeasurable_const hf.norm) stronglyMeasurable_const

-- @[measurability, fun_prop]
-- lemma AEMeasurable.trunc [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : AEMeasurable f μ) : AEMeasurable (trunc f t) μ := by
--   rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
--   exists (trunc g t)
--   constructor
--   · apply wg1.indicator (s := {x | ‖g x‖ ≤ t}) (measurableSet_le wg1.norm measurable_const)
--   apply measure_mono_null ?_ wg2
--   intro x
--   contrapose
--   simp only [mem_compl_iff, mem_setOf_eq, not_not]
--   intro h₂
--   unfold trunc
--   rewrite [h₂]
--   rfl

-- @[measurability, fun_prop]
-- lemma AEMeasurable.truncCompl [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : AEMeasurable f μ) : AEMeasurable (truncCompl f t) μ := by
--   rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
--   exists (truncCompl g t)
--   constructor
--   · unfold truncCompl
--     rw [truncCompl_eq]
--     exact wg1.indicator (s := {x | t < ‖g x‖}) (measurableSet_lt measurable_const wg1.norm)
--   · apply measure_mono_null ?_ wg2
--     intro x
--     contrapose
--     simp only [mem_compl_iff, mem_setOf_eq, not_not]
--     intro f_eq_g; unfold truncCompl; unfold trunc; dsimp only [Pi.sub_apply]; rw [f_eq_g]

@[measurability]
nonrec lemma AEStronglyMeasurable.trunc
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (trunc f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc g t)
  constructor
  · exact wg1.indicator (s := {x | ‖g x‖ ≤ t}) (wg1.norm.measurableSet_le stronglyMeasurable_const)
  · refine measure_mono_null (fun x ↦ ?_) wg2
    contrapose
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    intro h₂
    unfold trunc
    rw [h₂]

@[measurability]
nonrec lemma AEStronglyMeasurable.truncCompl
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (truncCompl f t) μ := by
  simp_rw [truncCompl]; exact hf.sub hf.trunc

@[measurability]
lemma aestronglyMeasurable_trnc {j : Bool}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trnc j f t) μ :=
  j.rec (.truncCompl hf) (.trunc hf)

lemma trunc_le {f : α → E₁} {a : ℝ} (x : α) :
    ‖trunc f a x‖ ≤ max 0 a := by
  unfold trunc
  split_ifs with h
  · rcases (lt_or_le a 0) with a_lt_0 | _
    · exact Trans.trans (Trans.trans h a_lt_0.le) (le_max_left 0 a)
    · exact Trans.trans h (le_max_right 0 a)
  · simp

/-- A small lemma that is helpful for rewriting -/
lemma coe_coe_eq_ofReal (a : ℝ) : ofNNReal a.toNNReal = ENNReal.ofReal a := by rfl

lemma trunc_eLpNormEssSup_le {f : α → E₁} {a : ℝ} :
    eLpNormEssSup (trunc f a) μ ≤ ENNReal.ofReal (max 0 a) := by
  refine essSup_le_of_ae_le _ (ae_of_all _ fun x ↦ ?_)
  simp only [enorm_eq_nnnorm, ← norm_toNNReal, coe_coe_eq_ofReal]
  exact ofReal_le_ofReal (trunc_le x)

lemma trunc_mono {f : α → E₁} {a b : ℝ} (hab : a ≤ b) {x : α} : ‖trunc f a x‖ ≤ ‖trunc f b x‖ := by
  unfold trunc
  split_ifs
  · rfl
  · linarith
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_refl _

/-- The norm of the truncation is monotone in the truncation parameter -/
lemma eLpNorm_trunc_mono {f : α → E₁} :
    Monotone fun s ↦ eLpNorm (trunc f s) p μ :=
  fun _a _b hab ↦ eLpNorm_mono fun _x ↦ trunc_mono hab

lemma trunc_buildup_norm {f : α → E₁} {x : α} :
    ‖trunc f t x‖ + ‖truncCompl f t x‖ = ‖f x‖ := by
  simp only [trunc, truncCompl, Pi.sub_apply]; split_ifs with h <;> simp

lemma trunc_le_func {f : α → E₁} {x : α} : ‖trunc f t x‖ ≤ ‖f x‖ := by
  unfold trunc; split_ifs <;> simp

lemma truncCompl_le_func {f : α → E₁} {x : α} :
    ‖(truncCompl f t) x‖ ≤ ‖f x‖ := by
  rw [truncCompl_eq]; dsimp only; split_ifs <;> simp

lemma truncCompl_anti {f : α → E₁} {x : α} (hab : t ≤ s) :
    ‖truncCompl f s x‖ ≤ ‖truncCompl f t x‖ := by
  have obs : ‖trunc f t x‖ + ‖(truncCompl f t) x‖ = ‖trunc f s x‖ + ‖(truncCompl f s) x‖ := by
    simp_rw [trunc_buildup_norm]
  have : ‖trunc f t x‖ ≤ ‖trunc f s x‖ := trunc_mono hab
  linarith

/-- The norm of the complement of the truncation is antitone in the truncation parameter -/
lemma eLpNorm_truncCompl_anti {f : α → E₁} :
    Antitone (fun s ↦ eLpNorm (truncCompl f s) p μ) :=
  fun _a _b hab ↦ eLpNorm_mono (fun _ ↦ truncCompl_anti hab)

/-- The norm of the truncation is meaurable in the truncation parameter -/
@[measurability, fun_prop]
lemma eLpNorm_trunc_measurable :
    Measurable (fun s ↦ eLpNorm (trunc f s) p μ) :=
  eLpNorm_trunc_mono.measurable

/-- The norm of the complement of the truncation is measurable in the truncation parameter -/
@[measurability, fun_prop]
lemma eLpNorm_truncCompl_measurable :
    Measurable (fun s ↦ eLpNorm (truncCompl f s) p μ) :=
  eLpNorm_truncCompl_anti.measurable

lemma trnc_le_func {j : Bool} {f : α → E₁} {a : ℝ} {x : α} :
    ‖trnc j f a x‖ ≤ ‖f x‖ := by
  unfold trnc trunc
  rcases j
  · dsimp only [Pi.sub_apply]
    split_ifs <;> simp
  · dsimp only
    split_ifs <;> simp

-- /-- ## Distribution functions of truncations -/

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (trunc f t) (.trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

/-! ## Truncations and L-p spaces -/

lemma power_estimate {a b t γ : ℝ} (hγ : 0 < γ) (htγ : γ ≤ t) (hab : a ≤ b) :
    (t / γ) ^ a ≤ (t / γ) ^ b := by
  gcongr
  exact (one_le_div hγ).mpr htγ

lemma power_estimate' {a b t γ : ℝ} (ht : 0 < t) (htγ : t ≤ γ) (hab: a ≤ b) :
    (t / γ) ^ b ≤ (t / γ) ^ a := by
  have γ_pos : 0 < γ := lt_of_lt_of_le ht htγ
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos ht (γ_pos)) (div_le_one_of_le₀ htγ γ_pos.le) hab

lemma rpow_le_rpow_of_exponent_le_base_le {a b t γ : ℝ} (ht : 0 < t) (htγ : t ≤ γ) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ b) ≤ ENNReal.ofReal (t ^ a) * ENNReal.ofReal (γ ^ (b - a)) := by
  rw [mul_comm]
  have γ_pos : 0 < γ := lt_of_lt_of_le ht htγ
  rw [Real.rpow_sub γ_pos]
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (γ ^ (-b) )) ?_ coe_ne_top).mp ?_
  · exact (ofReal_pos.mpr (Real.rpow_pos_of_pos γ_pos (-b))).ne'
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, neg_add_cancel,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul (by positivity)]
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    exact ofReal_le_ofReal (power_estimate' ht htγ hab)

-- TODO: there is a lot of overlap between above proof and below
lemma rpow_le_rpow_of_exponent_le_base_ge {a b t γ : ℝ} (hγ : 0 < γ) (htγ : γ ≤ t) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ a) ≤ ENNReal.ofReal (t ^ b) * ENNReal.ofReal (γ ^ (a - b)) := by
  rw [mul_comm]
  have t_pos : 0 < t := gt_of_ge_of_gt htγ hγ
  rw [Real.rpow_sub hγ]
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (γ ^ (-a) )) ?_ coe_ne_top).mp ?_
  · exact (ofReal_pos.mpr (Real.rpow_pos_of_pos hγ (-a))).ne'
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, neg_add_cancel,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul (by positivity)]
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    exact ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le ((one_le_div hγ).mpr htγ) hab)

lemma trunc_preserves_Lp {p : ℝ≥0∞} (hf : MemLp f p μ) : MemLp (trunc f t) p μ := by
  refine ⟨hf.1.trunc, lt_of_le_of_lt (eLpNorm_mono_ae (ae_of_all _ ?_)) hf.2⟩
  intro x
  unfold trunc
  split_ifs with is_fx_le_a <;> simp

-- lemma eLpNorm_truncCompl_le {p : ℝ≥0∞} :
--     eLpNorm (truncCompl f t) p μ ≤ eLpNorm f p μ :=
--   eLpNorm_mono (fun _ ↦ truncCompl_le_func)

lemma truncCompl_preserves_Lp {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp (truncCompl f t) p μ :=
  MemLp.sub hf (trunc_preserves_Lp hf)

lemma estimate_eLpNorm_truncCompl {p q : ℝ≥0∞} [MeasurableSpace E₁] [BorelSpace E₁]
    (hp : p ≠ ⊤) (hpq : q ∈ Ioo 0 p) (hf : AEMeasurable f μ) (ha : 0 < a) :
    eLpNorm (truncCompl f a) q μ ^ q.toReal ≤
    ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
    eLpNorm f p μ ^ p.toReal := by
  unfold eLpNorm eLpNorm'
  have q_ne_top: q ≠ ⊤ := hpq.2.ne_top
  have p_ne_zero : p ≠ 0 := (lt_trans hpq.1 hpq.2).ne'
  have q_ne_zero : q ≠ 0 := hpq.1.ne'
  have q_toReal_pos : 0 < q.toReal := exp_toReal_pos hpq.1 q_ne_top
  split_ifs
  · contradiction
  · calc
    _ = ∫⁻ x : α in {x | a < ‖f x‖}, ‖(truncCompl f a) x‖ₑ ^ q.toReal ∂μ := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      · apply (setLIntegral_eq_of_support_subset _).symm
        unfold Function.support
        intro x
        rw [truncCompl_eq]
        dsimp only [Pi.sub_apply, mem_setOf_eq]
        split_ifs with is_a_lt_fx
        · exact fun _ => is_a_lt_fx
        · contrapose; intro _; simpa [enorm_eq_nnnorm]
      · exact exp_toReal_ne_zero' hpq.1 q_ne_top
    _ ≤ ∫⁻ x : α in {x | a < ‖f x‖}, ‖f x‖ₑ ^ q.toReal ∂μ := by
      apply lintegral_mono_ae
      apply ae_of_all
      intro x
      gcongr
      rw [enorm_eq_nnnorm, ← norm_toNNReal, enorm_eq_nnnorm, ← norm_toNNReal]
      simp only [Pi.sub_apply, ENNReal.coe_le_coe, norm_nonneg, Real.toNNReal_le_toNNReal_iff]
      apply trnc_le_func (j := ⊥)
    _ ≤ ENNReal.ofReal (a ^ (q.toReal - p.toReal)) * ∫⁻ x : α in {x | a < ‖f x‖},
        ‖f x‖ₑ ^ p.toReal ∂μ := by
      rw [← lintegral_const_mul']; swap; · exact coe_ne_top
      simp only [enorm_eq_nnnorm]
      apply setLIntegral_mono_ae (AEMeasurable.restrict (by fun_prop))
      · apply ae_of_all
        intro x (hx : a < ‖f x‖)
        rw [mul_comm]
        rw [← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm (f x), ENNReal.ofReal_rpow_of_nonneg,
          ENNReal.ofReal_rpow_of_nonneg]
          <;> try positivity
        exact rpow_le_rpow_of_exponent_le_base_ge ha hx.le (toReal_mono hp hpq.2.le)
    _ ≤ ENNReal.ofReal (a ^ (q.toReal - p.toReal)) * ∫⁻ x : α,
        ‖f x‖ₑ ^ p.toReal ∂μ := by
      gcongr
      exact setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      exact exp_toReal_ne_zero' (lt_trans hpq.1 hpq.2) hp

lemma estimate_eLpNorm_trunc [MeasurableSpace E₁] [BorelSpace E₁]
    {p q : ℝ≥0∞} (hq : q ≠ ⊤) (hpq : p ∈ Ioo 0 q) (hf : AEMeasurable f μ) :
    eLpNorm (trunc f a) q μ ^ q.toReal ≤
    ENNReal.ofReal (a ^ (q.toReal - p.toReal)) * eLpNorm f p μ ^ p.toReal := by
  unfold eLpNorm eLpNorm'
  have p_ne_top : p ≠ ⊤ := hpq.2.ne_top
  have : p ≠ 0 := hpq.1.ne'
  have : q ≠ 0 := (lt_trans hpq.1 hpq.2).ne'
  split_ifs
  · contradiction
  · calc
    _ = ∫⁻ (x : α) in {x | 0 < ‖f x‖ ∧ ‖f x‖ ≤ a}, ↑‖trunc f a x‖ₑ ^ q.toReal ∂μ := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      · apply Eq.symm
        apply setLIntegral_eq_of_support_subset
        unfold Function.support
        intro x
        dsimp only [Pi.sub_apply, mem_setOf_eq]
        unfold trunc
        split_ifs with is_fx_le_a
        · intro fx_rpow_ne_zero
          refine ⟨?_, is_fx_le_a⟩
          contrapose! fx_rpow_ne_zero
          rw [norm_le_zero_iff.mp fx_rpow_ne_zero]
          simpa using toReal_pos this hq
        · contrapose; intro _; simpa using toReal_pos this hq
      · exact exp_toReal_ne_zero' (lt_trans hpq.1 hpq.2) hq
    _ ≤ ∫⁻ (x : α) in {x | 0 < ‖f x‖ ∧ ‖f x‖ ≤ a}, ‖f x‖ₑ ^ q.toReal ∂ μ := by
      apply lintegral_mono_ae
      apply ae_of_all
      intro x
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (trnc_le_func (j := ⊤))
    _ ≤ ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
        ∫⁻ (x : α) in {x | 0 < ‖f x‖ ∧ ‖f x‖ ≤ a}, ‖f x‖ₑ ^ p.toReal ∂ μ := by
      rw [← lintegral_const_mul']
      · apply setLIntegral_mono_ae (AEMeasurable.restrict (by fun_prop))
        · apply ae_of_all
          intro x hx
          rw [mul_comm]
          rw [← ofReal_norm_eq_enorm (f x), ENNReal.ofReal_rpow_of_nonneg,
            ENNReal.ofReal_rpow_of_nonneg] <;> try positivity
          apply rpow_le_rpow_of_exponent_le_base_le hx.1 hx.2
          exact toReal_mono hq hpq.2.le
      · exact coe_ne_top
    _ ≤ _ := by
      gcongr
      rw [one_div, ENNReal.rpow_inv_rpow]
      · exact setLIntegral_le_lintegral _ _
      · exact exp_toReal_ne_zero' hpq.1 p_ne_top

/-- If `f` is in `Lp`, the truncation is element of `Lq` for `q > p`. -/
lemma trunc_Lp_Lq_higher [MeasurableSpace E₁] [BorelSpace E₁]
    (hpq : p ∈ Ioo 0 q) (hf : MemLp f p μ) :
    MemLp (trnc ⊤ f a) q μ := by
  refine ⟨aestronglyMeasurable_trnc hf.1, ?_⟩
  rcases (eq_or_ne q ⊤) with q_eq_top | q_ne_top
  · rw [q_eq_top, eLpNorm_exponent_top]
    exact Trans.trans trunc_eLpNormEssSup_le coe_lt_top
  · rw [← rpow_lt_top_iff_of_pos (toReal_pos (lt_trans hpq.1 hpq.2).ne' q_ne_top)]
    apply lt_of_le_of_lt (estimate_eLpNorm_trunc q_ne_top hpq hf.1.aemeasurable)
    apply mul_lt_top coe_lt_top
    refine (rpow_lt_top_iff_of_pos ?_).mpr hf.2
    exact toReal_pos hpq.1.ne' hpq.2.ne_top

/-- If `f` is in `Lp`, the complement of the truncation is in `Lq` for `q < p`. -/
lemma truncCompl_Lp_Lq_lower [MeasurableSpace E₁] [BorelSpace E₁]
    (hp : p ≠ ⊤) (hpq : q ∈ Ioo 0 p) (ha : 0 < a) (hf : MemLp f p μ) :
    MemLp (trnc ⊥ f a) q μ := by
  refine ⟨aestronglyMeasurable_trnc hf.1, ?_⟩
  have : 0 < q.toReal := toReal_pos hpq.left.ne' hpq.right.ne_top
  refine (rpow_lt_top_iff_of_pos this).mp ?_
  refine lt_of_le_of_lt
    (estimate_eLpNorm_truncCompl hp hpq hf.1.aemeasurable ha) ?_
  apply mul_lt_top coe_lt_top
  refine (rpow_lt_top_iff_of_pos ?_).mpr hf.2
  exact toReal_pos (lt_trans hpq.left hpq.right).ne' hp

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  [NormedAddCommGroup E]
  [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂]
  [MeasurableSpace E] [BorelSpace E]
  {f : α → E₁} {t : ℝ}

/-! ## Some results about the integrals of truncations

-/
namespace MeasureTheory

def res (j : Bool) (β : ℝ) : Set ℝ :=
  if j then Ioo (0 : ℝ) β else Ioi β

lemma measurableSet_res {j : Bool} {β : ℝ} : MeasurableSet (res j β) := by
  unfold res
  split
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi

lemma res_subset_Ioi {j : Bool} {β : ℝ} (hβ : 0 < β) : res j β ⊆ Ioi 0 := by
  unfold res
  split
  · exact Ioo_subset_Ioi_self
  · simp only [Ioi, setOf_subset_setOf]
    intro s hs
    linarith

instance decidableMemRes {j : Bool} {β : ℝ} : Decidable (t ∈ res j β) := by
  exact Classical.propDecidable (t ∈ res j β)

def res' (j : Bool) (β : ℝ) : Set ℝ :=
  if j then Ioc (0 : ℝ) β else Ici β

lemma res'comp (j : Bool) (β : ℝ) (hβ : 0 < β) :
    Ioi (0 : ℝ) \ res' j β = res (¬j) β := by
  unfold res' res
  split_ifs with h₀ h₁ h₂
  · rw [h₀] at h₁; simp at h₁
  · ext x
    simp only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le]
    refine ⟨by tauto, fun h ↦ ⟨lt_trans hβ h, fun _ ↦ h⟩⟩
  · ext x
    simp only [Ioi_diff_Ici, mem_Ioo]
  · have : j = false := eq_false_of_ne_true h₀
    rw [this] at h₂
    simp at h₂

lemma measurableSet_res' {j : Bool} {β : ℝ} : MeasurableSet (res' j β) := by
  unfold res'
  measurability

lemma res'subset_Ioi {j : Bool} {β : ℝ} (hβ : 0 < β) : res' j β ⊆ Ioi 0 := by
  unfold res'
  split
  · exact Ioc_subset_Ioi_self
  · exact Ici_subset_Ioi.mpr hβ

lemma lintegral_trunc_mul₀ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {tc : ToneCouple} {p : ℝ} (hp : 0 < p)
    (hfx : 0 < ‖f x‖₊) :
    ∫⁻ s : ℝ in Ioi 0, (g s) * ‖trnc j f (tc.ton s) x‖ₑ ^ p =
    ∫⁻ s : ℝ in res' (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖ₑ ^ p := by
  rw [lintegral_double_restrict_set (B := res' (xor j tc.mon) (tc.inv ‖f x‖))
      measurableSet_Ioi measurableSet_res']
  · have : Ioi 0 ∩ res' (xor j tc.mon) (tc.inv ‖f x‖) = res' (xor j tc.mon) (tc.inv ‖f x‖) :=
      inter_eq_self_of_subset_right (res'subset_Ioi (tc.ran_inv (‖f x‖) hfx))
    rw [this]
  · apply ae_of_all
    rw [res'comp]
    · intro s
      unfold res trnc trunc
      have mon_pf := tc.inv_pf
      split_ifs at mon_pf with mon
      · rw [mon]
        rcases j
        · simp only [Bool.bne_true, Bool.not_false, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
          intro (hs : s > tc.inv ‖f x‖)
          split_ifs with h
          · simp [hp]
          · have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).2.mpr hs
            contrapose! h; linarith
        · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, decide_true]
          intro hs
          split_ifs with h
          · have := (mon_pf s hs.1 (‖f x‖) hfx).1.mpr hs.2
            linarith
          · simp [hp]
      · rw [Bool.not_eq_true] at mon
        rw [mon]
        rcases j
        · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, decide_true,
          ↓reduceIte, Pi.sub_apply]
          intro hs
          split_ifs with h
          · simp [hp]
          · have := (mon_pf s hs.1 (‖f x‖) hfx).2.mpr hs.2
            linarith
        · simp only [Bool.bne_false, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          intro (hs : tc.inv ‖f x‖ < s)
          have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).1.mpr hs
          split_ifs with h
          · linarith
          · simp [hp]
    · exact tc.ran_inv ‖f x‖ hfx

lemma lintegral_trunc_mul₁ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {p : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in res' (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖ₑ ^ p =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖ₑ ^ p := by
  apply setLIntegral_congr
  unfold res res'
  split_ifs
  · exact Ioo_ae_eq_Ioc.symm
  · exact Ioi_ae_eq_Ici.symm

lemma lintegral_trunc_mul₂ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {p : ℝ} {tc : ToneCouple}
    (hfx : 0 < ‖f x‖) :
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖ₑ ^ p =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖f x‖ₑ ^ p := by
  apply setLIntegral_congr_fun measurableSet_res
  · apply ae_of_all
    unfold res trnc trunc
    have mon_pf := tc.inv_pf
    split_ifs at mon_pf with mon
    · rw [mon]
      rcases j
      · simp only [Bool.bne_true, Bool.not_false, ↓reduceIte, Pi.sub_apply]
        intro s hs
        split_ifs with h
        · have := (mon_pf s hs.1 (‖f x‖) hfx).1.mpr hs.2
          contrapose! h; linarith
        · simp
      · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        intro s (hs : s > tc.inv ‖f x‖)
        split_ifs with h
        · rfl
        · have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).2.mpr hs
          contrapose! h; linarith
    · rw [Bool.not_eq_true] at mon
      rw [mon]
      rcases j
      · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
        intro s (hs : tc.inv ‖f x‖ < s)
        have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).1.mpr hs
        split_ifs with h
        · linarith
        · simp
      · simp only [Bool.bne_false, ↓reduceIte]
        intro s hs
        have := (mon_pf s hs.1 (‖f x‖) hfx).2.mpr hs.2
        split_ifs with h
        · rfl
        · linarith

lemma lintegral_trunc_mul {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {tc : ToneCouple} {p : ℝ}
    (hp : 0 < p) (hfx : ‖f x‖₊ > 0) :
    ∫⁻ s : ℝ in Ioi 0, (g s) * ‖trnc j f (tc.ton s) x‖ₑ ^ p =
    (∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s)) * ‖f x‖ₑ ^ p := by
  rw [lintegral_trunc_mul₀ hp hfx, lintegral_trunc_mul₁, lintegral_trunc_mul₂ hfx,
    lintegral_mul_const']
  exact ((rpow_lt_top_iff_of_pos hp).mpr coe_lt_top).ne


/-! Extract expressions for the lower Lebesgue integral of power functions -/

lemma lintegral_rpow_of_gt_abs {β γ : ℝ} (hβ : 0 < β) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  have hγ2 : 0 < γ + 1 := by linarith
  rw [abs_of_nonneg hγ2.le]
  exact lintegral_rpow_of_gt hβ hγ

-- TODO: treat symmetrically to Ioo case?
lemma lintegral_Ioi_rpow_of_lt_abs {β σ : ℝ} (hβ : 0 < β) (hσ : σ < -1):
    ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / |σ + 1|) := by
  have hσ2 : σ + 1 < 0 := by linarith
  rw [abs_of_neg hσ2, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt hσ hβ, div_neg, neg_div]
  · apply integrableOn_Ioi_rpow_of_lt hσ hβ
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun s hs ↦ Real.rpow_nonneg (lt_trans hβ hs).le σ

lemma lintegral_rpow_abs {j : Bool} {tc : ToneCouple} {γ : ℝ} {t : ℝ}
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) (ht : 0 < t) :
  ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t), ENNReal.ofReal s ^ γ =
    ENNReal.ofReal ((tc.inv t) ^ (γ + 1) / |γ + 1|) := by
  rw [← lintegral_congr_ae (Filter.mp_mem (self_mem_ae_restrict measurableSet_res)
      (Filter.univ_mem'
      (fun s hs ↦ (ofReal_rpow_of_pos (res_subset_Ioi (tc.ran_inv t ht) hs)).symm)))]
  unfold res
  split at hγ <;> rename_i xor_split
  · rw [xor_split]
    simp only [↓reduceIte]
    rw [lintegral_rpow_of_gt_abs (tc.ran_inv t ht) hγ]
  · rw [eq_false_of_ne_true xor_split]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lintegral_Ioi_rpow_of_lt_abs (tc.ran_inv t ht) hγ]

lemma value_lintegral_res₀ {j : Bool} {β γ : ℝ} {tc : ToneCouple} (hβ : 0 < β)
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) :
    ∫⁻ s : ℝ in res (xor j tc.mon) β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  unfold res
  split_ifs at hγ with h
  · rw [h]
    simp only [↓reduceIte]
    rw [lintegral_rpow_of_gt_abs hβ hγ]
  · have : xor j tc.mon = false := ((fun {a b} ↦ Bool.not_not_eq.mp) fun a ↦ h a.symm).symm
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lintegral_Ioi_rpow_of_lt_abs hβ hγ]

lemma value_lintegral_res₁ {t γ p': ℝ} {spf : ScaledPowerFunction} (ht : 0 < t) :
    ENNReal.ofReal (((spf_to_tc spf).inv t) ^ (γ + 1) / |γ + 1| ) * ENNReal.ofReal (t ^ p') =
    ENNReal.ofReal (spf.d ^ (γ + 1) * t ^ (spf.σ⁻¹ * (γ + 1) + p') / |γ + 1|) := by
  have := spf.hd
  unfold spf_to_tc
  dsimp only
  rw [← ENNReal.ofReal_mul, ← mul_div_right_comm, Real.mul_rpow, mul_assoc, ← Real.rpow_mul,
      ← Real.rpow_add] <;> positivity

end MeasureTheory

end
