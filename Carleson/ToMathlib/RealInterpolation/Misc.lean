module

public import Carleson.ToMathlib.RealInterpolation.InterpolatedExponents
public import Carleson.ToMathlib.WeakType
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Carleson.ToMathlib.MeasureTheory.Measure.NNReal

/-!
This file contains some miscellaneous prerequisites for proving the Marcinkiewisz real interpolation
theorem. There are the following sections:
- Interface for using cutoff functions
- Results about the particular choice of scale
- Some tools for measure theory computations
- Results about truncations of a function
- Measurability properties of truncations
- Truncations and Lp spaces

Upstreaming status:
- measure theory computations are basically ready
- truncations and their properties definitely belong into mathlib
- the details about cutoff functions and a particular scale function
  will depend on the particular proof chosen: design on the overall proof approach first
- except for using `distribution_lt_top`, this file does not use WeakType;
  it does use helper lemmas in `InterpolatedExponents`, though.
-/

@[expose] public section

noncomputable section

open ENNReal Real Set MeasureTheory

variable {p₀ q₀ p₁ q₁ p q t : ℝ≥0∞}

/-! ## Interface for using cutoff functions -/
section

open Real Set

/-- A ScaledPowerFunction is meant to represent a function of the form `t ↦ (t / d)^σ`,
    where `d` is strictly positive and either `σ > 0` or `σ < 0`. -/
structure ScaledPowerFunction where
  σ : ℝ
  d : ℝ≥0∞
  hd : 0 < d
  hd' : d ≠ ⊤
  hσ : (0 < σ) ∨ (σ < 0)

/-- A `ToneCouple` is a couple of two monotone functions that are practically inverses of each
    other. It is used in the proof of the real interpolation theorem.

    Note: originally it seemed useful to make the possible choice of this function general
    in the proof of the real inteprolation theorem. However, in the end really only one
    function works for all the different cases. This infrastructure, however, could potentially
    still be useful, if one would like to try to improve the constant. -/
structure ToneCouple where
  ton : ℝ≥0∞ → ℝ≥0∞
  inv : ℝ≥0∞ → ℝ≥0∞
  mon : Bool
  ton_is_ton : if mon then StrictMono ton else StrictAnti ton
  --ran_ton : ∀ t ∈ Ioi (0 : ℝ≥0∞), ton t ∈ Ioi 0
  --ran_inv : ∀ t ∈ Ioi (0 : ℝ≥0∞), inv t ∈ Ioi 0
  inv_pf : if mon
      then ∀ s t, (ton s < t ↔ s < inv t) ∧ (t < ton s ↔ inv t < s)
      else ∀ s t, (ton s < t ↔ inv t < s) ∧ (t < ton s ↔ s < inv t)

/-- A StrictRangeToneCouple is a `ToneCouple` for which the functions in the couple, when
    restricted to `Ioo 0 ∞`, map to `Ioo 0 ∞`. -/
structure StrictRangeToneCouple extends ToneCouple where
  ran_ton : ∀ t ∈ Ioo 0 ∞, ton t ∈ Ioo 0 ∞
  ran_inv : ∀ t ∈ Ioo 0 ∞, inv t ∈ Ioo 0 ∞

open scoped NNReal

/-- A scaled power function gives rise to a ToneCouple. -/
def spf_to_tc (spf : ScaledPowerFunction) : StrictRangeToneCouple where
  ton s := (s / spf.d) ^ spf.σ
  inv t := spf.d * t ^ spf.σ⁻¹
  mon := if 0 < spf.σ then true else false
  ran_ton := fun t ht ↦
      ⟨rpow_pos (ENNReal.div_pos ht.1.ne' spf.hd') ((div_lt_top ht.2.ne) spf.hd.ne').ne,
      rpow_lt_top_of_pos_ne_top_ne_zero (ENNReal.div_pos ht.1.ne' spf.hd').ne'
      ((div_lt_top ht.2.ne) spf.hd.ne').ne (by rcases spf.hσ <;> order)⟩
  ran_inv := fun t ht ↦
    ⟨ENNReal.mul_pos spf.hd.ne' (rpow_pos_of_pos_ne_top_ne_zero ht.1.ne' ht.2.ne
    (inv_ne_zero (by rcases spf.hσ <;> order))).ne',
    ENNReal.mul_lt_top spf.hd'.lt_top (rpow_lt_top_of_pos_ne_top_ne_zero ht.1.ne' ht.2.ne
    (inv_ne_zero (by rcases spf.hσ <;> order)))⟩
  ton_is_ton := by
    have := spf.hd
    have := spf.hd'
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte]
      intro s t hst
      beta_reduce
      gcongr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro s t hst
      rcases spf.hσ with σ_pos | σ_neg
      · exact (sgn_σ σ_pos).elim
      · by_cases ht' : t = ⊤
        · beta_reduce; rw [ht', top_div]
          simp only [spf.hd', ↓reduceIte, top_rpow_of_neg σ_neg]
          by_cases hs' : s = ⊤
          · simp_all [spf.hd']
          by_cases hs'' : s = 0
          · rewrite [hs'', ENNReal.zero_div, zero_rpow_of_neg σ_neg]; simp
          · have hs'' : 0 < s := pos_of_ne_zero hs''
            exact rpow_pos (ENNReal.div_pos hs''.ne' spf.hd') (div_ne_top hs' spf.hd.ne')
        by_cases hs : s = 0
        · beta_reduce
          rw [hs, ENNReal.zero_div, zero_rpow_of_neg σ_neg, ← neg_neg spf.σ, ENNReal.rpow_neg]
          have : 0 ≠ t := by order
          exact inv_lt_top.mpr <| rpow_pos (ENNReal.div_pos (by order) spf.hd') (by finiteness)
        · have hs' : 0 < s := pos_of_ne_zero hs
          apply rpow_lt_rpow_iff_neg ?_ ?_ ((ENNReal.div_lt_div spf.hd spf.hd').mpr hst) σ_neg
          · exact ENNReal.div_ne_zero.mpr ⟨hs'.ne', spf.hd'⟩
          · exact div_ne_top ht' spf.hd.ne'
  inv_pf := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte]
      have : 0 < spf.σ⁻¹ := by simpa
      refine fun s t => ⟨?_, ?_⟩
      · rw [← ENNReal.rpow_lt_rpow_iff this, ENNReal.rpow_rpow_inv sgn_σ.ne',
            ENNReal.div_lt_iff (.inl spf.hd.ne') (.inl spf.hd'), mul_comm]
      · rw [← ENNReal.rpow_lt_rpow_iff this, ENNReal.rpow_rpow_inv sgn_σ.ne',
          ENNReal.lt_div_iff_mul_lt (.inl spf.hd.ne') (.inl spf.hd'), mul_comm]
    · intro s t
      rcases spf.hσ with σ_pos | σ_neg
      · contradiction
      · have : 0 < (-spf.σ)⁻¹ := by simpa
        constructor
        all_goals rw [← ENNReal.inv_lt_inv, ← ENNReal.rpow_neg, ← ENNReal.rpow_lt_rpow_iff this,
          ENNReal.rpow_rpow_inv (by simpa using σ_neg.ne)]
        on_goal 1 => rw [ENNReal.lt_div_iff_mul_lt (.inl spf.hd.ne') (.inl spf.hd')]
        on_goal 2 => rw [ENNReal.div_lt_iff (.inl spf.hd.ne') (.inl spf.hd')]
        all_goals rw [mul_comm, ENNReal.inv_rpow, inv_neg, ENNReal.rpow_neg, inv_inv]
end
noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents
    ComputationsChoiceExponent

variable {α α' ε : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α}
  {a : ℝ≥0∞} -- truncation parameter
  [ENorm ε] {f : α → ε} {t : ℝ≥0∞}

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

def d :=
    (C₀ ^ (q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (eLpNorm f p μ ^ p.toReal) ^
      (p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (C₁ ^ (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (eLpNorm f p μ ^ p.toReal) ^
      (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal))))

lemma d_pos_aux₀ (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    0 < eLpNorm f p μ ^ p.toReal :=
  ENNReal.rpow_pos (pos_of_gt hF.1) (by finiteness)

lemma d_ne_top_aux₀ {b : ℝ} {F : ℝ≥0∞} (hF : F ∈ Ioo 0 ⊤) : F ^ b ≠ ⊤ := by
  finiteness [hF.1, hF.2]

lemma d_ne_zero_aux₀ {b : ℝ} (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (eLpNorm f p μ ^ p.toReal) ^ b ≠ 0 :=
  (ENNReal.rpow_pos (d_pos_aux₀ hF) (d_ne_top_aux₀ hF)).ne'

lemma d_ne_zero_aux₂ {C : ℝ≥0} {b c : ℝ} (hC : 0 < C)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    C ^ c * (eLpNorm f p μ ^ p.toReal) ^ b ≠ 0 :=
  (ENNReal.mul_pos (by positivity) (d_ne_zero_aux₀ hF)).ne'

lemma d_ne_top_aux₂ {b : ℝ} (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (eLpNorm f p μ ^ p.toReal) ^ b ≠ ⊤ :=
  rpow_ne_top' (d_pos_aux₀ hF).ne' (d_ne_top_aux₀ hF)

lemma d_ne_top_aux₃ {C : ℝ≥0} {b c : ℝ} (hC : 0 < C)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    C ^ c * (eLpNorm f p μ ^ p.toReal) ^ b ≠ ⊤ :=
  mul_ne_top (by finiteness) (d_ne_top_aux₂ hF)

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
    @d α ε m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f > 0 :=
  pos_of_ne_zero <| d_ne_zero_aux₃ hC₀ hC₁ hF

@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma d_ne_top (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    @d α ε m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f ≠ ⊤ := by
  rw [d]
  exact d_ne_top_aux₄ hC₀ hC₁ hF

lemma d_eq_top₀ (hp₀ : 0 < p₀) (hq₁ : 0 < q₁) (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ = ⊤) (hq₀q₁ : q₀ ≠ q₁) :
    @d α ε m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f =
    (↑C₀ ^ p₀.toReal * eLpNorm f p μ ^ p.toReal) ^ p₀.toReal⁻¹ := by
  unfold d
  rw [hq₀']
  simp only [inv_top, toReal_zero, sub_zero, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    div_one]
  rw [mul_div_cancel_right₀]
  · rw [div_eq_mul_inv, mul_inv_cancel₀, ENNReal.rpow_one]
    · rw [ENNReal.mul_rpow_of_nonneg (hz := by positivity), ENNReal.rpow_rpow_inv, toReal_inv]
      exact (exp_toReal_pos hp₀ hp₀').ne'
    · exact (inv_toReal_pos_of_ne_top hq₁ ((hq₀' ▸ hq₀q₁).symm)).ne'
  · exact (inv_toReal_pos_of_ne_top hq₁ ((hq₀' ▸ hq₀q₁).symm)).ne'

lemma d_eq_top₁ (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ = ⊤)
    (hq₀q₁ : q₀ ≠ q₁) (hC₁ : 0 < C₁) :
    @d α ε m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f =
    (↑C₁ ^ p₁.toReal * eLpNorm f p μ ^ p.toReal) ^ p₁.toReal⁻¹ := by
  unfold d
  rw [hq₁']
  simp only [inv_top, toReal_zero, zero_sub, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    one_div]
  rw [div_neg, div_neg]
  rw [mul_div_cancel_right₀]
  · rw [div_eq_mul_inv, mul_inv_cancel₀, ENNReal.rpow_neg_one]
    · rw [ENNReal.mul_rpow_of_nonneg]
      · rw [ENNReal.rpow_rpow_inv, ← toReal_inv, ENNReal.mul_inv, inv_inv]
        · rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, toReal_inv, mul_neg, mul_one, neg_neg]
        · left; exact ENNReal.inv_ne_zero.mpr coe_ne_top
        · left; finiteness
        · exact (exp_toReal_pos hp₁ hp₁').ne'
      · positivity
    · exact (inv_toReal_pos_of_ne_top hq₀ (hq₁' ▸ hq₀q₁)).ne'
  · exact (inv_toReal_pos_of_ne_top hq₀ (hq₁' ▸ hq₀q₁)).ne'

lemma d_eq_top_of_eq (hC₁ : 0 < C₁) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hq₀' : q₀ ≠ ⊤)
(hp₀' : p₀ ≠ ⊤) (hp₁ : 0 < p₁) (hp₀p₁ : p₀ = p₁) (hpp₀ : p = p₀) (hq₁' : q₁ = ⊤) :
    @d α ε m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f = C₁ * eLpNorm f p μ := by
  rw [d_eq_top₁, ← hp₀p₁, hpp₀] <;> try assumption
  on_goal 1 => rw [ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_rpow_inv, ENNReal.rpow_rpow_inv]
  · exact (toReal_pos hp₀.ne' hp₀').ne'
  · exact (toReal_pos hp₀.ne' hp₀').ne'
  · positivity
  · exact hp₀p₁ ▸ hp₀'
  · exact hq₁' ▸ hq₀'

lemma d_eq_top_top (hq₀ : 0 < q₀) (hq₀q₁ : q₀ ≠ q₁) (hp₁' : p₁ = ⊤) (hq₁' : q₁ = ⊤) :
    @d α ε m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f = C₁ := by
  unfold d
  rw [hp₁', hq₁']
  simp only [inv_top, toReal_zero, zero_sub, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    zero_mul, one_div]
  rw [div_neg, div_eq_mul_inv, mul_inv_cancel₀]
  · rw [ENNReal.rpow_neg, ENNReal.rpow_one, inv_inv]
  · exact (toReal_pos (ENNReal.inv_ne_zero.mpr (hq₁' ▸ hq₀q₁)) (by finiteness)).ne'

/-- The particular choice of scaled power function that works in the proof of the
real interpolation theorem. -/
def spf_ch {t : ℝ} (ht : t ∈ Ioo 0 1) (hq₀q₁ : q₀ ≠ q₁) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    ScaledPowerFunction where
  σ := ζ p₀ q₀ p₁ q₁ t
  d := @d _ ε _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f
  hσ := lt_or_gt_of_ne <| Ne.symm <|
    (toReal_ofReal ht.1.le) ▸ (ζ_ne_zero (ofReal_mem_Ioo_0_1 t ht) hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁)
  hd := d_pos hC₀ hC₁ hF
  hd' := d_ne_top_aux₄ hC₀ hC₁ hF

end ChoiceScale

end

noncomputable section -- TODO: move these lemmas to a better location!

open NNReal ENNReal MeasureTheory Set

variable {α α' : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞} {c : ℝ≥0} {μ : Measure α}

/-! ## Some tools for measure theory computations
    A collection of small lemmas to help with integral manipulations.
-/
namespace MeasureTheory

-- TODO: change lhs and rhs?
-- TODO: rewrite the condition in filter form?
lemma lintegral_double_restrict_set {A B : Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := setLIntegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]

-- local convenience function
lemma lintegral_rw_aux {g : ℝ → ℝ≥0∞} {f₁ f₂ : ℝ → ℝ≥0∞} {A : Set ℝ}
    (heq : f₁ =ᶠ[ae (volume.restrict A)] f₂) :
    ∫⁻ s in A, g s * f₁ s = ∫⁻ s in A, g s * f₂ s :=
  (lintegral_rw₂ (Filter.EventuallyEq.refl (ae (volume.restrict A)) g) heq HMul.hMul)

lemma power_aux {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ (p + q)) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal s ^ p * ENNReal.ofReal s ^ q) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : 0 < s)
  rw [ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs,
    ← ofReal_mul (by positivity), ← Real.rpow_add hs]

lemma power_aux_2 {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal (s ^ (p + q))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p) * ENNReal.ofReal (s ^ q)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : 0 < s)
  rw [← ofReal_mul (by positivity), ← Real.rpow_add hs]

lemma power_aux_3 {p q : ℝ} :
    (fun s : ℝ≥0∞ ↦ s ^ (p + q)) =ᶠ[ae volume] (fun s ↦ s ^ p * s ^ q) := by
  filter_upwards [Ioo_zero_top_ae_eq_univ] with a ha
  unfold Ioo at ha
  refine ENNReal.rpow_add p q ?_ ?_
  · simp [pos_iff_ne_zero] at ha; by_contra; have := (ha.mpr trivial).1; tauto
  · simp [lt_top_iff_ne_top] at ha; by_contra; have := (ha.mpr trivial).2; tauto

lemma power_aux_4 {p : ℝ} :
    (fun s ↦ ENNReal.ofReal (s ^ p)) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal s ^ p) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : 0 < s)
  rw [← ofReal_rpow_of_pos (by positivity)]

lemma ofReal_rpow_of_pos_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    with s (hs : 0 < s) using ofReal_rpow_of_pos hs

lemma extract_constant_double_integral_rpow {f : ℝ → ℝ → ℝ≥0∞} {q : ℝ} (hq : q ≥ 0) {a : ℝ≥0∞}
    (ha : a ≠ ⊤) :
    ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, a * f s t) ^ q =
    a ^ q * ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, f s t) ^ q := by
  simp_rw [← lintegral_const_mul' _ _ (rpow_ne_top_of_nonneg hq ha),
    ← ENNReal.mul_rpow_of_nonneg _ _ hq, lintegral_const_mul' a _ ha]

lemma ofReal_rpow_rpow_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    with s (hs : 0 < s) using ofReal_rpow_of_pos hs

lemma lintegral_rpow_of_gt {β γ : ℝ} (hβ : 0 ≤ β) (hγ : -1 < γ) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / (γ + 1)) := by
  have hγ2 : 0 < γ + 1 := by linarith
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hβ, integral_rpow]
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

variable {α α' ε : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞} {c : ℝ≥0} {a : ℝ}
  {μ : Measure α} {ν : Measure α'}
  [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {ε' : Type*} [TopologicalSpace ε'] [ENorm ε']
  {f : α → ε} {s t t' : ℝ≥0∞}

/-! ## Results about truncations of a function
-/
namespace MeasureTheory

section

variable {ε' : Type*} [ENorm ε'] [Zero ε'] {f : α → ε'}

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → ε') (t : ℝ≥0∞) (x : α) : ε' := if ‖f x‖ₑ ≤ t then f x else 0

lemma trunc_eq_indicator : trunc f t = {x | ‖f x‖ₑ ≤ t}.indicator f := by
  ext x; simp_rw [trunc, Set.indicator, mem_setOf_eq, ite_eq_ite]

@[simp]
lemma trunc_top : trunc f ∞ = f := by simp [trunc_eq_indicator]

/-- The complement of a `t`-truncation of a function `f`. -/
def truncCompl (f : α → ε') (t : ℝ≥0∞) (x : α) : ε' := if ‖f x‖ₑ ≤ t then 0 else f x

lemma truncCompl_eq_indicator : truncCompl f t = {x | ‖f x‖ₑ ≤ t}ᶜ.indicator f := by
  ext x
  simp only [truncCompl, Set.indicator, mem_compl_iff, mem_setOf_eq, ite_not]

@[simp]
lemma truncCompl_top : truncCompl f ∞ = (fun _ ↦ 0) := by simp [truncCompl_eq_indicator]

lemma truncCompl_eq :
    truncCompl f t = fun x ↦ if t < ‖f x‖ₑ then f x else 0 := by
  ext x
  rw [← ite_not]
  simp [truncCompl]

/-- A function to deal with truncations and complement of truncations in one go. -/
def trnc (j : Bool) (f : α → ε') (t : ℝ≥0∞) : α → ε' :=
  match j with
  | false => truncCompl f t
  | true => trunc f t

@[simp]
lemma trnc_false : trnc false f t = truncCompl f t := rfl

@[simp]
lemma trnc_true : trnc true f t = trunc f t := rfl

end

/-- A function is the complement if its truncation and the complement of the truncation. -/
@[simp]
lemma trunc_add_truncCompl {t : ℝ≥0∞} : trunc f t + truncCompl f t = f := by
  ext x
  unfold trunc truncCompl
  simp only [Pi.add_apply]
  split_ifs <;> simp

alias trnc_true_add_trnc_false := trunc_add_truncCompl

-- /-- If the truncation parameter is non-positive, the truncation vanishes. -/
-- lemma trunc_of_nonpos {f : α → ε'} (ht : t ≤ 0) : trunc f t = 0 := by
--   unfold trunc
--   ext x
--   split_ifs with h
--   · dsimp only [Pi.zero_apply]
--     apply enorm_eq_zero.mp
--     · have : 0 ≤ ‖f x‖ₑ := by positivity
--       -- TODO: this was just `linarith`
--       exact le_antisymm (h.trans (by norm_cast)) this
--   · rfl

-- /-- If the truncation parameter is non-positive, the complement of the truncation is the
-- function itself. -/
-- lemma truncCompl_of_nonpos {f : α → ε'} (ht : t ≤ 0) : truncCompl f t = f := by
--   rw [truncCompl_eq]
--   ext x
--   dsimp only [Pi.zero_apply]
--   split_ifs
--   · rfl
--   · apply (enorm_eq_zero.mp ?_).symm
--     have : ‖f x‖ₑ ≥ 0 := by positivity
--     -- was just `linarith`
--     exact le_antisymm (by order) this

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
protected lemma StronglyMeasurable.trunc (hf : StronglyMeasurable f) :
    StronglyMeasurable (trunc f t) :=
  StronglyMeasurable.ite (measurableSet_le hf.enorm.stronglyMeasurable stronglyMeasurable_const) hf
    stronglyMeasurable_const

@[measurability]
protected lemma StronglyMeasurable.truncCompl (hf : StronglyMeasurable f) :
    StronglyMeasurable (truncCompl f t) := by
  rw [truncCompl_eq]
  exact hf.ite (measurableSet_lt stronglyMeasurable_const hf.enorm.stronglyMeasurable) stronglyMeasurable_const

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
nonrec lemma AEStronglyMeasurable.trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc g t)
  constructor
  · rw [trunc_eq_indicator]
    exact wg1.indicator (s := {x | ‖g x‖ₑ ≤ t}) (measurableSet_le wg1.enorm (by fun_prop))
  · exact measure_mono_null (fun x ↦ by contrapose!; simp_all [trunc]) wg2

@[measurability]
nonrec lemma AEStronglyMeasurable.truncCompl
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (truncCompl f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (truncCompl g t)
  constructor
  · rw [truncCompl_eq_indicator]
    apply wg1.indicator
    simp only [MeasurableSet.compl_iff]
    exact measurableSet_le wg1.enorm measurable_const
  · exact measure_mono_null (fun x ↦ by contrapose!; simp_all [truncCompl]) wg2


@[measurability]
lemma aestronglyMeasurable_trnc {j : Bool} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trnc j f t) μ :=
  j.rec (.truncCompl hf) (.trunc hf)

lemma trunc_le {f : α → ε} (x : α) : ‖trunc f t x‖ₑ ≤ max 0 t := by
  unfold trunc
  split_ifs with h
  · rcases (lt_or_ge t 0) with t_lt_0 | _
    · exact Trans.trans (Trans.trans h t_lt_0.le) (le_max_left 0 t)
    · exact Trans.trans h (le_max_right 0 t)
  · simp

/-- A small lemma that is helpful for rewriting -/
lemma coe_coe_eq_ofReal (a : ℝ) : ofNNReal a.toNNReal = ENNReal.ofReal a := by rfl

lemma trunc_eLpNormEssSup_le {f : α → ε} (a : ℝ≥0∞) :
    eLpNormEssSup (trunc f a) μ ≤ (max 0 a) :=
  essSup_le_of_ae_le _ (ae_of_all _ fun x ↦ trunc_le x)

lemma trunc_mono {f : α → ε} {a b : ℝ≥0∞} (hab : a ≤ b) {x : α} : ‖trunc f a x‖ₑ ≤ ‖trunc f b x‖ₑ := by
  unfold trunc
  split_ifs
  · rfl
  · order
  · rw [enorm_zero]; positivity
  · exact le_rfl

/-- The norm of the truncation is monotone in the truncation parameter -/
lemma eLpNorm_trunc_mono :
    Monotone fun s ↦ eLpNorm (trunc f s) p μ :=
  fun _a _b hab ↦ eLpNorm_mono_enorm fun _x ↦ trunc_mono hab

lemma trunc_buildup_enorm {x : α} :
    ‖trunc f t x‖ₑ + ‖truncCompl f t x‖ₑ = ‖f x‖ₑ := by
  simp only [trunc, truncCompl]; split_ifs with h <;> simp

lemma trunc_le_func {x : α} : ‖trunc f t x‖ₑ ≤ ‖f x‖ₑ := by
  unfold trunc; split_ifs <;> simp

lemma truncCompl_le_func {x : α} :
    ‖(truncCompl f t) x‖ₑ ≤ ‖f x‖ₑ := by
  rw [truncCompl_eq]; dsimp only; split_ifs <;> simp

lemma foo {A B C D : ℝ≥0∞} (hA : A ≠ ∞) (h : A ≤ C) (h' : A + B = C + D) : D ≤ B := by
  obtain (done | contra) := le_or_gt D B
  · assumption
  · have : A + B < C + D := ENNReal.add_lt_add_of_le_of_lt hA h contra
    exact False.elim (by order)

lemma truncCompl_anti {x : α} (hab : t ≤ s) (hf : ‖trunc f t x‖ₑ ≠ ⊤) :
    ‖truncCompl f s x‖ₑ ≤ ‖truncCompl f t x‖ₑ := by
  have obs : ‖trunc f t x‖ₑ + ‖(truncCompl f t) x‖ₑ = ‖trunc f s x‖ₑ + ‖(truncCompl f s) x‖ₑ := by
    simp_rw [trunc_buildup_enorm]
  exact foo hf (trunc_mono hab) obs

/-- The norm of the complement of the truncation is antitone in the truncation parameter -/
-- XXX: the conditions `hf` and `mf` may need to be tweaked
lemma eLpNorm_truncCompl_anti (hf : eLpNorm f 1 μ ≠ ⊤) (mf : AEStronglyMeasurable f μ) :
    Antitone (fun s ↦ eLpNorm (truncCompl f s) p μ) := by
  intro a _b hab
  have : ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ⊤ := by
    rw [eLpNorm_one_eq_lintegral_enorm] at hf
    simp_rw [ae_iff, not_ne_iff]; exact measure_eq_top_of_lintegral_ne_top mf.enorm hf
  have : ∀ᵐ x ∂μ, ‖trunc f a x‖ₑ ≠ ⊤ := by
    refine this.mono fun x hx ↦ ?_
    rw [trunc]
    split_ifs; exacts [hx, by simp]
  exact eLpNorm_mono_enorm_ae <| this.mono fun x hx ↦ truncCompl_anti hab hx

/-- The norm of the truncation is meaurable in the truncation parameter -/
@[measurability, fun_prop]
lemma eLpNorm_trunc_measurable :
    Measurable (fun s ↦ eLpNorm (trunc f s) p μ) :=
  eLpNorm_trunc_mono.measurable

/-- The norm of the complement of the truncation is measurable in the truncation parameter -/
@[measurability, fun_prop]
lemma eLpNorm_truncCompl_measurable (hf : eLpNorm f 1 μ ≠ ⊤) (mf : AEStronglyMeasurable f μ) :
    Measurable (fun s ↦ eLpNorm (truncCompl f s) p μ) :=
  eLpNorm_truncCompl_anti hf mf |>.measurable

lemma trnc_le_func {j : Bool} {a : ℝ≥0∞} {x : α} :
    ‖trnc j f a x‖ₑ ≤ ‖f x‖ₑ := by
  unfold trnc trunc truncCompl
  rcases j
  · dsimp only [Pi.sub_apply]
    split_ifs <;> simp
  · dsimp only
    split_ifs <;> simp

-- /-- ## Distribution functions of truncations -/

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ≥0∞) : α →ₘ[μ] E :=
--   AEEqFun.mk (trunc f t) (.trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ≥0∞) : f.trunc t ∈ U

/-! ## Truncations and L-p spaces -/

lemma MemLp.trunc {p : ℝ≥0∞} (hf : MemLp f p μ) : MemLp (trunc f t) p μ := by
  refine ⟨hf.1.trunc, lt_of_le_of_lt (eLpNorm_mono_ae' (ae_of_all _ ?_)) hf.2⟩
  intro x
  unfold MeasureTheory.trunc
  split_ifs with is_fx_le_a <;> simp

-- lemma eLpNorm_truncCompl_le {p : ℝ≥0∞} :
--     eLpNorm (truncCompl f t) p μ ≤ eLpNorm f p μ :=
--   eLpNorm_mono (fun _ ↦ truncCompl_le_func)

lemma MemLp.truncCompl {p : ℝ≥0∞} (hf : MemLp f p μ) :
    MemLp (truncCompl f t) p μ := by
  refine ⟨hf.1.truncCompl, lt_of_le_of_lt (eLpNorm_mono_ae' (ae_of_all _ ?_)) hf.2⟩
  intro x
  unfold MeasureTheory.truncCompl
  split_ifs with is_fx_le_a <;> simp

lemma eLpNorm_truncCompl_le {q : ℝ≥0∞}
    (q_ne_zero : ¬ q = 0) (q_ne_top : q ≠ ⊤) :
    eLpNorm (truncCompl f t) q μ ^ q.toReal ≤
    ∫⁻ x : α in {x | t < ‖f x‖ₑ}, ‖f x‖ₑ ^ q.toReal ∂μ := by
  unfold eLpNorm eLpNorm'
  have q_toReal_pos : 0 < q.toReal := toReal_pos q_ne_zero q_ne_top
  split_ifs
  calc
  _ = ∫⁻ x : α in {x | t < ‖f x‖ₑ}, ‖(truncCompl f t) x‖ₑ ^ q.toReal ∂μ := by
    rw [one_div, ENNReal.rpow_inv_rpow]
    · apply (setLIntegral_eq_of_support_subset _).symm
      unfold Function.support
      intro x
      rw [truncCompl_eq, mem_setOf_eq]
      dsimp only [Pi.sub_apply]
      split_ifs with is_a_lt_fx
      · exact fun _ ↦ is_a_lt_fx
      · contrapose; intro _; simpa [enorm_eq_nnnorm]
    · exact q_toReal_pos.ne'
  _ ≤ ∫⁻ x : α in {x | t < ‖f x‖ₑ}, ‖f x‖ₑ ^ q.toReal ∂μ := by
    gcongr with x
    exact trnc_le_func (j := ⊥)

-- TODO: better name!
lemma estimate_eLpNorm_truncCompl {p q : ℝ≥0∞}
    (p_ne_top : p ≠ ⊤) (hpq : q ∈ Ioc 0 p) (hf : AEStronglyMeasurable f μ) (ht : 0 < t) :
    eLpNorm (truncCompl f t) q μ ^ q.toReal ≤
    (t ^ (q.toReal - p.toReal)) * eLpNorm f p μ ^ p.toReal := by
  have q_ne_top: q ≠ ⊤ := ne_top_of_le_ne_top p_ne_top hpq.2
  have p_ne_zero : p ≠ 0 := (hpq.1.trans_le hpq.2).ne'
  apply le_trans (eLpNorm_truncCompl_le hpq.1.ne' (ne_top_of_le_ne_top p_ne_top hpq.2))
  calc
    _ ≤ (t ^ (q.toReal - p.toReal)) * ∫⁻ x : α in {x | t < ‖f x‖ₑ},
        ‖f x‖ₑ ^ p.toReal ∂μ := by
      rw [← lintegral_const_mul']
      · apply setLIntegral_mono_ae (AEMeasurable.restrict (by fun_prop))
        filter_upwards with x hx
        rw [mul_comm]
        exact rpow_le_rpow_of_exponent_le_base_ge_enorm ht hx.ne_top hx.le (toReal_mono p_ne_top hpq.2)
      · by_cases ht' : t = ⊤
        · simp_all
        · finiteness
    _ ≤ (t ^ (q.toReal - p.toReal)) * ∫⁻ x : α, ‖f x‖ₑ ^ p.toReal ∂μ := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by
      congr
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal p_ne_zero p_ne_top, one_div, ENNReal.rpow_inv_rpow]
      exact (toReal_pos p_ne_zero p_ne_top).ne'

-- TODO: better name!
lemma estimate_eLpNorm_trunc {p q : ℝ≥0∞}
    (hq : q ≠ ⊤) (hpq : p ∈ Ioc 0 q) {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (trunc f t) q μ ^ q.toReal ≤
    (t ^ (q.toReal - p.toReal)) * eLpNorm f p μ ^ p.toReal := by
  have hq' : 0 < q := hpq.1.trans_le hpq.2
  have p_ne_top : p ≠ ∞ := (hpq.2.trans_lt (lt_top_iff_ne_top.mpr hq)).ne
  by_cases ht : t = ⊤
  · by_cases hf' : eLpNorm f p μ ^ p.toReal = 0
    · have : (fun x ↦ ‖f x‖ₑ) =ᵐ[μ] 0 := by
        rw [← eLpNorm_enorm] at hf'
        rwa [← eLpNorm_eq_zero_iff (by fun_prop) hpq.1.ne',
          ← ENNReal.rpow_eq_zero_iff_of_pos (toReal_pos hpq.1.ne' p_ne_top)]
      refine le_of_eq_of_le ?_ zero_le
      rw [rpow_eq_zero_iff_of_pos]
      · rw [← MeasureTheory.eLpNorm_enorm, eLpNorm_eq_zero_iff (by fun_prop) hq'.ne']
        filter_upwards [this] with x h₀
        exact nonpos_iff_eq_zero.mp (le_of_le_of_eq trunc_le_func h₀)
      · rw [toReal_pos_iff]
        exact ⟨hq', hq.lt_top⟩
    · -- The right hand side is `∞`, hence the statement is always true.
      simp only [ht, trunc_top, ge_iff_le]
      by_cases p_eq_q : p = q
      · simp [p_eq_q]
      rw [top_rpow_of_pos, top_mul hf']
      · apply le_top
      rw [sub_pos, toReal_lt_toReal p_ne_top hq]
      exact lt_of_le_of_ne hpq.2 p_eq_q
  unfold eLpNorm eLpNorm'
  have : p ≠ 0 := hpq.1.ne'
  split_ifs with h
  · exfalso
    exact hq'.ne' h
  · calc
    _ = ∫⁻ (x : α) in {x | 0 < ‖f x‖ₑ ∧ ‖f x‖ₑ ≤ t}, ‖trunc f t x‖ₑ ^ q.toReal ∂μ := by
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
          simpa [nonpos_iff_eq_zero.mp fx_rpow_ne_zero] using toReal_pos hq'.ne' hq
        · contrapose; intro _; simpa using toReal_pos hq'.ne' hq
      · exact (toReal_pos (hpq.1.trans_le hpq.2).ne' hq).ne'
    _ ≤ ∫⁻ (x : α) in {x | 0 < ‖f x‖ₑ ∧ ‖f x‖ₑ ≤ t}, ‖f x‖ₑ ^ q.toReal ∂ μ := by
      gcongr with x
      exact trnc_le_func (j := ⊤)
    _ ≤ (t ^ (q.toReal - p.toReal)) *
        ∫⁻ (x : α) in {x | 0 < ‖f x‖ₑ ∧ ‖f x‖ₑ ≤ t}, ‖f x‖ₑ ^ p.toReal ∂ μ := by
      rw [← lintegral_const_mul']
      · apply setLIntegral_mono_ae (AEMeasurable.restrict (by fun_prop))
        · filter_upwards with x hx
          rw [mul_comm]
          exact rpow_le_rpow_of_exponent_le_base_le_enorm hx.1 (ne_top_of_le_ne_top ht hx.2) hx.2 <| toReal_mono hq hpq.2
      · simp_all
    _ ≤ _ := by
      gcongr
      rw [one_div, ENNReal.rpow_inv_rpow]
      · exact setLIntegral_le_lintegral _ _
      · exact (toReal_pos hpq.1.ne' p_ne_top).ne'

-- TODO: is there a better name?
/-- If `f` is in `Lp`, the truncation is element of `Lq` for `q ≥ p`. -/
lemma trunc_Lp_Lq_higher (hpq : p ∈ Ioc 0 q) {f : α → ε} (hf : MemLp f p μ) (ht : t ≠ ∞) :
    MemLp (trnc ⊤ f t) q μ := by
  refine ⟨aestronglyMeasurable_trnc hf.1, ?_⟩
  rcases (eq_or_ne q ⊤) with q_eq_top | q_ne_top
  · rw [q_eq_top, eLpNorm_exponent_top]
    simp only [trnc]
    calc _
      _ ≤ max 0 t := trunc_eLpNormEssSup_le t
      _ < ∞ := by finiteness
  · have p_ne_top := ne_top_of_le_ne_top q_ne_top hpq.2
    rw [← rpow_lt_top_iff_of_pos (toReal_pos (hpq.1.trans_le hpq.2).ne' q_ne_top)]
    apply lt_of_le_of_lt (estimate_eLpNorm_trunc q_ne_top hpq hf.1)
    apply mul_lt_top ?_ ?_
    · by_cases ht'' : t = 0
      · rw [ht'']
        apply ENNReal.rpow_lt_top_of_nonneg (h := by finiteness)
        simp only [sub_nonneg]
        rw [toReal_le_toReal p_ne_top q_ne_top]
        exact hpq.2
      · finiteness
    · exact (rpow_lt_top_iff_of_pos (toReal_pos hpq.1.ne' p_ne_top)).mpr hf.2

lemma memLp_truncCompl_of_memLp_top (hf : MemLp f ⊤ μ) (h : μ {x | t < ‖f x‖ₑ} < ⊤) :
    MemLp (trnc ⊥ f t) p μ := by
  by_cases hp_top : p = ⊤
  · rw [hp_top]
    simp only [bot_eq_false, trnc_false]
    exact hf.truncCompl
  obtain ⟨hf_m, hf_lt_top⟩ := hf
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]
    exact aestronglyMeasurable_trnc hf_m
  /- TODO: We currently need this annoying extra step because
    we do not have `MeasurableSet {a | t < ‖f a‖ₑ}` in general
    (since f is only aestronglymeasurable).
  -/
  rcases hf_m with ⟨g, ⟨wg1, wg2⟩⟩
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have ae_eq_trunc : (trnc ⊥ f t) =ᶠ[ae μ] (trnc ⊥ g t) := by
    simp only [bot_eq_false, trnc_false]
    rw [truncCompl_eq_indicator, truncCompl_eq_indicator]
    rw [Filter.eventuallyEq_iff_exists_mem] at wg2
    rcases wg2 with ⟨s, hs, hfgs⟩
    rw [Filter.eventuallyEq_iff_exists_mem]
    use s, hs
    intro x hs
    rw [indicator, indicator]
    split_ifs with hx hx' hx''
    · exact hfgs hs
    · exfalso
      simp only [mem_compl_iff, mem_setOf_eq, not_le, not_lt, hfgs hs] at hx hx'
      order
    · exfalso
      simp only [mem_compl_iff, mem_setOf_eq, not_le, not_lt, hfgs hs] at hx hx''
      order
    · rfl
  apply MemLp.ae_eq ae_eq_trunc.symm
  use aestronglyMeasurable_trnc wg1.aestronglyMeasurable
  simp only [bot_eq_false, trnc_false]
  rw [truncCompl_eq_indicator,
      eLpNorm_indicator_eq_eLpNorm_restrict
        (by rw [compl_setOf]; simp only [not_le]; exact measurableSet_lt measurable_const (by fun_prop))]
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  apply (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos).trans_lt
  apply ENNReal.mul_lt_top
  · rw [← eLpNorm_exponent_top]
    apply (eLpNorm_restrict_le _ _ _ _).trans_lt
    rwa [eLpNorm_congr_ae wg2.symm]
  apply ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le])
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  rw [← lt_top_iff_ne_top, compl_setOf]
  calc
  _ = μ {a | t < ‖f a‖ₑ} := by
    apply measure_congr
    rw [Filter.eventuallyEq_iff_exists_mem] at wg2
    rcases wg2 with ⟨s, hs, hfgs⟩
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨s, hs, fun a ha ↦ by simp [setOf, hfgs.symm ha]⟩
  _ < ∞ := h

-- is there a better name?
/-- If `f` is in `Lp`, the complement of the truncation is in `Lq` for `q ≤ p`. -/
lemma truncCompl_Lp_Lq_lower
    (hp : p ≠ ⊤) (hpq : q ∈ Ioc 0 p) (ht : 0 < t) (hf : MemLp f p μ) :
    MemLp (trnc ⊥ f t) q μ := by
  have q_ne_top : q ≠ ∞ := ne_top_of_le_ne_top hp hpq.2
  by_cases ht' : t = ∞
  · simp [trnc, ht']
  refine ⟨aestronglyMeasurable_trnc hf.1, ?_⟩
  have : 0 < q.toReal := toReal_pos hpq.left.ne' q_ne_top
  refine (rpow_lt_top_iff_of_pos this).mp ?_
  refine lt_of_le_of_lt (estimate_eLpNorm_truncCompl hp hpq hf.1 ht) ?_
  apply mul_lt_top
  · push Not at ht'
    finiteness
  refine (rpow_lt_top_iff_of_pos ?_).mpr hf.2
  exact toReal_pos (hpq.1.trans_le hpq.2).ne' hp

-- Lemma 6.10 in Folland
-- XXX: is the `ContinuousAdd` hypothesis really necessary for `MemLp.add` (and hence here)?
lemma memLp_of_memLp_le_of_memLp_ge {f : α → ε} [ContinuousAdd ε]
    {r : ℝ≥0∞} (hp : 0 < p) (hr' : q ∈ Icc p r)
    (hf : MemLp f p μ) (hf' : MemLp f r μ) : MemLp f q μ := by
  by_cases p_ne_top : p = ⊤
  · rw [p_ne_top] at hf
    convert hf
    rw [eq_top_iff]
    convert hr'.1
    exact p_ne_top.symm
  set C := (1 : ℝ≥0∞)
  have h : MemLp (trnc ⊤ f C) q μ := trunc_Lp_Lq_higher ⟨hp, hr'.1⟩ hf (by norm_num)
  have h' : MemLp (trnc ⊥ f C) q μ := by
    by_cases hr : r = ⊤
    · exact memLp_truncCompl_of_memLp_top (hr ▸ hf') <| distribution_lt_top hf hp p_ne_top (by norm_num)
    exact truncCompl_Lp_Lq_lower hr ⟨hp.trans_le hr'.1, hr'.2⟩ (by norm_num) hf'
  have : f = (trnc ⊤ f C) + (trnc ⊥ f C) := trunc_add_truncCompl.symm
  rw [this]
  exact h.add h'

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set

variable {α α' ε : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁ : ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ≥0∞} -- truncation parameter
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α → ε} {t : ℝ≥0∞}

/-! ## Some results about the integrals of truncations

-/
namespace MeasureTheory

def res (j : Bool) (β : ℝ≥0∞) : Set ℝ :=
  if β = ∞ then if j then Ioi (0 : ℝ) else ∅
  else if j then Ioo (0 : ℝ) β.toReal else Ioi β.toReal

lemma measurableSet_res {j : Bool} {β : ℝ≥0∞} : MeasurableSet (res j β) := by
  unfold res
  split_ifs
  · exact measurableSet_Ioi
  · exact MeasurableSet.empty
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi

lemma res_subset_Ioi {j : Bool} {β : ℝ≥0∞} : res j β ⊆ Ioi 0 := by
  unfold res
  split_ifs
  · exact fun ⦃a⦄ a ↦ a
  · simp
  · simp only [Ioi]
    intro s hs
    rw [mem_setOf]
    exact hs.1
  · exact Ioi_subset_Ioi toReal_nonneg

instance decidableMemRes {t : ℝ} {j : Bool} {β : ℝ≥0∞} : Decidable (t ∈ res j β) := by
  exact Classical.propDecidable (t ∈ res j β)

def res' (j : Bool) (β : ℝ≥0∞) : Set ℝ :=
  if β = ∞ then if j then Ioi (0 : ℝ) else ∅
  else if j then Ioc (0 : ℝ) β.toReal else Ioi 0 ∩ Ici β.toReal

-- TODO: this one is probably obsolete
lemma res'comp₀ (j : Bool) (β : ℝ≥0∞) (hβ : 0 < β) :
    Ioi (0 : ℝ) \ res' j β = res (¬j) β := by
  unfold res' res
  split_ifs with h₀ h₁ h₂
  on_goal 6 =>
    ext x
    simp only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le]
    exact ⟨by tauto, fun h ↦ ⟨(toReal_pos (hβ.ne') h₀).trans h, fun x ↦ h⟩⟩
  all_goals simp_all

lemma res'comp (j : Bool) (β : ℝ≥0∞) :
    Ioi (0 : ℝ) \ res' j β = res (¬j) β := by
  unfold res' res
  split_ifs with h₀ h₁ h₂
  on_goal 6 =>
    ext x
    simp only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le]
    refine ⟨by tauto, fun hβ ↦ ?_⟩
    have : 0 ≤ β.toReal := toReal_nonneg
    exact ⟨by order, fun _ ↦ hβ⟩
  all_goals simp_all

lemma measurableSet_res' {j : Bool} {β : ℝ≥0∞} : MeasurableSet (res' j β) := by
  unfold res'
  measurability

lemma res'subset_Ioi {j : Bool} {β : ℝ≥0∞} : res' j β ⊆ Ioi 0 := by
  unfold res'
  split_ifs with h h'
  · simp
  · simp
  · exact Ioc_subset_Ioi_self
  · exact inter_subset_left

lemma res'subset_Ici {j : Bool} {β : ℝ≥0∞} : res' j β ⊆ Ici 0 := by
  unfold res'
  split_ifs with h h'
  · simp
  · simp
  · exact Trans.trans Ioc_subset_Icc_self Icc_subset_Ici_self
  · exact Trans.trans inter_subset_left Ioi_subset_Ici_self

lemma lintegral_trunc_mul₀ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {tc : ToneCouple} {p : ℝ} (hp : 0 < p)
    :
    ∫⁻ s : ℝ in Ioi 0, (g s) * ‖trnc j f (tc.ton (ENNReal.ofReal s)) x‖ₑ ^ p =
    ∫⁻ s : ℝ in res' (xor j tc.mon) (tc.inv ‖f x‖ₑ), (g s) *
        ‖trnc j f (tc.ton (ENNReal.ofReal s)) x‖ₑ ^ p := by
  rw [lintegral_double_restrict_set (B := res' (xor j tc.mon) (tc.inv ‖f x‖ₑ))
      measurableSet_Ioi measurableSet_res', inter_eq_self_of_subset_right res'subset_Ioi]
  filter_upwards
  rw [res'comp]
  intro s
  unfold res trnc trunc truncCompl
  have mon_pf := tc.inv_pf
  split_ifs at mon_pf with mon
  · rw [mon]
    rcases j
    · simp only [Bool.bne_true, Bool.not_false, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte]
      split_ifs with h <;> intro hs
      · simp [hp]
      · simp at hs
      · simp [hp]
      · have := (mon_pf (ENNReal.ofReal s) ‖f x‖ₑ).2.mpr ((lt_ofReal_iff_toReal_lt h).mpr hs)
        order
    · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, decide_true]
      split_ifs with h <;> intro hs
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).1.mpr (by rw [h]; exact coe_lt_top)
        order
      · simp [hp]
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).1.mpr <| (ofReal_lt_iff_lt_toReal hs.1.le h).mpr hs.2
        order
      · simp [hp]
  · rw [Bool.not_eq_true] at mon
    rw [mon]
    rcases j
    · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, decide_true,
      ↓reduceIte]
      split_ifs with h <;> intro hs
      · simp [hp]
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).2.mpr (by rw [h]; exact coe_lt_top)
        order
      · simp [hp]
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).2.mpr <| (ofReal_lt_iff_lt_toReal hs.1.le h).mpr hs.2
        order
    · simp only [Bool.bne_false, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs with h <;> intro hs
      · simp at hs
      · simp [hp]
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).1.mpr <| (lt_ofReal_iff_toReal_lt h).mpr hs
        order
      · simp [hp]

lemma lintegral_trunc_mul₁ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {p : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in res' (xor j tc.mon) (tc.inv ‖f x‖ₑ), (g s) * ‖trnc j f (tc.ton (ENNReal.ofReal s)) x‖ₑ ^ p =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖ₑ), (g s) * ‖trnc j f (tc.ton (ENNReal.ofReal s)) x‖ₑ ^ p := by
  apply setLIntegral_congr
  unfold res res'
  split_ifs
  · simp
  · simp
  · exact Ioo_ae_eq_Ioc.symm
  · by_cases h : (tc.inv ‖f x‖ₑ).toReal = 0; · rw [h, inter_eq_left.mpr Ioi_subset_Ici_self]
    rw [inter_eq_right.mpr]
    · exact Ioi_ae_eq_Ici.symm
    · refine Ici_subset_Ioi.mpr <| toReal_pos ?_ (by assumption)
      exact Ne.symm (ne_of_apply_ne ENNReal.toReal fun a ↦ h (id (Eq.symm a)))

lemma lintegral_trunc_mul₂ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {p : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖ₑ), (g s) * ‖trnc j f (tc.ton (ENNReal.ofReal s)) x‖ₑ ^ p =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖ₑ), (g s) * ‖f x‖ₑ ^ p := by
  apply setLIntegral_congr_fun measurableSet_res
  unfold res trnc trunc truncCompl
  have mon_pf := tc.inv_pf
  split_ifs at mon_pf with mon
  -- intro s hs
  · rw [mon]
    rcases j <;> intro s
    · simp only [Bool.bne_true, Bool.not_false, ↓reduceIte]
      split_ifs with h <;> intro hs
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).1.mpr (by rw [h]; exact coe_lt_top)
        order
      · simp
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).1.mpr <| (ofReal_lt_iff_lt_toReal hs.1.le h).mpr hs.2
        order
      · rfl
    · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs with h <;> intro hs
      · rfl
      · simp at hs
      · rfl
      · have := (mon_pf (ENNReal.ofReal s) ‖f x‖ₑ).2.mpr ((lt_ofReal_iff_toReal_lt h).mpr hs)
        order
  · rw [Bool.not_eq_true] at mon
    rw [mon]
    rcases j <;> intro s
    · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs with h <;> intro hs
      · simp at hs
      · simp at hs
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).1.mpr <| (lt_ofReal_iff_toReal_lt h).mpr hs
        order
      · rfl
    · simp only [Bool.bne_false, ↓reduceIte]
      split_ifs with h <;> intro hs
      · rfl
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).2.mpr (by rw [h]; exact coe_lt_top)
        order
      · rfl
      · have := (mon_pf (.ofReal s) ‖f x‖ₑ).2.mpr <| (ofReal_lt_iff_lt_toReal hs.1.le h).mpr hs.2
        order

lemma lintegral_trunc_mul {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g) {j : Bool} {x : α} {tc : ToneCouple} {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ s : ℝ in Ioi 0, (g s) * ‖trnc j f (tc.ton (ENNReal.ofReal s)) x‖ₑ ^ p =
    (∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖ₑ), (g s)) * ‖f x‖ₑ ^ p := by
  rw [lintegral_trunc_mul₀ hp, lintegral_trunc_mul₁, lintegral_trunc_mul₂, lintegral_mul_const'']
  exact hg.restrict

/-! Extract expressions for the lower Lebesgue integral of power functions
TODO: move to a lower-level file! -/

lemma lintegral_rpow_of_gt_abs {β γ : ℝ} (hβ : 0 ≤ β) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  have hγ2 : 0 < γ + 1 := by linarith
  rw [abs_of_nonneg hγ2.le]
  exact lintegral_rpow_of_gt hβ hγ

-- TODO: treat symmetrically to Ioo case?
lemma lintegral_Ioi_rpow_of_lt_abs {β σ : ℝ} (hβ : 0 < β) (hσ : σ < -1) :
    ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / |σ + 1|) := by
  have hσ2 : σ + 1 < 0 := by linarith
  rw [abs_of_neg hσ2, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt hσ hβ, div_neg, neg_div]
  · apply integrableOn_Ioi_rpow_of_lt hσ hβ
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun s hs ↦ Real.rpow_nonneg (lt_trans hβ hs).le σ

lemma lintegral_rpow_Ioi_top {γ : ℝ} :
    ∫⁻ s : ℝ in Ioi 0, .ofReal (s ^ γ) = ∞ := by
  by_contra h
  apply (not_integrableOn_Ioi_rpow γ)
  refine ⟨by fun_prop, ?_⟩
  calc
  _ = ∫⁻ (a : ℝ) in Ioi 0, .ofReal (a ^ γ) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun _ ha ↦ enorm_of_nonneg (rpow_nonneg ha.le γ)
  _ < ⊤ := Ne.lt_top' fun a ↦ h (Eq.symm a)

lemma value_lintegral_res₀ {j : Bool} {β : ℝ≥0∞} {γ : ℝ} (hγ : if j then γ > -1 else γ < -1) :
  ∫⁻ s : ℝ in res j β, ENNReal.ofReal (s ^ γ) = β ^ (γ + 1) / ENNReal.ofReal |γ + 1| := by
  · unfold res
    split at hγ <;> rename_i xor_split
    · rw [xor_split]
      simp only [↓reduceIte]
      split_ifs with htop
      · rw [htop, top_rpow_def]
        split_ifs
        · simp [lintegral_rpow_Ioi_top, top_div_of_lt_top]
        · linarith
        · linarith
      · by_cases hzero : β = 0
        · rw [hzero, ENNReal.zero_rpow_of_pos (by linarith)]; simp
        · have htcinv : 0 < β.toReal := toReal_pos hzero htop
          rw [lintegral_rpow_of_gt_abs htcinv.le hγ, ENNReal.ofReal_div_of_pos
              (by rw [abs_pos]; linarith), ← ENNReal.ofReal_rpow_of_pos htcinv,
              ofReal_toReal_eq_iff.mpr htop]
    · simp only [eq_false_of_ne_true xor_split, Bool.false_eq_true, ↓reduceIte]
      split_ifs with htop
      · rw [htop, top_rpow_of_neg (by linarith)]; simp
      · by_cases hzero : β = 0
        · rw [hzero, toReal_zero, lintegral_rpow_Ioi_top, zero_rpow_of_neg (by linarith),
              top_div_of_lt_top]
          exact coe_lt_top
        · have htcinv : 0 < β.toReal := toReal_pos hzero htop
          rw [lintegral_Ioi_rpow_of_lt_abs htcinv hγ, ofReal_div_of_pos
              (by rw [abs_pos]; linarith), ← ofReal_rpow_of_pos htcinv,
              ofReal_toReal_eq_iff.mpr htop]

lemma value_lintegral_res₁ {γ p' : ℝ} {spf : ScaledPowerFunction} (ht : 0 < t) (ht' : t ≠ ∞) :
    (((spf_to_tc spf).inv t) ^ (γ + 1) / ENNReal.ofReal |γ + 1|) * (t ^ p') =
    (spf.d ^ (γ + 1) * t ^ (spf.σ⁻¹ * (γ + 1) + p') / ENNReal.ofReal |γ + 1|) := by
  have := spf.hd
  unfold spf_to_tc
  dsimp only
  rw [← ENNReal.mul_div_right_comm, ENNReal.mul_rpow_of_ne_zero, mul_assoc, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add]
  · positivity
  · finiteness
  · positivity
  · exact (ENNReal.rpow_pos ht ht').ne'

lemma value_lintegral_res₂ {γ p' : ℝ} {spf : ScaledPowerFunction} (ht : 0 < t)
    (hσp' : 0 < spf.σ⁻¹ * (γ + 1) + p') :
    (((spf_to_tc spf).inv t) ^ (γ + 1) / ENNReal.ofReal |γ + 1|) * (t ^ p') ≤
    (spf.d ^ (γ + 1) * t ^ (spf.σ⁻¹ * (γ + 1) + p') / ENNReal.ofReal |γ + 1|) := by
  by_cases ht' : t = ∞; swap; · rw [value_lintegral_res₁ ht ht']
  have := spf.hd
  unfold spf_to_tc
  dsimp only
  simp [ht', top_rpow_of_pos hσp', mul_top (ENNReal.rpow_pos this spf.hd').ne',
      top_div_of_lt_top ofReal_lt_top]

-- TODO: move to a lower-level file!
lemma AEStronglyMeasurable.induction {α : Type*} {β : Type*} {mα : MeasurableSpace α} [TopologicalSpace β]
  {μ : Measure α} {motive : (α → β) → Prop}
  (ae_eq_implies : ∀ ⦃f g : α → β⦄ (_ : StronglyMeasurable f) (_ : f =ᶠ[ae μ] g), motive f → motive g)
  (measurable : ∀ ⦃f : α → β⦄ (_ : StronglyMeasurable f), motive f)
    ⦃f : α → β⦄ (hf : AEStronglyMeasurable f μ) : motive f := by
  have hg := hf.choose_spec
  set g := hf.choose
  apply ae_eq_implies hg.1 hg.2.symm (measurable hg.1)

end MeasureTheory

end
