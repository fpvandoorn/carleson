module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Carleson.ToMathlib.Analysis.RCLike.Basic
public import Carleson.ToMathlib.ENorm

/-
Upstreaming status: Not sure whether `Components` is the right definition and `RCLike.induction`
really is a good statement; if it should go to mathlib, this file needs significant cleanup
-/

public section

namespace RCLike

open NNReal

/-- TODO: check whether this is the right approach -/
@[expose]
def Components {𝕂 : Type*} [RCLike 𝕂] : Finset 𝕂 := {1, -1, RCLike.I, -RCLike.I}

lemma Components.norm_eq_one {𝕂 : Type*} [RCLike 𝕂] {c : 𝕂} (hc : c ∈ Components) (hc' : c ≠ 0) :
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

lemma Components.norm_le_one {𝕂 : Type*} [RCLike 𝕂] {c : 𝕂} (hc : c ∈ Components) : ‖c‖ ≤ 1 := by
  by_cases h : c = 0
  · rw [h]
    simp
  rw [norm_eq_one hc h]

open ComplexConjugate

/-- TODO: check whether this is the right approach -/
@[expose]
def component {𝕂 : Type*} [RCLike 𝕂] (c : 𝕂) (a : 𝕂) : ℝ≥0 :=
  Real.toNNReal (RCLike.re (a * conj c))

lemma component_le_norm {𝕂 : Type*} [RCLike 𝕂] {c a : 𝕂} (hc : c ∈ Components) :
    component c a ≤ ‖a‖ := by
  unfold component
  rw [Real.coe_toNNReal']
  apply max_le _ (by simp)
  apply (RCLike.re_le_norm (a * (starRingEnd 𝕂) c)).trans
  simp only [norm_mul, RCLike.norm_conj]
  nth_rw 2 [← mul_one ‖a‖]
  gcongr
  exact Components.norm_le_one hc

lemma component_le_nnnorm {𝕂 : Type*} [RCLike 𝕂] {c a : 𝕂} (hc : c ∈ Components) :
    component c a ≤ ‖a‖₊ := by
  rw [← norm_toNNReal]
  apply NNReal.le_toNNReal_of_coe_le
  exact component_le_norm hc

lemma decomposition {𝕂 : Type*} [RCLike 𝕂] {a : 𝕂} :
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

theorem nnnorm_ofReal
  {𝕂 : Type*} [RCLike 𝕂] {a : ℝ≥0} :
  a = ‖(@RCLike.ofReal 𝕂 _) (NNReal.toReal a)‖₊ := by
  apply NNReal.eq
  simp

theorem enorm_ofReal
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

private lemma component_one_add_neg_one {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    algebraMap ℝ 𝕂 (component 1 a).toReal +
      (-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal = algebraMap ℝ 𝕂 (re a) := by
  unfold component
  simp only [map_one, mul_one, map_neg, mul_neg, neg_mul, one_mul]
  rw [← map_neg, ← map_add]; congr 1
  simp only [Real.coe_toNNReal']
  linarith [max_zero_sub_eq_self (re a)]

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

/-- Norm of the real component part is at most `‖a‖`. -/
private lemma norm_realPart_le {𝕂 : Type*} [RCLike 𝕂] (a : 𝕂) :
    ‖algebraMap ℝ 𝕂 (component 1 a).toReal +
      (-1 : 𝕂) * algebraMap ℝ 𝕂 (component (-1) a).toReal‖ ≤ ‖a‖ := by
  rw [component_one_add_neg_one, norm_ofReal]
  exact abs_re_le_norm a

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
theorem induction {α : Type*} {𝕂 : Type*} [RCLike 𝕂]
  {β : Type*} [Mul β] {a b}
  {P : (α → 𝕂) → Prop}
  (P_add : ∀ {f g : α → 𝕂}, P f → P g → P (f + g))
  (P_components : ∀ {f : α → 𝕂} {c : 𝕂} (_ : c ∈ RCLike.Components),
    P f → P (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ RCLike.component c ∘ f))
  (P_mul_unit : ∀ {f : α → 𝕂} {c : 𝕂} (_ : c ∈ RCLike.Components), P f → P (c • f))
  {motive : (α → 𝕂) → β → Prop}
  (motive_nnreal : ∀ {f : α → ℝ≥0} (_ : P (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ f)),
    motive (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ f) a)
  (motive_add' : ∀ {n : β} {f g : α → 𝕂} (_ : ∀ {x}, ‖f x‖ ≤ ‖f x + g x‖)
    (_ : ∀ {x}, ‖g x‖ ≤ ‖f x + g x‖) (_ : P f) (_ : P g),
      motive f n → motive g n → motive (f + g) (n * b))
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
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
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
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, one_mul] at this
    rw [add_assoc] at this; exact this
  -- Outer split: real part vs imaginary part
  apply motive_add'
  · -- ‖real_part x‖ ≤ ‖(real_part + imag_part) x‖
    intro x
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [f_decomp_pt]
    exact norm_realPart_le (f x)
  · -- ‖imag_part x‖ ≤ ‖(real_part + imag_part) x‖
    intro x
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [f_decomp_pt]
    exact norm_imPart_le (f x)
  · exact P_add (hP_comp (by unfold Components; simp)) (hP_comp (by unfold Components; simp))
  · exact P_add (hP_comp (by unfold Components; simp)) (hP_comp (by unfold Components; simp))
  · -- Inner split: positive real vs negative real
    apply motive_add'
    · -- ‖1 * pos_re x‖ ≤ ‖(1 * pos_re + (-1) * neg_re) x‖
      intro x
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact norm_posReal_le (f x)
    · -- ‖(-1) * neg_re x‖ ≤ ‖(1 * pos_re + (-1) * neg_re) x‖
      intro x
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, one_mul]
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
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      exact norm_posIm_le (f x)
    · -- ‖(-I) * neg_im x‖ ≤ ‖(I * pos_im + (-I) * neg_im) x‖
      intro x
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      exact norm_negIm_le (f x)
    · exact hP_comp (by unfold Components; simp)
    · exact hP_comp (by unfold Components; simp)
    · exact motive_mul_unit (by unfold Components; simp) (P_components (by unfold Components; simp) hf)
        (motive_nnreal (P_components (by unfold Components; simp) hf))
    · exact motive_mul_unit (by unfold Components; simp) (P_components (by unfold Components; simp) hf)
        (motive_nnreal (P_components (by unfold Components; simp) hf))

end RCLike
