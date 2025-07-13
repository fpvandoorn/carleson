import Carleson.Classical.Basic
import Mathlib.Data.Real.Pi.Bounds

/- This file contains definitions and lemmas regarding the Hilbert kernel. -/

noncomputable section

open scoped Real Interval
open Complex ComplexConjugate MeasureTheory

def k (x : ℝ) : ℂ := max (1 - |x|) 0 / (1 - exp (I * x))

/- Basic properties of k. -/

lemma k_of_neg_eq_conj_k {x : ℝ} : k (-x) = conj (k x) := by
  simp [k, conj_ofReal, ← exp_conj, conj_I, neg_mul]

lemma k_of_abs_le_one {x : ℝ} (abs_le_one : |x| ≤ 1) : k x = (1 - |x|) / (1 - exp (I * x)) := by
  rw_mod_cast [k, max_eq_left (by linarith)]

lemma k_of_one_le_abs {x : ℝ} (abs_le_one : 1 ≤ |x|) : k x = 0 := by
  rw [k, max_eq_right (by linarith)]
  simp

lemma k_le_of_le_abs {x r : ℝ} (hr : 0 < r) (hx : r ≤ |x|) : ‖k x‖ ≤ 2 / r := by
  rcases le_or_gt 1 (|x|) with h'x | h'x
  · simp only [k_of_one_le_abs h'x, norm_zero]
    positivity
  have : r / 2 ≤ ‖1 - exp (I * x)‖ := by
    apply lower_secant_bound ?_ hx
    have : r < 1 := by linarith
    simp only [abs_lt] at h'x
    exact ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  simp only [k, Complex.norm_div, norm_real, Real.norm_eq_abs, ge_iff_le]
  rw [abs_of_nonneg (by positivity)]
  calc (max (1 - |x|) 0) / ‖1 - cexp (I * ↑x)‖
  _ ≤ max 1 0 / (r / 2) := by
    gcongr
    linarith [abs_nonneg x]
  _ = 2 / r := by simp

@[fun_prop]
lemma k_measurable : Measurable k := by
  unfold k
  fun_prop

def K : ℝ → ℝ → ℂ := fun x y ↦ k (x - y)

lemma K_def : K = fun x y ↦ k (x - y) := rfl

lemma Hilbert_kernel_conj_symm {x y : ℝ} : K y x = conj (K x y) := by
  rw [K, ← neg_sub, k_of_neg_eq_conj_k, ← K]

@[fun_prop]
lemma Hilbert_kernel_measurable : Measurable (Function.uncurry K) :=
  k_measurable.comp measurable_sub

/- Lemma 11.1.11 (Hilbert kernel bound) -/
lemma Hilbert_kernel_bound {x y : ℝ} : ‖K x y‖ ≤ 2 ^ (2 : ℝ) / (2 * |x - y|) := by
  by_cases h : 0 < |x - y| ∧ |x - y| < 1
  · calc ‖K x y‖
      _ ≤ 1 / ‖1 - exp (I * ↑(x - y))‖ := by
        rw [K, k, norm_div]
        gcongr
        rw [norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg]
        · apply max_le _ zero_le_one; linarith [abs_nonneg (x-y)]
        · exact le_max_right _ _
      _ ≤ 1 / (|x - y| / 2) := by
        gcongr
        · linarith
        · apply lower_secant_bound _ (by rfl)
          rw [Set.mem_Icc]
          constructor
          · simp only [neg_mul, neg_add_le_iff_le_add]
            calc |x - y|
              _ ≤ 1 := h.2.le
              _ ≤ 2 * π - 1 := by rw [le_sub_iff_add_le]; linarith [Real.two_le_pi]
              _ ≤ 2 * π + (x - y) := by
                rw [sub_eq_add_neg]
                gcongr
                exact (abs_le.mp h.2.le).1
          · calc x - y
              _ ≤ |x - y| := le_abs_self (x - y)
              _ ≤ 1 := h.2.le
              _ ≤ 2 * π - 1 := by rw [le_sub_iff_add_le]; linarith [Real.two_le_pi]
              _ ≤ 2 * π - |x - y| := by gcongr; exact h.2.le
      _ = 2 / |x - y| := by rw [one_div, inv_div]
      _ ≤ (2 : ℝ) ^ (2 : ℝ) / (2 * |x - y|) := by ring_nf; trivial
  · push_neg at h
    have : ‖K x y‖ = 0 := by
      rw [norm_eq_zero, K, k, _root_.div_eq_zero_iff]
      by_cases xeqy : x = y
      · simp [xeqy]
      · left
        rw [ofReal_eq_zero, max_eq_right_iff, tsub_le_iff_right, zero_add]
        exact h (abs_pos.mpr (sub_ne_zero.mpr xeqy))
    rw [this]
    exact div_nonneg (by norm_num) (by linarith [abs_nonneg (x-y)])

/-Main part of the proof of Hilbert_kernel_regularity -/
/-TODO: This can be local, i.e. invisible to other files. -/
lemma Hilbert_kernel_regularity_main_part {y y' : ℝ} (yy'nonneg : 0 ≤ y ∧ 0 ≤ y') (ypos : 0 < y)
    (y2ley' : y / 2 ≤ y') (hy : y ≤ 1) (hy' : y' ≤ 1) :
    ‖k (-y) - k (-y')‖ ≤ 2 ^ 6 * (1 / |y|) * (|y - y'| / |y|) := by
  rw [k_of_abs_le_one, k_of_abs_le_one]
  · simp only [abs_neg, ofReal_neg, mul_neg]
    rw [_root_.abs_of_nonneg yy'nonneg.1, _root_.abs_of_nonneg yy'nonneg.2]
    set f : ℝ → ℂ := fun t ↦ (1 - t) / (1 - exp (-(I * t))) with hf
    set f' : ℝ → ℂ := fun t ↦ (-1 + exp (-(I * t)) + I * (t - 1) * exp (-(I * t)))
      / (1 - exp (-(I * t))) ^ 2 with f'def
    set c : ℝ → ℂ := fun t ↦ (1 - t) with cdef
    set c' : ℝ → ℂ := fun t ↦ -1 with c'def
    set d : ℝ → ℂ := fun t ↦ (1 - exp (-(I * t))) with ddef
    set d' : ℝ → ℂ := fun t ↦ I * exp (-(I * t)) with d'def
    have d_nonzero {t : ℝ} (ht : t ∈ Set.uIcc y' y) : d t ≠ 0 := by
      rw [Set.mem_uIcc] at ht
      have ht' : 0 < t ∧ t ≤ 1 := by
        rcases ht with ht | ht <;> (constructor <;> linarith)
      rw [ddef]
      simp only [ne_eq]
      rw [←norm_eq_zero]
      apply ne_of_gt
      calc ‖1 - exp (-(I * ↑t))‖
        _ ≥ |(1 - exp (-(I * ↑t))).im| := by
          simp only [ge_iff_le]
          apply abs_im_le_norm
        _ = Real.sin t := by
          simp only [sub_im, one_im, exp_im, neg_re, mul_re,
            I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
            sub_self, neg_zero, Real.exp_zero, neg_im, mul_im, one_mul, zero_add,
            Real.sin_neg, mul_neg, sub_neg_eq_add, abs_eq_self]
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.two_le_pi])
        _ > 0 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.two_le_pi])
    have f_deriv : ∀ t ∈ Set.uIcc y' y, HasDerivAt f (f' t) t := by
      intro t ht
      have : f = fun t ↦ c t / d t := rfl
      rw [this]
      have : f' = fun t ↦ ((c' t * d t - c t * d' t) / d t ^ 2) := by ext t; ring
      rw [this]
      apply HasDerivAt.div _ _ _
      · exact cdef ▸ c'def ▸ HasDerivAt.const_sub _ (HasDerivAt.ofReal_comp (hasDerivAt_id' _))
      · rw [ddef, d'def]
        simp only
        rw [←neg_neg (I * exp (-(I * ↑t)))]
        rw [←neg_mul, mul_comm]
        apply HasDerivAt.const_sub _ (HasDerivAt.cexp (HasDerivAt.neg _))
        conv in fun (x : ℝ) ↦ I * (x : ℝ) => ext; rw [mul_comm]
        set e : ℂ → ℂ := fun t ↦ t * I with edef
        have : (fun (t : ℝ) ↦ t * I) = fun (t : ℝ) ↦ e t := by rw [edef]
        rw [this]
        apply HasDerivAt.comp_ofReal
        rw [edef]
        apply hasDerivAt_mul_const
      · exact d_nonzero ht
    have f'_cont : ContinuousOn (fun t ↦ f' t) (Set.uIcc y' y) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) (by simpa using fun _ ht ↦ d_nonzero ht)
    calc ‖(1 - ↑y) / (1 - exp (-(I * ↑y))) - (1 - ↑y') / (1 - exp (-(I * ↑y')))‖
      _ = ‖f y - f y'‖ := by simp [hf]
      _ = ‖∫ (t : ℝ) in y'..y, f' t‖ := by
        congr 1
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
        · exact f_deriv
        · exact f'_cont.intervalIntegrable
      _ = ‖∫ (t : ℝ) in Ι y' y, f' t‖ := intervalIntegral.norm_intervalIntegral_eq _ _ _ _
      _ ≤ ∫ (t : ℝ) in Ι y' y, ‖f' t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ (t : ℝ) in Ι y' y, 3 / ((y / 2) / 2) ^ 2 := by
        apply setIntegral_mono_on
        · exact f'_cont.norm.integrableOn_uIcc.mono_set Set.Ioc_subset_Icc_self
        · apply (integrableOn_const_iff).mpr
          rw [Real.volume_uIoc]
          right
          exact ENNReal.ofReal_lt_top
        · exact measurableSet_uIoc
        · intro t ht
          rw [Set.mem_uIoc] at ht
          have ht' : 0 < t ∧ t ≤ 1 := by
            rcases ht with ht | ht <;> (constructor <;> linarith)
          rw [f'def]
          simp only [norm_div, norm_pow]
          gcongr
          · calc ‖(-1 + exp (-(I * ↑t)) +
              I * (↑t - 1) * exp (-(I * ↑t)))‖
              _ ≤ ‖(-1 + exp (-(I * ↑t)))‖ +
                ‖(I * (↑t - 1) * exp (-(I * ↑t)))‖ :=
                  norm_add_le ..
              _ ≤ ‖(-1 : ℂ)‖ + ‖(exp (-(I * ↑t)))‖ +
                ‖(I * (↑t - 1) * exp (-(I * ↑t)))‖ := by
                gcongr
                exact norm_add_le ..
              _ ≤ 1 + 1 + 1 := by
                gcongr
                · simp
                · rw [mul_comm, ←neg_mul]
                  norm_cast
                  exact le_of_eq (norm_exp_ofReal_mul_I _)
                · simp only [Complex.norm_mul, norm_I, one_mul]
                  apply mul_le_one₀
                  on_goal 1 => norm_cast
                  rw [Real.norm_of_nonpos] <;> linarith
                  · exact norm_nonneg _
                  rw [mul_comm, ←neg_mul]
                  norm_cast
                  exact le_of_eq (norm_exp_ofReal_mul_I _)
              _ = 3 := by norm_num
          · rw_mod_cast [mul_comm, ←neg_mul, mul_comm]
            apply lower_secant_bound
            · simp only [neg_mul, Set.mem_Icc, neg_add_le_iff_le_add, le_add_neg_iff_add_le,
              neg_le_sub_iff_le_add]
              constructor <;> linarith [Real.two_le_pi, Real.two_pi_pos]
            · rw [abs_neg, le_abs]
              left
              rcases ht with ht | ht <;> linarith [ht.1]
      _ = (volume (Ι y' y)).toReal * (3 / ((y / 2) / 2) ^ 2) :=
        setIntegral_const _
      _ = |y - y'| * (3 / ((y / 2) / 2) ^ 2) := by
        rw [Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg (y - y'))]
      _ = (3 * (2 * 2) ^ 2) * (1 / y) * (|y - y'| / y) := by ring
      _ ≤ 2 ^ 6 * (1 / y) * (|y - y'| / y) := by gcongr; norm_num
  · rwa [abs_neg, _root_.abs_of_nonneg yy'nonneg.2]
  · rwa [abs_neg, _root_.abs_of_nonneg yy'nonneg.1]

/- Lemma 11.1.12 (Hilbert kernel regularity) -/
lemma Hilbert_kernel_regularity {x y y' : ℝ} :
    2 * |y - y'| ≤ |x - y| → ‖K x y - K x y'‖ ≤ 2 ^ 8 * (1 / |x - y|) * (|y - y'| / |x - y|)  := by
  rw [K, K]
  wlog x_eq_zero : x = 0 generalizing x y y'
  · intro h
    set x_ := (0 : ℝ) with x_def
    set y_ := y - x with y_def
    set y'_ := y' - x with y'_def
    have h_ : 2 * |y_ - y'_| ≤ |x_ - y_| := by simpa [x_def, y_def, y'_def]
    have := this x_def h_
    rw [x_def, y_def, y'_def] at this
    simpa
  rw [x_eq_zero]
  intro h
  simp only [zero_sub, abs_neg] at h
  simp only [zero_sub, abs_neg]
  wlog yy'nonneg : 0 ≤ y ∧ 0 ≤ y' generalizing y y'
  · by_cases yge0 : 0 ≤ y
    · push_neg at yy'nonneg
      exfalso
      rw [_root_.abs_of_nonneg yge0, _root_.abs_of_nonneg] at h <;> linarith [yy'nonneg yge0]
    push_neg at yge0
    by_cases y'ge0 : 0 ≤ y'
    · exfalso
      rw [abs_of_neg yge0, abs_of_neg] at h <;> linarith
    /- This is the only interesting case. -/
    push_neg at y'ge0
    set! y_ := -y with y_def
    set! y'_ := -y' with y'_def
    have h_ : 2 * |y_ - y'_| ≤ |y_| := by
      rw [y_def, y'_def, ← abs_neg]
      simpa [neg_add_eq_sub]
    have y_y'_nonneg : 0 ≤ y_ ∧ 0 ≤ y'_ := by constructor <;> linarith
    have := this h_ y_y'_nonneg
    rw [y_def, y'_def] at this
    simp only [neg_neg, abs_neg, sub_neg_eq_add, neg_add_eq_sub] at this
    rw [← RCLike.norm_conj, map_sub, ← k_of_neg_eq_conj_k, ← k_of_neg_eq_conj_k,
      ← abs_neg (y' - y)] at this
    simpa
  /-"Wlog" 0 < y-/
  by_cases ypos : y ≤ 0
  · have y_eq_zero : y = 0 := le_antisymm ypos yy'nonneg.1
    have y'_eq_zero : y' = 0 := by
      simp [y_eq_zero, _root_.abs_of_nonneg yy'nonneg.2] at h
      linarith
    simp [y_eq_zero, y'_eq_zero]
  push_neg at ypos

  /- Beginning of the main proof -/
  have y2ley' : y / 2 ≤ y' := by
    rw [div_le_iff₀ two_pos]
    calc y
      _ = 2 * (y - y') - y + 2 * y' := by ring
      _ ≤ 2 * |y - y'| - y + 2 * y' := by gcongr; exact le_abs_self _
      _ ≤ y - y + 2 * y' := by
        gcongr
        rw [abs_eq_self.mpr yy'nonneg.1] at h
        exact h
      _ = y' * 2 := by ring
  /- Distinguish four cases -/
  rcases le_or_gt y 1, le_or_gt y' 1 with ⟨hy | hy, hy' | hy'⟩
  · apply le_trans (Hilbert_kernel_regularity_main_part yy'nonneg ypos y2ley' hy hy')
    gcongr <;> norm_num
  · rw [@k_of_one_le_abs (-y')]
    · calc ‖k (-y) - 0‖
        _ = ‖k (-y) - k (-1)‖ := by
          congr
          apply (k_of_one_le_abs _).symm
          simp
        _ ≤ 2 ^ 6 * (1 / |y|) * (|y - 1| / |y|) := by
          apply Hilbert_kernel_regularity_main_part
          constructor
          all_goals linarith
        _ ≤ 2 ^ 6 * (1 / |y|) * (|y - y'| / |y|) := by
          gcongr 2 ^ 6 * (1 / |y|) * (?_ / |y|)
          rw [abs_sub_comm, _root_.abs_of_nonneg, abs_sub_comm, _root_.abs_of_nonneg] <;> linarith
        _ ≤ 2 ^ 8 * (1 / |y|) * (|y - y'| / |y|) := by
          gcongr <;> norm_num
    · rw [abs_neg, _root_.abs_of_nonneg] <;> linarith
  · rw [@k_of_one_le_abs (-y)]
    · calc ‖0 - k (-y')‖
        _ = ‖k (-1) - k (-y')‖ := by
          congr
          apply (k_of_one_le_abs _).symm
          simp only [abs_neg, abs_one, le_refl]
        _ = ‖k (-y') - k (-1)‖ := by rw [norm_sub_rev]
        _ ≤ 2 ^ 6 * (1 / |y'|) * (|y' - 1| / |y'|) := by
          apply Hilbert_kernel_regularity_main_part
          constructor
          all_goals linarith
        _ = 2 ^ 6 * (1 / y') * ((1 - y') / y') := by
          congr
          · simp [_root_.abs_of_nonneg, yy'nonneg.2]
          · rw [abs_of_nonpos, neg_sub]
            linarith
          · simp [_root_.abs_of_nonneg, yy'nonneg.2]
        _ ≤ 2 ^ 6 * (1 / (y / 2)) * ((1 - y') / (y / 2)) := by
          gcongr
          · apply div_nonneg <;> linarith
          · linarith
        _ = (2 ^ 6 * 2 * 2) * (1 / y) * ((1 - y') / y) := by
          ring
        _ ≤ (2 ^ 6 * 2 * 2) * (1 / |y|) * (|y - y'| / |y|) := by
          gcongr
          apply div_nonneg <;> linarith
          on_goal 2 => rw [_root_.abs_of_nonneg] <;> linarith
          all_goals rw [_root_.abs_of_nonneg yy'nonneg.1]
        _ ≤ 2 ^ 8 * (1 / |y|) * (|y - y'| / |y|) := by norm_num
    · rw [abs_neg, _root_.abs_of_nonneg] <;> linarith
  · calc ‖k (-y) - k (-y')‖
      _ = 0 := by
        rw [norm_sub_eq_zero_iff, k_of_one_le_abs,
          k_of_one_le_abs] <;> (rw [abs_neg, _root_.abs_of_nonneg] <;> linarith)
      _ ≤ 2 ^ 8 * (1 / |y|) * (|y - y'| / |y|) := mul_nonneg (mul_nonneg (by norm_num) (by simp))
        (mul_nonneg (by norm_num) (by simp))
