import Carleson.Carleson
import Carleson.HomogeneousType
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convolution

open BigOperators
open Finset
--open Complex

noncomputable section


--TODO : add reasonable notation
--local notation "S_" => partialFourierSum f

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
--fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))

@[simp]
lemma fourierCoeffOn_mul {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {c : ℂ} {n : ℤ} : fourierCoeffOn hab (fun x ↦ c * f x) n =
    c * (fourierCoeffOn hab f n):= by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp
  rw [←mul_assoc, mul_comm c, mul_assoc _ c, mul_comm c, ←intervalIntegral.integral_mul_const]
  congr
  ext x
  ring

@[simp]
lemma fourierCoeffOn_neg {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {n : ℤ} : fourierCoeffOn hab (-f) n =
    - (fourierCoeffOn hab f n):= by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp

@[simp]
lemma fourierCoeffOn_add {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ} (hf : IntervalIntegrable f MeasureTheory.volume a b) (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f + g) n = fourierCoeffOn hab f n + fourierCoeffOn hab g n:= by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp
  rw [←mul_add, ←intervalIntegral.integral_add]
  congr
  ext x
  ring
  . apply IntervalIntegrable.continuousOn_mul hf
    apply Continuous.continuousOn
    continuity
  . apply IntervalIntegrable.continuousOn_mul hg
    apply Continuous.continuousOn
    continuity

@[simp]
lemma fourierCoeffOn_sub {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ} (hf : IntervalIntegrable f MeasureTheory.volume a b) (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f - g) n = fourierCoeffOn hab f n - fourierCoeffOn hab g n:= by
  rw [sub_eq_add_neg, fourierCoeffOn_add hf hg.neg, fourierCoeffOn_neg, ← sub_eq_add_neg]


@[simp]
lemma partialFourierSum_add {f g : ℝ → ℂ} {N : ℕ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi)): partialFourierSum (f + g) N = partialFourierSum f N + partialFourierSum g N := by
  ext x
  simp
  rw [partialFourierSum, partialFourierSum, partialFourierSum, ←sum_add_distrib]
  congr
  ext n
  rw [fourierCoeffOn_add hf hg, add_mul]

@[simp]
lemma partialFourierSum_sub {f g : ℝ → ℂ} {N : ℕ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi)): partialFourierSum (f - g) N = partialFourierSum f N - partialFourierSum g N := by
  ext x
  simp
  rw [partialFourierSum, partialFourierSum, partialFourierSum, ←sum_sub_distrib]
  congr
  ext n
  rw [fourierCoeffOn_sub hf hg, sub_mul]


@[simp]
lemma partialFourierSum_mul {f: ℝ → ℂ} {a : ℂ} {N : ℕ}: partialFourierSum (fun x ↦ a * f x) N = fun x ↦ a * partialFourierSum f N x := by
  ext x
  rw [partialFourierSum, partialFourierSum, mul_sum]
  congr
  ext n
  rw [fourierCoeffOn_mul, mul_assoc]

lemma fourier_periodic {n : ℤ} : Function.Periodic (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * Real.pi))) (2 * Real.pi) := by
  intro x
  simp

lemma partialFourierSum_periodic {f : ℝ → ℂ} {N : ℕ} : Function.Periodic (partialFourierSum f N) (2 * Real.pi) := by
  rw [Function.Periodic]
  intro x
  rw [partialFourierSum, partialFourierSum]
  congr
  ext n
  congr 1
  exact fourier_periodic x

/-TODO: Add lemma Periodic.uniformContinuous_of_continuous. -/
lemma fourier_uniformContinuous {n : ℤ} : UniformContinuous (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * Real.pi))) := by
  rw [fourier]
  simp
  --apply Complex.exp_mul_I_periodic.
  sorry

lemma partialFourierSum_uniformContinuous {f : ℝ → ℂ} {N : ℕ} : UniformContinuous (partialFourierSum f N) := by
  --apply continuous_finset_sum
  sorry



/-Lemmas 9-14 (except lemma 10).-/


/-Slightly different and stronger version of Lemma 10.11 (lower secant bound). -/
lemma lower_secant_bound' {η : ℝ}  {x : ℝ} (le_abs_x : η ≤ |x|) (abs_x_le : |x| ≤ 2 * Real.pi - η) :
    η / 4 ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
  by_cases ηpos : η ≤ 0
  . calc η / 4
    _ ≤ 0 := by linarith
    _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by apply norm_nonneg
  push_neg at ηpos
  wlog x_nonneg : 0 ≤ x generalizing x
  . convert (@this (-x) _ (by simpa) (by linarith)) using 1
    . rw [Complex.norm_eq_abs, ←Complex.abs_conj, map_sub, map_one, Complex.ofReal_neg, mul_neg, Complex.norm_eq_abs,
          ←Complex.exp_conj, map_mul, Complex.conj_I, neg_mul, Complex.conj_ofReal]
    . rwa [abs_neg]
  rw [abs_of_nonneg x_nonneg] at *
  wlog x_le_pi : x ≤ Real.pi generalizing x
  . convert (@this (2 * Real.pi - x) _ _ _ _) using 1
    . rw [Complex.norm_eq_abs, ←Complex.abs_conj]
      simp
      rw [←Complex.exp_conj]
      simp
      rw [mul_sub, Complex.conj_ofReal, Complex.exp_sub, mul_comm Complex.I (2 * Real.pi), Complex.exp_two_pi_mul_I, ←inv_eq_one_div, ←Complex.exp_neg]
    all_goals linarith
  by_cases h : x ≤ Real.pi / 2
  . calc η / 4
    _ ≤ (2 / Real.pi) * η := by
      rw [div_le_iff (by norm_num)]
      field_simp
      rw [le_div_iff Real.pi_pos, mul_comm 2, mul_assoc]
      gcongr
      linarith [Real.pi_le_four]
    _ ≤ (2 / Real.pi) * x := by gcongr
    _ = (1 - (2 / Real.pi) * x) * Real.sin 0 + ((2 / Real.pi) * x) * Real.sin (Real.pi / 2) := by simp
    _ ≤ Real.sin ((1 - (2 / Real.pi) * x) * 0 + ((2 / Real.pi) * x) * (Real.pi / 2)) := by
      apply (strictConcaveOn_sin_Icc.concaveOn).2 (by simp [Real.pi_nonneg])
      . simp
        constructor <;> linarith [Real.pi_nonneg]
      . rw [sub_nonneg, mul_comm]
        apply mul_le_of_nonneg_of_le_div (by norm_num) (div_nonneg (by norm_num) Real.pi_nonneg) (by simpa)
      . exact mul_nonneg (div_nonneg (by norm_num) Real.pi_nonneg) x_nonneg
      . simp
    _ = Real.sin x := by
      congr
      field_simp
      ring
    _ ≤ Real.sqrt ((Real.sin x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      apply le_abs_self
    _ ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
        rw [mul_comm, Complex.exp_mul_I, Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq]
        simp
        rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
        apply (Real.sqrt_le_sqrt_iff _).mpr
        . simp [pow_two_nonneg]
        . linarith [pow_two_nonneg (1 - Real.cos x), pow_two_nonneg (Real.sin x)]
  . push_neg at h
    calc η / 4
    _ ≤ 1 := by
      rw [div_le_iff (by norm_num), one_mul]
      exact (le_abs_x.trans x_le_pi).trans Real.pi_le_four
    _ ≤ |(1 - Complex.exp (Complex.I * ↑x)).re| := by
      rw [mul_comm, Complex.exp_mul_I]
      simp
      rw [Complex.cos_ofReal_re, le_abs]
      left
      simp
      apply Real.cos_nonpos_of_pi_div_two_le_of_le h.le
      linarith
    _ ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
      rw [Complex.norm_eq_abs]
      apply Complex.abs_re_le_abs

/- Lemma 10.11 (lower secant bound) from the paper. -/
lemma lower_secant_bound {η : ℝ} (ηpos : η > 0) {x : ℝ} (xIcc : x ∈ Set.Icc (-2 * Real.pi + η) (2 * Real.pi - η)) (xAbs : η ≤ |x|) :
    η / 8 ≤ Complex.abs (1 - Complex.exp (Complex.I * x)) := by
  calc η / 8
  _ ≤ η / 4 := by
    ring_nf
    gcongr
    norm_num
  _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
    apply lower_secant_bound' xAbs
    rw [abs_le, neg_sub', sub_neg_eq_add, neg_mul_eq_neg_mul]
    exact xIcc

def k (x : ℝ) : ℂ := max (1 - |x|) 0 / (1 - Complex.exp (Complex.I * x))

lemma k_of_neg_eq_conj_k {x : ℝ} : k (-x) = (starRingEnd ℂ) (k x) := by
  sorry

/- Little helper lemmas. -/
lemma k_of_abs_le_one {x : ℝ} (abs_le_one : |x| ≤ 1) : k x = (1 - |x|) / (1 - Complex.exp (Complex.I * x)) := by
  sorry
lemma k_of_one_le_abs {x : ℝ} (abs_le_one : 1 ≤ |x|) : k x = 0 := by
  sorry

def K (x y : ℝ) : ℂ := k (x-y)

/- Lemma 10.13 (Hilbert kernel bound) -/
lemma Hilbert_kernel_bound {x y : ℝ} : ‖K x y‖ ≤ 2 ^ (4 : ℝ) / (2 * |x - y|) := by
  --intro x y
  by_cases h : 0 < |x - y| ∧ |x - y| < 1
  . calc ‖K x y‖
      _ ≤ 1 / ‖1 - Complex.exp (Complex.I * ↑(x - y))‖ := by
        rw [K, k, norm_div]
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        . apply max_le
          linarith [abs_nonneg (x-y)]
          linarith
        . apply le_max_right
      _ ≤ 1 / (|x - y| / 8) := by
        gcongr
        . linarith
        . apply lower_secant_bound
          . exact h.1
          . rw [Set.mem_Icc]
            --TODO : improve calculations
            constructor
            . simp
              calc |x - y|
                _ ≤ 1 := h.2.le
                _ ≤ 2 * Real.pi - 1 := by
                  rw [le_sub_iff_add_le]
                  linarith [Real.two_le_pi]
                _ ≤ 2 * Real.pi + (x - y) := by
                  rw [sub_eq_add_neg]
                  gcongr
                  exact (abs_le.mp h.2.le).1
            . calc x - y
                _ ≤ |x - y| := le_abs_self (x - y)
                _ ≤ 1 := h.2.le
                _ ≤ 2 * Real.pi - 1 := by
                  rw [le_sub_iff_add_le]
                  linarith [Real.two_le_pi]
                _ ≤ 2 * Real.pi - |x - y| := by
                  gcongr
                  exact h.2.le
          . trivial
      _ = 8 / |x - y| := by
        field_simp
      _ ≤ (2 : ℝ) ^ (4 : ℝ) / (2 * |x - y|) := by
        ring_nf
        trivial
  . push_neg at h
    have : ‖K x y‖ = 0 := by
      rw [norm_eq_zero, K, k, _root_.div_eq_zero_iff]
      by_cases xeqy : x = y
      . right
        simp [xeqy]
      . left
        simp
        apply h (abs_pos.mpr (sub_ne_zero.mpr xeqy))
    rw [this]
    apply div_nonneg
    . norm_num
    . linarith [abs_nonneg (x-y)]


/-TODO: to mathlib-/
theorem Real.volume_uIoc {a b : ℝ} : MeasureTheory.volume (Set.uIoc a b) = ENNReal.ofReal |b - a| := by
  /- Cf. proof of Real.volume_interval-/
  rw [Set.uIoc, volume_Ioc, max_sub_min_eq_abs]

/-Main part of the proof of Hilbert_kernel_regularity -/
/-TODO: This can be local, i.e. invisible to other files. -/
/-TODO: might be improved using lower_secant_bound' -/
lemma Hilbert_kernel_regularity_main_part {y y' : ℝ} (yy'nonneg : 0 ≤ y ∧ 0 ≤ y') (ypos : 0 < y) (y2ley' : y / 2 ≤ y') (hy : y ≤ 1) (hy' : y' ≤ 1) :
    ‖k (-y) - k (-y')‖ ≤ 2 ^ 10 * (1 / |y|) * (|y - y'| / |y|) := by
  rw [k_of_abs_le_one, k_of_abs_le_one]
  . simp only [abs_neg, Complex.ofReal_neg, mul_neg, ge_iff_le]
    rw [abs_of_nonneg yy'nonneg.1, abs_of_nonneg yy'nonneg.2]
    let f : ℝ → ℂ := fun t ↦ (1 - t) / (1 - Complex.exp (-(Complex.I * t)))
    set f' : ℝ → ℂ := fun t ↦ (-1 + Complex.exp (-(Complex.I * t)) + Complex.I * (t - 1) * Complex.exp (-(Complex.I * t))) / (1 - Complex.exp (-(Complex.I * t))) ^ 2 with f'def
    /-TODO: externalize as lemma?-/
    set c : ℝ → ℂ := fun t ↦ (1 - t) with cdef
    set c' : ℝ → ℂ := fun t ↦ -1 with c'def
    set d : ℝ → ℂ := fun t ↦ (1 - Complex.exp (-(Complex.I * t))) with ddef
    set d' : ℝ → ℂ := fun t ↦ Complex.I * Complex.exp (-(Complex.I * t)) with d'def
    have d_nonzero {t : ℝ} (ht : t ∈ Set.uIcc y' y) : d t ≠ 0 := by
      rw [Set.mem_uIcc] at ht
      have ht' : 0 < t ∧ t ≤ 1 := by
        rcases ht with ht | ht <;> (constructor <;> linarith)
      rw [ddef]
      simp
      rw [←norm_eq_zero]
      apply ne_of_gt
      calc ‖1 - Complex.exp (-(Complex.I * ↑t))‖
        _ ≥ |(1 - Complex.exp (-(Complex.I * ↑t))).im| := by
          simp only [Complex.norm_eq_abs, ge_iff_le]
          apply Complex.abs_im_le_abs
        _ = Real.sin t := by
          simp
          rw [Complex.exp_im]
          simp
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          . linarith
          . linarith [Real.two_le_pi]
        _ > 0 := by
          apply Real.sin_pos_of_pos_of_lt_pi
          . linarith
          . linarith [Real.two_le_pi]
    have f_deriv : ∀ t ∈ Set.uIcc y' y, HasDerivAt f (f' t) t := by
      intro t ht
      have : f = fun t ↦ c t / d t := by simp
      rw [this]
      have : f' = fun t ↦ ((c' t * d t - c t * d' t) / d t ^ 2) := by
        ext t
        rw [f'def, cdef, c'def, ddef, d'def]
        simp
        congr
        ring
      rw [this]
      apply HasDerivAt.div
      . rw [cdef, c'def]
        simp
        apply HasDerivAt.const_sub
        apply HasDerivAt.ofReal_comp
        apply hasDerivAt_id'
      . rw [ddef, d'def]
        simp
        rw [←neg_neg (Complex.I * Complex.exp (-(Complex.I * ↑t)))]
        apply HasDerivAt.const_sub
        rw [←neg_mul, mul_comm]
        apply HasDerivAt.cexp
        apply HasDerivAt.neg
        conv in fun (x : ℝ) ↦ Complex.I * (x : ℝ) =>
          ext
          rw [mul_comm]
        set e : ℂ → ℂ := fun t ↦ t * Complex.I with edef
        have : (fun (t : ℝ) ↦ t * Complex.I) = fun (t : ℝ) ↦ e t := by
          rw [edef]
        rw [this]
        apply HasDerivAt.comp_ofReal
        rw [edef]
        apply hasDerivAt_mul_const
      . exact d_nonzero ht
    have f'_cont : ContinuousOn (fun t ↦ f' t) (Set.uIcc y' y) := by
      apply ContinuousOn.div
      . apply Continuous.continuousOn
        continuity
      . /-TODO: investigate why continuity tactic fails-/
        apply Continuous.continuousOn
        apply Continuous.pow
        apply Continuous.sub
        . apply continuous_const
        . apply Continuous.cexp
          apply Continuous.neg
          apply Continuous.mul
          . apply continuous_const
          . apply Complex.continuous_ofReal
      . intro t ht
        simp
        apply d_nonzero ht
    calc ‖(1 - ↑y) / (1 - Complex.exp (-(Complex.I * ↑y))) - (1 - ↑y') / (1 - Complex.exp (-(Complex.I * ↑y')))‖
      _ = ‖f y - f y'‖ := by simp
      _ = ‖∫ (t : ℝ) in y'..y, f' t‖ := by
        congr 1
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
        . exact f_deriv
        . apply f'_cont.intervalIntegrable
      _ = ‖∫ (t : ℝ) in Ι y' y, f' t‖ := by
        apply intervalIntegral.norm_intervalIntegral_eq
      _ ≤ ∫ (t : ℝ) in Ι y' y, ‖f' t‖ := by
        apply MeasureTheory.norm_integral_le_integral_norm
      _ ≤ ∫ (t : ℝ) in Ι y' y, 3 / ((y / 2) / 8) ^ 2 := by
        apply MeasureTheory.set_integral_mono_on
        . apply f'_cont.norm.integrableOn_uIcc.mono_set
          apply Set.Ioc_subset_Icc_self
        . apply MeasureTheory.integrableOn_const.mpr
          right
          rw [Real.volume_uIoc]
          apply ENNReal.ofReal_lt_top
        . apply measurableSet_uIoc
        . intro t ht
          rw [Set.mem_uIoc] at ht
          have ht' : 0 < t ∧ t ≤ 1 := by
            rcases ht with ht | ht <;> (constructor <;> linarith)
          rw [f'def]
          simp only [norm_div, Complex.norm_eq_abs, norm_pow]
          gcongr
          . calc Complex.abs (-1 + Complex.exp (-(Complex.I * ↑t)) + Complex.I * (↑t - 1) * Complex.exp (-(Complex.I * ↑t)))
              _ ≤ Complex.abs (-1 + Complex.exp (-(Complex.I * ↑t))) + Complex.abs (Complex.I * (↑t - 1) * Complex.exp (-(Complex.I * ↑t))) := by
                apply Complex.abs.isAbsoluteValue.abv_add
              _ ≤ Complex.abs (-1) + Complex.abs (Complex.exp (-(Complex.I * ↑t))) + Complex.abs (Complex.I * (↑t - 1) * Complex.exp (-(Complex.I * ↑t))) := by
                gcongr
                apply Complex.abs.isAbsoluteValue.abv_add
              _ ≤ 1 + 1 + 1 := by
                gcongr
                . simp
                . rw [mul_comm, ←neg_mul]
                  norm_cast
                  apply le_of_eq
                  apply Complex.abs_exp_ofReal_mul_I
                . simp
                  apply mul_le_one
                  norm_cast
                  rw [abs_of_nonpos] <;> linarith
                  simp
                  rw [mul_comm, ←neg_mul]
                  norm_cast
                  apply le_of_eq
                  apply Complex.abs_exp_ofReal_mul_I
              _ = 3 := by norm_num
          . rw [mul_comm, ←neg_mul, mul_comm]
            norm_cast
            apply lower_secant_bound
            . linarith
            . simp
              constructor <;> linarith [Real.two_le_pi, Real.two_pi_pos]
            . rw [abs_neg, le_abs]
              left
              rcases ht with ht | ht <;> linarith [ht.1]
      _ = (MeasureTheory.volume (Ι y' y)).toReal * (3 / ((y / 2) / 8) ^ 2) := by
        apply MeasureTheory.set_integral_const
      _ = |y - y'| * (3 / ((y / 2) / 8) ^ 2) := by
        congr
        rw [Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg (y - y'))]
      _ = (3 * (8 * 2) ^ 2) * (1 / y) * (|y - y'| / y) := by
        ring
      _ ≤ 2 ^ 10 * (1 / y) * (|y - y'| / y) := by
        gcongr
        norm_num
  . rw [abs_neg, abs_of_nonneg yy'nonneg.2]
    assumption
  . rw [abs_neg, abs_of_nonneg yy'nonneg.1]
    assumption

/- Lemma 10.14 (Hilbert kernel regularity) -/
lemma Hilbert_kernel_regularity {x y y' : ℝ} :
    2 * |y - y'| ≤ |x - y| → ‖K x y - K x y'‖ ≤ 2 ^ 10 * (1 / |x - y|) * (|y - y'| / |x - y|)  := by
  rw [K, K]
  wlog x_eq_zero : x = 0 generalizing x y y'
  . intro h
    set x_ := (0 : ℝ) with x_def
    set y_ := y - x with y_def
    set y'_ := y' - x with y'_def
    have h_ : 2 * |y_ - y'_| ≤ |x_ - y_| := by
      rw [x_def, y_def, y'_def]
      simpa
    have := this x_def h_
    rw [x_def, y_def, y'_def] at this
    simpa
  rw [x_eq_zero]
  intro h
  simp at h
  simp only [zero_sub, abs_neg]
  wlog yy'nonneg : 0 ≤ y ∧ 0 ≤ y' generalizing y y'
  . --TODO : improve case distinction to avoid nesting
    by_cases yge0 : 0 ≤ y
    . push_neg at yy'nonneg
      exfalso
      rw [abs_of_nonneg yge0, abs_of_nonneg] at h <;> linarith [yy'nonneg yge0]
    --rcases ltTrichotomy
    . push_neg at yge0
      by_cases y'ge0 : 0 ≤ y'
      . exfalso
        rw [abs_of_neg yge0, abs_of_neg] at h <;> linarith
      . -- This is the only interesting case.
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
        rw [← IsROrC.norm_conj, map_sub, ← k_of_neg_eq_conj_k, ← k_of_neg_eq_conj_k, ←abs_neg (y' - y)] at this
        simpa
  /-"Wlog" 0 < y-/
  by_cases ypos : y ≤ 0
  . have y_eq_zero : y = 0 := by
      exact le_antisymm ypos yy'nonneg.1
    have y'_eq_zero : y' = 0 := by
      rw [y_eq_zero] at h
      simp at h
      rw [abs_of_nonneg yy'nonneg.2] at h
      linarith
    rw [y_eq_zero, y'_eq_zero]
    simp
  push_neg at ypos

  -- Beginning of the main proof.
  have y2ley' : y / 2 ≤ y' := by
    rw [div_le_iff two_pos]
    calc y
      _ = 2 * (y - y') - y + 2 * y' := by ring
      _ ≤ 2 * |y - y'| - y + 2 * y' := by
        gcongr
        apply le_abs_self
      _ ≤ y - y + 2 * y' := by
        gcongr
        rw [abs_eq_self.mpr yy'nonneg.1] at h
        exact h
      _ = y' * 2 := by ring
  /- Distinguish four cases. -/
  rcases le_or_gt y 1, le_or_gt y' 1 with ⟨hy | hy, hy' | hy'⟩
  . exact Hilbert_kernel_regularity_main_part yy'nonneg ypos y2ley' hy hy'
  . rw [@k_of_one_le_abs (-y')]
    . calc ‖k (-y) - 0‖
        _ = ‖k (-y) - k (-1)‖ := by
          congr
          apply (k_of_one_le_abs _).symm
          simp
        _ ≤ 2 ^ 10 * (1 / |y|) * (|y - 1| / |y|) := by
          apply Hilbert_kernel_regularity_main_part
          constructor
          all_goals linarith
        _ ≤ 2 ^ 10 * (1 / |y|) * (|y - y'| / |y|) := by
          gcongr 2 ^ 10 * (1 / |y|) * (?_ / |y|)
          rw [abs_sub_comm, abs_of_nonneg, abs_sub_comm, abs_of_nonneg] <;> linarith
    . rw [abs_neg, abs_of_nonneg] <;> linarith
  . rw [@k_of_one_le_abs (-y)]
    /-TODO: This case does not seem to function as in the paper. Maybe the constant must be increased. -/
    . calc ‖0 - k (-y')‖
        _ = ‖k (-1) - k (-y')‖ := by
          congr
          apply (k_of_one_le_abs _).symm
          simp
        _ = ‖k (-y') - k (-1)‖ := by
          rw [norm_sub_rev]
        _ ≤ 2 ^ 10 * (1 / |y'|) * (|y' - 1| / |y'|) := by
          apply Hilbert_kernel_regularity_main_part
          constructor
          all_goals linarith
        _ = 2 ^ 10 * (1 / y') * ((1 - y') / y') := by
          congr
          . rw [abs_of_nonneg]
            exact yy'nonneg.2
          . rw [abs_of_nonpos]
            simp
            linarith
          . rw [abs_of_nonneg]
            exact yy'nonneg.2
        _ ≤ 2 ^ 10 * (1 / (y / 2)) * ((1 - y') / (y / 2)) := by
          gcongr
          . apply div_nonneg <;> linarith
          . linarith
        _ = (2 ^ 10 * 2 * 2) * (1 / y) * ((1 - y') / y) := by
          ring
        _ ≤ (2 ^ 10 * 2 * 2) * (1 / |y|) * (|y - y'| / |y|) := by
          gcongr
          apply div_nonneg <;> linarith
          rw [abs_of_nonneg yy'nonneg.1]
          rw [abs_of_nonneg] <;> linarith
          rw [abs_of_nonneg yy'nonneg.1]
        _ ≤ 2 ^ 10 * (1 / |y|) * (|y - y'| / |y|) := by
          gcongr
          /-TODO: not possible because constant is too small-/
          sorry
    . rw [abs_neg, abs_of_nonneg] <;> linarith

  . calc ‖k (-y) - k (-y')‖
      _ = 0 := by
        simp
        rw [k_of_one_le_abs, k_of_one_le_abs] <;> (rw [abs_neg, abs_of_nonneg] <;> linarith)
      _ ≤ 2 ^ 10 * (1 / |y|) * (|y - y'| / |y|) := by
        apply mul_nonneg
        apply mul_nonneg
        . norm_num
        . simp
        . apply div_nonneg <;> simp


/-Further definitions-/
/-TODO : relocate this-/

--TODO : call constructor in a better way?
def integer_linear (n : ℤ) : C(ℝ, ℂ) := ⟨fun (x : ℝ) ↦ (n * x : ℂ), by continuity⟩

--local notation "θ" => integer_linear

--lemma θcont {n : ℤ} : Continuous (θ n) := sorry

--local notation "Θ" => {(θ n) | n : ℤ}

def CarlesonOperatorReal (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ⨆ (n : ℤ) (r : ℝ) (rpos : 0 < r),
  ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, K x y * f y * Complex.exp (Complex.I * n * y)‖
