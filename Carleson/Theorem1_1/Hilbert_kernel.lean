import Carleson.Theorem1_1.Basic

noncomputable section



def k (x : ℝ) : ℂ := max (1 - |x|) 0 / (1 - Complex.exp (Complex.I * x))
--TODO: maybe change to
--def k : ℝ → ℂ := fun x ↦ max (1 - |x|) 0 / (1 - Complex.exp (Complex.I * x))

/- Little helper lemmas. -/
lemma k_of_neg_eq_conj_k {x : ℝ} : k (-x) = (starRingEnd ℂ) (k x) := by
  rw [k, k]
  simp
  rw [Complex.conj_ofReal, ←Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul]

lemma k_of_abs_le_one {x : ℝ} (abs_le_one : |x| ≤ 1) : k x = (1 - |x|) / (1 - Complex.exp (Complex.I * x)) := by
  rw [k, max_eq_left (by linarith)]
  norm_cast

lemma k_of_one_le_abs {x : ℝ} (abs_le_one : 1 ≤ |x|) : k x = 0 := by
  rw [k, max_eq_right (by linarith)]
  simp

@[measurability]
lemma k_measurable : Measurable k := by
  apply Measurable.div
  . apply Measurable.comp'
    . exact Complex.measurable_ofReal
    . apply Measurable.max
      . apply Measurable.const_sub
        apply measurable_norm
      . apply measurable_const
  . measurability

def K (x y : ℝ) : ℂ := k (x - y)
--TODO: maybe change to
--def K : ℝ → ℝ → ℂ := fun x y ↦ k (x - y)

@[measurability]
lemma Hilbert_kernel_measurable : Measurable (Function.uncurry K) := by
  apply Measurable.comp
  . exact k_measurable
  . apply measurable_sub

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
        apply MeasureTheory.setIntegral_mono_on
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
        apply MeasureTheory.setIntegral_const
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
        rw [← RCLike.norm_conj, map_sub, ← k_of_neg_eq_conj_k, ← k_of_neg_eq_conj_k, ←abs_neg (y' - y)] at this
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
