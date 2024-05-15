import Carleson.Carleson
import Carleson.HomogeneousType
import Mathlib.Analysis.Fourier.AddCircle


open BigOperators
open Finset

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


/-Lemmas 9-14.-/

/-Lemma 10.10 (Dirichlet kernel) from the paper.-/
--lemma dirichlet_kernel :

/- Lemma 10.11 (lower secant bound) from the paper. -/
lemma lower_secant_bound {η : ℝ} (ηpos : η > 0) {x : ℝ} (xIcc : x ∈ Set.Icc (-2 * Real.pi + η) (2 * Real.pi - η)) (xAbs : η ≤ |x|) :
    η / 8 ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
  sorry


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
  simp only [zero_sub, abs_neg] --, one_div
  wlog yy'nonneg : 0 ≤ y ∧ 0 ≤ y' generalizing y y'
  . --TODO : improve case distinction to avoid nesting
    --rcases (not_and_or.mp yy'_nonneg) with
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
  . rw [k_of_abs_le_one, k_of_abs_le_one]
    . simp only [abs_neg, Complex.ofReal_neg, mul_neg, ge_iff_le]
      rw [abs_of_nonneg yy'nonneg.1, abs_of_nonneg yy'nonneg.2]
      sorry
    . rw [abs_neg, abs_of_nonneg yy'nonneg.2]
      assumption
    . rw [abs_neg, abs_of_nonneg yy'nonneg.1]
      assumption
  . sorry
  . sorry
  . sorry
