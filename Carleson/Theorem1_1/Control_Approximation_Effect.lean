/- This file formalizes section 10.8 (The error bound) from the paper. -/
import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Dirichlet_kernel
import Carleson.Theorem1_1.Carleson_on_the_real_line

import Mathlib.Analysis.Fourier.AddCircle


noncomputable section

local notation "T" => CarlesonOperatorReal K

/-TODO: version with general measure on X ?-/
lemma le_on_subset {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {f g : α → ℝ} {E : Set α} (hE : MeasurableSet E)
    (hf : Measurable f) (hg : Measurable g) {a : ℝ} (h : ∀ x ∈ E, a ≤ f x + g x) :
    (∃ E' ⊆ E, MeasurableSet E' ∧ μ E ≤ 2 * μ E' ∧ ∀ x ∈ E', a / 2 ≤ f x) ∨ (∃ E' ⊆ E, MeasurableSet E' ∧ μ E ≤ 2 * μ E' ∧ ∀ x ∈ E', a / 2 ≤ g x) := by
  set Ef := E ∩ f⁻¹' (Set.Ici (a / 2)) with Ef_def
  set Eg := E ∩ g⁻¹' (Set.Ici (a / 2)) with Eg_def
  have : E ⊆ Ef ∪ Eg := by
    intro x hx
    rw [Ef_def, Eg_def]
    simp
    by_contra hx'
    push_neg at hx'
    absurd le_refl a
    push_neg
    calc a
      _ ≤ f x + g x := h x hx
      _ < a / 2 + a / 2 := by
        gcongr
        . exact hx'.1 hx
        . exact hx'.2 hx
      _ = a := by linarith
  have : μ E ≤ 2 * μ Ef ∨ μ E ≤ 2 * μ Eg := by
    by_contra hEfg
    push_neg at hEfg
    absurd le_refl (2 * μ E)
    push_neg
    calc 2 * μ E
    _ ≤ 2 * μ (Ef ∪ Eg) := by
      gcongr
    _ ≤ 2 * (μ Ef + μ Eg) := by
      gcongr
      apply MeasureTheory.measure_union_le
    _ = 2 * μ Ef + 2 * μ Eg := by ring
    _ < μ E + μ E := by
      gcongr
      . exact hEfg.1
      . exact hEfg.2
    _ = 2 * μ E := by ring
  rcases this with hEf | hEg
  . left
    use Ef
    constructor
    . apply Set.inter_subset_left
    constructor
    . apply MeasurableSet.inter hE
      apply hf measurableSet_Ici
    use hEf
    rw [Ef_def]
    simp
  . right
    use Eg
    constructor
    . apply Set.inter_subset_left
    constructor
    . apply MeasurableSet.inter hE
      apply hg measurableSet_Ici
    use hEg
    rw [Eg_def]
    simp

/-Slightly more general version of Lemma 10.3 (control approximation effect).-/
--TODO : review measurability assumption
--TODO : add assumption that h is periodic?
--TODO : introduce δ instead of explicit dependency on term of ε
--added subset assumption
--changed interval to match the interval in the theorem

lemma control_approximation_effect {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (h x) ≤ (2 ^ (- (2 ^ 50 : ℝ))) * ε ^ 2 ):
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, Complex.abs (partialFourierSum h N x) ≤ ε / 4 := by sorry
/-
  set E := {x ∈ Set.Icc 0 (2 * Real.pi) | ∃ N, ε / 4 < Complex.abs (partialFourierSum h N x)} with Edef
  use E
  constructor
  . intro x hx
    rw [Edef] at hx
    simp at hx
    exact hx.1
  constructor
  . have : E = Set.Icc 0 (2 * Real.pi) ∩ ⋃ N : ℕ, {x | ε / 4 < ‖partialFourierSum h N x‖} := by
      rw [Edef]
      ext x
      simp
    rw [this]
    apply MeasurableSet.inter
    . apply measurableSet_Icc
    apply MeasurableSet.iUnion
    intro N
    apply measurableSet_lt
    . apply measurable_const
    apply Measurable.norm
    apply partialFourierSum_uniformContinuous.continuous.measurable
  constructor
  . set F := Set.Icc (-Real.pi) (3 * Real.pi) with Fdef
    set f := fun x ↦ h x * F.indicator 1 x with fdef
    have le_operator_add: ∀ x ∈ E, ε / 8 ≤ 1 / (2 * Real.pi) * (T f x + T ((starRingEnd ℂ) ∘ f) x) := by
      have h_intervalIntegrable : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) := by
        apply @IntervalIntegrable.mono_fun' _ _ _ _ _ _ (fun x ↦ (2 ^ (- (2 ^ 50 : ℝ))) * ε ^ 2)
        apply intervalIntegrable_const
        exact hh.1.aestronglyMeasurable
        rw [Filter.EventuallyLE, ae_restrict_iff_subtype]
        apply Filter.eventually_of_forall
        simp only [Complex.norm_eq_abs, Subtype.forall]
        intro x hx
        apply hh.2 x
        apply Set.Ioc_subset_Icc_self
        rwa [Set.uIoc_of_le Real.two_pi_pos.le] at hx
        apply measurableSet_uIoc
      intro x hx
      obtain ⟨xIcc, N, hN⟩ := hx
      rw [partialFourierSum_eq_conv_dirichletKernel h_intervalIntegrable] at hN
      rw [←add_le_add_iff_right (ε / 8)]
      calc ε / 8 + ε / 8
        _ ≤ ε / 4 := by linarith
        _ ≤ Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h y * dirichletKernel N (x - y)) := hN.le
        _ = Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h (x - y) * dirichletKernel N y) := by
          --Change of variables
          sorry
        _ = Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * dirichletKernel N y) := by
          --Shift domain of integration using periodicity
          sorry
        _ =   Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (max (1 - |y|) 0) * dirichletKernel N y)
            + Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel N y) :=
          --Split into two parts
          sorry
        --Exchange f for h somewhere here
        _ ≤ 1 / (2 * Real.pi) * (T f x + T (⇑(starRingEnd ℂ) ∘ f) x) + ε / 8:= by
          --Estimate the two parts
          gcongr
          . sorry
          . sorry
    conv at le_operator_add in ε / 8 ≤ _ =>
      rw [←(div_le_iff' (by norm_num; exact Real.pi_pos)), div_div_div_eq]
      simp
    /-TODO: avoid completely analogous cases by wlog tactic?-/
    rcases le_on_subset MeasureTheory.volume sorry sorry sorry le_operator_add with ⟨E', E'subset, measurableSetE', E'measure, hE'⟩ | ⟨E', E'subset, measurableSetE', E'measure, hE'⟩
    . have : ε * (2 * Real.pi) / 8 * MeasureTheory.volume.real E' ≤ 2 ^ (-2 ^ 40 : ℝ) * ε ^ 2 / 8 * (MeasureTheory.volume.real E') ^ (1 / 2) := by
        calc ε * (2 * Real.pi) / 8 * MeasureTheory.volume.real E'
          _ = MeasureTheory.volume.real E' * (ε * (2 * Real.pi) / 8 / 2) := by ring
          _ = ∫ x in E', ε * (2 * Real.pi) / 8 / 2 := by
            symm
            apply MeasureTheory.set_integral_const
          _ ≤ ∫ x in E', T f x := by
            apply MeasureTheory.set_integral_mono_on _ _ measurableSetE'
            . exact hE'
            . sorry
            . sorry
          _ ≤ 2 ^ (-2 ^ 40 : ℝ) * ε ^ 2 / 8 * (MeasureTheory.volume.real E') ^ (1 / 2) := by sorry
      sorry
    . -- Analogous to first case.
      sorry
  rw [Edef]
  simp
  exact fun x x_nonneg x_le_two_pi h ↦ h x_nonneg x_le_two_pi
-/



--changed statement
lemma control_approximation_effect' {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) {δ : ℝ} (hδ : 0 < δ)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc (-Real.pi) (3 * Real.pi), Complex.abs (h x) ≤ δ ):
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, Complex.abs (partialFourierSum h N x) ≤ ε / 4 := by
  --TODO: change later
  set ε' := ε / 4 with ε'def
  set E := {x ∈ Set.Icc 0 (2 * Real.pi) | ∃ N, ε' < Complex.abs (partialFourierSum h N x)} with Edef
  have measurableSetE : MeasurableSet E := by
    have : E = Set.Icc 0 (2 * Real.pi) ∩ ⋃ N : ℕ, {x | ε' < ‖partialFourierSum h N x‖} := by
      rw [Edef]
      ext x
      simp
    rw [this]
    apply MeasurableSet.inter
    . apply measurableSet_Icc
    apply MeasurableSet.iUnion
    intro N
    apply measurableSet_lt
    . apply measurable_const
    apply Measurable.norm
    apply partialFourierSum_uniformContinuous.continuous.measurable
  use E
  constructor
  . intro x hx
    rw [Edef] at hx
    simp at hx
    exact hx.1
  use measurableSetE
  constructor
  . set F := Set.Icc (-Real.pi) (3 * Real.pi) with Fdef
    set f := fun x ↦ h x * F.indicator 1 x with fdef
    have le_operator_add: ∀ x ∈ E, ε' - 8 * δ ≤ 1 / (2 * Real.pi) * (T f x + T ((starRingEnd ℂ) ∘ f) x) := by
      have h_intervalIntegrable : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) := by
        apply @IntervalIntegrable.mono_fun' _ _ _ _ _ _ (fun x ↦ δ)
        apply intervalIntegrable_const
        exact hh.1.aestronglyMeasurable
        rw [Filter.EventuallyLE, ae_restrict_iff_subtype]
        apply Filter.eventually_of_forall
        simp only [Complex.norm_eq_abs, Subtype.forall]
        intro x hx
        apply hh.2 x
        apply Set.Ioc_subset_Icc_self
        --rwa [Set.uIoc_of_le Real.two_pi_pos.le] at hx
        sorry
        apply measurableSet_uIoc
      intro x hx
      obtain ⟨xIcc, N, hN⟩ := hx
      rw [partialFourierSum_eq_conv_dirichletKernel' h_intervalIntegrable] at hN
      rw [←add_le_add_iff_right (8 * δ)]
      calc ε' - 8 * δ + 8 * δ
        _ = ε' := by linarith
        _ ≤ Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h y * dirichletKernel' N (x - y)) := hN.le
        _ = Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h (x - y) * dirichletKernel' N y) := by
          --Change of variables
          sorry
        _ = Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * dirichletKernel' N y) := by
          --Shift domain of integration using periodicity
          sorry
        _ =   Complex.abs (1 / (2 * ↑Real.pi) * (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (max (1 - |y|) 0) * dirichletKernel' N y)
                         + 1 / (2 * ↑Real.pi) * (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel' N y)) := by
          --Split into two parts
          congr
          rw [←mul_add, ←intervalIntegral.integral_add]
          . congr
            ext y
            rw [←add_mul, ←mul_add]
            congr
            conv => lhs; rw [←mul_one (h (x - y))]
            congr
            norm_cast
            rw [min_def]
            split_ifs
            . rw [max_eq_left (by linarith)]
              simp
            . rw [max_eq_right (by linarith)]
              simp
          --use lemma that dirichletKernel is bounded
          sorry
          sorry
        _ ≤   Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (max (1 - |y|) 0) * dirichletKernel' N y)
            + Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel' N y) := by
          apply Complex.abs.isAbsoluteValue.abv_add
        --Exchange f for h somewhere here
        _ ≤ 1 / (2 * Real.pi) * (T f x + T (⇑(starRingEnd ℂ) ∘ f) x) + 8 * δ:= by
          --Estimate the two parts
          gcongr
          . --first part
            sorry
          . --second part
            calc Complex.abs (1 / (2 * ↑Real.pi) * ∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel' N y)
              _ ≤ 1 / (2 * Real.pi) * ((δ * 8) * |Real.pi - -Real.pi|) := by
                simp only [one_div, mul_inv_rev, map_mul, map_inv₀, Complex.abs_ofReal,
                  Complex.abs_ofNat]
                rw [abs_of_nonneg Real.pi_pos.le]
                gcongr
                rw [←Complex.norm_eq_abs]
                apply intervalIntegral.norm_integral_le_of_norm_le_const
                intro y hy
                rw [Set.uIoc_of_le (by linarith)] at hy
                rw [mul_assoc, norm_mul]
                gcongr
                . rw [Complex.norm_eq_abs]
                  apply hh.2
                  rw [Fdef]
                  simp
                  constructor <;> linarith [xIcc.1, xIcc.2, hy.1, hy.2]
                rw [dirichletKernel', mul_add]
                calc ‖  (min |y| 1) * (Complex.exp (Complex.I * N * y) / (1 - Complex.exp (-Complex.I * y)))
                      + (min |y| 1) * (Complex.exp (-Complex.I * N * y) / (1 - Complex.exp (Complex.I * y)))‖
                  _ ≤   ‖(min |y| 1) * (Complex.exp (Complex.I * N * y) / (1 - Complex.exp (-Complex.I * y)))‖
                      + ‖(min |y| 1) * (Complex.exp (-Complex.I * N * y) / (1 - Complex.exp (Complex.I * y)))‖ := by
                    apply norm_add_le
                  _ = min |y| 1 * 1 / ‖1 - Complex.exp (Complex.I * y)‖ + min |y| 1 * 1 / ‖1 - Complex.exp (Complex.I * y)‖ := by
                    simp
                    congr
                    . simp only [abs_eq_self, le_min_iff, abs_nonneg, zero_le_one, and_self]
                    . rw [mul_assoc Complex.I, mul_comm Complex.I]
                      norm_cast
                      rw [Complex.abs_exp_ofReal_mul_I, one_div, ←Complex.abs_conj, map_sub, map_one, ←Complex.exp_conj, ← neg_mul, map_mul,
                            Complex.conj_neg_I, Complex.conj_ofReal]
                    . /-Duplicate from above:
                      TODO: how to remove duplicate goals? -/
                      simp only [abs_eq_self, le_min_iff, abs_nonneg, zero_le_one, and_self]
                    . rw [mul_assoc Complex.I, mul_comm Complex.I, ←neg_mul]
                      norm_cast
                      rw [Complex.abs_exp_ofReal_mul_I, one_div]
                  _ = 2 * (min |y| 1 / ‖1 - Complex.exp (Complex.I * y)‖) := by ring
                  _ ≤ 2 * 4 := by
                    gcongr
                    . by_cases h : (1 - Complex.exp (Complex.I * y)) = 0
                      . rw [h]
                        simp
                      simp
                      rw [div_le_iff', ←div_le_iff, ←Complex.norm_eq_abs]
                      apply lower_secant_bound'
                      . apply min_le_left
                      . have : |y| ≤ Real.pi := by
                          rw [abs_le]
                          exact ⟨hy.1.le, hy.2⟩
                        rw [min_def]
                        split_ifs <;> linarith
                      . norm_num
                      . rwa [←Complex.norm_eq_abs, norm_pos_iff]
                  _ = 8 := by norm_num
              _ = 8 * δ := by
                rw [sub_neg_eq_add, ←two_mul, abs_of_nonneg Real.two_pi_pos.le]
                field_simp
                ring
    conv at le_operator_add in ε' - 8 * δ ≤ _ =>
      rw [←(div_le_iff' (by norm_num; exact Real.pi_pos)), div_div_eq_mul_div]
      simp
    /-TODO: avoid completely analogous cases by wlog tactic?
      maybe switch "rcases" and first "have"-/
    rcases le_on_subset MeasureTheory.volume measurableSetE sorry sorry le_operator_add with ⟨E', E'subset, measurableSetE', E'measure, hE'⟩ | ⟨E', E'subset, measurableSetE', E'measure, hE'⟩
    . have : Real.pi * (ε' - 8 * δ) * MeasureTheory.volume.real E' ≤ δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real E') ^ (2 : ℝ)⁻¹ := by
        calc Real.pi * (ε' - 8 * δ) * MeasureTheory.volume.real E'
          _ = MeasureTheory.volume.real E' * ((ε' - 8 * δ) * (2 * Real.pi) / 2) := by ring
          _ = ∫ x in E', (ε' - 8 * δ) * (2 * Real.pi) / 2 := by
            symm
            apply MeasureTheory.set_integral_const
          _ ≤ ∫ x in E', T f x := by
            apply MeasureTheory.set_integral_mono_on _ _ measurableSetE'
            . exact hE'
            . rw [MeasureTheory.integrableOn_const]
              right
              have : E' ⊆ Set.Icc 0 (2 * Real.pi) := by sorry
              sorry
              --rw [ENNReal.lt_top]
              --linarith
              --simp
              --rw [lt_top]
              --use ⟨2 * ε, by linarith⟩
              --simp
              --apply E'measure
            . sorry
          _ = δ * ∫ x in E', T (fun x ↦ (1 / δ) * f x) x := by
            --add lemma CarlesonOperatorReal_mul
            sorry
          _ ≤ δ * (C1_2 4 2 * (MeasureTheory.volume.real E') ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real F) ^ (2 : ℝ)⁻¹) := by
            gcongr
            apply rcarleson
            . apply measurableSet_Icc
            . exact measurableSetE'
            . sorry
            . sorry
            . intro x
              rw [fdef]
              simp
              rw [abs_of_nonneg hδ.le, inv_mul_le_iff hδ, Set.indicator_apply, Set.indicator_apply]
              split_ifs with inF
              . simp
                exact hh.2 x inF
              . simp
          _ = δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real E') ^ (2 : ℝ)⁻¹ := by
            ring_nf
            congr
            rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
            . ring
            . ring_nf
              positivity
      calc MeasureTheory.volume.real E
        _ ≤ 2 * MeasureTheory.volume.real E' := by
          -- use E'measure
          rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, ←@ENNReal.toReal_ofReal 2 (by norm_num),
            ←ENNReal.toReal_mul, ENNReal.toReal_le_toReal, ENNReal.ofReal_ofNat]
          exact E'measure
          sorry
          sorry
        _ = 2 * MeasureTheory.volume.real E' ^ ((1 + -(2 : ℝ)⁻¹) * 2) := by
          conv => lhs; rw [←Real.rpow_one (MeasureTheory.volume.real E')]
          congr
          norm_num
        _ ≤ 2 * (δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ / (Real.pi * (ε' - 8 * δ))) ^ (2 : ℝ) := by
          gcongr
          have two_pos : 0 < (2 : ℝ) := by linarith
          rw [←mul_inv_le_iff', ←Real.rpow_neg, mul_assoc, ←Real.rpow_one_add', ←le_div_iff', ←(Real.rpow_le_rpow_iff _ _ two_pos), ←Real.rpow_mul] at this
          exact this
          -- multiple small goals remaining
          all_goals sorry
        _ = ε := by
          --choose ε' such that this works
          sorry
    . -- Analogous to first case.
      sorry
  rw [Edef]
  simp
  exact fun x x_nonneg x_le_two_pi h ↦ h x_nonneg x_le_two_pi
