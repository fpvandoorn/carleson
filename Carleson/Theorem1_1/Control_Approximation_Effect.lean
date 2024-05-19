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
lemma le_on_subset {α : Type} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ} {E : Set α} (hE : MeasurableSet E) (hf : Measurable f) (hg : Measurable g) {a : ℝ} (h : ∀ x ∈ E, a ≤ f x + g x) :
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
--added subset assumption
--changed interval to match the interval in the theorem
lemma control_approximation_effect {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (h x) ≤ (2 ^ (- (2 ^ 50 : ℝ))) * ε ^ 2 ):
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, Complex.abs (partialFourierSum h N x) ≤ ε / 4 := by
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
  . have le_operator_add: ∀ x ∈ E, ε / 8 ≤ 1 / (2 * Real.pi) * (T h x + T ((starRingEnd ℂ) ∘ h) x) := by
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
        _ ≤ 1 / (2 * Real.pi) * (T h x + T (⇑(starRingEnd ℂ) ∘ h) x) + ε / 8:= by
          --Estimate the two parts
          gcongr
          . sorry
          . sorry
    sorry
  rw [Edef]
  simp
  exact fun x x_nonneg x_le_two_pi h ↦ h x_nonneg x_le_two_pi
