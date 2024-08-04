/- This file contains most of Section 11.6 (The error bound) from the blueprint.
   The main result is control_approximation_effect.
-/
import Carleson.MetricCarleson
import Carleson.Classical.Helper
import Carleson.Classical.Basic
import Carleson.Classical.HilbertKernel
import Carleson.Classical.DirichletKernel
import Carleson.Classical.CarlesonOperatorReal
import Carleson.Classical.CarlesonOnTheRealLine

import Mathlib.Analysis.Fourier.AddCircle


noncomputable section

local notation "T" => CarlesonOperatorReal K
local notation "S_" => partialFourierSum



/- TODO: might be generalized. -/
lemma ENNReal.le_on_subset {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) {f g : X → ENNReal} {E : Set X} (hE : MeasurableSet E)
    (hf : Measurable f) (hg : Measurable g) {a : ENNReal} (h : ∀ x ∈ E, a ≤ f x + g x) :
    ∃ E' ⊆ E, MeasurableSet E' ∧ μ E ≤ 2 * μ E' ∧ ((∀ x ∈ E', a / 2 ≤ f x) ∨ (∀ x ∈ E', a / 2 ≤ g x)) := by
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
        · exact hx'.1 hx
        · exact hx'.2 hx
      _ = a := by
        ring_nf
        apply ENNReal.div_mul_cancel <;> norm_num
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
      exact MeasureTheory.measure_union_le _ _
    _ = 2 * μ Ef + 2 * μ Eg := by ring
    _ < μ E + μ E := by
      gcongr
      · exact hEfg.1
      · exact hEfg.2
    _ = 2 * μ E := by ring
  rcases this with hEf | hEg
  · use Ef
    constructor
    · exact Set.inter_subset_left
    constructor
    · apply MeasurableSet.inter hE
      exact hf measurableSet_Ici
    use hEf
    left
    rw [Ef_def]
    simp
  · use Eg
    constructor
    · exact Set.inter_subset_left
    constructor
    · apply MeasurableSet.inter hE
      exact hg measurableSet_Ici
    use hEg
    right
    rw [Eg_def]
    simp


open Complex ComplexConjugate

lemma Dirichlet_Hilbert_eq {N : ℕ} {x : ℝ} :
    (max (1 - |x|) 0) * dirichletKernel' N (x) = exp (I * (-N * x)) * k x + conj (exp (I * (-N * x)) * k x) := by
  simp [dirichletKernel', K, k, conj_ofReal, ←exp_conj, mul_comm, ←mul_assoc, ←exp_add]
  ring_nf

lemma Dirichlet_Hilbert_diff {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-Real.pi) Real.pi):
    ‖dirichletKernel' N (x) - (exp (I * (-N * x)) * k x + conj (exp (I * (-N * x)) * k x))‖ ≤ Real.pi := by
  rw [← Dirichlet_Hilbert_eq]
  by_cases h : 1 - cexp (I * ↑x) = 0
  · rw [sub_eq_zero] at h
    rw [dirichletKernel'_eq_zero h.symm]
    simp [Real.pi_pos.le]
  push_neg at h
  conv => pattern (dirichletKernel' N x); rw [← (one_mul (dirichletKernel' N x))]
  rw [← sub_mul]
  norm_cast
  rw [← min_sub_sub_left]
  simp only [sub_sub_cancel, sub_zero]
  rw [dirichletKernel', mul_add]
  calc ‖  (min |x| 1) * (exp (I * N * x) / (1 - exp (-I * x)))
        + (min |x| 1) * (exp (-I * N * x) / (1 - exp (I * x)))‖
    _ ≤   ‖(min |x| 1) * (exp (I * N * x) / (1 - exp (-I * x)))‖
        + ‖(min |x| 1) * (exp (-I * N * x) / (1 - exp (I * x)))‖ := by
      apply norm_add_le
    _ ≤ |x| * (1 / ‖1 - exp (I * x)‖) + |x| * (1 / ‖1 - exp (I * x)‖) := by
      simp only [neg_mul, norm_mul, norm_eq_abs, abs_ofReal, norm_div]
      rw [_root_.abs_of_nonneg (by simp)]
      gcongr
      · apply min_le_left
      · simpa
      · rw [mul_assoc I, mul_comm I]
        norm_cast
        rw [abs_exp_ofReal_mul_I]
      . rw [←abs_conj, map_sub, map_one, ←exp_conj, ← neg_mul, map_mul, conj_I, conj_ofReal]
      . apply min_le_left
      . /-Duplicate from above:
        TODO: how to remove duplicate goals? -/
        rw [mul_assoc I, mul_comm I, ← neg_mul]
        norm_cast
        rw [abs_exp_ofReal_mul_I]
    _ = 2 * (|x| / ‖1 - exp (I * x)‖) := by ring
    _ ≤ 2 * (Real.pi / 2) := by
      gcongr 2 * ?_
      rw [div_le_iff' (by rwa [norm_pos_iff]), ←div_le_iff (by linarith [Real.pi_pos]), div_div_eq_mul_div, mul_div_assoc, mul_comm]
      apply lower_secant_bound' (by rfl)
      have : |x| ≤ Real.pi := by
        rwa [abs_le]
      linarith
    _ = Real.pi := by ring


section
open Filter Topology

lemma le_iSup_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (ha : Tendsto f atTop (𝓝 a)) : a ≤ iSup f := by
  apply le_of_forall_lt
  intro c hc
  have : ∀ᶠ (x : β) in atTop, c < f x := eventually_gt_of_tendsto_gt hc ha
  rcases this.exists with ⟨x, hx⟩
  exact lt_of_lt_of_le hx (le_iSup _ _)

lemma integrable_annulus {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {r : ℝ} (r_nonneg : 0 ≤ r) (rle1 : r < 1) :
    MeasureTheory.Integrable (fun x ↦ f x) (MeasureTheory.volume.restrict {y | dist x y ∈ Set.Ioo r 1}) := by
  rw [← MeasureTheory.IntegrableOn, annulus_real_eq r_nonneg]
  apply MeasureTheory.IntegrableOn.union <;>
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    apply hf.mono_set
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith [Real.pi_pos])]
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.two_le_pi]

lemma intervalIntegrable_mul_dirichletKernel' {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * dirichletKernel' N (x - y)) MeasureTheory.volume (x - Real.pi) (x + Real.pi) := by
  apply (hf.mono_set _).mul_bdd (dirichletKernel'_measurable.comp (measurable_id.const_sub _)).aestronglyMeasurable
  · use (2 * N + 1)
    intro y
    apply norm_dirichletKernel'_le
  · rw [Set.uIcc_of_le, Set.uIcc_of_le]
    apply Set.Icc_subset_Icc
    all_goals linarith [hx.1, hx.2, Real.pi_pos]

lemma intervalIntegrable_mul_dirichletKernel'_max {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))) MeasureTheory.volume (x - Real.pi) (x + Real.pi) := by
  conv => pattern ((f _) * _); rw [← mul_assoc]
  apply intervalIntegrable_mul_dirichletKernel' hx (IntervalIntegrable.mul_bdd hf (Complex.measurable_ofReal.comp ((Measurable.const_sub (_root_.continuous_abs.measurable.comp (measurable_id.const_sub _)) _).max measurable_const)).aestronglyMeasurable _)
  use 1
  intro y
  simp only [id_eq, Function.comp_apply, norm_eq_abs, abs_ofReal]
  rw [_root_.abs_of_nonneg (le_max_right _ _)]
  simp

lemma intervalIntegrable_mul_dirichletKernel'_max' {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))) MeasureTheory.volume (x - Real.pi) (x + Real.pi) := by
  conv => pattern ((f _) * _); rw [mul_sub]
  exact (intervalIntegrable_mul_dirichletKernel' hx hf).sub (intervalIntegrable_mul_dirichletKernel'_max hx hf)

lemma domain_reformulation {g : ℝ → ℂ} (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) :
      ∫ (y : ℝ) in x - Real.pi..x + Real.pi,
        g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))
    = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1},
        g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
  calc _
    _ = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 Real.pi}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
      rw [annulus_real_eq (le_refl 0), MeasureTheory.integral_union (by simp) measurableSet_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_union (Set.disjoint_of_subset_right Set.Ioo_subset_Ioc_self (by simp)) measurableSet_Ioo,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), MeasureTheory.integral_Ioc_eq_integral_Ioo,
        sub_zero, add_zero, Set.Ioc_union_Ioo_eq_Ioo (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
      --TODO: Many similar goals => improve this further?
      · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
        apply (intervalIntegrable_mul_dirichletKernel'_max hx hg).mono_set
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos]), Set.uIcc_of_le (by linarith [Real.pi_pos])]
        apply Set.Icc_subset_Icc_right (by linarith [Real.pi_pos])
      all_goals
        rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
        apply (intervalIntegrable_mul_dirichletKernel'_max hx hg).mono_set
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos]), Set.uIcc_of_le (by linarith [Real.pi_pos])]
      · apply Set.Icc_subset_Icc_left (by linarith [Real.pi_pos])
      · apply Set.Icc_subset_Icc_right (by linarith [Real.pi_pos])
      · apply Set.Icc_subset_Icc_left (by linarith [Real.pi_pos])
    _ = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
      rw [←MeasureTheory.integral_indicator annulus_measurableSet, ←MeasureTheory.integral_indicator annulus_measurableSet]
      congr with y
      rw [Set.indicator_apply, Set.indicator_apply, Dirichlet_Hilbert_eq]
      split_ifs with h₀ h₁ h₂
      · trivial
      · dsimp at h₀ h₁
        rw [Real.dist_eq, Set.mem_Ioo] at h₀ h₁
        push_neg at h₁
        rw [k_of_one_le_abs (h₁ h₀.1)]
        simp
      · rw [k_of_one_le_abs]
        . simp
        dsimp at h₀ h₂
        rw [Real.dist_eq, Set.mem_Ioo] at h₀ h₂
        push_neg at h₀
        exact le_trans' (h₀ h₂.1) (by linarith [Real.two_le_pi])
      . trivial

lemma intervalIntegrable_mul_dirichletKernel'_specific {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    MeasureTheory.IntegrableOn (fun y ↦ f y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))) {y | dist x y ∈ Set.Ioo 0 1} MeasureTheory.volume := by
  have : IntervalIntegrable (fun y ↦ f y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))) MeasureTheory.volume (x - Real.pi) (x + Real.pi) := intervalIntegrable_mul_dirichletKernel'_max hx hf
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])] at this
  apply this.mono_set
  intro y hy
  rw [annulus_real_eq (by rfl)] at hy
  rcases hy with h | h <;> constructor <;> linarith [h.1, h.2, hx.1, hx.2, Real.two_le_pi]


lemma le_CarlesonOperatorReal {g : ℝ → ℂ} (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) :
    ‖∫ (y : ℝ) in x - Real.pi..x + Real.pi, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊
    ≤ T g x + T (conj ∘ g) x := by
  rw [domain_reformulation hg hx]
  set s : ℕ → Set ℝ := fun n ↦ {y | dist x y ∈ Set.Ioo (1 / (n + 2 : ℝ)) 1} with sdef
  have hs : {y | dist x y ∈ Set.Ioo 0 1} = ⋃ n, s n := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_setOf_eq, Set.mem_Ioo] at hy
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / dist x y)
      rw [Set.mem_iUnion]
      use n
      rw [sdef, Set.mem_setOf_eq, one_div]
      refine ⟨?_, hy.2⟩
      rw [inv_lt (by linarith) hy.1, inv_eq_one_div]
      apply lt_trans hn
      linarith
    · intro hy
      simp at hy
      rcases hy with ⟨n, hn⟩
      rw [sdef] at hn
      simp at hn
      refine ⟨lt_trans' hn.1 ?_, hn.2⟩
      norm_num
      linarith
  have : Tendsto (fun i => ∫ y in s i, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
          atTop (𝓝 (∫ y in ⋃ n, s n, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))) := by
    apply MeasureTheory.tendsto_setIntegral_of_monotone
    · intro n
      exact annulus_measurableSet
    · intro n m nlem
      simp only [Set.le_eq_subset]
      intro y hy
      rw [sdef] at *
      simp only [one_div, Set.mem_Ioo, Set.mem_setOf_eq] at *
      refine ⟨lt_of_le_of_lt ?_ hy.1, hy.2⟩
      rw [inv_le_inv]
      norm_cast
      all_goals linarith
    · rw [← hs]
      --uses that dirichletKernel' is bounded
      exact intervalIntegrable_mul_dirichletKernel'_specific hx hg
  calc ENNReal.ofNNReal ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊
    _ = ‖∫ y in ⋃ n, s n, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊ := by congr
    _ ≤ ⨆ (i : ℕ), ↑‖∫ y in s i, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊ := by
      apply le_iSup_of_tendsto
      rw [ENNReal.tendsto_coe]
      exact Tendsto.nnnorm this
    _ ≤ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊ := by
      apply iSup_le
      intro n
      apply le_iSup_of_le (1 / (n + 2 : ℝ))
      apply le_iSup₂_of_le (by simp; linarith) (by rw [div_lt_iff] <;> linarith)
      rfl
    _ = ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * N * y) + conj (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * (Int.ofNat N) * y)))‖₊ := by
      apply iSup_congr
      intro r
      apply iSup_congr
      intro _
      apply iSup_congr
      intro _
      congr with y
      congr
      rw [Dirichlet_Hilbert_eq]
      simp only [ofReal_sub, mul_comm, mul_neg, ← mul_assoc, k, map_mul, ← exp_conj, map_neg,
        conj_I, map_sub, conj_ofReal, map_natCast, neg_neg, map_div₀, map_one, Int.ofNat_eq_coe,
        Int.cast_natCast, K, ← exp_add, map_add]
      ring_nf
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊ := by
      let F : ℤ → ENNReal := fun (n : ℤ) ↦ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊
      exact le_iSup F ((Int.ofNat N))
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1), (  ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * K x y * exp (I * n * y)‖₊
                                                    + ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, (conj ∘ g) y * K x y * exp (I * n * y)‖₊) := by
      apply iSup₂_mono
      intro n r
      apply iSup₂_mono
      intro rpos rle1
      norm_cast
      push_cast
      calc ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊
        _ = ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y)) + g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          congr with y
          rw [mul_add]
        _ = ‖ (∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y)))
             + ∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          congr
          -- Integrability follows from r > 0
          have measurable₁ : Measurable fun x_1 ↦ (I * (-↑n * ↑x)).exp * K x x_1 * (I * ↑n * ↑x_1).exp := by
            apply Measurable.mul (Measurable.mul _ Hilbert_kernel_measurable.of_uncurry_left) <;> measurability
          have boundedness₁ {y : ℝ} (h : r ≤ dist x y) : ‖(I * (-↑n * ↑x)).exp * K x y * (I * ↑n * ↑y).exp‖ ≤ (2 ^ (2 : ℝ) / (2 * r)) := by
            calc ‖(I * (-↑n * ↑x)).exp * K x y * (I * ↑n * ↑y).exp‖
              _ = ‖(I * (-↑n * ↑x)).exp‖ * ‖K x y‖ * ‖(I * ↑n * ↑y).exp‖ := by
                rw [norm_mul, norm_mul]
              _ ≤ 1 * (2 ^ (2 : ℝ) / (2 * |x - y|)) * 1 := by
                gcongr
                · rw [norm_eq_abs, mul_comm]
                  norm_cast
                  rw [abs_exp_ofReal_mul_I]
                · exact Hilbert_kernel_bound
                · rw [norm_eq_abs, mul_assoc, mul_comm]
                  norm_cast
                  rw [abs_exp_ofReal_mul_I]
              _ ≤ (2 ^ (2 : ℝ) / (2 * r)) := by
                rw [one_mul, mul_one, ← Real.dist_eq]
                gcongr
          have integrable₁ := (integrable_annulus hx hg rpos.le rle1)
          rw [MeasureTheory.integral_add]
          · conv => pattern ((g _) * _); rw [mul_comm]
            apply MeasureTheory.Integrable.bdd_mul' integrable₁ measurable₁.aestronglyMeasurable
            · rw [MeasureTheory.ae_restrict_iff' annulus_measurableSet]
              apply eventually_of_forall
              exact fun _ hy ↦ boundedness₁ hy.1.le
          · conv => pattern ((g _) * _); rw [mul_comm]
            apply MeasureTheory.Integrable.bdd_mul' integrable₁
            · apply Measurable.aestronglyMeasurable
              exact continuous_star.measurable.comp measurable₁
            · rw [MeasureTheory.ae_restrict_iff' annulus_measurableSet]
              apply eventually_of_forall
              intro y hy
              rw [RCLike.norm_conj]
              exact boundedness₁ hy.1.le
        _ ≤   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          apply nnnorm_add_le
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (g y * K x y * exp (I * n * y))‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * ((conj ∘ g) y * K x y * exp (I * n * y))‖₊ := by
            congr 1
            · congr with y
              ring
            · rw [←nnnorm_star, ←starRingEnd_apply, ←integral_conj]
              congr with y
              simp
              ring
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * K x y * exp (I * n * y)‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, (conj ∘ g) y * K x y * exp (I * n * y)‖₊ := by
          rw [← NNReal.coe_inj]
          push_cast
          norm_cast
          congr 1 <;>
          . rw [MeasureTheory.integral_mul_left, norm_mul, norm_eq_abs, mul_comm I, abs_exp_ofReal_mul_I, one_mul]
    _ ≤ T g x + T (conj ∘ g) x := by
      rw [CarlesonOperatorReal, CarlesonOperatorReal]
      apply iSup₂_le
      intro n r
      apply iSup₂_le
      intro rpos rle1
      gcongr <;>
      · apply le_iSup₂_of_le n r
        apply le_iSup₂_of_le rpos rle1
        trivial

lemma partialFourierSum_bound {δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℂ} (measurable_g : Measurable g)
    (periodic_g : Function.Periodic g (2 * Real.pi)) (bound_g : ∀ x, ‖g x‖ ≤ δ)
    {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) :
    ‖S_ N g x‖₊
      ≤ (T g x + T (conj ∘ g) x) / (ENNReal.ofReal (2 * Real.pi)) + ENNReal.ofReal (Real.pi * δ) := by
  have intervalIntegrable_g : IntervalIntegrable g MeasureTheory.volume (-Real.pi) (3 * Real.pi) := intervalIntegrable_of_bdd measurable_g bound_g
  have decomposition : S_ N g x
      = (  (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi),
              g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
         + (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi),
              g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))))
        / (2 * Real.pi) := by
    calc S_ N g x
      _ = (∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), g y * dirichletKernel' N (x - y)) / (2 * Real.pi) := by
        rw [partialFourierSum_eq_conv_dirichletKernel' (intervalIntegrable_g.mono_set _)]
        ring
        rw [Set.uIcc_of_le, Set.uIcc_of_le]
        apply Set.Icc_subset_Icc
        all_goals linarith [Real.pi_pos]
      _ = (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), g y * dirichletKernel' N (x - y)) / (2 * Real.pi) := by
        --Shift domain of integration using periodicity
        congr 1
        rw [← zero_add (2 * Real.pi), Function.Periodic.intervalIntegral_add_eq _ 0 (x - Real.pi)]
        congr 1
        ring
        exact (periodic_g.mul (dirichletKernel'_periodic.const_sub x))
      _ = (  (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
           + (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))) / (2 * Real.pi) := by
        --Split into two parts
        rw [← intervalIntegral.integral_add (intervalIntegrable_mul_dirichletKernel'_max hx intervalIntegrable_g) (intervalIntegrable_mul_dirichletKernel'_max' hx intervalIntegrable_g)]
        congr with y
        ring

  calc ENNReal.ofNNReal ‖S_ N g x‖₊
    _ ≤ (  ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊
         + ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖₊) / ENNReal.ofReal (2 * Real.pi) := by
      rw [decomposition, nnnorm_div, ENNReal.coe_div (by simp [Real.pi_pos.ne.symm])]
      norm_cast
      gcongr
      . apply nnnorm_add_le
      . rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_of_nonneg Real.two_pi_pos.le]
    _ ≤ (T g x + T (⇑conj ∘ g) x + ENNReal.ofReal (Real.pi * δ * (2 * Real.pi))) / ENNReal.ofReal (2 * Real.pi) := by
      gcongr
      . apply le_CarlesonOperatorReal intervalIntegrable_g hx
      . rw [ENNReal.ofReal]
        norm_cast
        apply NNReal.le_toNNReal_of_coe_le
        rw [coe_nnnorm]

        calc ‖∫ (y : ℝ) in x - Real.pi..x + Real.pi, g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖
          _ ≤ (δ * Real.pi) * |(x + Real.pi) - (x - Real.pi)| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro y hy
            rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hy
            rw [norm_mul]
            gcongr
            · apply bound_g
            . rw [Dirichlet_Hilbert_eq]
              apply Dirichlet_Hilbert_diff
              constructor <;> linarith [hy.1, hy.2]
          _ = Real.pi * δ * (2 * Real.pi) := by
            simp
            rw [←two_mul, _root_.abs_of_nonneg Real.two_pi_pos.le]
            ring
    _ = (T g x + T (conj ∘ g) x) / ENNReal.ofReal (2 * Real.pi) + ENNReal.ofReal (Real.pi * δ) := by
      rw [ENNReal.add_div]
      congr
      rw [← ENNReal.ofReal_div_of_pos Real.two_pi_pos, mul_div_assoc, div_self Real.two_pi_pos.ne.symm, mul_one]

end section

lemma rcarleson_exceptional_set_estimate {δ : ℝ} (δpos : 0 < δ) {f : ℝ → ℂ} {F : Set ℝ} (measurableSetF : MeasurableSet F) (hf : ∀ x, ‖f x‖ ≤ δ * F.indicator 1 x)
    {E : Set ℝ} (measurableSetE : MeasurableSet E) {ε : ENNReal} (hE : ∀ x ∈ E, ε ≤ T f x) :
      ε * MeasureTheory.volume E ≤ ENNReal.ofReal (δ * C10_1 4 2) * MeasureTheory.volume F ^ (2 : ℝ)⁻¹ * MeasureTheory.volume E ^ (2 : ℝ)⁻¹ := by
  calc ε * MeasureTheory.volume E
    _ = ∫⁻ _ in E, ε := by
      symm
      apply MeasureTheory.setLIntegral_const
    _ ≤ ∫⁻ x in E, T f x := by
      apply MeasureTheory.setLIntegral_mono' measurableSetE hE
    _ = ENNReal.ofReal δ * ∫⁻ x in E, T (fun x ↦ (1 / δ) * f x) x := by
      rw [← MeasureTheory.lintegral_const_mul']
      congr with x
      rw [CarlesonOperatorReal_mul δpos]
      congr
      exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal δ * (ENNReal.ofReal (C10_1 4 2) * (MeasureTheory.volume E) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹) := by
      gcongr
      apply rcarleson measurableSetF measurableSetE
      intro x
      simp
      rw [_root_.abs_of_nonneg δpos.le, inv_mul_le_iff δpos]
      exact hf x
    _ = ENNReal.ofReal (δ * C10_1 4 2) * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume E) ^ (2 : ℝ)⁻¹ := by
      rw [ENNReal.ofReal_mul δpos.le]
      ring

lemma rcarleson_exceptional_set_estimate_specific {δ : ℝ} (δpos : 0 < δ) {f : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ δ)
    {E : Set ℝ} (measurableSetE : MeasurableSet E) (E_subset : E ⊆ Set.Icc 0 (2 * Real.pi)) {ε : ENNReal} (hE : ∀ x ∈ E, ε ≤ T f x) :
      ε * MeasureTheory.volume E ≤ ENNReal.ofReal (δ * C10_1 4 2 * (2 * Real.pi + 2) ^ (2 : ℝ)⁻¹) * MeasureTheory.volume E ^ (2 : ℝ)⁻¹ := by
  rw [ENNReal.ofReal_mul (by apply mul_nonneg δpos.le (C10_1_pos one_lt_two).le), ← ENNReal.ofReal_rpow_of_pos (by linarith [Real.pi_pos])]
  set F := (Set.Ioo (0 - 1) (2 * Real.pi + 1)) with Fdef
  set h := F.indicator f with hdef
  have hh : ∀ x, ‖h x‖ ≤ δ * F.indicator 1 x := by
    intro x
    rw [hdef, norm_indicator_eq_indicator_norm, Set.indicator, Set.indicator]
    split_ifs with hx
    . simp only [norm_eq_abs, Pi.one_apply, mul_one]; exact hf x
    . simp
  convert rcarleson_exceptional_set_estimate δpos measurableSet_Ioo hh measurableSetE ?_
  . rw [Real.volume_Ioo]
    ring_nf
  . intro x hx
    rw [hdef, Fdef, ← CarlesonOperatorReal_eq_of_restrict_interval (E_subset hx)]
    exact hE x hx


def C_control_approximation_effect (ε : ℝ) := (C10_1 4 2 * (8 / (Real.pi * ε)) ^ (2 : ℝ)⁻¹) + Real.pi

lemma lt_C_control_approximation_effect {ε : ℝ} (εpos : 0 < ε) : Real.pi < C_control_approximation_effect ε := by
  rw [C_control_approximation_effect]
  apply lt_add_of_pos_of_le _ (by rfl)
  apply mul_pos (C10_1_pos (by norm_num))
  apply Real.rpow_pos_of_pos
  apply div_pos (by norm_num)
  apply mul_pos Real.pi_pos εpos

lemma C_control_approximation_effect_pos {ε : ℝ} (εpos : 0 < ε) : 0 < C_control_approximation_effect ε := lt_trans' (lt_C_control_approximation_effect εpos) Real.pi_pos

lemma C_control_approximation_effect_eq {ε : ℝ} {δ : ℝ} (ε_nonneg : 0 ≤ ε) : C_control_approximation_effect ε * δ = ((δ * C10_1 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ * (2 / ε) ^ (2 : ℝ)⁻¹) / Real.pi) + Real.pi * δ := by
  symm
  rw [C_control_approximation_effect, mul_comm, mul_div_right_comm, mul_comm δ, mul_assoc,
    mul_comm δ, ← mul_assoc, ← mul_assoc, ← add_mul, mul_comm _ (C10_1 4 2), mul_assoc]
  congr
  rw [Real.div_rpow, Real.div_rpow _ (mul_nonneg _ _), Real.mul_rpow, Real.mul_rpow]
  ring_nf
  rw [mul_assoc, mul_comm (2 ^ _), mul_assoc, mul_assoc, mul_assoc, mul_comm (4 ^ _), ← mul_assoc Real.pi⁻¹,
      ← Real.rpow_neg_one Real.pi, ← Real.rpow_add, mul_comm (Real.pi ^ _), ← mul_assoc (2 ^ _), ← Real.mul_rpow]
  congr
  norm_num
  ring_nf
  rw [neg_div, Real.rpow_neg]
  all_goals linarith [Real.pi_pos]



/- This is Lemma 11.6.4 (partial Fourier sums of small) in the blueprint.-/
lemma control_approximation_effect {ε : ℝ} (εpos : 0 < ε) {δ : ℝ} (hδ : 0 < δ)
    {h : ℝ → ℂ} (h_measurable : Measurable h) (h_periodic : h.Periodic (2 * Real.pi)) (h_bound : ∀ x, ‖h x‖ ≤ δ ) :
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, ‖S_ N h x‖ ≤ C_control_approximation_effect ε * δ := by
  set ε' := C_control_approximation_effect ε * δ with ε'def
  set E := {x ∈ Set.Icc 0 (2 * Real.pi) | ∃ N, ε' < abs (S_ N h x)} with Edef
  have E_eq: E = Set.Icc 0 (2 * Real.pi) ∩ ⋃ N : ℕ, {x | ε' < ‖S_ N h x‖} := by
      rw [Edef]
      ext x
      simp
  have measurableSetE : MeasurableSet E := by
    rw [E_eq]
    apply measurableSet_Icc.inter (MeasurableSet.iUnion _)
    intro N
    apply measurableSet_lt measurable_const (Measurable.norm partialFourierSum_uniformContinuous.continuous.measurable)
  have Esubset : E ⊆ Set.Icc 0 (2 * Real.pi) := by
    intro x hx
    rw [Edef] at hx
    simp at hx
    exact hx.1
  use E, Esubset, measurableSetE
  --Change order of proofs to start with the simple part
  rw [and_comm]
  constructor
  · rw [Edef]
    simp only [Set.mem_Icc, Set.mem_diff, Set.mem_setOf_eq, not_and, not_exists, not_lt, and_imp]
    exact fun x x_nonneg x_le_two_pi h ↦ h x_nonneg x_le_two_pi
  -- This is needed later but better fits in here.
  have conj_h_bound : ∀ (x : ℝ), ‖(star ∘ h) x‖ ≤ δ := by
    intro x
    simp only [RCLike.star_def, Function.comp_apply, RingHomIsometric.is_iso]
    exact h_bound x

  have le_operator_add : ∀ x ∈ E, ENNReal.ofReal ((ε' - Real.pi * δ) * (2 * Real.pi)) ≤ T h x + T (conj ∘ h) x := by
    intro x hx
    obtain ⟨xIcc, N, hN⟩ := hx
    have : ENNReal.ofReal (Real.pi * δ * (2 * Real.pi)) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [← (ENNReal.add_le_add_iff_right this)]
    calc ENNReal.ofReal ((ε' - Real.pi * δ) * (2 * Real.pi)) + ENNReal.ofReal (Real.pi * δ * (2 * Real.pi))
      _ = ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ε' := by
        rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
        · ring_nf
        · apply mul_nonneg _ Real.two_pi_pos.le
          rw [ε'def, C_control_approximation_effect_eq εpos.le, add_sub_cancel_right]
          apply div_nonneg (mul_nonneg _ (Real.rpow_nonneg (div_nonneg (by norm_num) εpos.le) _)) Real.pi_pos.le
          rw [mul_assoc]
          apply mul_nonneg hδ.le (mul_nonneg (C10_1_pos one_lt_two).le (Real.rpow_nonneg _ _))
          linarith [Real.pi_pos]
        · apply mul_nonneg (mul_nonneg Real.pi_pos.le hδ.le) Real.two_pi_pos.le
      _ ≤ ENNReal.ofReal (2 * Real.pi) * ‖S_ N h x‖₊ := by
        rw [← ofReal_norm_eq_coe_nnnorm]
        gcongr
        exact hN.le
      _ ≤ ENNReal.ofReal (2 * Real.pi) * ((T h x + T (conj ∘ h) x) / (ENNReal.ofReal (2 * Real.pi)) + ENNReal.ofReal (Real.pi * δ)) := by
        gcongr
        apply partialFourierSum_bound hδ h_measurable h_periodic h_bound xIcc
      _ = (T h x + T (conj ∘ h) x) + ENNReal.ofReal (Real.pi * δ * (2 * Real.pi)) := by
        rw [mul_add]
        congr
        . rw [ENNReal.mul_div_cancel' (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top]
        . rw [← ENNReal.ofReal_mul Real.two_pi_pos.le]
          ring_nf
  --TODO: align this with paper version
  have Evolume : MeasureTheory.volume E < ⊤ := by
    calc MeasureTheory.volume E
      _ ≤ MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) := by
        apply MeasureTheory.measure_mono
        rw [E_eq]
        apply Set.inter_subset_left
      _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [Real.volume_Icc, sub_zero]
      _ < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨E', E'subset, measurableSetE', E'measure, h⟩ := ENNReal.le_on_subset MeasureTheory.volume measurableSetE (CarlesonOperatorReal_measurable h_measurable h_bound) (CarlesonOperatorReal_measurable (continuous_star.measurable.comp h_measurable) conj_h_bound) le_operator_add
  have E'volume : MeasureTheory.volume E' < ⊤ := lt_of_le_of_lt (MeasureTheory.measure_mono E'subset) Evolume
  have E'volume_bound: ENNReal.ofReal (Real.pi * (ε' - Real.pi * δ)) * MeasureTheory.volume E' ≤ ENNReal.ofReal (δ * C10_1 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹) * (MeasureTheory.volume E') ^ (2 : ℝ)⁻¹ := by
    calc ENNReal.ofReal (Real.pi * (ε' - Real.pi * δ)) * MeasureTheory.volume E'
    _ = ENNReal.ofReal ((ε' - Real.pi * δ) * (2 * Real.pi)) / 2 * MeasureTheory.volume E' := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      ring_nf
    _ ≤ ENNReal.ofReal (δ * C10_1 4 2 * (2 * Real.pi + 2) ^ (2 : ℝ)⁻¹) * (MeasureTheory.volume E') ^ (2 : ℝ)⁻¹ := by
      rcases h with hE' | hE'
      · exact rcarleson_exceptional_set_estimate_specific hδ h_bound measurableSetE' (E'subset.trans Esubset) hE'
      . exact rcarleson_exceptional_set_estimate_specific hδ conj_h_bound measurableSetE' (E'subset.trans Esubset) hE'
    _ ≤ ENNReal.ofReal (δ * C10_1 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹) * (MeasureTheory.volume E') ^ (2 : ℝ)⁻¹ := by
      gcongr
      . exact mul_nonneg hδ.le (C10_1_pos one_lt_two).le
      . linarith [Real.two_le_pi]
  have δ_mul_const_pos : 0 < δ * C10_1 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ := mul_pos (mul_pos hδ (C10_1_pos one_lt_two)) (Real.rpow_pos_of_pos (by linarith [Real.two_pi_pos]) _)
  have ε'_δ_expression_pos : 0 < Real.pi * (ε' - Real.pi * δ) := by
    rw [ε'def, C_control_approximation_effect_eq εpos.le, add_sub_cancel_right, mul_div_cancel₀ _ Real.pi_pos.ne.symm]
    exact mul_pos δ_mul_const_pos (Real.rpow_pos_of_pos (div_pos (by norm_num) εpos) _)
  calc MeasureTheory.volume.real E
    _ ≤ 2 * MeasureTheory.volume.real E' := by
      --uses E'measure
      rwa [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, ←@ENNReal.toReal_ofReal 2 (by norm_num),
        ←ENNReal.toReal_mul, ENNReal.toReal_le_toReal Evolume.ne, ENNReal.ofReal_ofNat]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top E'volume.ne
    _ = 2 * MeasureTheory.volume.real E' ^ ((1 + -(2 : ℝ)⁻¹) * 2) := by
      conv => lhs; rw [←Real.rpow_one (MeasureTheory.volume.real E')]
      norm_num
    _ ≤ 2 * (δ * C10_1 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ / (Real.pi * (ε' - Real.pi * δ))) ^ (2 : ℝ) := by
      rw [Real.rpow_mul MeasureTheory.measureReal_nonneg]
      gcongr
      rw [Real.rpow_add' MeasureTheory.measureReal_nonneg (by norm_num), Real.rpow_one, le_div_iff' ε'_δ_expression_pos, ← mul_assoc]
      apply mul_le_of_nonneg_of_le_div δ_mul_const_pos.le
      apply Real.rpow_nonneg MeasureTheory.measureReal_nonneg
      rw[Real.rpow_neg MeasureTheory.measureReal_nonneg, div_inv_eq_mul]
      rw [← ENNReal.ofReal_le_ofReal_iff, ENNReal.ofReal_mul ε'_δ_expression_pos.le, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal E'volume.ne]
      apply le_trans E'volume_bound
      rw [ENNReal.ofReal_mul δ_mul_const_pos.le, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal E'volume.ne]
      apply mul_nonneg δ_mul_const_pos.le
      apply Real.rpow_nonneg MeasureTheory.measureReal_nonneg
    _ = ε := by
      --We have defined C_control_approximation_effect such that this works.
      rw [ε'def, C_control_approximation_effect_eq εpos.le, add_sub_cancel_right, mul_div_cancel₀ _ Real.pi_pos.ne.symm,
          div_mul_eq_div_div, div_self δ_mul_const_pos.ne.symm, one_div, Real.inv_rpow (Real.rpow_nonneg (div_nonneg zero_le_two εpos.le) _),
          ← Real.rpow_mul (div_nonneg zero_le_two εpos.le), inv_mul_cancel (by norm_num), Real.rpow_one, inv_div]
      ring
