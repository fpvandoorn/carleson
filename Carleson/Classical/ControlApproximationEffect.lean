module

public import Carleson.Classical.CarlesonOnTheRealLine
public import Carleson.ToMathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Carleson.ToMathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/- This file contains most of Section 11.6 (The error bound) from the blueprint.
   The main result is control_approximation_effect.
-/

noncomputable section

local notation "T" => carlesonOperatorReal K
local notation "S_" => partialFourierSum

open scoped Real
open MeasureTheory
open Real (pi_pos)


/- TODO: might be generalized. -/
lemma ENNReal.le_on_subset {X : Type} [MeasurableSpace X] (μ : Measure X) {f g : X → ENNReal}
    {E : Set X} (hE : MeasurableSet E)
    (hf : Measurable f) (hg : Measurable g) {a : ENNReal} (h : ∀ x ∈ E, a ≤ f x + g x) :
    ∃ E' ⊆ E, MeasurableSet E' ∧ μ E ≤ 2 * μ E'
      ∧ ((∀ x ∈ E', a / 2 ≤ f x) ∨ (∀ x ∈ E', a / 2 ≤ g x)) := by
  set Ef := E ∩ f⁻¹' (Set.Ici (a / 2)) with Ef_def
  set Eg := E ∩ g⁻¹' (Set.Ici (a / 2)) with Eg_def
  have : E ⊆ Ef ∪ Eg := by
    intro x hx
    rw [Ef_def, Eg_def]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    by_contra! hx'
    absurd le_refl a
    push Not
    calc a
      _ ≤ f x + g x := h x hx
      _ < a / 2 + a / 2 := by
        exact ENNReal.add_lt_add (hx'.1 hx) (hx'.2 hx)
      _ = a := by
        ring_nf
        apply ENNReal.div_mul_cancel <;> norm_num
  have : μ E ≤ 2 * μ Ef ∨ μ E ≤ 2 * μ Eg := by
    by_contra! hEfg
    absurd le_refl (2 * μ E)
    push Not
    calc 2 * μ E
    _ ≤ 2 * μ (Ef ∪ Eg) := by
      gcongr
    _ ≤ 2 * (μ Ef + μ Eg) := by
      gcongr
      exact measure_union_le _ _
    _ = 2 * μ Ef + 2 * μ Eg := by ring
    _ < μ E + μ E := by
      exact ENNReal.add_lt_add hEfg.1 hEfg.2
    _ = 2 * μ E := by ring
  rcases this with hEf | hEg
  · refine ⟨Ef, Set.inter_subset_left, hE.inter (hf measurableSet_Ici), hEf, Or.inl ?_⟩
    simp [Ef_def]
  · refine ⟨Eg, Set.inter_subset_left, hE.inter (hg measurableSet_Ici), hEg, Or.inr ?_⟩
    simp [Eg_def]

open Complex ComplexConjugate

lemma Dirichlet_Hilbert_eq {N : ℕ} {x : ℝ} :
    (max (1 - |x|) 0) * dirichletKernel' N (x) =
      exp (I * (-N * x)) * k x + conj (exp (I * (-N * x)) * k x) := by
  simp [dirichletKernel', k, conj_ofReal, ← exp_conj, mul_comm, ← mul_assoc]
  ring

lemma Dirichlet_Hilbert_diff {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-π) π) :
    ‖dirichletKernel' N (x) - (exp (I * (-N * x)) * k x + conj (exp (I * (-N * x)) * k x))‖ ≤ π := by
  rw [← Dirichlet_Hilbert_eq]
  by_cases! h : 1 - cexp (I * ↑x) = 0
  · rw [sub_eq_zero] at h
    rw [dirichletKernel'_eq_zero h.symm]
    simp [pi_pos.le]
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
      simp only [neg_mul, norm_mul, norm_real, norm_div]
      rw [Real.norm_of_nonneg (by simp)]
      gcongr
      · apply min_le_left
      · rw [mul_assoc I, mul_comm I]
        norm_cast
        rw [norm_exp_ofReal_mul_I]
      · rw [← norm_conj, map_sub, map_one, ←exp_conj, ← neg_mul, map_mul, conj_I, conj_ofReal]
      · apply min_le_left
      · /-Duplicate from above:
        TODO: how to remove duplicate goals? -/
        rw [mul_assoc I, mul_comm I, ← neg_mul]
        norm_cast
        rw [norm_exp_ofReal_mul_I]
    _ = 2 * (|x| / ‖1 - exp (I * x)‖) := by ring
    _ ≤ 2 * (π / 2) := by
      gcongr 2 * ?_
      rw [div_le_iff₀' (by rwa [norm_pos_iff]), ← div_le_iff₀ (by linarith [pi_pos]),
        div_div_eq_mul_div, mul_div_assoc, mul_comm]
      apply lower_secant_bound' (by rfl)
      have : |x| ≤ π := by
        rwa [abs_le]
      linarith
    _ = π := by ring

section

open Filter Topology

lemma le_iSup_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (ha : Tendsto f atTop (𝓝 a)) : a ≤ iSup f := by
  apply le_of_forall_lt
  intro c hc
  have : ∀ᶠ (x : β) in atTop, c < f x := Filter.Tendsto.eventually_const_lt hc ha
  rcases this.exists with ⟨x, hx⟩
  exact lt_of_lt_of_le hx (le_iSup _ _)

lemma integrable_annulus {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) (3 * π)) {r : ℝ} (r_nonneg : 0 ≤ r) (rle1 : r < 1) :
    Integrable (fun x ↦ f x) (volume.restrict {y | dist x y ∈ Set.Ioo r 1}) := by
  rw [← IntegrableOn, annulus_real_eq r_nonneg]
  apply IntegrableOn.union <;>
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    apply hf.mono_set
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith [pi_pos])]
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.two_le_pi]

lemma intervalIntegrable_mul_dirichletKernel' {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * dirichletKernel' N (x - y)) volume (x - π) (x + π) := by
  apply (hf.mono_set _).mul_bdd
    (dirichletKernel'_measurable.comp (measurable_id.const_sub _)).aestronglyMeasurable
  · use (2 * N + 1)
    intro y
    apply norm_dirichletKernel'_le
  · rw [Set.uIcc_of_le, Set.uIcc_of_le]
    on_goal 1 => apply Set.Icc_subset_Icc
    all_goals linarith [hx.1, hx.2, pi_pos]

lemma intervalIntegrable_mul_dirichletKernel'_max {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
   (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y * ((max (1 - |x - y|) 0)
      * dirichletKernel' N (x - y))) volume (x - π) (x + π) := by
  conv => pattern ((f _) * _); rw [← mul_assoc]
  apply intervalIntegrable_mul_dirichletKernel' hx
    (IntervalIntegrable.mul_bdd hf (Complex.measurable_ofReal.comp
      ((Measurable.const_sub (_root_.continuous_abs.measurable.comp
        (measurable_id.const_sub _)) _).max measurable_const)).aestronglyMeasurable _)
  use 1
  intro y
  simp [Real.norm_of_nonneg (le_max_right _ _)]

lemma intervalIntegrable_mul_dirichletKernel'_max' {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntervalIntegrable (fun y ↦ f y
      * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
      volume (x - π) (x + π) := by
  conv => pattern ((f _) * _); rw [mul_sub]
  exact (intervalIntegrable_mul_dirichletKernel' hx hf).sub
    (intervalIntegrable_mul_dirichletKernel'_max hx hf)

lemma domain_reformulation {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-π) (3 * π)) {N : ℕ}
    {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) :
    ∫ (y : ℝ) in x - π..x + π, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))
    = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1},
        g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
  calc _
    _ = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 π}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
      rw [annulus_real_eq (le_refl 0),
        setIntegral_union (by simp) measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← setIntegral_union (Set.disjoint_of_subset_right Set.Ioo_subset_Ioc_self (by simp)) measurableSet_Ioo,
        intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo,
        sub_zero, add_zero, Set.Ioc_union_Ioo_eq_Ioo (by linarith [pi_pos]) (by linarith [pi_pos])]
      --TODO: Many similar goals => improve this further?
      · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])]
        apply (intervalIntegrable_mul_dirichletKernel'_max hx hg).mono_set
        rw [Set.uIcc_of_le (by linarith [pi_pos]), Set.uIcc_of_le (by linarith [pi_pos])]
        apply Set.Icc_subset_Icc_right (by linarith [pi_pos])
      all_goals
        rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [pi_pos])]
        apply (intervalIntegrable_mul_dirichletKernel'_max hx hg).mono_set
        rw [Set.uIcc_of_le (by linarith [pi_pos]), Set.uIcc_of_le (by linarith [pi_pos])]
      · apply Set.Icc_subset_Icc_left (by linarith [pi_pos])
      · apply Set.Icc_subset_Icc_right (by linarith [pi_pos])
      · apply Set.Icc_subset_Icc_left (by linarith [pi_pos])
    _ = ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) := by
      rw [←integral_indicator annulus_measurableSet, ←integral_indicator annulus_measurableSet]
      congr with y
      rw [Set.indicator_apply, Set.indicator_apply, Dirichlet_Hilbert_eq]
      split_ifs with h₀ h₁ h₂
      · trivial
      · dsimp at h₀ h₁
        rw [Real.dist_eq, Set.mem_Ioo] at h₀ h₁
        push Not at h₁
        rw [k_of_one_le_abs (h₁ h₀.1)]
        simp
      · rw [k_of_one_le_abs]
        · simp
        dsimp at h₀ h₂
        rw [Real.dist_eq, Set.mem_Ioo] at h₀ h₂
        push Not at h₀
        exact le_trans' (h₀ h₂.1) (by linarith [Real.two_le_pi])
      · trivial

lemma intervalIntegrable_mul_dirichletKernel'_specific {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π))
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) (3 * π)) {N : ℕ} :
    IntegrableOn (fun y ↦ f y * ((max (1 - |x - y|) 0)
      * dirichletKernel' N (x - y))) {y | dist x y ∈ Set.Ioo 0 1} volume := by
  have : IntervalIntegrable (fun y ↦ f y * ((max (1 - |x - y|) 0)
      * dirichletKernel' N (x - y))) volume (x - π) (x + π) :=
    intervalIntegrable_mul_dirichletKernel'_max hx hf
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [pi_pos])] at this
  apply this.mono_set
  intro y hy
  rw [annulus_real_eq (by rfl)] at hy
  rcases hy with h | h <;> constructor <;> linarith [h.1, h.2, hx.1, hx.2, Real.two_le_pi]

attribute [gcongr] iSup_congr

set_option backward.isDefEq.respectTransparency false in
lemma le_CarlesonOperatorReal {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-π) (3 * π)) {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) :
    ‖∫ (y : ℝ) in x - π..x + π, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ
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
      rw [inv_lt_comm₀ (by linarith) hy.1, inv_eq_one_div]
      apply lt_trans hn
      linarith
    · intro hy
      simp only [Set.mem_iUnion] at hy
      rcases hy with ⟨n, hn⟩
      rw [sdef] at hn
      simp only [one_div, Set.mem_Ioo, Set.mem_setOf_eq] at hn
      refine ⟨lt_trans' hn.1 ?_, hn.2⟩
      norm_num
      linarith
  have : Tendsto (fun i => ∫ y in s i, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
          atTop (𝓝 (∫ y in ⋃ n, s n, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))) := by
    apply tendsto_setIntegral_of_monotone
    · exact fun n ↦ annulus_measurableSet
    · intro n m nlem
      simp only [Set.le_eq_subset]
      intro y hy
      rw [sdef] at *
      simp only [one_div, Set.mem_Ioo, Set.mem_setOf_eq] at *
      refine ⟨lt_of_le_of_lt ?_ hy.1, hy.2⟩
      rw [inv_le_inv₀]
      on_goal 1 => norm_cast
      all_goals linarith
    · rw [← hs]
      --uses that dirichletKernel' is bounded
      exact intervalIntegrable_mul_dirichletKernel'_specific hx hg
  calc
    _ = ‖∫ y in ⋃ n, s n, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ := by congr
    _ ≤ ⨆ (i : ℕ), ↑‖∫ y in s i, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ := by
      apply le_iSup_of_tendsto
      exact Tendsto.enorm this
    _ ≤ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ := by
      apply iSup_le
      intro n
      apply le_iSup_of_le (1 / (n + 2 : ℝ))
      apply le_iSup₂_of_le (by simp only [one_div, inv_pos]; linarith)
        (by rw [div_lt_iff₀] <;> linarith)
      rfl
    _ = ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * N * y) + conj (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * (Int.ofNat N) * y)))‖ₑ := by
      gcongr
      congr with y
      congr
      rw [Dirichlet_Hilbert_eq]
      simp only [ofReal_sub, mul_comm, mul_neg, ← mul_assoc, k, map_mul, ← exp_conj, map_neg,
        conj_I, map_sub, conj_ofReal, map_natCast, neg_neg, map_div₀, map_one, Int.ofNat_eq_natCast,
        Int.cast_natCast, K, ← exp_add, map_add]
      ring_nf
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖ₑ := by
      let F : ℤ → ENNReal := fun (n : ℤ) ↦ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + conj (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖ₑ
      exact le_iSup F ((Int.ofNat N))
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1),
        (‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * K x y * exp (I * n * y)‖ₑ
        + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, (conj ∘ g) y * K x y * exp (I * n * y)‖ₑ) := by
      gcongr with n r rpos rle1
      norm_cast
      push_cast
      calc
        _ = ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y)) + g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ := by
          congr with y
          rw [mul_add]
        _ = ‖(∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y)))
            + ∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ := by
          congr
          -- Integrability follows from r > 0
          have measurable₁ : Measurable fun x_1 ↦ (I * (-↑n * ↑x)).exp * K x x_1 * (I * ↑n * ↑x_1).exp := by
            apply Measurable.mul (Measurable.mul _ Hilbert_kernel_measurable.of_uncurry_left) <;>
              fun_prop
          have boundedness₁ {y : ℝ} (h : r ≤ dist x y) : ‖(I * (-↑n * ↑x)).exp * K x y * (I * ↑n * ↑y).exp‖ ≤ (2 ^ (2 : ℝ) / (2 * r)) := by
            calc ‖(I * (-↑n * ↑x)).exp * K x y * (I * ↑n * ↑y).exp‖
              _ = ‖(I * (-↑n * ↑x)).exp‖ * ‖K x y‖ * ‖(I * ↑n * ↑y).exp‖ := by
                rw [norm_mul, norm_mul]
              _ ≤ 1 * (2 ^ (2 : ℝ) / (2 * |x - y|)) * 1 := by
                gcongr
                · rw [mul_comm]
                  norm_cast
                  rw [norm_exp_ofReal_mul_I]
                · exact Hilbert_kernel_bound
                · rw [mul_assoc, mul_comm]
                  norm_cast
                  rw [norm_exp_ofReal_mul_I]
              _ ≤ (2 ^ (2 : ℝ) / (2 * r)) := by
                rw [one_mul, mul_one, ← Real.dist_eq]
                gcongr
          have integrable₁ := integrable_annulus hx hg rpos.le rle1
          rw [integral_add]
          · conv => pattern ((g _) * _); rw [mul_comm]
            apply Integrable.bdd_mul integrable₁ measurable₁.aestronglyMeasurable
            · rw [ae_restrict_iff' annulus_measurableSet]
              on_goal 1 => apply Eventually.of_forall
              exact fun _ hy ↦ boundedness₁ hy.1.le
          · conv => pattern ((g _) * _); rw [mul_comm]
            apply Integrable.bdd_mul integrable₁ (by fun_prop)
            · rw [ae_restrict_iff' annulus_measurableSet]
              · apply Eventually.of_forall
                intro y hy
                rw [RCLike.norm_conj]
                exact boundedness₁ hy.1.le
        _ ≤   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * conj (exp (I * (-n * x)) * K x y * exp (I * n * y))‖ₑ := by
          apply enorm_add_le
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (g y * K x y * exp (I * n * y))‖ₑ
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * ((conj ∘ g) y * K x y * exp (I * n * y))‖ₑ := by
            congr 1
            · congr! 3 with y; ring
            · rw [← RCLike.enorm_conj, ← integral_conj]
              congr! 3 with _ y
              simp
              ring
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, g y * K x y * exp (I * n * y)‖ₑ
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, (conj ∘ g) y * K x y * exp (I * n * y)‖ₑ := by
          congr 1 <;>
          rw [integral_const_mul, enorm_mul, show (-n * x : ℂ) = ((-n * x : ℝ) : ℂ) by norm_cast,
            enorm_exp_I_mul_ofReal, one_mul]
    _ ≤ T g x + T (conj ∘ g) x := by
      simp_rw [carlesonOperatorReal]
      apply iSup₂_le
      intro n r
      apply iSup₂_le
      intro rpos rle1
      gcongr <;>
      · apply le_iSup₂_of_le n r
        apply le_iSup₂_of_le rpos rle1
        trivial

/-- The function used to bound the partial Fourier sum in `partialFourierSum_bound` -/
def operatorBound (g : ℝ → ℂ) (x : ℝ) : ENNReal :=
  (T g x + T (conj ∘ g) x) / ENNReal.ofReal (2 * π)
  + eLpNorm g 1 (volume.restrict (Set.Ioc 0 (2 * π))) / 2

lemma partialFourierSum_bound {g : ℝ → ℂ} (periodic_g : Function.Periodic g (2 * π))
  (hg : IntervalIntegrable g volume 0 (2 * π)) {N : ℕ} {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * π)) :
    ‖S_ N g x‖ₑ ≤
      operatorBound g x := by
  have intervalIntegrable_g : IntervalIntegrable g volume (-π) (3 * π) := by
    apply periodic_g.intervalIntegrable₀ Real.two_pi_pos.ne' hg
  have decomposition : S_ N g x
      = (  (∫ (y : ℝ) in (x - π)..(x + π),
              g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
         + (∫ (y : ℝ) in (x - π)..(x + π),
              g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))))
        / (2 * π) := by
    calc S_ N g x
      _ = (∫ (y : ℝ) in (0 : ℝ)..(2 * π), g y * dirichletKernel' N (x - y)) / (2 * π) := by
        rw [partialFourierSum_eq_conv_dirichletKernel' (intervalIntegrable_g.mono_set _)]
        · ring
        rw [Set.uIcc_of_le, Set.uIcc_of_le]
        on_goal 1 => apply Set.Icc_subset_Icc
        all_goals linarith [pi_pos]
      _ = (∫ (y : ℝ) in (x - π)..(x + π), g y * dirichletKernel' N (x - y)) / (2 * π) := by
        --Shift domain of integration using periodicity
        congr 1
        rw [← zero_add (2 * π), Function.Periodic.intervalIntegral_add_eq _ 0 (x - π)]
        · congr 1
          ring
        exact (periodic_g.mul (dirichletKernel'_periodic.const_sub x))
      _ = (  (∫ (y : ℝ) in (x - π)..(x + π), g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))
           + (∫ (y : ℝ) in (x - π)..(x + π), g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)))) / (2 * π) := by
        --Split into two parts
        rw [← intervalIntegral.integral_add (intervalIntegrable_mul_dirichletKernel'_max hx intervalIntegrable_g) (intervalIntegrable_mul_dirichletKernel'_max' hx intervalIntegrable_g)]
        congr with y
        ring
  calc
    _ ≤ (‖∫ y in (x - π)..(x + π), g y * ((max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ
        + ‖∫ y in (x - π)..(x + π), g y * (dirichletKernel' N (x - y) - (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))‖ₑ) / ENNReal.ofReal (2 * π) := by
      rw [decomposition, div_eq_mul_inv, enorm_mul, enorm_inv (by simp [pi_pos.ne']),
        ← div_eq_mul_inv]
      norm_cast; gcongr
      · apply enorm_add_le
      · rw [Real.enorm_eq_ofReal Real.two_pi_pos.le]
    _ ≤ (T g x + T (⇑conj ∘ g) x
          + ENNReal.ofReal π * eLpNorm g 1 (volume.restrict (Set.Ioc 0 (2 * π))))
            / ENNReal.ofReal (2 * π) := by
      gcongr
      · apply le_CarlesonOperatorReal intervalIntegrable_g hx
      · apply intervalIntegral.enorm_integral_le_lintegral_enorm_uIoc.trans
        rw [Set.uIoc_of_le (by linarith [pi_pos])]
        simp_rw [enorm_mul]
        calc _
          _ ≤ ∫⁻ (y : ℝ) in Set.Ioc (x - π) (x + π), ‖g y‖ₑ * ‖π‖ₑ := by
            apply setLIntegral_mono' (measurableSet_Ioc)
            intro y hy
            gcongr
            rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (by linarith [pi_pos])]
            rw [Dirichlet_Hilbert_eq]
            apply Dirichlet_Hilbert_diff
            constructor <;> linarith [hy.1, hy.2]
          _ = ENNReal.ofReal π * eLpNorm g 1 (volume.restrict (Set.Ioc 0 (2 * π))) := by
            simp_rw [Real.enorm_eq_ofReal pi_pos.le, mul_comm _ (ENNReal.ofReal _)]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr
            have : x + π = x - π + 2 * π := by linarith
            rw [this, Function.Periodic.setLIntegral_Ioc_add_eq _ _ 0, zero_add,
              eLpNorm_one_eq_lintegral_enorm]
            apply periodic_g.comp
    _ = (T g x + T (conj ∘ g) x) / ENNReal.ofReal (2 * π)
      + eLpNorm g 1 (volume.restrict (Set.Ioc 0 (2 * π))) / 2 := by
      rw [ENNReal.add_div, mul_comm (ENNReal.ofReal _), mul_div_assoc]
      congr
      rw [← ENNReal.ofReal_div_of_pos Real.two_pi_pos, div_mul_cancel_right₀ Real.pi_pos.ne']
      simp

end

lemma rcarleson'_restrict {p : NNReal} (hp : p ∈ Set.Ioo 1 2) {f : ℝ → ℂ}
  (f_periodic : f.Periodic (2 * π)) (hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π)))) :
    eLpNorm (T f) p (volume.restrict (Set.Ioc 0 (2 * π)))
      ≤ 2 * (C_carleson_hasStrongType 4 p) * eLpNorm f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have meas_f : AEStronglyMeasurable f := by
    have : Fact (0 < 2 * π) := fact_iff.mpr Real.two_pi_pos
    rw [← zero_add (2 * π)] at hf
    exact (f_periodic.aestronglyMeasurable hf.1)
  have h : eLpNorm ((Set.Ioo (-1) (2 * π + 1)).indicator f) (↑p) volume
      ≤ 2 * eLpNorm f (↑p) (volume.restrict (Set.Ioc 0 (2 * π))) := by
    calc _
        _ ≤ eLpNorm ((Set.Ioc (-1) (-1 + 2 * π)).indicator f) (↑p) volume
            + eLpNorm ((Set.Ioc (-1 + 2 * π) (-1 + 2 * π + 2 * π)).indicator f) (↑p) volume := by
          apply (eLpNorm_add_le _ _ (by simp [hp.1.le])).trans'
          · apply eLpNorm_mono
            intro x
            rw [← Set.indicator_union_add_inter, Set.Ioc_inter_Ioc, Set.Ioc_union_Ioc_eq_Ioc]
            · nth_rw 2 [Set.Ioc_eq_empty_of_le]
              · simp only [Set.indicator_empty, Pi.add_apply, add_zero]
                rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
                gcongr
                intro x hx
                use hx.1
                linarith [hx.2, Real.two_le_pi]
              · apply le_max_of_le_right
                apply min_le_left
            · linarith [Real.two_pi_pos]
            · linarith [Real.two_pi_pos]
          · rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
            exact meas_f.restrict
          · rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
            exact meas_f.restrict
        _ = 2 * eLpNorm f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
          have : Fact (0 < 2 * π) := by
            rw [fact_iff]
            exact Real.two_pi_pos
          rw [two_mul (eLpNorm _ _ _)]
          rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc,
            eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc]
          congr 1
          · nth_rw 2 [← zero_add (2 * π)]
            exact f_periodic.eLpNorm (by simp)
          · nth_rw 4 [← zero_add (2 * π)]
            exact f_periodic.eLpNorm (by simp)
  calc _
    _ = eLpNorm (T ((Set.Ioo (0 - 1) (2 * π + 1)).indicator f)) p (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply eLpNorm_congr_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact carlesonOperatorReal_eq_of_restrict_interval (Set.Ioc_subset_Icc_self hx)
    _ ≤ eLpNorm (T ((Set.Ioo (-1) (2 * π + 1)).indicator f)) p volume := by
      simp only [zero_sub]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ (C_carleson_hasStrongType 4 p) * eLpNorm ((Set.Ioo (-1) (2 * π + 1)).indicator f) p volume := by
      apply rcarleson' hp
      rw [memLp_indicator_iff_restrict measurableSet_Ioo]
      use meas_f.restrict
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo]
      apply h.trans_lt
      apply ENNReal.mul_lt_top (by simp) hf.2
    _ ≤ 2 * (C_carleson_hasStrongType 4 p) * eLpNorm f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
      rw [mul_comm 2 (ENNReal.ofNNReal _), mul_assoc]
      gcongr

/-- The constant used in `C_distribution_carlesonOperatorReal_le`. -/
def C_distribution_carlesonOperatorReal_le (δ ε p : NNReal) : NNReal :=
  (2 * (C_carleson_hasStrongType 4 p))⁻¹ * C_distribution_le_of_eLpNorm_le δ ε p

lemma C_distribution_carlesonOperatorReal_le_pos {δ ε p : NNReal} (δpos : 0 < δ) (εpos : 0 < ε) :
    0 < C_distribution_carlesonOperatorReal_le δ ε p := by
  unfold C_distribution_carlesonOperatorReal_le
  apply mul_pos _ (C_distribution_le_of_eLpNorm_le_pos δpos εpos)
  simp [C_carleson_hasStrongType_pos]

lemma distribution_carlesonOperatorReal_le {δ ε p : NNReal} (δpos : 0 < δ)
  (hp : p ∈ Set.Ioo 1 2) {g : ℝ → ℂ}
  (g_periodic : g.Periodic (2 * π)) (g_measurable : AEStronglyMeasurable g)
  (hg : eLpNorm g p (volume.restrict (Set.Ioc 0 (2 * π))) ≤ C_distribution_carlesonOperatorReal_le δ ε p) :
    distribution (T g) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  apply distribution_le_of_eLpNorm_le δpos (zero_lt_one.trans hp.1)
  · apply (carlesonOperatorReal_measurable g_measurable _).aestronglyMeasurable
    intro x
    have : Set.Ioo x (x + 2) ⊆ Set.Ioc x (x + (2 * π)) := by
      apply Set.Ioo_subset_Ioc_self.trans'
      apply Set.Ioo_subset_Ioo_right
      linarith [Real.two_le_pi]
    apply IntegrableOn.mono_set _ this
    apply MemLp.integrable (q := p) (by simp [hp.1.le])
    use g_measurable.restrict
    rw [g_periodic.eLpNorm (s := 0) (by simp), zero_add]
    apply hg.trans_lt
    simp
  · apply (rcarleson'_restrict hp g_periodic _).trans
    · calc _
        _ ≤ 2 * ↑(C_carleson_hasStrongType 4 p)
              * ENNReal.ofNNReal (C_distribution_carlesonOperatorReal_le δ ε p) := by
          gcongr
        _ = C_distribution_le_of_eLpNorm_le δ ε p := by
          unfold C_distribution_carlesonOperatorReal_le
          norm_cast
          rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by simp) C_carleson_hasStrongType_pos.ne'),
            one_mul]
    · use g_measurable.restrict, hg.trans_lt (by simp)

/-- The constant used in `C_control_approximation_effect`. -/
def C_control_approximation_effect (δ ε p : NNReal) : NNReal :=
  min (2 * (↑δ / 2) * ((2 * Real.toNNReal π) ^ (1 - p.toReal⁻¹))⁻¹)
    (C_distribution_carlesonOperatorReal_le (2 * π * (↑δ / 2) / 2).toNNReal (ε / 2) p)

lemma C_control_approximation_effect_pos {δ ε p : NNReal} (δpos : 0 < δ) (εpos : 0 < ε) :
    0 < C_control_approximation_effect δ ε p :=
  lt_min (by positivity)
    (C_distribution_carlesonOperatorReal_le_pos (by positivity) (by positivity))

lemma C_control_approximation_effect_property {δ ε p : NNReal} (hp : 1 ≤ p) :
    C_control_approximation_effect δ ε p * (2 * ENNReal.ofReal π) ^ (1 - p.toReal⁻¹) ≤ 2 * (↑δ / 2) := by
  calc _
    _ ≤ 2 * (↑δ / 2) * ((2 * Real.toNNReal π) ^ (1 - p.toReal⁻¹))⁻¹ * (2 * ENNReal.ofReal π) ^ (1 - p.toReal⁻¹) := by
      gcongr
      norm_cast
      exact min_le_left _ _
    _ = 2 * (↑δ / 2) := by
      rw [ENNReal.coe_inv (by simp [Real.pi_pos]), ENNReal.coe_rpow_of_nonneg _
        (by simp only [sub_nonneg]; exact inv_le_one_of_one_le₀ hp),
        ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.ofNNReal_toNNReal,
        ENNReal.inv_mul_cancel_right (by positivity) (ENNReal.rpow_ne_top' (by positivity)
        (ENNReal.mul_ne_top (by simp) (by simp)))]

lemma C_control_approximation_effect_le {δ ε p : NNReal} :
  ENNReal.ofNNReal (C_control_approximation_effect δ ε p) ≤
    (C_distribution_carlesonOperatorReal_le (2 * π * (↑δ / 2) / 2).toNNReal (ε / 2) p) := by
  simp only [ENNReal.coe_le_coe]
  exact min_le_right _ _

/- This is Lemma 11.6.4 (partial Fourier sums of small) in the blueprint.-/
lemma control_approximation_effect {δ ε : NNReal} (δpos : 0 < δ)
  {g : ℝ → ℂ} (g_measurable : AEStronglyMeasurable g)
  (g_periodic : g.Periodic (2 * π))
  {p : NNReal} (hp : p ∈ Set.Ioo 1 2)
  (g_bound : eLpNorm g p (volume.restrict (Set.Ioc 0 (2 * π))) ≤ C_control_approximation_effect δ ε p) :
    distribution (fun x ↦ ⨆ N, ‖S_ N g x‖ₑ) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  calc _
    _ ≤ distribution (operatorBound g) δ (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_mono_left
      rw [ae_restrict_iff' (measurableSet_Ioc)]
      filter_upwards [] with x hx
      simp only [enorm_eq_self, iSup_le_iff]
      intro N
      apply partialFourierSum_bound g_periodic _ (Set.Ioc_subset_Icc_self hx)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le, IntegrableOn]
      apply MemLp.integrable (q := p) (by simp [hp.1.le])
      use g_measurable.restrict
      exact g_bound.trans_lt (by simp)
    _ = distribution (operatorBound g) (δ / 2 + δ / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      congr
      simp
    _ ≤ distribution (fun x ↦ (T g x + T (conj ∘ g) x) / ENNReal.ofReal (2 * π)) (δ / 2) (volume.restrict (Set.Ioc 0 (2 * π)))
          + distribution (fun x ↦ eLpNorm g 1 (volume.restrict (Set.Ioc 0 (2 * π))) / 2) (δ / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_add_le
    _ ≤ ε + 0 := by
      gcongr
      · rw [← distribution_mul (by left; exact ENNReal.ofReal_ne_top) (by left; simp [pi_pos])]
        calc _
          _ ≤ distribution (T g) (ENNReal.ofReal (2 * π) * (↑δ / 2) / 2) (volume.restrict (Set.Ioc 0 (2 * π)))
                + distribution (T (conj ∘ g)) (ENNReal.ofReal (2 * π) * (↑δ / 2) / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
            apply distribution_add_le.trans'
            gcongr
            · simp
            rw [← two_mul, ENNReal.mul_div_cancel (by simp) (by simp)]
          _ ≤ ENNReal.ofNNReal (ε / 2) + ENNReal.ofNNReal  (ε / 2) := by
            have : ENNReal.ofReal (2 * π) * (↑δ / 2) / 2 = ENNReal.ofReal ((2 * π) * (↑δ / 2) / 2) := by
              rw [ENNReal.ofReal_div_of_pos (by simp), ENNReal.ofReal_mul (by simp),
                ENNReal.ofReal_mul Real.two_pi_pos.le, ENNReal.ofReal_mul (by simp),
                ENNReal.ofReal_ofNat, ENNReal.ofReal_div_of_pos (by simp),
                ENNReal.ofReal_ofNat]
              simp
            rw [this]
            gcongr
            · apply distribution_carlesonOperatorReal_le (by positivity) hp g_periodic
                g_measurable
              exact g_bound.trans C_control_approximation_effect_le
            · have conj_g_periodic : (conj ∘ g).Periodic (2 * π) := by
                intro x
                simp only [Function.comp_apply]
                congr 1
                apply g_periodic
              have conj_g_measurable : AEStronglyMeasurable (conj ∘ g) := by fun_prop
              have conj_g_bound : eLpNorm (conj ∘ g) p (volume.restrict (Set.Ioc 0 (2 * π)))
                  ≤ C_control_approximation_effect δ ε p := by
                convert g_bound using 1
                apply eLpNorm_congr_norm_ae
                simp
              apply distribution_carlesonOperatorReal_le (by positivity) hp
                conj_g_periodic conj_g_measurable
              exact conj_g_bound.trans C_control_approximation_effect_le
          _ = ε := by simp
      · rw [← distribution_mul (by simp) (by simp)]
        simp only [nonpos_iff_eq_zero]
        rw [Function.const_def, distribution_const, Set.indicator_of_notMem]
        simp only [enorm_eq_self, Set.mem_Iio, not_lt]
        have hp' : (1 : ENNReal) ≤ p := by simp [hp.1.le]
        apply (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp' g_measurable.restrict).trans
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        simp only [sub_zero, Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat,
          ENNReal.toReal_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, ENNReal.coe_toReal,
          one_div]
        apply (C_control_approximation_effect_property hp.1.le).trans'
        gcongr
    _ = ε := by simp

end
