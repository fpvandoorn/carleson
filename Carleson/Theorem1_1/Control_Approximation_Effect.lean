/- This file formalizes section 10.8 (The error bound) from the paper. -/
import Carleson.MetricCarleson
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Hilbert_kernel
import Carleson.Theorem1_1.Dirichlet_kernel
import Carleson.Theorem1_1.CarlesonOperatorReal
import Carleson.Theorem1_1.Carleson_on_the_real_line

import Mathlib.Analysis.Fourier.AddCircle
--import Mathlib.Analysis.RCLike.Basic

noncomputable section

local notation "T" => CarlesonOperatorReal K
local notation "T'" => CarlesonOperatorReal' K

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

open Complex

/-TODO: might go to mathlib-/
lemma intervalIntegral.integral_conj' {μ : MeasureTheory.Measure ℝ} {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}:
    ∫ x in a..b, (starRingEnd 𝕜) (f x) ∂μ = (starRingEnd 𝕜) (∫ x in a..b, f x ∂μ) := by
  rw [intervalIntegral_eq_integral_uIoc, integral_conj, intervalIntegral_eq_integral_uIoc,
      RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, map_mul]
  simp

-- Corrected rewrite
lemma dirichlet_Hilbert_eq {N : ℕ} {x y : ℝ} :
    (max (1 - |x - y|) 0) * dirichletKernel' N (x - y) = exp (I * (-N * x)) * K x y * exp (I * N * y) + (starRingEnd ℂ) (exp (I * (-N * x)) * K x y * exp (I * N * y)) := by
  simp [dirichletKernel', K, k, conj_ofReal, ←exp_conj, mul_comm, ←mul_assoc, ←exp_add]
  ring_nf

section
open Filter Topology

--TODO: proof might be improved
lemma le_iSup_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (ha : Tendsto f atTop (𝓝 a)) : a ≤ iSup f := by
  apply le_of_forall_lt
  intro c hc
  have : ∀ᶠ (x : β) in atTop, c < f x := by
    apply eventually_gt_of_tendsto_gt hc ha
  rcases this.exists with ⟨x, hx⟩
  apply lt_of_lt_of_le hx
  exact le_iSup _ _

lemma integrable_annulus {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {r : ℝ} (r_nonneg : 0 ≤ r) (rle1 : r < 1) :
    MeasureTheory.Integrable (fun x ↦ f x) (MeasureTheory.volume.restrict {y | dist x y ∈ Set.Ioo r 1}) := by
  rw [← MeasureTheory.IntegrableOn, annulus_real_eq r_nonneg]
  apply MeasureTheory.IntegrableOn.union <;>
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    apply hf.mono_set
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith [Real.pi_pos])]
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.two_le_pi]

lemma integrableOn_mul_dirichletKernel'_max {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    MeasureTheory.IntegrableOn (fun y ↦ f y * ↑(max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) (Set.Icc (x - Real.pi) (x + Real.pi)) MeasureTheory.volume := by
  conv => pattern ((f _) * _ * _); rw [mul_assoc, mul_comm]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])] at hf
  apply MeasureTheory.Integrable.bdd_mul'
  · apply hf.mono_set
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.two_le_pi]
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Complex.measurable_ofReal.comp
      apply Measurable.max
      apply Measurable.const_sub
      apply _root_.continuous_abs.measurable.comp
      apply measurable_id.const_sub
      exact measurable_const
    · apply dirichletKernel'_measurable.comp
      exact measurable_id.const_sub _
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    apply eventually_of_forall
    intro y _
    calc ‖(max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖
      _ = ‖max (1 - |x - y|) 0‖ * ‖dirichletKernel' N (x - y)‖ := by
        rw [norm_mul, Complex.norm_real]
      _ ≤ 1 * (2 * N + 1) := by
        gcongr
        · rw [Real.norm_of_nonneg]
          apply max_le
          linarith [abs_nonneg (x - y)]
          norm_num
          exact le_max_right _ _
        exact norm_dirichletKernel'_le

/-TODO : only slightly different from previous lemma; unify the proofs of the two-/
lemma integrableOn_mul_dirichletKernel'_min {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    MeasureTheory.IntegrableOn (fun y ↦ f y * ↑(min |x - y| 1) * dirichletKernel' N (x - y)) (Set.Icc (x - Real.pi) (x + Real.pi)) MeasureTheory.volume := by
  conv => pattern ((f _) * _ * _); rw [mul_assoc, mul_comm]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])] at hf
  apply MeasureTheory.Integrable.bdd_mul'
  · apply hf.mono_set
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.two_le_pi]
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Complex.measurable_ofReal.comp
      apply Measurable.min
      apply _root_.continuous_abs.measurable.comp
      apply measurable_id.const_sub
      exact measurable_const
    · apply dirichletKernel'_measurable.comp
      exact measurable_id.const_sub _
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    apply eventually_of_forall
    intro y _
    calc ‖(min |x - y| 1) * dirichletKernel' N (x - y)‖
      _ = ‖min |x - y| 1‖ * ‖dirichletKernel' N (x - y)‖ := by
        rw [norm_mul, Complex.norm_real]
      _ ≤ 1 * (2 * N + 1) := by
        gcongr
        · rw [Real.norm_of_nonneg]
          apply min_le_right
          apply le_min
          linarith [abs_nonneg (x - y)]
          norm_num
        exact norm_dirichletKernel'_le


lemma integrableOn_mul_dirichletKernel'_specific {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * Real.pi)) {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    MeasureTheory.IntegrableOn (fun y ↦ f y * ↑(max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) {y | dist x y ∈ Set.Ioo 0 1} MeasureTheory.volume := by
  apply (integrableOn_mul_dirichletKernel'_max hx hf).mono_set
  intro y hy
  rw [annulus_real_eq (by rfl)] at hy
  rcases hy with h | h <;> constructor <;> linarith [h.1, h.2, hx.1, hx.2, Real.two_le_pi]

lemma le_CarlesonOperatorReal' {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi)) {N : ℕ} :
    ∀ x ∈ Set.Icc 0 (2 * Real.pi),
    ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ ≤ T' f x + T' ((starRingEnd ℂ) ∘ f) x := by
  intro x hx
  set s : ℕ → Set ℝ := fun n ↦ {y | dist x y ∈ Set.Ioo (1 / (n + 2 : ℝ)) 1} with sdef
  have hs : {y | dist x y ∈ Set.Ioo 0 1} = ⋃ n, s n := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_setOf_eq, Set.mem_Ioo] at hy
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / dist x y)
      simp
      use n
      rw [sdef]
      simp
      constructor
      · rw [inv_lt, inv_eq_one_div]
        apply lt_trans hn
        linarith
        linarith
        exact hy.1
      · exact hy.2
    · intro hy
      simp at hy
      rcases hy with ⟨n, hn⟩
      rw [sdef] at hn
      simp at hn
      constructor
      · apply lt_trans' hn.1
        norm_num
        linarith
      · exact hn.2
  have : Tendsto (fun i => ∫ y in s i, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) atTop (𝓝 (∫ y in ⋃ n, s n, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))) := by
    apply MeasureTheory.tendsto_setIntegral_of_monotone
    · intro n
      exact annulus_measurableSet
    · intro n m nlem
      simp
      intro y hy
      rw [sdef]
      rw [sdef] at hy
      simp
      simp at hy
      constructor
      · apply lt_of_le_of_lt _ hy.1
        rw [inv_le_inv]
        norm_cast
        all_goals linarith
      · exact hy.2
    · rw [← hs]
      --uses that dirichletKernel' is bounded
      exact integrableOn_mul_dirichletKernel'_specific hx hf
  calc ENNReal.ofNNReal ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊
    _ = ‖∫ y in ⋃ n, s n, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by congr
    _ ≤ ⨆ (i : ℕ), ↑‖∫ y in s i, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
      apply le_iSup_of_tendsto
      rw [ENNReal.tendsto_coe]
      exact Tendsto.nnnorm this
    _ ≤ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
      apply iSup_le
      intro n
      apply le_iSup_of_le (1 / (n + 2 : ℝ))
      apply le_iSup₂_of_le (by simp; linarith) (by rw [div_lt_iff] <;> linarith)
      rfl
    _ = ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * N * y) + (starRingEnd ℂ) (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * (Int.ofNat N) * y)))‖₊ := by
      apply iSup_congr
      intro r
      apply iSup_congr
      intro _
      apply iSup_congr
      intro _
      congr with y
      rw [mul_assoc, dirichlet_Hilbert_eq]
      norm_cast
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊ := by
      let F : ℤ → ENNReal := fun (n : ℤ) ↦ ⨆ (r : ℝ) (_ : 0 < r) (_ : r < 1), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊
      exact le_iSup F ((Int.ofNat N))
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1), (  ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * exp (I * n * y)‖₊
                                                    + ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, ((starRingEnd ℂ) ∘ f) y * K x y * exp (I * n * y)‖₊) := by
      apply iSup₂_mono
      intro n r
      apply iSup₂_mono
      intro rpos rle1
      norm_cast
      push_cast
      calc ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊
        _ = ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y)) + f y * (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          congr with y
          rw [mul_add]
        _ = ‖ (∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y)))
             + ∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          congr
          -- Integrability follows from r > 0
          have measurable₁ : Measurable fun x_1 ↦ (I * (-↑n * ↑x)).exp * K x x_1 * (I * ↑n * ↑x_1).exp := by
            apply Measurable.mul
            apply Measurable.mul
            measurability
            apply Measurable.of_uncurry_left
            exact Hilbert_kernel_measurable
            measurability
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
          have integrable₁ := (integrable_annulus hx hf rpos.le rle1)
          rw [MeasureTheory.integral_add]
          · conv => pattern ((f _) * _); rw [mul_comm]
            apply MeasureTheory.Integrable.bdd_mul' integrable₁ measurable₁.aestronglyMeasurable
            · rw [MeasureTheory.ae_restrict_iff' annulus_measurableSet]
              apply eventually_of_forall
              exact fun _ hy ↦ boundedness₁ hy.1.le
          · conv => pattern ((f _) * _); rw [mul_comm]
            apply MeasureTheory.Integrable.bdd_mul' integrable₁
            · apply Measurable.aestronglyMeasurable
              exact continuous_star.measurable.comp measurable₁
            · rw [MeasureTheory.ae_restrict_iff' annulus_measurableSet]
              apply eventually_of_forall
              intro y hy
              rw [RCLike.norm_conj]
              exact boundedness₁ hy.1.le
        _ ≤   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          apply nnnorm_add_le
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (f y * K x y * exp (I * n * y))‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (((starRingEnd ℂ) ∘ f) y *  K x y * exp (I * n * y))‖₊ := by
            congr 1
            · congr with y
              ring
            · rw [←nnnorm_star, ←starRingEnd_apply, ←integral_conj]
              congr with y
              simp
              ring
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * exp (I * n * y)‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, ((starRingEnd ℂ) ∘ f) y * K x y * exp (I * n * y)‖₊ := by
          rw [← NNReal.coe_inj]
          push_cast
          norm_cast
          congr 1 <;>
          · rw [MeasureTheory.integral_mul_left, norm_mul, norm_eq_abs, mul_comm I, abs_exp_ofReal_mul_I, one_mul]
    _ ≤ T' f x + T' ((starRingEnd ℂ) ∘ f) x := by
      rw [CarlesonOperatorReal', CarlesonOperatorReal']
      apply iSup₂_le
      intro n r
      apply iSup₂_le
      intro rpos rle1
      gcongr <;>
      · apply le_iSup₂_of_le n r
        apply le_iSup₂_of_le rpos rle1
        trivial

end section

theorem rcarleson_exceptional_set_estimate {δ : ℝ} (δpos : 0 < δ) {f : ℝ → ℂ} {F : Set ℝ} (measurableSetF : MeasurableSet F) (hf : ∀ x, ‖f x‖ ≤ δ * F.indicator 1 x)
    {E : Set ℝ} (measurableSetE : MeasurableSet E) {ε : ENNReal} (hE : ∀ x ∈ E, ε ≤ T' f x) :
      ε * MeasureTheory.volume E ≤ ENNReal.ofReal (δ * C1_2 4 2) * MeasureTheory.volume F ^ (2 : ℝ)⁻¹ * MeasureTheory.volume E ^ (2 : ℝ)⁻¹ := by
  calc ε * MeasureTheory.volume E
    _ = ∫⁻ _ in E, ε := by
      symm
      apply MeasureTheory.set_lintegral_const
    _ ≤ ∫⁻ x in E, T' f x := by
      apply MeasureTheory.set_lintegral_mono' measurableSetE hE
    _ = ENNReal.ofReal δ * ∫⁻ x in E, T' (fun x ↦ (1 / δ) * f x) x := by
      rw [← MeasureTheory.lintegral_const_mul']
      congr with x
      rw [CarlesonOperatorReal'_mul δpos]
      congr
      exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal δ * (ENNReal.ofReal (C1_2 4 2) * (MeasureTheory.volume E) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹) := by
      gcongr
      apply rcarleson' measurableSetF measurableSetE
      intro x
      simp
      rw [_root_.abs_of_nonneg δpos.le, inv_mul_le_iff δpos]
      exact hf x
    _ = ENNReal.ofReal (δ * C1_2 4 2) * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume E) ^ (2 : ℝ)⁻¹ := by
      rw [ENNReal.ofReal_mul δpos.le]
      ring

theorem rcarleson_exceptional_set_estimate_specific {δ : ℝ} (δpos : 0 < δ) {f : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ δ * Set.indicator (Set.Icc (-Real.pi) (3 * Real.pi)) 1 x)
    {E : Set ℝ} (measurableSetE : MeasurableSet E) {ε : ENNReal} (hE : ∀ x ∈ E, ε ≤ T' f x) :
      ε * MeasureTheory.volume E ≤ ENNReal.ofReal (δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹) * MeasureTheory.volume E ^ (2 : ℝ)⁻¹ := by
  rw [ENNReal.ofReal_mul (by apply mul_nonneg δpos.le; rw [C1_2]; norm_num), ← ENNReal.ofReal_rpow_of_pos (by linarith [Real.pi_pos])]
  convert rcarleson_exceptional_set_estimate δpos measurableSet_Icc hf measurableSetE hE
  rw [Real.volume_Icc]
  ring_nf

def C_control_approximation_effect (ε : ℝ) := (C1_2 4 2 * (8 / (Real.pi * ε)) ^ (2 : ℝ)⁻¹) + Real.pi

lemma lt_C_control_approximation_effect {ε : ℝ} (εpos : 0 < ε) : Real.pi < C_control_approximation_effect ε := by
  rw [C_control_approximation_effect]
  apply lt_add_of_pos_of_le _ (by rfl)
  apply mul_pos (C1_2_pos (by norm_num))
  apply Real.rpow_pos_of_pos
  apply div_pos (by norm_num)
  apply mul_pos Real.pi_pos εpos

lemma C_control_approximation_effect_pos {ε : ℝ} (εpos : 0 < ε) : 0 < C_control_approximation_effect ε := lt_trans' (lt_C_control_approximation_effect εpos) Real.pi_pos

lemma C_control_approximation_effect_eq {ε : ℝ} {δ : ℝ} (ε_nonneg : 0 ≤ ε) : C_control_approximation_effect ε * δ = ((δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ * (2 / ε) ^ (2 : ℝ)⁻¹) / Real.pi) + Real.pi * δ := by
  symm
  rw [C_control_approximation_effect, mul_comm, mul_div_right_comm, mul_comm δ, mul_assoc,
    mul_comm δ, ← mul_assoc, ← mul_assoc, ← add_mul, mul_comm _ (C1_2 4 2), mul_assoc]
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

/-ENNReal version of a generalized Lemma 10.3 (control approximation effect).-/
--TODO : review measurability assumption
--added subset assumption
--changed interval to match the interval in the theorem
lemma control_approximation_effect' {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) {δ : ℝ} (hδ : 0 < δ)
    {h : ℝ → ℂ} (h_measurable : Measurable h) (h_periodic : Function.Periodic h (2 * Real.pi)) (h_bound : ∀ x ∈ Set.Icc (-Real.pi) (3 * Real.pi), abs (h x) ≤ δ ) :
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, abs (partialFourierSum h N x) ≤ C_control_approximation_effect ε * δ := by
  --TODO: change later
  set ε' := C_control_approximation_effect ε * δ with ε'def
  set E := {x ∈ Set.Icc 0 (2 * Real.pi) | ∃ N, ε' < abs (partialFourierSum h N x)} with Edef
  have E_eq: E = Set.Icc 0 (2 * Real.pi) ∩ ⋃ N : ℕ, {x | ε' < ‖partialFourierSum h N x‖} := by
      rw [Edef]
      ext x
      simp
  have measurableSetE : MeasurableSet E := by
    rw [E_eq]
    apply MeasurableSet.inter
    · exact measurableSet_Icc
    apply MeasurableSet.iUnion
    intro N
    apply measurableSet_lt
    · exact measurable_const
    apply Measurable.norm
    exact partialFourierSum_uniformContinuous.continuous.measurable
  use E
  constructor
  · intro x hx
    rw [Edef] at hx
    simp at hx
    exact hx.1
  use measurableSetE
  --Change order of proofs to start with the simple part
  rw [and_comm]
  constructor
  · rw [Edef]
    simp
    exact fun x x_nonneg x_le_two_pi h ↦ h x_nonneg x_le_two_pi
  have h_intervalIntegrable : IntervalIntegrable h MeasureTheory.volume (-Real.pi) (3 * Real.pi) := by
    apply @IntervalIntegrable.mono_fun' _ _ _ _ _ _ (fun _ ↦ δ)
    apply intervalIntegrable_const
    exact h_measurable.aestronglyMeasurable
    rw [Filter.EventuallyLE, ae_restrict_iff_subtype]
    apply Filter.eventually_of_forall
    simp only [norm_eq_abs, Subtype.forall]
    intro x hx
    apply h_bound x
    apply Set.Ioc_subset_Icc_self
    rw [Set.uIoc_of_le (by linarith)] at hx
    constructor <;> linarith [hx.1, hx.2]
    exact measurableSet_uIoc
  set F := Set.Icc (-Real.pi) (3 * Real.pi) with Fdef
  set f := fun x ↦ h x * F.indicator 1 x with fdef
  have f_measurable : Measurable f := by
    apply h_measurable.mul
    exact measurable_const.indicator measurableSet_Icc
  --TODO : improve this proof, should be much easier...
  have f_integrable : IntervalIntegrable f MeasureTheory.volume (-Real.pi) (3 * Real.pi) := by
    rw [fdef, intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    conv => pattern (h _) * _; rw [mul_comm]
    apply MeasureTheory.Integrable.bdd_mul'
    rwa [← MeasureTheory.IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    apply Measurable.aestronglyMeasurable
    apply measurable_const.indicator measurableSet_Icc
    apply Filter.eventually_of_forall
    intro x
    rw [norm_indicator_eq_indicator_norm]
    simp
    calc F.indicator (fun _ ↦ (1 : ℝ)) x
      _ ≤ 1 := by
        apply Set.indicator_apply_le'
        intro _
        rfl
        intro _
        norm_num
  have le_operator_add : ∀ x ∈ E, ENNReal.ofReal ((ε' - Real.pi * δ) * (2 * Real.pi)) ≤ T' f x + T' ((starRingEnd ℂ) ∘ f) x := by
    have h_intervalIntegrable' : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) := by
      apply h_intervalIntegrable.mono_set
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos]), Set.uIcc_of_le (by linarith [Real.pi_pos])]
      intro y hy
      constructor <;> linarith [hy.1, hy.2]
    intro x hx
    --set S := {y | dist x y ∈ Set.Ioo 0 Real.pi} with Sdef
    --set S := Set.Ioo (x - Real.pi) (x + Real.pi) with Sdef
    obtain ⟨xIcc, N, hN⟩ := hx
    rw [partialFourierSum_eq_conv_dirichletKernel' h_intervalIntegrable'] at hN
    have : ENNReal.ofReal (Real.pi * δ * (2 * Real.pi)) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [← (ENNReal.add_le_add_iff_right this)]
    calc ENNReal.ofReal ((ε' - Real.pi * δ) * (2 * Real.pi)) + ENNReal.ofReal (Real.pi * δ * (2 * Real.pi))
      _ = ENNReal.ofReal ((2 * Real.pi) * ε') := by
        rw [← ENNReal.ofReal_add]
        · ring_nf
        · apply mul_nonneg _ Real.two_pi_pos.le
          rw [ε'def, C_control_approximation_effect_eq hε.1.le, add_sub_cancel_right]
          apply div_nonneg _ Real.pi_pos.le
          apply mul_nonneg
          · rw [mul_assoc]
            apply mul_nonneg hδ.le
            rw [C1_2]
            apply mul_nonneg (by norm_num)
            apply Real.rpow_nonneg
            linarith [Real.pi_pos]
          · apply Real.rpow_nonneg (div_nonneg (by norm_num) hε.1.le)
        · apply mul_nonneg (mul_nonneg Real.pi_pos.le hδ.le) Real.two_pi_pos.le
      _ ≤ ENNReal.ofReal ((2 * Real.pi) * abs (1 / (2 * Real.pi) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h y * dirichletKernel' N (x - y))) := by gcongr
      _ = ‖∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h y * dirichletKernel' N (x - y)‖₊  := by
        rw [map_mul, map_div₀, ←mul_assoc]
        rw [ENNReal.ofReal, ← norm_toNNReal]
        conv => rhs; rw [← one_mul ‖_‖]
        simp
        rw [_root_.abs_of_nonneg Real.pi_pos.le]
        field_simp
        ring
      _ = ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * dirichletKernel' N (x - y)‖₊ := by
        --Shift domain of integration using periodicity
        congr 2
        rw [← zero_add (2 * Real.pi), Function.Periodic.intervalIntegral_add_eq _ 0 (x - Real.pi)]
        congr 1
        ring
        apply Function.Periodic.mul h_periodic
        exact Function.Periodic.const_sub dirichletKernel'_periodic _
      _ = ‖  (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))
           + (∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * (min |x - y| 1) * dirichletKernel' N (x - y))      ‖₊ := by
        --Split into two parts
        rw [← intervalIntegral.integral_add]
        · congr with y
          rw [←add_mul, ←mul_add]
          conv => lhs; rw [←mul_one (h y)]
          norm_cast
          rw [min_def]
          split_ifs
          · rw [max_eq_left (by linarith)]
            simp
          · rw [max_eq_right (by linarith)]
            simp
        --use lemma that dirichletKernel is bounded
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])]
        apply integrableOn_mul_dirichletKernel'_max xIcc h_intervalIntegrable
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])]
        apply integrableOn_mul_dirichletKernel'_min xIcc h_intervalIntegrable
      _ ≤   ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊
          + ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * (min |x - y| 1) * dirichletKernel' N (x - y)‖₊ := by
        --apply abs.isAbsoluteValue.abv_add
        norm_cast
        apply nnnorm_add_le
      _ ≤ (T' f x + T' ((starRingEnd ℂ) ∘ f) x) + ENNReal.ofReal (Real.pi * δ * (2 * Real.pi)) := by
        --Estimate the two parts
        gcongr
        · --first part
          calc ENNReal.ofNNReal ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊
            _ = ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
              --Exchange h for f
              congr 2
              apply intervalIntegral.integral_congr
              intro y hy
              simp
              rw [Set.uIcc_of_le (by linarith)] at hy
              left
              left
              rw [fdef, ←mul_one (h y)]
              congr
              rw [Set.indicator_apply]
              have : y ∈ F := by
                rw [Fdef]
                simp
                constructor <;> linarith [xIcc.1, xIcc.2, hy.1, hy.2]
              simp [this]
            _ = ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 Real.pi}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
              rw [annulus_real_eq (le_refl 0), MeasureTheory.integral_union (by simp), ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_union,
                intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
              simp
              rw [Set.Ioc_union_Ioo_eq_Ioo (by linarith) (by linarith)]
              · simp
                apply Set.disjoint_of_subset_right Set.Ioo_subset_Ioc_self
                simp
              · exact measurableSet_Ioo
              -- Many similar goals => improve this?
              · apply (integrableOn_mul_dirichletKernel'_max xIcc f_integrable).mono_set
                intro y hy
                constructor <;> linarith [hy.1, hy.2, Real.pi_pos]
              · apply (integrableOn_mul_dirichletKernel'_max xIcc f_integrable).mono_set
                intro y hy
                constructor <;> linarith [hy.1, hy.2, Real.pi_pos]
              · exact measurableSet_Ioo
              · apply (integrableOn_mul_dirichletKernel'_max xIcc f_integrable).mono_set
                intro y hy
                constructor <;> linarith [hy.1, hy.2, Real.pi_pos]
              · apply (integrableOn_mul_dirichletKernel'_max xIcc f_integrable).mono_set
                intro y hy
                constructor <;> linarith [hy.1, hy.2, Real.pi_pos]

            _ = ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
              --Adjust integration domain
              congr 2
              rw [←MeasureTheory.integral_indicator annulus_measurableSet, ←MeasureTheory.integral_indicator annulus_measurableSet]
              congr with y
              rw [Set.indicator_apply, Set.indicator_apply, mul_assoc, dirichlet_Hilbert_eq, K]
              split_ifs with h₀ h₁ h₂
              · trivial
              · dsimp at h₀
                dsimp at h₁
                rw [Real.dist_eq, Set.mem_Ioo] at h₀
                rw [Real.dist_eq, Set.mem_Ioo] at h₁
                push_neg at h₁
                rw [k_of_one_le_abs (h₁ h₀.1)]
                simp
              · rw [k_of_one_le_abs]
                simp
                dsimp at h₀
                dsimp at h₂
                rw [Real.dist_eq, Set.mem_Ioo] at h₀
                rw [Real.dist_eq, Set.mem_Ioo] at h₂
                push_neg at h₀
                apply le_trans' (h₀ h₂.1)
                linarith [Real.two_le_pi]
              · trivial
            _ ≤ (T' f x + T' ((starRingEnd ℂ) ∘ f) x) := by
              apply le_CarlesonOperatorReal' f_integrable x xIcc
        · --second part
          rw [ENNReal.ofReal]
          norm_cast
          apply NNReal.le_toNNReal_of_coe_le
          rw [coe_nnnorm]
          calc ‖∫ (y : ℝ) in (x - Real.pi)..(x + Real.pi), h y * (min |x - y| 1) * dirichletKernel' N (x - y)‖
            _ ≤ (δ * Real.pi) * |(x + Real.pi) - (x - Real.pi)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro y hy
              rw [Set.uIoc_of_le (by linarith)] at hy
              rw [mul_assoc, norm_mul]
              gcongr
              · rw [norm_eq_abs]
                apply h_bound
                rw [Fdef]
                simp
                constructor <;> linarith [xIcc.1, xIcc.2, hy.1, hy.2]
              rw [dirichletKernel', mul_add]
              set z := x - y with zdef
              calc ‖  (min |z| 1) * (exp (I * N * z) / (1 - exp (-I * z)))
                    + (min |z| 1) * (exp (-I * N * z) / (1 - exp (I * z)))‖
                _ ≤   ‖(min |z| 1) * (exp (I * N * z) / (1 - exp (-I * z)))‖
                    + ‖(min |z| 1) * (exp (-I * N * z) / (1 - exp (I * z)))‖ := by
                  apply norm_add_le
                _ = min |z| 1 * 1 / ‖1 - exp (I * z)‖ + min |z| 1 * 1 / ‖1 - exp (I * z)‖ := by
                  simp
                  congr
                  · simp
                  · rw [mul_assoc I, mul_comm I]
                    norm_cast
                    rw [abs_exp_ofReal_mul_I, one_div, ←abs_conj, map_sub, map_one, ←exp_conj, ← neg_mul, map_mul,
                          conj_neg_I, conj_ofReal]
                  · /-Duplicate from above:
                    TODO: how to remove duplicate goals? -/
                    simp only [abs_eq_self, le_min_iff, abs_nonneg, zero_le_one, and_self]
                  · rw [mul_assoc I, mul_comm I, ←neg_mul]
                    norm_cast
                    rw [abs_exp_ofReal_mul_I, one_div]
                _ = 2 * (min |z| 1 / ‖1 - exp (I * z)‖) := by ring
                _ ≤ 2 * (Real.pi / 2) := by
                  gcongr 2 * ?_
                  --· apply min_le_right
                  · by_cases h : (1 - exp (I * z)) = 0
                    · rw [h, norm_zero, div_zero]
                      linarith [Real.pi_pos]
                    rw [div_le_iff', ←div_le_iff, div_div_eq_mul_div, mul_div_assoc, mul_comm]
                    apply lower_secant_bound'
                    · exact min_le_left _ _
                    · have : |z| ≤ Real.pi := by
                        rw [abs_le, zdef]
                        constructor <;> linarith [hy.1, hy.2]
                      rw [min_def]
                      split_ifs <;> linarith
                    · linarith [Real.pi_pos]
                    · rwa [norm_pos_iff]
                _ = Real.pi := by ring
            _ = Real.pi * δ * (2 * Real.pi) := by
              simp
              rw [←two_mul, _root_.abs_of_nonneg Real.two_pi_pos.le]
              ring
  have Evolume : MeasureTheory.volume E < ⊤ := by
    calc MeasureTheory.volume E
      _ ≤ MeasureTheory.volume (Set.Icc 0 (2 * Real.pi)) := by
        apply MeasureTheory.measure_mono
        rw [E_eq]
        apply Set.inter_subset_left
      _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [Real.volume_Icc, sub_zero]
      _ < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨E', E'subset, measurableSetE', E'measure, h⟩ := ENNReal.le_on_subset MeasureTheory.volume measurableSetE (CarlesonOperatorReal'_measurable f_measurable) (CarlesonOperatorReal'_measurable (continuous_star.measurable.comp f_measurable)) le_operator_add
  have E'volume : MeasureTheory.volume E' < ⊤ := lt_of_le_of_lt (MeasureTheory.measure_mono E'subset) Evolume
  have : ENNReal.ofReal (Real.pi * (ε' - Real.pi * δ)) * MeasureTheory.volume E' ≤ ENNReal.ofReal (δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹) * (MeasureTheory.volume E') ^ (2 : ℝ)⁻¹ := by
    calc ENNReal.ofReal (Real.pi * (ε' - Real.pi * δ)) * MeasureTheory.volume E'
    _ = ENNReal.ofReal ((ε' - Real.pi * δ) * (2 * Real.pi)) / 2 * MeasureTheory.volume E' := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      ring_nf
    _ ≤ ENNReal.ofReal (δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹) * (MeasureTheory.volume E') ^ (2 : ℝ)⁻¹ := by
      rcases h with hE' | hE' <;>
      · apply rcarleson_exceptional_set_estimate_specific hδ  _ measurableSetE' hE'
        intro x
        rw [fdef, ← Fdef]
        simp (config := { failIfUnchanged := false }) only [RCLike.star_def, Function.comp_apply,
          map_mul, norm_mul, RingHomIsometric.is_iso]
        rw [norm_indicator_eq_indicator_norm]
        simp only [norm_eq_abs, Pi.one_apply, norm_one]
        rw [Set.indicator_apply, Set.indicator_apply]
        split_ifs with inF
        · simp [h_bound x inF]
        · simp
  have δ_mul_const_pos : 0 < δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ := by
    apply mul_pos
    apply mul_pos hδ (by rw [C1_2]; norm_num)
    apply Real.rpow_pos_of_pos
    linarith [Real.two_pi_pos]
  have ε'_δ_expression_pos : 0 < Real.pi * (ε' - Real.pi * δ) := by
    rw [ε'def, C_control_approximation_effect_eq hε.1.le, add_sub_cancel_right, mul_div_cancel₀ _ Real.pi_pos.ne.symm]
    apply mul_pos δ_mul_const_pos
    apply Real.rpow_pos_of_pos
    apply div_pos (by norm_num) hε.1
  calc MeasureTheory.volume.real E
    _ ≤ 2 * MeasureTheory.volume.real E' := by
      -- uses E'measure
      rwa [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, ←@ENNReal.toReal_ofReal 2 (by norm_num),
        ←ENNReal.toReal_mul, ENNReal.toReal_le_toReal Evolume.ne, ENNReal.ofReal_ofNat]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top E'volume.ne
    _ = 2 * MeasureTheory.volume.real E' ^ ((1 + -(2 : ℝ)⁻¹) * 2) := by
      conv => lhs; rw [←Real.rpow_one (MeasureTheory.volume.real E')]
      norm_num
    _ ≤ 2 * (δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ / (Real.pi * (ε' - Real.pi * δ))) ^ (2 : ℝ) := by
      rw [Real.rpow_mul MeasureTheory.measureReal_nonneg]
      gcongr
      rw [Real.rpow_add' MeasureTheory.measureReal_nonneg (by norm_num), Real.rpow_one, le_div_iff' ε'_δ_expression_pos, ← mul_assoc]
      apply mul_le_of_nonneg_of_le_div δ_mul_const_pos.le
      apply Real.rpow_nonneg MeasureTheory.measureReal_nonneg
      rw[Real.rpow_neg MeasureTheory.measureReal_nonneg, div_inv_eq_mul]
      rw [← ENNReal.ofReal_le_ofReal_iff, ENNReal.ofReal_mul ε'_δ_expression_pos.le, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal E'volume.ne]
      --here, we use this
      apply le_trans this
      rw [ENNReal.ofReal_mul δ_mul_const_pos.le, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal E'volume.ne]
      --small goal remaining
      apply mul_nonneg δ_mul_const_pos.le
      apply Real.rpow_nonneg MeasureTheory.measureReal_nonneg
    _ = ε := by
      --choose ε' such that this works
      rw [ε'def, C_control_approximation_effect_eq hε.1.le, add_sub_cancel_right, mul_div_cancel₀,
          div_mul_eq_div_div, div_self, one_div, Real.inv_rpow, ← Real.rpow_mul, inv_mul_cancel, Real.rpow_one, inv_div]
      ring
      norm_num
      apply div_nonneg <;> linarith [hε.1]
      apply Real.rpow_nonneg
      apply div_nonneg <;> linarith [hε.1]
      exact δ_mul_const_pos.ne.symm
      exact Real.pi_pos.ne.symm
