/- This file formalizes section 10.8 (The error bound) from the paper. -/
import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Hilbert_kernel
import Carleson.Theorem1_1.Dirichlet_kernel
import Carleson.Theorem1_1.Carleson_on_the_real_line

import Mathlib.Analysis.Fourier.AddCircle
--import Mathlib.Analysis.RCLike.Basic

noncomputable section

local notation "T" => CarlesonOperatorReal K
local notation "T'" => CarlesonOperatorReal' K


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

open Complex

/-Slightly more general version of Lemma 10.3 (control approximation effect).-/
--TODO : review measurability assumption
--TODO : add assumption that h is periodic?
--TODO : introduce δ instead of explicit dependency on term of ε
--added subset assumption
--changed interval to match the interval in the theorem

lemma control_approximation_effect {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi), abs (h x) ≤ (2 ^ (- (2 ^ 50 : ℝ))) * ε ^ 2 ):
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, abs (partialFourierSum h N x) ≤ ε / 4 := by sorry


/-TODO: might go to mathlib-/
lemma intervalIntegral.integral_conj' {μ : MeasureTheory.Measure ℝ} {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}:
    ∫ x in a..b, (starRingEnd 𝕜) (f x) ∂μ = (starRingEnd 𝕜) (∫ x in a..b, f x ∂μ) := by
  rw [intervalIntegral_eq_integral_uIoc, integral_conj, intervalIntegral_eq_integral_uIoc,
      RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, map_mul]
  congr
  simp

-- Corrected rewrite
lemma dirichlet_Hilbert_eq {N : ℕ} {x y : ℝ} :
    (max (1 - |x - y|) 0) * dirichletKernel' N (x - y) = exp (I * (-N * x)) * K x y * exp (I * N * y) + (starRingEnd ℂ) (exp (I * (-N * x)) * K x y * exp (I * N * y)) := by
  rw [dirichletKernel', K, k]
  rw [map_mul, map_mul, map_div₀, conj_ofReal, map_sub, ←exp_conj, ←exp_conj, ←exp_conj,
    map_mul, map_mul, map_mul, map_mul, map_mul, conj_ofReal, conj_ofReal, conj_ofReal]
  simp
  field_simp
  symm
  rw [mul_comm, ←mul_assoc, ←exp_add, mul_comm, add_comm, mul_comm, ←mul_assoc, ←exp_add, mul_comm, mul_add, mul_div_assoc, mul_div_assoc]
  congr <;> ring


section
open Filter Topology

--TODO: probably not needed anymore
lemma le_ciSup_of_tendsto {α β} [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (h : BddAbove (Set.range f)) (ha : Tendsto f atTop (𝓝 a)) : a ≤ iSup f := by
  apply le_of_forall_lt
  intro c hc
  have : ∀ᶠ (x : β) in atTop, c < f x := by
    apply eventually_gt_of_tendsto_gt hc ha
  rcases this.exists with ⟨x, hx⟩
  apply lt_of_lt_of_le hx
  apply le_ciSup h

--TODO: proof might be improved
lemma le_iSup_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (ha : Tendsto f atTop (𝓝 a)) : a ≤ iSup f := by
  apply le_of_forall_lt
  intro c hc
  have : ∀ᶠ (x : β) in atTop, c < f x := by
    apply eventually_gt_of_tendsto_gt hc ha
  rcases this.exists with ⟨x, hx⟩
  apply lt_of_lt_of_le hx
  apply le_iSup

/-TODO: The following three lemmas are probably not needed anymore. -/
--adapted from mathlib le_iSup₂
lemma le_iSup₃ {α : Type} {ι : Type} {β : ι → Type} {γ : (i : ι) → β i → Type} [CompleteLattice α] {a : α}
    {f : (i : ι) → (j : β i) → γ i j → α} (i : ι) (j : β i) (k : γ i j) : f i j k ≤ ⨆ (i) (j) (k), f i j k :=
  le_iSup₂_of_le i j <| le_iSup (f i j) k

--adapted from mathlib iSup₂_le
lemma iSup₃_le {α : Type} {ι : Type} {β : ι → Type} {γ : (i : ι) → β i → Type} [CompleteLattice α] {a : α}
    {f : (i : ι) → (j : β i) → γ i j → α} (h : ∀ (i : ι) (j : β i) (k : γ i j), f i j k ≤ a) : ⨆ i, ⨆ j, ⨆ k, f i j k ≤ a :=
  iSup₂_le fun i j => iSup_le <| h i j

--adapted from mathlib le_iSup₂_of_le
lemma le_iSup₃_of_le {α : Type} {ι : Type} {β : ι → Type} {γ : (i : ι) → β i → Type} [CompleteLattice α] {a : α}
    {f : (i : ι) → (j : β i) → γ i j → α} (i : ι) (j : β i) (k : γ i j) (h : a ≤ f i j k) :
    a ≤ ⨆ (i) (j) (k), f i j k :=
  h.trans <| @le_iSup₃ _ _ _ _ _ a f i j k

/-Version of previous lemma where we try to circumvent some difficulties with sup on the Reals by going to ENNReal. -/
lemma le_CarlesonOperatorReal' {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) {N : ℕ} :
    ∀ x ∈ Set.Icc 0 (2 * Real.pi),
    ↑‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ ≤ T' f x + T' ((starRingEnd ℂ) ∘ f) x := by
  intro x hx
  set s : ℕ → Set ℝ := fun n ↦ {y | dist x y ∈ Set.Ioo (1 / (n + 1 : ℝ)) 1} with sdef
  have hs : {y | dist x y ∈ Set.Ioo 0 1} = ⋃ n, s n := by
    ext y
    constructor
    . intro hy
      rw [Set.mem_setOf_eq, Set.mem_Ioo] at hy
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / dist x y)
      simp
      use n
      rw [sdef]
      simp
      constructor
      . rw [inv_lt, inv_eq_one_div]
        apply lt_trans hn
        linarith
        linarith
        exact hy.1
      . exact hy.2
    . intro hy
      simp at hy
      rcases hy with ⟨n, hn⟩
      rw [sdef] at hn
      simp at hn
      constructor
      . apply lt_trans' hn.1
        norm_num
        linarith
      . exact hn.2
  have : Tendsto (fun i => ∫ y in s i, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)) atTop (𝓝 (∫ y in ⋃ n, s n, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y))) := by
    apply MeasureTheory.tendsto_setIntegral_of_monotone
    . intro n
      rw [sdef]
      simp only [one_div, Set.mem_Ioo]
      --apply measurableSet_Ioo
      sorry
    . intro n m nlem
      simp
      intro y hy
      rw [sdef]
      rw [sdef] at hy
      simp
      simp at hy
      constructor
      . apply lt_of_le_of_lt _ hy.1
        rw [inv_le_inv]
        norm_cast
        all_goals linarith
      . exact hy.2
    . rw [← hs]
      --use that dirichletKernel' is bounded
      sorry
  calc ENNReal.ofNNReal ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊
    _ = ‖∫ y in ⋃ n, s n, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
      congr
    _ ≤ ⨆ (i : ℕ), ↑‖∫ y in s i, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
      apply le_iSup_of_tendsto
      rw [ENNReal.tendsto_coe]
      apply Tendsto.nnnorm this
    _ ≤ ⨆ (r : ℝ) (_ : 0 < r), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊ := by
      apply sSup_le_sSup_of_forall_exists_le
      intro z hz
      rw [Set.mem_range] at hz
      rcases hz with ⟨n, hn⟩
      use z
      constructor
      . rw [Set.mem_range]
        use 1 / (n + 1 : ℝ)
        rw [iSup]
        have : (Set.range fun (_ : 0 < 1 / (n + 1: ℝ)) ↦ ↑‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo (1 / (n + 1: ℝ)) 1}, f y * (max (1 - |x - y|) 0) * dirichletKernel' N (x - y)‖₊) = {z} := by
          rw [Set.eq_singleton_iff_unique_mem]
          constructor
          . rw [Set.mem_range, exists_prop]
            constructor
            . rw [one_div, inv_pos]
              linarith
            exact hn
          . intro z' hz'
            rw [Set.mem_range, exists_prop] at hz'
            rw [hn] at hz'
            exact hz'.2.symm
        rw [this]
        apply sSup_singleton
      trivial
    _ = ⨆ (r : ℝ) (_ : 0 < r), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * N * y) + (starRingEnd ℂ) (exp (I * (-(Int.ofNat N) * x)) * K x y * exp (I * (Int.ofNat N) * y)))‖₊ := by
      apply iSup_congr
      intro r
      apply iSup_congr
      intro hr
      congr
      ext y
      rw [mul_assoc, dirichlet_Hilbert_eq]
      norm_cast
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊ := by
      let F : ℤ → ENNReal := fun (n : ℤ) ↦ ⨆ (r : ℝ) (_ : 0 < r), ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊
      apply le_iSup F ((Int.ofNat N))
    _ ≤ ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r), (  ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * exp (I * n * y)‖₊
                                        + ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, ((starRingEnd ℂ) ∘ f) y * K x y * exp (I * n * y)‖₊) := by
      apply iSup₂_mono
      intro n r
      apply iSup_mono
      intro hr
      norm_cast
      push_cast
      calc ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y) + (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y)))‖₊
        _ = ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y)) + f y * (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          congr
          ext y
          rw [mul_add]
        _ = ‖ (∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y)))
             + ∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          congr
          rw [MeasureTheory.integral_add]
          --integrability is ok since r>0
          . sorry
          . sorry
        _ ≤   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * (starRingEnd ℂ) (exp (I * (-n * x)) * K x y * exp (I * n * y))‖₊ := by
          apply nnnorm_add_le
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (f y * K x y * exp (I * n * y))‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, exp (I * (-n * x)) * (((starRingEnd ℂ) ∘ f) y *  K x y * exp (I * n * y))‖₊ := by
            congr 1
            . congr
              ext y
              ring
            . rw [←nnnorm_star, ←starRingEnd_apply, ←integral_conj]
              congr
              ext y
              simp
              ring
        _ =   ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * exp (I * n * y)‖₊
            + ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, ((starRingEnd ℂ) ∘ f) y * K x y * exp (I * n * y)‖₊ := by
          rw [← NNReal.coe_inj]
          push_cast
          norm_cast
          congr 1 <;>
          . rw [MeasureTheory.integral_mul_left, norm_mul, norm_eq_abs, mul_comm I, abs_exp_ofReal_mul_I, one_mul]
    _ ≤ T' f x + T' ((starRingEnd ℂ) ∘ f) x := by
      rw [CarlesonOperatorReal', CarlesonOperatorReal']
      apply iSup₂_le
      intro n r
      apply iSup_le
      intro hr
      gcongr <;>
      . apply le_iSup₂_of_le n r
        apply le_iSup_of_le hr
        trivial


  --apply limsup_le_iSup
  --apply iUnion_Ici_eq_Ioi_of_lt_of_tendsto
end section

/- Only keep this because of some useful rewrites in here.  -/
lemma le_CarlesonOperatorReal_specific {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) {N : ℤ} :
    ∀ x ∈ Set.Icc 0 (2 * Real.pi), ‖∫ (y : ℝ) in -Real.pi..Real.pi,  k y * f (x - y) * exp (I * N * y)‖ ≤ T f x := by
  intro x hx
  calc ‖∫ (y : ℝ) in -Real.pi..Real.pi, k y * f (x - y) * exp (I * N * y)‖
    _ = ‖∫ (y : ℝ) in -Real.pi..Real.pi,  k (x - ↑(x - 1 * y)) * f (x - 1 * y) * exp (I * N * (x - ↑(x - 1 * y)))‖ := by
      congr
      ext y
      simp
    _ = ‖(1 : ℝ)⁻¹ • ∫ (y : ℝ) in x - 1 * Real.pi..x - 1 * -Real.pi,  k (x - y) * f y * exp (I * N * (x - y))‖ := by
      congr 1
      rw [←intervalIntegral.integral_comp_sub_mul]
      norm_num
    _ = ‖∫ (y : ℝ) in x - 1 * Real.pi..x - 1 * -Real.pi,  K x y * f y * exp (I * N * (x - y))‖ := by
      simp
      congr
    _ = ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1},  K x y * f y * exp (I * N * (x - y))‖ := by
      congr
      rw [intervalIntegral.integral_of_le, ←MeasureTheory.integral_indicator, ←MeasureTheory.integral_indicator]
      congr
      ext y
      rw [Set.indicator_apply, Set.indicator_apply]
      split_ifs with h₀ h₁ h₂
      . trivial
      . by_cases h : x = y
        . rw [h, K, k]
          simp
        rw [K, k_of_one_le_abs, mul_assoc, zero_mul]
        dsimp at h₁
        rw [Real.dist_eq, Set.mem_Ioo] at h₁
        push_neg at h₁
        apply h₁
        rw [abs_pos]
        contrapose! h
        rwa [sub_eq_zero] at h
      . --rw [K, k_of_one_le_abs, mul_assoc, zero_mul]
        rw [Set.mem_Ioc, not_and_or] at h₀
        dsimp at h₂
        rw [Real.dist_eq, Set.mem_Ioo] at h₂
        exfalso
        rcases h₀
        --simp at *
        --linarith [h₂.1, h₂.2]
        sorry
        sorry
        --push_neg at h₂
        --simp? at h₀
      . trivial
      sorry
      apply measurableSet_Ioc
      linarith [Real.pi_pos]
      --apply MeasureTheory.setIntegral_congr_set_ae
    _ = ‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo 0 1},  K x y * f y * exp (I * N * y)‖ := by
      --not sure whether this works
      sorry
    _ ≤ T f x := by
      --use intervalIntegral.continuousOn_primitive_interval_left ?
      --(need to go back to intervalIntegral first)

      rw [CarlesonOperatorReal]
      sorry

--changed statement
lemma control_approximation_effect' {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) {δ : ℝ} (hδ : 0 < δ)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc (-Real.pi) (3 * Real.pi), abs (h x) ≤ δ ):
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E,
      ∀ N, abs (partialFourierSum h N x) ≤ ε / 4 := by
  --TODO: change later
  set ε' := ε / 4 with ε'def
  set E := {x ∈ Set.Icc 0 (2 * Real.pi) | ∃ N, ε' < abs (partialFourierSum h N x)} with Edef
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
    have le_operator_add: ∀ x ∈ E, (ε' - 8 * δ) * (2 * Real.pi) ≤ (T f x + T ((starRingEnd ℂ) ∘ f) x) := by
      have h_intervalIntegrable : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) := by
        apply @IntervalIntegrable.mono_fun' _ _ _ _ _ _ (fun x ↦ δ)
        apply intervalIntegrable_const
        exact hh.1.aestronglyMeasurable
        rw [Filter.EventuallyLE, ae_restrict_iff_subtype]
        apply Filter.eventually_of_forall
        simp only [norm_eq_abs, Subtype.forall]
        intro x hx
        apply hh.2 x
        apply Set.Ioc_subset_Icc_self
        rw [Set.uIoc_of_le Real.two_pi_pos.le] at hx
        constructor <;> linarith [hx.1, hx.2]
        apply measurableSet_uIoc
      intro x hx
      obtain ⟨xIcc, N, hN⟩ := hx
      rw [partialFourierSum_eq_conv_dirichletKernel' h_intervalIntegrable] at hN
      rw [←add_le_add_iff_right (8 * δ * (2 * Real.pi))]
      calc (ε' - 8 * δ) * (2 * Real.pi) + 8 * δ * (2 * Real.pi)
        _ = (2 * Real.pi) * ε':= by linarith
        _ ≤ (2 * Real.pi) * abs (1 / (2 * Real.pi) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h y * dirichletKernel' N (x - y)) := by gcongr
        _ = abs (∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), h y * dirichletKernel' N (x - y)) := by
          rw [map_mul, map_div₀, ←mul_assoc]
          conv => rhs; rw [← one_mul (Complex.abs _)]
          congr
          simp
          rw [_root_.abs_of_nonneg Real.pi_pos.le]
          field_simp
          ring
        _ = abs ((1 : ℝ)⁻¹ • ∫ (y : ℝ) in (x - 1 * (2 * Real.pi))..x - 1 * 0, h (x - y) * dirichletKernel' N y) := by
          --Change of variables
          congr 1
          rw [←intervalIntegral.integral_comp_sub_mul]
          simp
          norm_num
        _ = abs (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * dirichletKernel' N y) := by
          --Shift domain of integration using periodicity
          --use Function.Periodic.intervalIntegral_add_eq
          sorry
        _ =   abs (  (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (max (1 - |y|) 0) * dirichletKernel' N y)
                   + (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel' N y)) := by
          --Split into two parts
          congr
          rw [←intervalIntegral.integral_add]
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
        _ ≤   abs (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (max (1 - |y|) 0) * dirichletKernel' N y)
            + abs (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel' N y) := by
          apply abs.isAbsoluteValue.abv_add
        _ ≤ (T f x + T ((starRingEnd ℂ) ∘ f) x) + 8 * δ * (2 * Real.pi):= by
          --Estimate the two parts
          gcongr
          . --first part
            calc abs (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * ↑(max (1 - |y|) 0) * dirichletKernel' N y)
              _ = abs (∫ (y : ℝ) in -Real.pi..Real.pi, f (x - y) * ↑(max (1 - |y|) 0) * dirichletKernel' N y) := by
                --Exchange h for f
                congr 1
                apply intervalIntegral.integral_congr
                intro y hy
                rw [Set.uIcc_of_le (by linarith)] at hy
                simp
                left
                left
                rw [fdef, ←mul_one (h (x - y))]
                congr
                rw [Set.indicator_apply]
                have : x - y ∈ F := by
                  rw [Fdef]
                  simp
                  constructor <;> linarith [xIcc.1, xIcc.2, hy.1, hy.2]
                simp [this]
              _ = ‖∫ (y : ℝ) in -Real.pi..Real.pi, f (x - y) * ↑(max (1 - |y|) 0) * dirichletKernel' N y‖ := by
                rw [←norm_eq_abs]
              /-
              _ ≤ 1 / (2 * Real.pi) * (  ‖∫ (y : ℝ) in -Real.pi..Real.pi, (f (x - y) * ↑(max (1 - |y|) 0) * exp (I * N * y) / (1 - exp (-I * y)))‖ +
                                          ‖∫ (y : ℝ) in -Real.pi..Real.pi, (f (x - y) * ↑(max (1 - |y|) 0) * exp (-I * N * y) / (1 - exp (I * y)))‖) := by
                gcongr
                --apply norm_add_le
                --rw [dirichletKernel']
                --rw [dirichletKernel', mul_add, add_comm, k]
                sorry
              _ = 1 / (2 * Real.pi) * (  ‖∫ (y : ℝ) in -Real.pi..Real.pi, (f (x - y) * exp (-I * N * y) * k y )‖
                                        + ‖∫ (y : ℝ) in -Real.pi..Real.pi, ((starRingEnd ℂ) ∘ f) (x - y) * exp (-I * N * y) * k y‖) := by
                rw [add_comm]
                congr 2
                . congr
                  ext y
                  rw [k]
                  ring
                . rw [norm_eq_abs, norm_eq_abs, ←abs_conj]
                  congr
                  rw [←intervalIntegral.integral_conj']
                  congr
                  ext y
                  simp
                  rw [mul_div_assoc, mul_assoc, mul_assoc, mul_assoc]
                  congr 1
                  rw [k, conj_ofReal, ←exp_conj, ←exp_conj]
                  simp
                  rw [conj_ofReal]
                  ring
              -/
              _ ≤ (T f x + T ((starRingEnd ℂ) ∘ f) x) := by
                --use le_CarlesonOperatorReal
                sorry


            --rw [dirichletKernel', mul_add]
          . --second part
            calc abs (∫ (y : ℝ) in -Real.pi..Real.pi, h (x - y) * (min |y| 1) * dirichletKernel' N y)
              _ ≤ (δ * 8) * |Real.pi - -Real.pi| := by
                --simp only [one_div, mul_inv_rev, map_mul, map_inv₀, abs_ofReal, abs_ofNat]
                --rw [_root_.abs_of_nonneg Real.pi_pos.le]
                --gcongr
                rw [←norm_eq_abs]
                apply intervalIntegral.norm_integral_le_of_norm_le_const
                intro y hy
                rw [Set.uIoc_of_le (by linarith)] at hy
                rw [mul_assoc, norm_mul]
                gcongr
                . rw [norm_eq_abs]
                  apply hh.2
                  rw [Fdef]
                  simp
                  constructor <;> linarith [xIcc.1, xIcc.2, hy.1, hy.2]
                rw [dirichletKernel', mul_add]
                calc ‖  (min |y| 1) * (exp (I * N * y) / (1 - exp (-I * y)))
                      + (min |y| 1) * (exp (-I * N * y) / (1 - exp (I * y)))‖
                  _ ≤   ‖(min |y| 1) * (exp (I * N * y) / (1 - exp (-I * y)))‖
                      + ‖(min |y| 1) * (exp (-I * N * y) / (1 - exp (I * y)))‖ := by
                    apply norm_add_le
                  _ = min |y| 1 * 1 / ‖1 - exp (I * y)‖ + min |y| 1 * 1 / ‖1 - exp (I * y)‖ := by
                    simp
                    congr
                    . simp only [abs_eq_self, le_min_iff, abs_nonneg, zero_le_one, and_self]
                    . rw [mul_assoc I, mul_comm I]
                      norm_cast
                      rw [abs_exp_ofReal_mul_I, one_div, ←abs_conj, map_sub, map_one, ←exp_conj, ← neg_mul, map_mul,
                            conj_neg_I, conj_ofReal]
                    . /-Duplicate from above:
                      TODO: how to remove duplicate goals? -/
                      simp only [abs_eq_self, le_min_iff, abs_nonneg, zero_le_one, and_self]
                    . rw [mul_assoc I, mul_comm I, ←neg_mul]
                      norm_cast
                      rw [abs_exp_ofReal_mul_I, one_div]
                  _ = 2 * (min |y| 1 / ‖1 - exp (I * y)‖) := by ring
                  _ ≤ 2 * 4 := by
                    gcongr
                    . by_cases h : (1 - exp (I * y)) = 0
                      . rw [h]
                        simp
                      simp
                      rw [div_le_iff', ←div_le_iff, ←norm_eq_abs]
                      apply lower_secant_bound'
                      . apply min_le_left
                      . have : |y| ≤ Real.pi := by
                          rw [abs_le]
                          exact ⟨hy.1.le, hy.2⟩
                        rw [min_def]
                        split_ifs <;> linarith
                      . norm_num
                      . rwa [←norm_eq_abs, norm_pos_iff]
                  _ = 8 := by norm_num
              _ = 8 * δ * (2 * Real.pi) := by
                rw [sub_neg_eq_add, ←two_mul, _root_.abs_of_nonneg Real.two_pi_pos.le]
                field_simp
                ring
    /-TODO: avoid completely analogous cases by wlog tactic?
      maybe switch "rcases" and first "have"-/
    rcases le_on_subset MeasureTheory.volume measurableSetE sorry sorry le_operator_add with ⟨E', E'subset, measurableSetE', E'measure, hE'⟩ | ⟨E', E'subset, measurableSetE', E'measure, hE'⟩
    . have : Real.pi * (ε' - 8 * δ) * MeasureTheory.volume.real E' ≤ δ * C1_2 4 2 * (4 * Real.pi) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume.real E') ^ (2 : ℝ)⁻¹ := by
        calc Real.pi * (ε' - 8 * δ) * MeasureTheory.volume.real E'
          _ = MeasureTheory.volume.real E' * ((ε' - 8 * δ) * (2 * Real.pi) / 2) := by ring
          _ = ∫ x in E', (ε' - 8 * δ) * (2 * Real.pi) / 2 := by
            symm
            apply MeasureTheory.setIntegral_const
          _ ≤ ∫ x in E', T f x := by
            apply MeasureTheory.setIntegral_mono_on _ _ measurableSetE'
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
          --_ = δ * ∫⁻ x in E', T' (fun x ↦ (1 / δ) * f x) x := by
          _ = δ * ∫ x in E', T (fun x ↦ (1 / δ) * f x) x := by
            --add lemma CarlesonOperatorReal_mul
            sorry
-- use MeasureTheory.lintegral_coe_eq_integral somewhere here?
-- or MeasureTheory.ofReal_integral_eq_lintegral_ofReal?
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
              rw [_root_.abs_of_nonneg hδ.le, inv_mul_le_iff hδ, Set.indicator_apply, Set.indicator_apply]
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
