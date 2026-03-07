module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/- This file contains helper lemmas. Either they should be replaced by a mathlib version if there is
   one or they might be candidates to go there, possibly in a generalized form. -/

open MeasureTheory

lemma intervalIntegral.integral_conj' {μ : Measure ℝ} {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ} :
    ∫ x in a..b, (starRingEnd 𝕜) (f x) ∂μ = (starRingEnd 𝕜) (∫ x in a..b, f x ∂μ) := by
  rw [intervalIntegral_eq_integral_uIoc, integral_conj, intervalIntegral_eq_integral_uIoc,
      RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, map_mul, RCLike.conj_ofReal]

lemma intervalIntegrable_of_bdd {a b : ℝ} {δ : ℝ} {g : ℝ → ℂ} (measurable_g : Measurable g)
    (bddg : ∀ x, ‖g x‖ ≤ δ) : IntervalIntegrable g volume a b := by
  apply @IntervalIntegrable.mono_fun' _ _ _ _ _ _ (fun _ ↦ δ)
  · exact intervalIntegrable_const
  · exact measurable_g.aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff_subtype measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    rw [Subtype.forall]
    exact fun x _ ↦ bddg x

lemma IntervalIntegrable.bdd_mul {F : Type*} [NormedDivisionRing F] {f g : ℝ → F} {a b : ℝ}
    {μ : Measure ℝ} (hg : IntervalIntegrable g μ a b) (hm : AEStronglyMeasurable f μ)
    (hfbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) : IntervalIntegrable (fun x ↦ f x * g x) μ a b := by
  rw [intervalIntegrable_iff, IntegrableOn]
  obtain ⟨C, hC⟩ := hfbdd
  apply Integrable.bdd_mul _ hm.restrict (ae_of_all _ hC)
  rwa [← IntegrableOn, ← intervalIntegrable_iff]

lemma IntervalIntegrable.mul_bdd {F : Type*} [NormedField F] {f g : ℝ → F} {a b : ℝ}
    {μ : Measure ℝ} (hf : IntervalIntegrable f μ a b) (hm : AEStronglyMeasurable g μ)
    (hgbdd : ∃ C, ∀ x, ‖g x‖ ≤ C) : IntervalIntegrable (fun x ↦ f x * g x) μ a b := by
  conv => pattern (fun x ↦ f x * g x); ext x; rw [mul_comm]
  exact hf.bdd_mul hm hgbdd

lemma IntegrableOn.sub {α : Type*} {β : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup β] {s : Set α} {f g : α → β}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) : IntegrableOn (f - g) s μ := by
  apply Integrable.sub <;> rwa [← IntegrableOn]

lemma ConditionallyCompleteLattice.le_biSup {α : Type*} [ConditionallyCompleteLinearOrder α]
    {ι : Type*} {f : ι → α} {s : Set ι} {a : α} (hfs : BddAbove (f '' s)) (ha : ∃ i ∈ s, f i = a) :
    a ≤ ⨆ i ∈ s, f i := by
  apply ConditionallyCompleteLattice.le_csSup
  · --TODO: improve this
    rw [bddAbove_def] at *
    rcases hfs with ⟨x, hx⟩
    use (max x (sSup ∅))
    intro y hy
    simp only [Set.mem_range] at hy
    rcases hy with ⟨z, hz⟩
    rw [iSup] at hz
    by_cases h : z ∈ s
    · have : (@Set.range α (z ∈ s) fun _ ↦ f z) = {f z} := by
        rw [Set.eq_singleton_iff_unique_mem]
        exact ⟨Set.mem_range_self h, fun x hx ↦ hx.2.symm⟩
      rw [this, csSup_singleton _] at hz
      have : f z ≤ x := by
        simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hx
        exact hx z h
      rw [hz] at this
      exact le_max_of_le_left this
    have : (@Set.range α (z ∈ s) fun _ ↦ f z) = ∅ := by simpa
    rw [this] at hz
    exact hz ▸ le_max_right x y
  rw [Set.mem_range]
  rcases ha with ⟨i, hi, fia⟩
  use i
  rw [iSup]
  convert csSup_singleton _
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨hi, fia⟩, fun x hx ↦ ?_⟩
  simp only [Set.mem_range, exists_prop] at hx
  rwa [hx.2] at fia

/- Adapted from mathlib Function.Periodic.exists_mem_Ico₀ -/
theorem Function.Periodic.exists_mem_Ico₀' {α β : Type*} {f : α → β} {c : α}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Archimedean α]
    (h : Periodic f c) (hc : 0 < c) (x : α) :
    ∃ (n : ℤ), (x - n • c) ∈ Set.Ico 0 c ∧ f x = f (x - n • c) :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨n, H, (h.sub_zsmul_eq n).symm⟩

/- Adapted from mathlib Function.Periodic.exists_mem_Ico₀ -/
theorem Function.Periodic.exists_mem_Ico' {α β : Type*} {f : α → β} {c : α}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Archimedean α]
    (h : Periodic f c) (hc : 0 < c) (x a : α) :
    ∃ (n : ℤ), (x - n • c) ∈ Set.Ico a (a + c) ∧ f x = f (x - n • c) :=
  let ⟨n, H, _⟩ := existsUnique_sub_zsmul_mem_Ico hc x a
  ⟨n, H, (h.sub_zsmul_eq n).symm⟩
