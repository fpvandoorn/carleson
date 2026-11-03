/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Defs
public import Mathlib.MeasureTheory.Measure.Prod

-- Upstreaming status: Needs significant clean-up (refactoring, code style, extracting lemmas,
-- moving to proper location etc.)

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace Function

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- For a `(s : Set (α × β))` and `(ν : Measure β)`, we define `essProjFst` such that
`x ∈ essProjFst s ν` iff `0 < ν {y | ⟨x, y⟩ ∈ s}`. -/
def essProjFst (s : Set (α × β)) (ν : Measure β) : Set α := {x | 0 < ν ((x, ·) ⁻¹' s)}

/-- For a `(s : Set (α × β))` and `(μ : Measure α)`, we define `essProjSnd` such that
`y ∈ essProjSnd s μ` iff `0 < μ {x | ⟨x, y⟩ ∈ s}`. -/
def essProjSnd (s : Set (α × β)) (μ : Measure α) : Set β := {y | 0 < μ ((·, y) ⁻¹' s)}

variable {μ : Measure α} {ν : Measure β}

theorem essProjSnd_eq_essProjFst_swap {s : Set (α × β)} :
    essProjSnd s μ = essProjFst (Prod.swap ⁻¹' s) μ := by
  unfold essProjFst essProjSnd
  ext y
  simp only [mem_ofPred_eq]
  congr!

theorem essProjFst_subset {s : Set (α × β)} :
    essProjFst s ν ⊆ Prod.fst '' s := by
  unfold essProjFst
  intro x
  contrapose
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right, not_exists, mem_ofPred_eq,
    not_lt, nonpos_iff_eq_zero]
  intro h
  convert measure_empty (μ := ν)
  aesop

theorem essProjSnd_subset {s : Set (α × β)} :
    essProjSnd s μ ⊆ Prod.snd '' s := by
  rw [essProjSnd_eq_essProjFst_swap]
  apply essProjFst_subset.trans_eq
  aesop

theorem essProjFst_eq {s : Set (α × β)} :
    essProjFst s ν = (fun x => ν ((fun y => (x, y)) ⁻¹' s)) ⁻¹' (Set.Ioi 0) := by
  unfold essProjFst
  ext b
  simp

theorem essProjSnd_eq {s : Set (α × β)} :
    essProjSnd s μ = (fun y => μ ((fun x => (x, y)) ⁻¹' s)) ⁻¹' (Set.Ioi 0) := by
  rw [essProjSnd_eq_essProjFst_swap, essProjFst_eq]
  congr with y

theorem essProjFst_eq' {s : Set (α × β)} :
    essProjFst s ν = support (fun x => ν ((fun y => (x, y)) ⁻¹' s)) := by
  rw [essProjFst_eq]
  ext b
  simp only [mem_preimage, mem_Ioi, mem_support, ne_eq, pos_iff_ne_zero]

theorem essProjSnd_eq' {s : Set (α × β)} :
    essProjSnd s μ = support (fun y => μ ((fun x => (x, y)) ⁻¹' s)) := by
  rw [essProjSnd_eq_essProjFst_swap, essProjFst_eq']
  congr with y

@[simp]
theorem essProjFst_times_univ {s : Set α} (h : ν ≠ 0) :
    essProjFst (s ×ˢ univ) ν = s := by
  unfold essProjFst
  ext y
  simp only [mem_ofPred_eq]
  constructor
  · contrapose!
    intro hy
    simp only [nonpos_iff_eq_zero]
    convert measure_empty (μ := ν)
    aesop
  · intro hy
    convert measure_univ_pos.mpr h
    aesop

@[simp]
theorem essProjSnd_univ_times {s : Set β} (h : μ ≠ 0) :
    essProjSnd (univ ×ˢ s) μ = s := by
  rw [essProjSnd_eq_essProjFst_swap, preimage_swap_prod, essProjFst_times_univ h]

@[gcongr]
theorem essProjFst_mono {s t : Set (α × β)} (h : s ⊆ t) :
    essProjFst s ν ⊆ essProjFst t ν := by
  unfold essProjFst
  intro x hx
  simp_all only [mem_ofPred_eq]
  apply hx.trans_le
  gcongr

@[gcongr]
theorem essProjSnd_mono {s t : Set (α × β)} (h : s ⊆ t) :
    essProjSnd s μ ⊆ essProjSnd t μ := by
  rw [essProjSnd_eq_essProjFst_swap, essProjSnd_eq_essProjFst_swap]
  exact essProjFst_mono (preimage_mono h)

/-
theorem essProjFst_essProjFst {s : Set (α × β)} {q : Set β} :
    essProjFst (s ∩ univ ×ˢ (essProjFst s ν)) ν = essProjFst s ν := by
  sorry

theorem essProjFst_inter {s t : Set (α × β)} {ν : Measure α} :
    essProjFst (s ∩ t) ν ⊆ essProjFst s ν ∩ essProjFst t ν := by
  intro b
  unfold essProjFst
  simp only [preimage_inter, mem_ofPred_eq, mem_inter_iff]
  sorry
-/

theorem essProjFst_inter_times_univ {s : Set (α × β)} {t : Set α} :
    essProjFst (s ∩ t ×ˢ univ) ν = essProjFst s ν ∩ t := by
  unfold essProjFst
  ext y
  simp only [preimage_inter, mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro hy
    constructor
    · apply hy.trans_le
      apply measure_mono Set.inter_subset_left
    · contrapose! hy
      simp only [nonpos_iff_eq_zero]
      convert measure_empty (μ := ν)
      simp_all only [not_false_eq_true, mk_preimage_prod_right_eq_empty, inter_empty]
  · intro ⟨hy, hyt⟩
    convert hy
    aesop

theorem essProjSnd_inter_univ_times {s : Set (α × β)} {t : Set β} :
    essProjSnd (s ∩ univ ×ˢ t) μ = essProjSnd s μ ∩ t := by
  rw [essProjSnd_eq_essProjFst_swap, essProjSnd_eq_essProjFst_swap, preimage_inter,
    preimage_swap_prod, essProjFst_inter_times_univ]

theorem measurableSet_essProjFst [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    MeasurableSet (essProjFst s ν) := by
  rw [essProjFst_eq]
  exact measurable_measure_prodMk_left hs measurableSet_Ioi

theorem measurableSet_essProjSnd [SFinite μ] {s : Set (α × β)} (hs : MeasurableSet s) :
    MeasurableSet (essProjSnd s μ) := by
  rw [essProjSnd_eq_essProjFst_swap]
  apply measurableSet_essProjFst (measurableSet_swap_iff.mpr hs)

theorem measure_essProjFst_pos_iff [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    0 < μ (essProjFst s ν) ↔ 0 < (μ.prod ν) s := by
  rw [Measure.prod_apply hs, lintegral_pos_iff_support (measurable_measure_prodMk_left hs),
      ← essProjFst_eq']

theorem measure_essProjSnd_pos_iff [SFinite μ] [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    0 < ν (essProjSnd s μ) ↔ 0 < (μ.prod ν) s := by
  rw [Measure.prod_apply_symm hs, lintegral_pos_iff_support (measurable_measure_prodMk_right hs),
      ← essProjSnd_eq']

theorem exists_subset_measure_fst_image_lt_top [SigmaFinite μ] {s : Set (α × β)}
  (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ μ (Prod.fst '' t) < ⊤ := by
  obtain ⟨n, hn⟩ : ∃ n, 0 < μ.prod ν (s ∩ spanningSets μ n ×ˢ univ) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    simpa [← inter_iUnion, ← iUnion_prod_const] using h.ne'
  refine ⟨_, inter_subset_left, hs.inter ((measurableSet_spanningSets μ n).prod .univ), hn, ?_⟩
  exact measure_lt_top_of_subset (by grind) (measure_spanningSets_lt_top μ n).ne

theorem exists_subset_measure_snd_image_lt_top [SigmaFinite ν] {s : Set (α × β)}
  (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ ν (Prod.snd '' t) < ⊤ := by
  obtain ⟨n, hn⟩ : ∃ n, 0 < μ.prod ν (s ∩ univ ×ˢ spanningSets ν n) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    simpa [← inter_iUnion, ← prod_iUnion] using h.ne'
  refine ⟨_, inter_subset_left, hs.inter (.prod .univ (measurableSet_spanningSets ν n)), hn, ?_⟩
  exact measure_lt_top_of_subset (by grind) (measure_spanningSets_lt_top ν n).ne

theorem exists_subset_measure_essProjFst_lt [NoAtoms' μ] {s : Set (α × β)}
  (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ μ (essProjFst t ν) < μ (essProjFst s ν) := by
  by_cases hν : SFinite ν; swap
  · simp [Measure.prod_def, hν] at h
  obtain ⟨q, _, meas_q, _, _⟩ := NoAtoms'.exists_measurable_subset_lt
    (measurableSet_essProjFst hs) ((measure_essProjFst_pos_iff hs).mpr h)
  have meas := hs.inter (meas_q.prod .univ)
  have hq : essProjFst (s ∩ q ×ˢ univ) ν = q := by grind [essProjFst_inter_times_univ]
  exact ⟨_, inter_subset_left, meas, by grind [measure_essProjFst_pos_iff], by grind⟩

theorem exists_subset_measure_essProjSnd_lt [SFinite μ] [NoAtoms' ν] {s : Set (α × β)}
    (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ ν (essProjSnd t μ) < ν (essProjSnd s μ) := by
  by_cases hν : SFinite ν; swap;
  · simp [Measure.prod_def, hν] at h
  obtain ⟨q, _, meas_q, _, _⟩ := NoAtoms'.exists_measurable_subset_lt
    (measurableSet_essProjSnd hs) ((measure_essProjSnd_pos_iff hs).mpr h)
  have meas := hs.inter (.prod .univ meas_q)
  have hq : essProjSnd (s ∩ univ ×ˢ q) μ = q := by grind [essProjSnd_inter_univ_times]
  exact ⟨_, inter_subset_left, meas, by grind [measure_essProjSnd_pos_iff], by grind⟩

open ENNReal

--TODO: move
theorem setLIntegral_strict_mono_set {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  {f : α → ℝ≥0∞} {s t : Set α} (hf : Measurable f) (hsm : MeasurableSet s) (htm : MeasurableSet t)
  (htsf : t \ s ⊆ support f) (hfi : ∫⁻ (x : α) in s, f x ∂μ ≠ ∞) (hst : s ⊆ t) (h : μ s < μ t) :
    ∫⁻ (x : α) in s, f x ∂μ < ∫⁻ (x : α) in t, f x ∂μ := by
  have : 0 < ∫⁻ (x : α) in t \ s, f x ∂μ := by
    rwa [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf),
      inter_eq_right.mpr htsf, measure_sdiff hst hsm.nullMeasurableSet h.ne_top, tsub_pos_iff_lt]
  calc _
    _ < ∫⁻ (x : α) in s, f x ∂μ + ∫⁻ (x : α) in (t \ s), f x ∂μ := by
      apply lt_add_right hfi this.ne'
    _ = ∫⁻ (x : α) in t, f x ∂μ := by
      rw [← lintegral_union (htm.diff hsm) disjoint_sdiff_right, union_sdiff_cancel hst]

instance prod.instNoAtoms_fst [NoAtoms' μ] [SigmaFinite ν] : NoAtoms' (μ.prod ν) := by
  rw [no_atoms_iff]
  intro s meas_s hs
  rcases exists_subset_measure_snd_image_lt_top meas_s hs with ⟨s', hs's, meas_s', hs', hs'_top⟩
  rcases exists_subset_measure_essProjFst_lt meas_s' hs' with ⟨t, hts', meas_t, ht, ht_lt⟩
  have hts : t ⊆ s := hts'.trans hs's
  use t, hts, meas_t, ht
  rw [Measure.prod_apply meas_t, Measure.prod_apply meas_s,
    ← setLIntegral_eq_of_support_subset subset_rfl, ← essProjFst_eq']
  nth_rw 2 [← setLIntegral_eq_of_support_subset subset_rfl]
  rw [← essProjFst_eq']
  have : ∫⁻ (x : α) in essProjFst t ν, ν (Prod.mk x ⁻¹' s') ∂μ
    < ∫⁻ (x : α) in essProjFst s' ν, ν (Prod.mk x ⁻¹' s') ∂μ := by
    apply setLIntegral_strict_mono_set (measurable_measure_prodMk_left meas_s')
      (measurableSet_essProjFst meas_t) (measurableSet_essProjFst meas_s') _ _ _ ht_lt
    · rw [← essProjFst_eq']
      exact sdiff_subset
    · rw [← lt_top_iff_ne_top]
      calc _
        _ ≤ ∫⁻ (x : α) in essProjFst t ν, ν (Prod.snd '' s') ∂μ := by
          gcongr
          intro y
          aesop
        _ = ν (Prod.snd '' s') * μ (essProjFst t ν) := setLIntegral_const _ _
        _ < ∞ := mul_lt_top hs'_top ht_lt.lt_top
    · gcongr
  calc _
    _ ≤ ∫⁻ (x : α) in essProjFst t ν, ν (Prod.mk x ⁻¹' s') ∂μ := by
      gcongr
    _ < ∫⁻ (x : α) in essProjFst s' ν, ν (Prod.mk x ⁻¹' s') ∂μ := this
    _ ≤ ∫⁻ (x : α) in essProjFst s ν, ν (Prod.mk x ⁻¹' s) ∂μ := by
      gcongr

--TODO: move?
theorem isAtom_swap_iff [SFinite μ] [SFinite ν] {s : Set (α × β)} :
    IsAtom (Prod.swap ⁻¹' s) (ν.prod μ) ↔ IsAtom s (μ.prod ν) := by
  unfold IsAtom
  rw [measurableSet_swap_iff]
  simp only [and_congr_right_iff]
  intro hs
  rw [← map_apply measurable_swap hs, prod_swap]
  simp only [and_congr_right_iff]
  intro h_νμ
  constructor
  · intro h' t hts meas_t
    have := h' (Prod.swap ⁻¹' t)
    rw [preimage_subset_preimage_iff (subset_range_of_surjective Prod.swap_surjective _),
      measurableSet_swap_iff, ← map_apply measurable_swap meas_t, prod_swap] at this
    exact this hts meas_t
  · intro h' t hts meas_t
    have := h' (Prod.swap ⁻¹' t)
    nth_rw 1 [← image_swap_eq_preimage_swap, image_subset_iff] at this
    rw [measurableSet_swap_iff,
      ← map_apply measurable_swap meas_t, prod_swap] at this
    exact this hts meas_t

instance prod.instNoAtoms_snd [SigmaFinite μ] [NoAtoms' ν] : NoAtoms' (μ.prod ν) where
  no_atoms s := by
    by_cases hν : SFinite ν
    · exact fun h ↦ no_atoms _ (isAtom_swap_iff.mpr h)
    simp [Measure.prod_def, hν, IsAtom]

end MeasureTheory
