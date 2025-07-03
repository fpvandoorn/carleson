import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory NNReal ENNReal Set

noncomputable
instance NNReal.MeasureSpace : MeasureSpace ℝ≥0 := ⟨Measure.Subtype.measureSpace.volume⟩

lemma NNReal.volume_val {s : Set ℝ≥0} : volume s = volume (Subtype.val '' s) := by
  apply comap_subtype_coe_apply measurableSet_Ici

-- sanity check: this measure is what you expect
example : volume (Ioo (3 : ℝ≥0) 5) = 2 := by
  have : Subtype.val '' Ioo (3 : ℝ≥0) 5 = Ioo (3 : ℝ) 5 := by
    ext x
    constructor
    · simp only [val_eq_coe, mem_image, mem_Ioo, Subtype.exists, coe_mk, exists_and_right,
      exists_eq_right, forall_exists_index, and_imp]
      intro hx1 hx2 hx3
      exact ⟨hx2, hx3⟩
    · intro hx
      simp only [val_eq_coe, mem_image, mem_Ioo, Subtype.exists, coe_mk, exists_and_right,
        exists_eq_right]
      have : 0 ≤ x := by linarith [hx.1]
      use this
      rw [← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe]
      exact hx

  rw [NNReal.volume_val, this]
  simpa only [Real.volume_Ioo, ENNReal.ofReal_eq_ofNat] using by norm_num

-- integral over a function over NNReal equals the integral over the right set of real numbers

noncomputable
instance : MeasureSpace ℝ≥0∞ where
  volume := (volume : Measure ℝ≥0).map ENNReal.ofNNReal

--TODO: move these lemmas somewhere else?
lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} (h : ∞ ∉ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  ext x
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨y, hys, hyx⟩
    have : y ≠ ∞ := ne_of_mem_of_not_mem hys h
    use y.toNNReal
    rw [coe_toNNReal this]
    use hys
    rwa [coe_toNNReal_eq_toReal]
  · rintro ⟨y, hys, hyx⟩
    use ENNReal.ofNNReal y, hys, hyx

lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal' {s : Set ℝ≥0∞} (h : ∞ ∈ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) ∪ {0}:= by
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨y, hys, hyx⟩
    by_cases hy : y = ∞
    · rw [← hyx, hy]
      simp
    left
    use y.toNNReal
    simp only [mem_preimage]
    rw [coe_toNNReal hy]
    use hys
    rwa [coe_toNNReal_eq_toReal]
  · rintro (⟨y, hys, hyx⟩ | hx)
    · use ENNReal.ofNNReal y, hys, hyx
    · use ∞, h
      simp only [toReal_top, hx.symm]

lemma ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} :
    ENNReal.toReal '' s =ᵐ[volume] NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  by_cases h : ∞ ∈ s
  · rw [ENNReal.map_toReal_eq_map_toReal_comap_ofReal' h, union_singleton]
    apply insert_ae_eq_self
  rw [ENNReal.map_toReal_eq_map_toReal_comap_ofReal h]

lemma ENNReal.volume_val {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.toReal '' s) := by
  calc volume s
    _ = volume (ENNReal.ofNNReal ⁻¹' s) :=
      MeasureTheory.Measure.map_apply_of_aemeasurable (by fun_prop) hs
    _ = volume (NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s)) := NNReal.volume_val
    _ = volume (ENNReal.toReal '' s) := Eq.symm (measure_congr ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal)

lemma ENNReal.volume_eq_volume_preimage {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.ofReal ⁻¹' s ∩ Ici 0) := by
  rw [ENNReal.volume_val hs, measure_congr ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal]
  congr; ext x; simp only [mem_image, mem_preimage, mem_inter_iff, mem_Ici]
  constructor <;> intro h
  · obtain ⟨x', hx', rfl⟩ := h; simpa
  · lift x to ℝ≥0 using h.2; rw [ofReal_coe_nnreal] at h; use x, h.1

lemma map_restrict_Ioi_eq_restrict_Ioi :
    (volume.restrict (Ioi 0)).map ENNReal.ofReal = volume.restrict (Ioi 0) := by
  ext s hs
  rw [Measure.map_apply measurable_ofReal hs]
  simp only [measurableSet_Ioi, Measure.restrict_apply']
  rw [ENNReal.volume_eq_volume_preimage (by measurability)]
  congr 1
  ext x
  simp +contextual [LT.lt.le]

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Icc_eq_Icc {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Icc a b = Set.Icc a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hyx,
          toReal_le_toReal ha (lt_top_iff_ne_top.mp (hy.2.trans_lt (lt_top_iff_ne_top.mpr hb))),
          toReal_le_toReal (lt_top_iff_ne_top.mp (hy.2.trans_lt (lt_top_iff_ne_top.mpr hb))) hb ]
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [le_ofReal_iff_toReal_le ha (le_trans toReal_nonneg hx.1), ofReal_le_iff_le_toReal hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1)

-- sanity check: this measure is what you expect
example : volume (Set.Icc (3 : ℝ≥0∞) 42) = 39 := by
  rw [ENNReal.volume_val measurableSet_Icc]
  rw [ENNReal.toReal_Icc_eq_Icc (Ne.symm top_ne_ofNat) (Ne.symm top_ne_ofNat)]
  rw [toReal_ofNat, Real.volume_Icc, ofReal_eq_ofNat]
  norm_num

lemma lintegral_nnreal_eq_lintegral_Ici_ofReal {f : ℝ≥0 → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ici (0 : ℝ), f x.toNNReal := by
  change ∫⁻ (x : ℝ≥0), f x = ∫⁻ (x : ℝ) in Ici 0, (f ∘ Real.toNNReal) x
  rw [← lintegral_subtype_comap measurableSet_Ici]
  simp
  rfl

lemma lintegral_nnreal_eq_lintegral_Ioi_ofReal {f : ℝ≥0∞ → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

-- TODO: are there better names?
lemma lintegral_nnreal_eq_lintegral_toNNReal_Ioi (f : ℝ≥0 → ℝ≥0∞) :
    ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f x.toNNReal := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

-- TODO: do we actually use this?
lemma lintegral_nnreal_toReal_eq_lintegral_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ x : ℝ≥0, f (x.toReal) = ∫⁻ x in Ioi (0 : ℝ), f x := by
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  refine setLIntegral_congr_fun_ae measurableSet_Ioi ?_
  filter_upwards with x hx
  have : max x 0 = x := max_eq_left_of_lt hx
  simp [this]

lemma lintegral_nnreal_toReal_eq_lintegral_Ici (f : ℝ → ℝ≥0∞) :
    ∫⁻ x : ℝ≥0, f (x.toReal) = ∫⁻ x in Ici (0 : ℝ), f x := by
  rw [lintegral_nnreal_toReal_eq_lintegral_Ioi]
  exact setLIntegral_congr Ioi_ae_eq_Ici

-- TODO: lemmas about interaction with the Bochner integral
