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

lemma NNReal.volume_eq_volume_ennreal {s : Set ℝ≥0} (hs : MeasurableSet (ofNNReal '' s)) :
    volume s = volume (ENNReal.ofNNReal '' s) := by
  rw [ENNReal.volume_val hs, NNReal.volume_val]
  congr 1
  exact Eq.symm (image_image ENNReal.toReal ofNNReal s)

lemma ENNReal.volume_eq_volume_preimage {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.ofReal ⁻¹' s ∩ Ici 0) := by
  rw [ENNReal.volume_val hs, measure_congr ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal]
  congr; ext x; simp only [mem_image, mem_preimage, mem_inter_iff, mem_Ici]
  constructor <;> intro h
  · obtain ⟨x', hx', rfl⟩ := h; simpa
  · lift x to ℝ≥0 using h.2; rw [ofReal_coe_nnreal] at h; use x, h.1

lemma Ioo_zero_top_ae_eq_univ : Ioo 0 ∞ =ᶠ[ae volume] Set.univ := by
    simp only [ae_eq_univ]
    rw [ENNReal.volume_val]
    · have : (Ioo 0 ⊤)ᶜ = {0, ∞} := by rw [@compl_def]; ext x; simp [pos_iff_ne_zero]; tauto
      rw [this]
      have : ENNReal.toReal '' {0, ⊤} = { 0 } := by unfold image; simp
      rw [this]
      simp
    · measurability

lemma ae_in_Ioo_zero_top : ∀ᵐ x : ℝ≥0∞, x ∈ Ioo 0 ∞ := by
  filter_upwards [Ioo_zero_top_ae_eq_univ] with a ha
  simp only [eq_iff_iff] at ha; exact ha.mpr trivial

lemma map_restrict_Ioi_eq_restrict_Ioi :
    (volume.restrict (Ioi 0)).map ENNReal.ofReal = volume.restrict (Ioi 0) := by
  ext s hs
  rw [Measure.map_apply measurable_ofReal hs]
  simp only [measurableSet_Ioi, Measure.restrict_apply']
  rw [ENNReal.volume_eq_volume_preimage (by measurability)]
  congr 1
  ext x
  simp +contextual [LT.lt.le]

lemma map_restrict_Ioi_eq_volume :
    (volume.restrict (Ioi 0)).map ENNReal.ofReal = volume := by
  refine Eq.trans map_restrict_Ioi_eq_restrict_Ioi ?_
  refine Measure.restrict_eq_self_of_ae_mem ?_
  filter_upwards [ae_in_Ioo_zero_top] with a ha using ha.1


--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma NNReal.toReal_Iio_eq_Ico {b : ℝ≥0} :
    NNReal.toReal '' Set.Iio b = Set.Ico 0 b.toReal := by
  ext x
  simp only [mem_image, mem_Iio, mem_Ico]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa
  · rintro hx
    use x.toNNReal, (Real.toNNReal_lt_iff_lt_coe hx.1).mpr hx.2
    simp [hx.1]

lemma NNReal.toReal_Ioo_eq_Ioo {a b : ℝ≥0} :
    NNReal.toReal '' Set.Ioo a b = Set.Ioo a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa
  · intro h
    have x_nonneg : 0 ≤ x := by
      apply le_trans _ h.1.le
      simp
    use x.toNNReal
    rw [Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_lt_iff_lt_coe x_nonneg]
    use h, Real.coe_toNNReal x x_nonneg

lemma NNReal.volume_Iio {b : ℝ≥0} : volume (Set.Iio b) = b := by
  rw [NNReal.volume_val]
  simp only [val_eq_coe]
  rw [toReal_Iio_eq_Ico, Real.volume_Ico]
  simp

lemma NNReal.volume_Ioo {a b : ℝ≥0} : volume (Set.Ioo a b) = b - a:= by
  rw [NNReal.volume_val]
  simp only [val_eq_coe]
  rw [toReal_Ioo_eq_Ioo, Real.volume_Ioo, ENNReal.ofReal_sub] <;> simp

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Icc_eq_Icc {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Icc a b = Set.Icc a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hyx,
          toReal_le_toReal ha (lt_top_iff_ne_top.mp (hy.2.trans_lt (lt_top_iff_ne_top.mpr hb))),
          toReal_le_toReal (lt_top_iff_ne_top.mp (hy.2.trans_lt (lt_top_iff_ne_top.mpr hb))) hb]
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [le_ofReal_iff_toReal_le ha (le_trans toReal_nonneg hx.1), ofReal_le_iff_le_toReal hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1)

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Ioo_eq_Ioo {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Ioo a b = Set.Ioo a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hyx,
          toReal_lt_toReal ha (lt_top_iff_ne_top.mp (hy.2.trans (lt_top_iff_ne_top.mpr hb))),
          toReal_lt_toReal (lt_top_iff_ne_top.mp (hy.2.trans (lt_top_iff_ne_top.mpr hb))) hb]
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [lt_ofReal_iff_toReal_lt ha, ofReal_lt_iff_lt_toReal (le_trans toReal_nonneg hx.1.le) hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1.le)

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Ioo_top_eq_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Ioo a ⊤ = Set.Ioi a.toReal := by
  ext x
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨y, ⟨hay, y_lt_top⟩, hyx⟩
    rwa [← hyx, toReal_lt_toReal ha y_lt_top.ne]
  · rintro hax
    use ENNReal.ofReal x
    constructor
    · simp only [ofReal_lt_top, and_true]
      rwa [lt_ofReal_iff_toReal_lt ha]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hax.le)

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Ioi_eq_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Ioi a = Set.Ioi a.toReal ∪ {0} := by
  ext x
  simp only [mem_image, mem_Ioi, union_singleton, mem_insert_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_cases h : y = ⊤
    · left
      rw [← hyx, h, ENNReal.toReal_top]
    right
    rw [← hyx]
    rwa [ENNReal.toReal_lt_toReal ha h]
  · rintro (x_zero | hxa)
    · use ⊤
      rw [x_zero]
      simp only [toReal_top, and_true]
      exact Ne.lt_top' (id (Ne.symm ha))
    use ENNReal.ofReal x
    simp only [toReal_ofReal_eq_iff]
    constructor
    · rwa [ENNReal.lt_ofReal_iff_toReal_lt ha]
    · exact (le_trans toReal_nonneg hxa.le)

lemma ENNReal.volume_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    volume (Set.Ioi a) = ⊤ := by
  rw [ENNReal.volume_val measurableSet_Ioi, ENNReal.toReal_Ioi_eq_Ioi ha]
  rw [measure_union_eq_top_iff]
  left
  exact Real.volume_Ioi

--TODO: move somewhere else?
theorem ENNReal.Ioi_eq_Ioc_top {a : ℝ≥0∞} : Ioi a = Ioc a ⊤ := by
  unfold Ioi Ioc
  ext x
  simp

lemma ENNReal.volume_Ioo {a b : ℝ≥0∞} (ha : a ≠ ∞) :
    volume (Set.Ioo a b) = b - a := by
  rw [ENNReal.volume_val measurableSet_Ioo]
  by_cases hb : b = ⊤
  · have : ⊤ - ⊤ = (0 : ENNReal) := by simp only [tsub_self]
    rw [hb, ENNReal.top_sub ha, ENNReal.toReal_Ioo_top_eq_Ioi ha]
    apply Real.volume_Ioi
  rw [ENNReal.toReal_Ioo_eq_Ioo ha hb]
  rw [Real.volume_Ioo, ENNReal.ofReal_sub _ (by simp), ENNReal.ofReal_toReal hb, ENNReal.ofReal_toReal ha]

-- sanity check: this measure is what you expect
example : volume (Set.Icc (3 : ℝ≥0∞) 42) = 39 := by
  rw [ENNReal.volume_val measurableSet_Icc]
  rw [ENNReal.toReal_Icc_eq_Icc (Ne.symm top_ne_ofNat) (Ne.symm top_ne_ofNat)]
  rw [toReal_ofNat, Real.volume_Icc, ofReal_eq_ofNat]
  norm_num

instance : Measure.IsOpenPosMeasure (@volume ℝ≥0∞ _) where
  open_pos := by
    intro U open_U nonempty_U
    rcases open_U.exists_Ioo_subset nonempty_U with ⟨a, b, a_lt_b, Ioo_subset⟩
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot]
    apply lt_of_lt_of_le _ (measure_mono Ioo_subset)
    rw [ENNReal.volume_Ioo a_lt_b.ne_top]
    simpa

instance : Measure.IsOpenPosMeasure (@volume ℝ≥0 _) where
  open_pos := by
    intro U open_U nonempty_U
    rcases open_U.exists_Ioo_subset nonempty_U with ⟨a, b, a_lt_b, Ioo_subset⟩
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot]
    apply lt_of_lt_of_le _ (measure_mono Ioo_subset)
    rw [NNReal.volume_Ioo]
    simpa

instance : NoAtoms (@volume ℝ≥0∞ _) where
  measure_singleton := by
    intro x
    rw [ENNReal.volume_val (measurableSet_singleton _), image_singleton]
    simp

--TODO: move this general result to an appropriate place
--TODO: maybe generalize further to general measures restricted to a subtype
lemma Measure.Subtype.noAtoms {δ : Type*} [MeasureSpace δ] [NoAtoms (volume : Measure δ)] {p : δ → Prop} (hp : MeasurableSet p) :
    NoAtoms (Measure.Subtype.measureSpace.volume : Measure (Subtype p)) where
  measure_singleton := by
    intro x
    calc _
      _ = volume (Subtype.val '' {x}) := by
        apply comap_subtype_coe_apply hp volume
      _ = 0 := by
        simp

instance : NoAtoms (@volume ℝ≥0 _) := Measure.Subtype.noAtoms measurableSet_Ici

--TODO: move this general result to an appropriate place
--TODO: maybe generalize further to general measures restricted to a subtype
lemma Measure.Subtype.sigmaFinite {δ : Type*} [MeasureSpace δ] [sf : SigmaFinite (@volume δ _)] {p : δ → Prop} (hp : MeasurableSet p) :
    SigmaFinite (Measure.Subtype.measureSpace.volume : Measure (Subtype p)) where
  out' := by
    refine Nonempty.intro ?_
    rw [sigmaFinite_iff] at sf
    rcases Classical.choice sf with ⟨set, set_mem, finite, spanning⟩
    set set' := fun n ↦ (Subtype.val ⁻¹' (set n))
    apply Measure.FiniteSpanningSetsIn.mk set'
    · simp
    · intro n
      calc _
        _ = volume (Subtype.val '' set' n) := by
          apply comap_subtype_coe_apply hp volume (set' n)
        _ ≤ volume (set n) := by
          apply measure_mono
          unfold set'
          exact image_preimage_subset Subtype.val (set n)
        _ < ⊤ := finite n
    · unfold set'
      rw [← preimage_iUnion]
      refine preimage_eq_univ_iff.mpr ?_
      rw [spanning]
      exact fun ⦃a⦄ a ↦ trivial

instance : SigmaFinite (@volume ℝ≥0 _) := Measure.Subtype.sigmaFinite measurableSet_Ici


lemma lintegral_nnreal_eq_lintegral_Ici_ofReal {f : ℝ≥0 → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ici (0 : ℝ), f x.toNNReal := by
  change ∫⁻ (x : ℝ≥0), f x = ∫⁻ (x : ℝ) in Ici 0, (f ∘ Real.toNNReal) x
  rw [← lintegral_subtype_comap measurableSet_Ici]
  simp
  rfl

lemma lintegral_nnreal_eq_lintegral_Ioi_ofReal {f : ℝ≥0∞ → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

lemma lintegral_ennreal_eq_lintegral_of_nnreal {f : ℝ≥0∞ → ℝ≥0∞} :
    ∫⁻ x : ℝ≥0∞, f x = ∫⁻ x : ℝ≥0, f x := by
  refine (MeasurePreserving.lintegral_comp_emb ⟨by fun_prop, rfl⟩ ?_ f).symm
  refine isEmbedding_coe.measurableEmbedding ?_
  rw [range_coe']; exact measurableSet_Iio

lemma lintegral_ennreal_eq_lintegral_Ioi_ofReal {f : ℝ≥0∞ → ℝ≥0∞} :
    ∫⁻ x : ℝ≥0∞, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) :=
  lintegral_ennreal_eq_lintegral_of_nnreal.trans lintegral_nnreal_eq_lintegral_Ioi_ofReal

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
