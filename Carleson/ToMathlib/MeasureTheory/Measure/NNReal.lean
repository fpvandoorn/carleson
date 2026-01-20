import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Carleson.ToMathlib.MeasureTheory.Integral.Lebesgue

open MeasureTheory NNReal ENNReal Set

noncomputable
instance NNReal.MeasureSpace : MeasureSpace ℝ≥0 := ⟨Measure.Subtype.measureSpace.volume⟩

-- Upstreaming status:
-- The results in this file are generally worth having, but the proofs can be golfed
-- and refactored more (e.g., helper lemmas split out).

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
lemma ENNReal.ofNNReal_preimage {s : Set ℝ≥0∞} :
    ENNReal.ofNNReal ⁻¹' s = ENNReal.toNNReal '' (s \ {⊤}) := by
  ext x
  simp only [mem_image, mem_diff, mem_singleton_iff, mem_preimage]
  constructor
  · intro h
    use ENNReal.ofNNReal x
    simpa
  · rintro ⟨y, hys, hyx⟩
    rw [← hyx, coe_toNNReal hys.2]
    exact hys.1

--TODO: move these lemmas somewhere else?
lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} (h : ∞ ∉ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  rw [ofNNReal_preimage, image_image, diff_singleton_eq_self h]
  congr

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
      have : ENNReal.toReal '' {0, ⊤} = { 0 } := by simp [image]
      simp [this]
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

lemma NNReal.toReal_Ioi_eq_Ioi {b : ℝ≥0} :
    NNReal.toReal '' Set.Ioi b = Set.Ioi b.toReal := by
  ext x
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa
  · rintro hx
    use x.toNNReal
    rw [Real.lt_toNNReal_iff_coe_lt]
    use hx
    simp only [Real.coe_toNNReal', sup_eq_left]
    exact (coe_nonneg b).trans hx.le

lemma NNReal.toReal_Ioo_eq_Ioo {a b : ℝ≥0} :
    NNReal.toReal '' Set.Ioo a b = Set.Ioo a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Ioo]
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← hyx]
    simpa
  · have x_nonneg : 0 ≤ x := zero_le_coe.trans h.1.le
    refine ⟨x.toNNReal, ?_, Real.coe_toNNReal x (zero_le_coe.trans h.1.le)⟩
    rwa [Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_lt_iff_lt_coe x_nonneg]

theorem NNReal.Ici_eq {a : ℝ≥0} :
  Ici (↑a) = (Real.toNNReal ⁻¹' Ici a ∩ Ici 0) := by
  ext x
  constructor
  · intro hx
    constructor
    · simp only [mem_preimage, mem_Ici]
      exact le_toNNReal_of_coe_le hx
    · apply zero_le_coe.trans hx
  · rintro ⟨hx1, hx2⟩
    simp only [mem_preimage, mem_Ici] at *
    rwa [← Real.le_toNNReal_iff_coe_le hx2]

lemma NNReal.volume_Iio {b : ℝ≥0} : volume (Set.Iio b) = b := by
  rw [NNReal.volume_val]
  simp only [val_eq_coe]
  rw [toReal_Iio_eq_Ico, Real.volume_Ico]
  simp

lemma NNReal.volume_Ioi {b : ℝ≥0} : volume (Set.Ioi b) = ⊤ := by
  rw [NNReal.volume_val]
  simp only [val_eq_coe]
  rw [toReal_Ioi_eq_Ioi, Real.volume_Ioi]

lemma NNReal.volume_Ioo {a b : ℝ≥0} : volume (Set.Ioo a b) = b - a:= by
  rw [NNReal.volume_val]
  simp only [val_eq_coe]
  rw [toReal_Ioo_eq_Ioo, Real.volume_Ioo, ENNReal.ofReal_sub] <;> simp

-- TODO: the proofs in the following lemmas feel quite repetitive
-- extract helper lemma to re-use some of the argument!

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Iio_eq_Ico {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Iio a = Set.Ico 0 a.toReal := by
  ext x
  simp only [mem_image, mem_Iio, mem_Ico]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩⟩
    rw [← hy₂]
    constructor
    · simp
    · exact (ENNReal.toReal_lt_toReal hy₁.ne_top ha).mpr hy₁
  · rintro ⟨zero_le_x, x_lt⟩
    use ENNReal.ofReal x
    constructor
    · exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_x ha).mpr x_lt
    · simpa

lemma ENNReal.toReal_Iio_top_eq_Ici :
    ENNReal.toReal '' Set.Iio ⊤ = Set.Ici 0 := by
  ext x
  simp only [mem_image, mem_Iio, mem_Ici]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩⟩
    rw [← hy₂]
    simp
  · rintro zero_le_x
    use ENNReal.ofReal x
    simpa

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Icc_eq_Icc {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Icc a b = Set.Icc a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, hxy⟩
    rw [← hxy]
    constructor <;> gcongr
    · exact ne_top_of_le_ne_top hb hy₂
    · assumption
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [le_ofReal_iff_toReal_le ha (le_trans toReal_nonneg hx.1), ofReal_le_iff_le_toReal hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1)

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Ioo_eq_Ioo {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Ioo a b = Set.Ioo a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, hyx⟩
    rw [← hyx]
    constructor <;> gcongr
    · finiteness
    · assumption
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [lt_ofReal_iff_toReal_lt ha, ofReal_lt_iff_lt_toReal (le_trans toReal_nonneg hx.1.le) hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1.le)

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
lemma ENNReal.toReal_Ioo_top_eq_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Ioo a ⊤ = Set.Ioi a.toReal := by
  ext x
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨y, ⟨hay, y_lt_top⟩, hyx⟩
    rwa [← hyx, toReal_lt_toReal ha y_lt_top.ne]
  · rintro hax
    use ENNReal.ofReal x
    refine ⟨⟨?_, by finiteness⟩, ?_⟩
    · rwa [lt_ofReal_iff_toReal_lt ha]
    · rw [toReal_ofReal_eq_iff]
      exact toReal_nonneg.trans hax.le

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
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
    gcongr; assumption
  · rintro (x_zero | hxa)
    · exact ⟨⊤, by finiteness, by simp [x_zero]⟩
    use ENNReal.ofReal x
    simp only [toReal_ofReal_eq_iff]
    constructor
    · rwa [ENNReal.lt_ofReal_iff_toReal_lt ha]
    · exact (le_trans toReal_nonneg hxa.le)

lemma ENNReal.ofReal_Ico_eq {b : ℝ≥0∞} : ENNReal.ofReal ⁻¹' Set.Ico 0 b
    = if b = 0 then ∅ else if b = ∞ then Set.univ else Set.Iio b.toReal := by
  split_ifs with hb hb'
  · rw [hb]
    simp
  · rw [hb']
    simp only [preimage_eq_univ_iff]
    intro x hx
    simp only [mem_Ico, zero_le, true_and]
    rcases hx with ⟨y, hy⟩
    rw [← hy]
    simp
  · ext x
    simp only [mem_preimage, mem_Ico, zero_le, true_and, mem_Iio]
    by_cases! hx : x < 0
    · rw [ENNReal.ofReal_of_nonpos hx.le]
      exact ⟨fun _ ↦ hx.trans_le (by positivity), fun _ ↦ by positivity⟩
    exact ofReal_lt_iff_lt_toReal hx hb'

lemma ENNReal.toNNReal_Iio {b : ℝ≥0∞} : ENNReal.toNNReal '' Set.Iio b
    = if b = ∞ then Set.univ else Set.Iio b.toNNReal := by
  split_ifs with hb
  · rw [hb]
    ext x
    simp only [mem_image, mem_Iio, mem_univ, iff_true]
    use ofNNReal x
    simp
  · ext x
    simp only [mem_image, mem_Iio]
    constructor
    · rintro ⟨y, hyb, hyx⟩
      rwa [← hyx, ENNReal.toNNReal_lt_toNNReal _ hb]
      grind
    · intro h
      use ofNNReal x
      simp only [toNNReal_coe, and_true]
      rw [← ENNReal.toNNReal_lt_toNNReal (by simp) hb]
      simpa

lemma ENNReal.volume_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    volume (Set.Ioi a) = ⊤ := by
  rw [ENNReal.volume_val measurableSet_Ioi, ENNReal.toReal_Ioi_eq_Ioi ha, measure_union_eq_top_iff]
  left
  exact Real.volume_Ioi

-- TODO: move somewhere else?
theorem ENNReal.Ioi_eq_Ioc_top {a : ℝ≥0∞} : Ioi a = Ioc a ⊤ := by
  unfold Ioi Ioc
  ext x
  simp

lemma ENNReal.volume_Iio {a : ℝ≥0∞} :
    volume (Set.Iio a) = a := by
  rw [ENNReal.volume_val measurableSet_Iio]
  by_cases ha : a = ⊤
  · rw [ha, ENNReal.toReal_Iio_top_eq_Ici, Real.volume_Ici]
  · rw [ENNReal.toReal_Iio_eq_Ico ha, Real.volume_Ico]
    simpa

lemma ENNReal.volume_Ioo {a b : ℝ≥0∞} (ha : a ≠ ∞) :
    volume (Set.Ioo a b) = b - a := by
  rw [ENNReal.volume_val measurableSet_Ioo]
  by_cases hb : b = ⊤
  · have : ⊤ - ⊤ = (0 : ENNReal) := by simp only [tsub_self]
    rw [hb, ENNReal.top_sub ha, ENNReal.toReal_Ioo_top_eq_Ioi ha]
    apply Real.volume_Ioi
  rw [toReal_Ioo_eq_Ioo ha hb, Real.volume_Ioo, ofReal_sub _ (by simp), ofReal_toReal hb, ofReal_toReal ha]

-- sanity check: this measure is what you expect
example : volume (Set.Icc (3 : ℝ≥0∞) 42) = 39 := by
  rw [volume_val measurableSet_Icc,
    toReal_Icc_eq_Icc (by finiteness) (by finiteness),
    toReal_ofNat, Real.volume_Icc, ofReal_eq_ofNat]
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

-- TODO: move this general result to an appropriate place
-- TODO: maybe generalize further to general measures restricted to a subtype
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

lemma lintegral_nnreal_Ici_eq_lintegral_Ici_ofReal {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} :
    ∫⁻ x in Ici a, f x = ∫⁻ x in Ici (a : ℝ), f x.toNNReal := by
  rw [← lintegral_indicator measurableSet_Ici, lintegral_nnreal_eq_lintegral_Ici_ofReal]
  simp_rw [← indicator_comp_right]
  rw [setLIntegral_indicator (MeasurableSet.preimage measurableSet_Ici measurable_real_toNNReal)]
  simp only [Function.comp_apply]
  apply setLIntegral_congr
  rw [NNReal.Ici_eq]

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

lemma setLIntegral_nnreal_Ici {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} :
    ∫⁻ (t : ℝ≥0) in Set.Ici a, f t = ∫⁻ (t : ℝ≥0), f (t + a) := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal, ← lintegral_shift' (a := -a)]
  simp only [preimage_add_const_Ici, sub_neg_eq_add, zero_add]
  rw [lintegral_nnreal_Ici_eq_lintegral_Ici_ofReal]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro x hx
  simp only
  congr
  have : (a : ℝ).toNNReal = a := by exact Real.toNNReal_coe
  nth_rw 2 [← this]
  rw [← Real.toNNReal_add]
  · simp only [neg_add_cancel_right]
  · simpa
  · exact zero_le_coe

lemma lintegral_nnreal_scale_constant' {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0) :
    a * ∫⁻ x : ℝ≥0, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi, lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  symm
  rw [← lintegral_scale_constant_halfspace' (a:=a) (by rw [NNReal.coe_pos, pos_iff_ne_zero]; exact h)]
  congr 1
  · simp
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  congr
  rw [Real.toNNReal_mul (by simp)]
  simp

-- TODO: lemmas about interaction with the Bochner integral
