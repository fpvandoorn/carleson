import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Defs
import Carleson.ToMathlib.RealInterpolation.Misc
import Carleson.ToMathlib.Topology.Order.Basic

noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α} {p q : ℝ≥0∞} {μ : Measure α} [ENorm ε]
  [ENorm ε']

namespace MeasureTheory


lemma eLorentzNorm'_mono_enorm_ae {f : α → ε'} {g : α → ε} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm' f p q μ ≤ eLorentzNorm' g p q μ := by
  unfold eLorentzNorm'
  gcongr
  apply eLpNorm_mono_enorm
  intro x
  simp only [ENNReal.toReal_inv, enorm_eq_self]
  gcongr
  exact h

lemma eLorentzNorm_mono_enorm_ae {f : α → ε'} {g : α → ε} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  unfold eLorentzNorm
  split_ifs
  · trivial
  · trivial
  · exact essSup_mono_ae h
  · gcongr
    exact essSup_mono_ae h
  · exact eLorentzNorm'_mono_enorm_ae h

--Proof analogous to eLpNorm_congr_enorm_ae
theorem eLorentzNorm_congr_enorm_ae {f : α → ε'} {g : α → ε} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  le_antisymm (eLorentzNorm_mono_enorm_ae <| Filter.EventuallyEq.le hfg)
    (eLorentzNorm_mono_enorm_ae <| (Filter.EventuallyEq.symm hfg).le)

--Proof analogous to eLpNorm_congr_ae
theorem eLorentzNorm_congr_ae {f g : α → ε'} (hfg : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  eLorentzNorm_congr_enorm_ae <| hfg.mono fun _x hx => hx ▸ rfl


variable {ε : Type*} [TopologicalSpace ε]

--TODO: make this an iff, for p, r ≠ 0?
lemma eLorentzNorm_zero_of_ae_zero [ESeminormedAddMonoid ε] {f : α → ε} (h : enorm ∘ f =ᵐ[μ] 0) :
    eLorentzNorm f p q μ = 0 := by
  simp only [eLorentzNorm, ite_eq_left_iff]
  intro p_ne_zero
  rw [← eLpNorm_exponent_top, eLpNorm_zero_of_ae_zero' h]
  simp only [mul_zero, ite_self, ite_eq_left_iff]
  intro p_ne_top
  unfold eLorentzNorm'
  conv in ↑t * distribution f _ μ ^ p⁻¹.toReal =>
    rw [distribution_zero' h,
    ENNReal.zero_rpow_of_pos (by simp only [ENNReal.toReal_inv, inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top),
    mul_zero]
  simp

variable [ESeminormedAddMonoid ε]

@[simp]
lemma eLorentzNorm_zero : eLorentzNorm (0 : α → ε) p q μ = 0 := by
  apply eLorentzNorm_zero_of_ae_zero
  simp

@[simp]
lemma eLorentzNorm_zero' : eLorentzNorm (fun _ : α ↦  (0 : ε)) p q μ = 0 := eLorentzNorm_zero

lemma eLorentzNorm_eq_eLpNorm {f : α → ε} (hf : AEStronglyMeasurable f μ) :
  eLorentzNorm f p p μ = eLpNorm f p μ := by
  by_cases p_zero : p = 0
  · simp [p_zero]
  by_cases p_eq_top : p = ∞
  · simp [p_eq_top]
  have p_eq : p = .ofReal p.toReal := by simp [p_eq_top]
  simp only [eLorentzNorm, eLorentzNorm', p_zero, ↓reduceIte, p_eq_top]
  calc _
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal t ^ (p.toReal - 1) ) ^ p⁻¹.toReal := by
        rw [← p_eq, eLpNorm_eq_eLpNorm' p_zero p_eq_top, eLpNorm'_eq_lintegral_enorm,
          ENNReal.mul_rpow_of_nonneg, lintegral_withDensity_eq_lintegral_mul_non_measurable]
        · simp only [ENNReal.toReal_inv, enorm_eq_self, one_div]
          congr 2
          simp only [Pi.mul_apply]
          rw [lintegral_nnreal_eq_lintegral_Ioi_ofReal
            (f := fun x ↦ x⁻¹ * (x * distribution f x μ ^ p.toReal⁻¹)^ p.toReal)]
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht
          simp only
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← mul_assoc, ← ENNReal.rpow_neg_one,
              ← ENNReal.rpow_add _ _ (by simpa) (by simp), mul_comm]
          congr 2
          · rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨p_zero, p_eq_top⟩),
              ENNReal.rpow_one]
          · exact neg_add_eq_sub 1 p.toReal
        · exact Measurable.inv measurable_coe_nnreal_ennreal
        · rw[Filter.eventually_iff_exists_mem]
          use {x | x ≠ 0}
          constructor
          · refine mem_ae_iff.mpr ?_
            rw [NNReal.volume_val]
            simp
          · intro x hx
            rw[ENNReal.inv_lt_top, ENNReal.coe_pos]
            exact pos_of_ne_zero hx
        · simp
    _ = (ENNReal.ofReal p.toReal  * ∫⁻ t in Set.Ioi (0 : ℝ), distribution f (.ofReal t) μ *
      ENNReal.ofReal (t ^ (p.toReal - 1)) ) ^ p.toReal⁻¹ := by
        rw [ENNReal.toReal_inv]
        congr 2
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [ENNReal.ofReal_rpow_of_pos ht]
    _ = eLpNorm f (.ofReal p.toReal) μ := (eLpNorm_eq_distribution hf (ENNReal.toReal_pos p_zero p_eq_top)).symm
    _ = eLpNorm f p μ := by congr; exact p_eq.symm


--TODO: move to essSup.lean
lemma essSup_le_iSup {α : Type*} {β : Type*} {m : MeasurableSpace α} {μ : Measure α} [CompleteLattice β]
    (f : α → β) : essSup f μ ≤ ⨆ i, f i := by
  apply essSup_le_of_ae_le
  apply Filter.Eventually.of_forall
  intro i
  apply le_iSup

--TODO: move
lemma iSup_le_essSup {f : α → ℝ≥0∞}
  (h : ∀ {x}, ∀ {a}, a < f x → μ {y | a < f y} ≠ 0) :
    ⨆ x, f x ≤ essSup f μ := by
  apply iSup_le
  intro i
  rw [essSup_eq_sInf]
  apply le_sInf
  intro b hb
  simp only [Set.mem_setOf_eq] at hb
  apply le_of_forall_lt
  intro c hc
  have := h hc
  contrapose! this
  rw [← ENNReal.bot_eq_zero, ← le_bot_iff] at *
  apply le_trans _ hb
  apply measure_mono
  intro x
  simp only [Set.mem_setOf_eq]
  intro hc
  exact lt_of_le_of_lt this hc

lemma helper {f : ℝ≥0∞ → ℝ≥0∞} {x : ℝ≥0∞} (hx : x ≠ ⊤)
  (hf : ContinuousWithinAt f (Set.Ioi x) x)
  {a : ℝ≥0∞} (ha : a < f x) :
    volume {y | a < f y} ≠ 0 := by
  unfold ContinuousWithinAt at hf
  set s := Set.Ioi a
  have mem_nhds_s : s ∈ nhds (f x) := by
    rw [IsOpen.mem_nhds_iff isOpen_Ioi]
    simpa
  have := hf mem_nhds_s
  simp only [Filter.mem_map] at this
  rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot]
  rw [mem_nhdsWithin] at this
  rcases this with ⟨u, u_open, x_in_u, u_inter_subset⟩
  calc _
    _ < volume (u ∩ Set.Ioi x) := by
      rw [bot_lt_iff_ne_bot]
      apply IsOpen.measure_ne_zero
      · apply u_open.inter isOpen_Ioi
      apply nonempty_nhds_inter_Ioi (IsOpen.mem_nhds u_open x_in_u) (not_isMax_iff_ne_top.mpr hx)
    _ ≤ volume (f ⁻¹' s) := by
      apply measure_mono u_inter_subset
    _ ≤ volume {y | a < f y} := by
      apply measure_mono
      unfold s Set.preimage
      simp only [Set.mem_Ioi, Set.setOf_subset_setOf]
      intro y h
      exact h

--TODO: move
theorem ContinuousWithinAt.ennreal_mul {X : Type*}
  [TopologicalSpace X] {f g : X → ℝ≥0∞} {s : Set X} {t : X} (hf : ContinuousWithinAt f s t)
  (hg : ContinuousWithinAt g s t)
  (h₁ : f t ≠ 0 ∨ g t ≠ ∞)
  (h₂ : g t ≠ 0 ∨ f t ≠ ∞) :
    ContinuousWithinAt (fun x ↦ f x * g x) s t := fun _ hx =>
  ENNReal.Tendsto.mul hf h₁ hg h₂ hx

--TODO: move
nonrec theorem ContinuousWithinAt.ennrpow_const [TopologicalSpace α] {f : α → ℝ≥0∞} {s : Set α} {x : α}
  {p : ℝ}
  (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => f x ^ p) s x := by
  apply hf.ennrpow_const


lemma eLorentzNorm_eq_wnorm (hp : p ≠ 0) {f : α → ε} : eLorentzNorm f p ∞ μ = wnorm f p μ := by
  by_cases p_eq_top : p = ∞
  · rw [p_eq_top]
    simp
  rw [eLorentzNorm_eq_eLorentzNorm' hp p_eq_top, wnorm_ne_top p_eq_top]
  unfold eLorentzNorm' wnorm'
  simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, ENNReal.toReal_inv,
    eLpNorm_exponent_top, one_mul]
  unfold eLpNormEssSup
  simp only [enorm_eq_self]
  apply le_antisymm
  · apply essSup_le_iSup
  · apply iSup_le_essSup
    intro x a ha
    rw [ne_eq, withDensity_apply_eq_zero' (by measurability)]
    simp only [ne_eq, ENNReal.inv_eq_zero, ENNReal.coe_ne_top, not_false_eq_true, Set.setOf_true,
      Set.univ_inter]
    have : ENNReal.ofNNReal '' {y | a < ↑y * distribution f (↑y) μ ^ p.toReal⁻¹}
        = {y | a < y * distribution f y μ ^ p.toReal⁻¹} \ {⊤}:= by
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, hxy⟩
        rw [← hxy]
        use hx
        simp
      · intro hy
        by_cases y_eq_top : y = ⊤
        · exfalso
          exact hy.2 y_eq_top
        use y.toNNReal
        rw [ENNReal.coe_toNNReal y_eq_top]
        use hy.1
    rw [← ne_eq, NNReal.volume_eq_volume_ennreal]
    · rw [this, measure_diff_null (measure_singleton ⊤)]
      apply @helper _ x
      · simp
      · apply ContinuousWithinAt.ennreal_mul continuous_id'.continuousWithinAt
          (continuousWithinAt_distribution _).ennrpow_const
        · rw [or_iff_not_imp_left]
          push_neg
          intro h
          exfalso
          rw [h] at ha
          simp at ha
        · right
          simp
      · exact ha
    rw [this]
    apply MeasurableSet.diff _ (measurableSet_singleton ⊤)
    refine measurableSet_lt measurable_const ?_
    measurability

lemma eLorentzNorm'_indicator_const {a : ε} (ha : ‖a‖ₑ ≠ ⊤)
  {s : Set α} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) :
    eLorentzNorm' (s.indicator (Function.const α a)) p 1 μ = p * (‖a‖ₑ * μ s ^ p⁻¹.toReal) := by
  rw [eLorentzNorm'_eq_integral_distribution_rpow]
  congr
  simp_rw [distribution_indicator_const (ε := ε) (μ := μ) (s := s) (a := a)]
  unfold Set.indicator
  simp only [ENNReal.toReal_inv, ite_pow]
  symm
  calc ‖a‖ₑ * μ s ^ p.toReal⁻¹
    _ = (∫⁻ (t : ℝ≥0), (Set.Iio ‖a‖ₑ.toNNReal).indicator (fun x ↦ μ s ^ p.toReal⁻¹) t) := by
      rw [lintegral_indicator_const measurableSet_Iio, mul_comm]
      congr 1
      rw [NNReal.volume_Iio, ENNReal.coe_toNNReal ha]
  congr with t
  unfold Set.indicator
  rw [ENNReal.zero_rpow_of_pos (by simp only [inv_pos]; exact ENNReal.toReal_pos p_ne_zero p_ne_top)]
  congr 1
  simp only [Set.mem_Iio, eq_iff_iff]
  exact (ENNReal.coe_lt_iff_lt_toNNReal ha).symm


lemma eLorentzNorm'_indicator_const' {a : ε} {s : Set α} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) :
    eLorentzNorm' (s.indicator (Function.const α a)) p q μ
      = (p / q) ^ q.toReal⁻¹ * μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  rw [eLorentzNorm'_eq p_ne_zero p_ne_top]
  simp_rw [rearrangement_indicator_const]
  rw [eLpNorm_eq_lintegral_rpow_enorm q_ne_zero q_ne_top]
  simp only [ENNReal.toReal_inv, enorm_eq_self, one_div]
  conv in (_ * _) ^ _ => rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    Set.comp_indicator (fun t ↦ t ^ q.toReal),
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos q_ne_zero q_ne_top),
    Function.comp_const, Function.const_zero, Set.piecewise_eq_indicator,
    ← Set.indicator_mul_right _ (fun t ↦ (t ^ p.toReal⁻¹) ^ q.toReal) _,
    ← Set.indicator_comp_right]
  rw [lintegral_indicator (by measurability)]
  simp only [Function.const_apply, Function.comp_apply]
  rw [lintegral_mul_const _ (by fun_prop),
    ENNReal.mul_rpow_of_nonneg _ _ (by simp),
    ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨q_ne_zero, q_ne_top⟩)]
  congr
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop) (by measurability)]
  simp only [Pi.mul_apply]
  simp_rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul]
  rw [← lintegral_indicator (by measurability), lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  simp_rw [← Set.indicator_comp_right]
  rw [setLIntegral_indicator (by measurability)]
  have : ENNReal.ofNNReal ∘ Real.toNNReal = ENNReal.ofReal := rfl
  rw [← Set.preimage_comp, this]
  simp only [Function.comp_apply]
  have : ((μ s ^ p.toReal⁻¹) ^ q.toReal) ^ q.toReal⁻¹ = μ s ^ p.toReal⁻¹:= by
    apply ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨q_ne_zero, q_ne_top⟩)
  rw [← this, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp), ← ENNReal.rpow_mul]
  congr
  calc _
    _ = ∫⁻ (a : ℝ) in ENNReal.ofReal ⁻¹' Set.Ico 0 (μ s) ∩ Set.Ioi 0,
          ENNReal.ofReal (a ^ (p.toReal⁻¹ * q.toReal - 1)) := by
      apply setLIntegral_congr_fun (by measurability)
      intro x hx
      simp only
      rw [← ENNReal.rpow_add _ _
        (by simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]; exact hx.2)
        (by simp)]
      ring_nf
      rw [← ENNReal.ofReal_rpow_of_pos hx.2]
      congr
  rw [ENNReal.ofReal_Ico_eq]
  have hpq : 0 < p.toReal⁻¹ * q.toReal := by
    apply mul_pos
    · rw [inv_pos]
      exact ENNReal.toReal_pos p_ne_zero p_ne_top
    · exact ENNReal.toReal_pos q_ne_zero q_ne_top
  split_ifs with h h
  · simp only [Set.empty_inter, Measure.restrict_empty, lintegral_zero_measure, zero_eq_mul,
    ENNReal.div_eq_zero_iff, ENNReal.rpow_eq_zero_iff]
    right
    left
    use h, hpq
  · rw [Set.univ_inter]
    rw [lintegral_rpow_Ioi_top]
    rw [h, ENNReal.top_rpow_of_pos hpq, ENNReal.mul_top]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    use p_ne_zero, q_ne_top
  · rw [Set.Iio_inter_Ioi, lintegral_rpow_of_gt ENNReal.toReal_nonneg (by simpa)]
    simp only [sub_add_cancel]
    rw [ENNReal.ofReal_div_of_pos hpq, ENNReal.ofReal_mul (by simp),
        ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos p_ne_zero p_ne_top),
        ENNReal.ofReal_toReal p_ne_top, ENNReal.ofReal_toReal q_ne_top, ← ENNReal.div_eq_inv_mul,
        ← ENNReal.div_mul _ (by left; assumption) (by left; assumption), ENNReal.mul_comm_div,
        mul_comm, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
        ENNReal.ofReal_toReal h]

@[simp]
lemma eLorentzNorm_indicator_const {a : ε} {s : Set α} :
  eLorentzNorm (s.indicator (Function.const α a)) p q μ
    = if p = 0 then 0
      else if q = 0 then 0
      else if p = ∞ then
        (if μ s = 0 then 0 else if q = ∞ then ‖a‖ₑ else ∞ * ‖a‖ₑ)
      else if q = ∞ then
        μ s ^ p.toReal⁻¹ * ‖a‖ₑ
      else
        (p / q) ^ q.toReal⁻¹ * μ s ^ p.toReal⁻¹ * ‖a‖ₑ := by
  unfold eLorentzNorm
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  all_goals try rfl
  · exact eLpNormEssSup_indicator_const_eq' h₄
  · unfold Function.const
    rw [eLpNormEssSup_indicator_const_eq s a h₄]
  · unfold Function.const
    rw [eLpNormEssSup_indicator_const_eq' h₅]
    exact CommMonoidWithZero.mul_zero ⊤
  · congr
    exact eLpNormEssSup_indicator_const_eq s a h₅
  · simp [h₆]
  · rw [← eLorentzNorm_eq_eLorentzNorm' h₀ h₁, h₇, eLorentzNorm_eq_wnorm h₀]
    rw [wnorm_indicator_const h₀ h₁]
  · exact eLorentzNorm'_indicator_const' h₀ h₁ h₆ h₇


lemma MemLorentz_iff_MemLp {f : α → ε} :
    MemLorentz f p p μ ↔ MemLp f p μ := by
  unfold MemLorentz MemLp
  constructor
  · intro h
    rwa [← eLorentzNorm_eq_eLpNorm h.1]
  · intro h
    rwa [eLorentzNorm_eq_eLpNorm h.1]


-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_of_MemLorentz_ge {r₁ r₂ : ℝ≥0∞} (r₁_pos : 0 < r₁) (r₁_le_r₂ : r₁ ≤ r₂) {f : α → ε}
  (hf : MemLorentz f p r₁ μ) :
    MemLorentz f p r₂ μ := by
  unfold MemLorentz at *
  rcases hf with ⟨meas_f, norm_f⟩
  use meas_f
  unfold eLorentzNorm at *
  split_ifs at * with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exfalso
    exact r₁_pos.ne h₆.symm
  · exact norm_f
  · rw [ENNReal.top_mul'] at norm_f
    split_ifs at norm_f with h
    · rwa [h]
    · exfalso
      exact (lt_self_iff_false ⊤).mp norm_f
  · exfalso
    exact r₁_pos.ne h₈.symm
  · exfalso
    rw [h₉, top_le_iff] at r₁_le_r₂
    exact h₅ r₁_le_r₂
  · exact norm_f
  · by_cases r₁_top : r₁ = ∞
    · convert norm_f
      rw [r₁_top, top_le_iff] at r₁_le_r₂
      rw [r₁_top, r₁_le_r₂]
    --Now the only interesting case
    have measurable_mul_distribution_rpow : Measurable fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal := by measurability
    unfold eLorentzNorm' at norm_f
    rw [ENNReal.mul_lt_top_iff] at norm_f
    rcases norm_f with ⟨_, norm_lt_top⟩ | p_zero | norm_zero
    · wlog r₂_top : r₂ = ⊤ generalizing r₂
      · have memLp_r₁: MemLp (fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal) r₁
                        (volume.withDensity fun t ↦ (↑t)⁻¹) := by
          constructor
          · exact (aeMeasurable_withDensity_inv measurable_mul_distribution_rpow.aemeasurable).aestronglyMeasurable
          exact norm_lt_top
        have memLp_top : MemLp (fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal) ⊤
                          (volume.withDensity fun t ↦ (↑t)⁻¹) := by
          constructor
          · exact (aeMeasurable_withDensity_inv measurable_mul_distribution_rpow.aemeasurable).aestronglyMeasurable
          have := this le_top rfl
          unfold eLorentzNorm' at this
          rw [ENNReal.mul_lt_top_iff] at this
          rcases this with ⟨_, norm_lt_top⟩ | p_zero | norm_zero
          · exact norm_lt_top
          · --TODO: duplicate from below
            exfalso
            rw [ENNReal.rpow_eq_zero_iff] at p_zero
            rcases p_zero with ⟨p_zero, _⟩ | ⟨p_top, _⟩
            · exact h₀ p_zero
            · exact h₁ p_top
          · rw [norm_zero]
            exact ENNReal.zero_lt_top
        unfold eLorentzNorm'
        rw [ENNReal.mul_lt_top_iff]
        left
        use ENNReal.rpow_lt_top_of_nonneg (by simp) h₁
        exact (MeasureTheory.memLp_of_memLp_le_of_memLp_ge r₁_pos ⟨r₁_le_r₂, le_top⟩ memLp_r₁ memLp_top).2
      /- Hardest part -/
      rw [eLpNorm_eq_lintegral_rpow_enorm r₁_pos.ne' r₁_top,
          lintegral_withDensity_eq_lintegral_mul₀ (by measurability) (measurable_mul_distribution_rpow.aestronglyMeasurable.enorm.pow_const r₁.toReal),
          lintegral_nnreal_eq_lintegral_toNNReal_Ioi] at norm_lt_top
      simp only [ENNReal.toReal_inv, enorm_eq_self, Pi.mul_apply, one_div] at norm_lt_top
      rw [r₂_top, ← eLorentzNorm_eq_eLorentzNorm' h₀ h₁, eLorentzNorm_eq_wnorm h₀, wnorm_ne_top h₁, wnorm']
      rw [iSup_lt_iff]
      have toReal_r₁_pos := ENNReal.toReal_pos r₁_pos.ne' r₁_top
      have : r₁ ^ r₁.toReal⁻¹ < ∞ := ENNReal.rpow_lt_top_of_nonneg (by simp) r₁_top
      have norm_lt_top' := ENNReal.mul_lt_top norm_lt_top this
      exists _, norm_lt_top'
      intro s
      rw [← ENNReal.div_le_iff_le_mul (by left; apply (ENNReal.rpow_pos r₁_pos r₁_top).ne') (by left; exact this.ne)] --TODO: improve this
      calc _
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (↑s / r₁ ^ r₁.toReal⁻¹) := by
          rw [mul_comm, mul_div_assoc]
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          rw [ENNReal.div_rpow_of_nonneg,
              ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne', r₁_top⟩)]
          simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          congr 1
          · rw [ENNReal.rpow_mul, ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne', r₁_top⟩)]
          --·
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, ENNReal.ofReal (x ^ (r₁.toReal - 1))) ^ r₁.toReal⁻¹:= by
          congr
          rw [lintegral_rpow_of_gt NNReal.zero_le_coe (by linarith), ENNReal.ofReal_div_of_pos (by simpa),
              ← ENNReal.ofReal_rpow_of_nonneg NNReal.zero_le_coe (by linarith)]
          ring_nf
          rw [ENNReal.ofReal_toReal r₁_top, ENNReal.ofReal, Real.toNNReal_coe]
        _ = (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal ^ r₁.toReal * distribution f s μ ^ (p.toReal⁻¹ * r₁.toReal))) ^ r₁.toReal⁻¹ := by
          rw [← ENNReal.mul_rpow_of_nonneg, ← lintegral_const_mul]
          · congr 1
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro x hx
            simp only
            rw [mul_comm, ← mul_assoc]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_pos hx.1, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ (by simp [hx.1]) (by simp), neg_add_eq_sub]
            congr
          · measurability
          · simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal * distribution f s μ ^ p.toReal⁻¹) ^ r₁.toReal) ^ r₁.toReal⁻¹ := by
          congr with x
          rw [ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul]
          exact ENNReal.toReal_nonneg
        _ ≤ (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal * distribution f (↑x.toNNReal) μ ^ p.toReal⁻¹) ^ r₁.toReal) ^ r₁.toReal⁻¹ := by
          apply ENNReal.rpow_le_rpow _ (by simp only [inv_nonneg, ENNReal.toReal_nonneg])
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ht
          gcongr
          exact Real.toNNReal_le_iff_le_coe.mpr ht.2.le
        _ ≤ (∫⁻ (x : ℝ) in Set.Ioi 0, (↑x.toNNReal)⁻¹ * (↑x.toNNReal * distribution f (↑x.toNNReal) μ ^ p.toReal⁻¹) ^ r₁.toReal) ^
            r₁.toReal⁻¹ := by
          gcongr
          exact Set.Ioo_subset_Ioi_self
    · exfalso
      rw [ENNReal.rpow_eq_zero_iff] at p_zero
      rcases p_zero with ⟨p_zero, _⟩ | ⟨p_top, _⟩
      · exact h₀ p_zero
      · exact h₁ p_top
    · unfold eLorentzNorm'
      rw [ENNReal.mul_lt_top_iff]
      right; right
      rw [eLpNorm_eq_zero_iff measurable_mul_distribution_rpow.aestronglyMeasurable r₁_pos.ne'] at norm_zero
      rwa [eLpNorm_eq_zero_iff measurable_mul_distribution_rpow.aestronglyMeasurable (r₁_pos.trans_le r₁_le_r₂).ne']

lemma MemLorentz.memLp {f : α → ε} (hf : MemLorentz f p q μ) (h : q ∈ Set.Ioc 0 p) :
    MemLp f p μ := by
  rw [← MemLorentz_iff_MemLp]
  apply MemLorentz_of_MemLorentz_ge h.1 h.2 hf

end MeasureTheory
