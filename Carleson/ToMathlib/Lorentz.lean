import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Carleson.Defs
import Carleson.ToMathlib.Data.ENNReal
import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.MeasureTheory.Function.SimpleFunc
import Carleson.ToMathlib.WeakType
import Carleson.ToMathlib.RealInterpolation.Misc

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α}

namespace MeasureTheory

/-
section decreasing_rearrangement
variable [ENorm ε] [ENorm ε']

def decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0) : ℝ≥0 :=
  sInf {σ | distribution f σ μ ≤ t}

lemma decreasing_rearrangement_antitone {f : α → ε} {μ : Measure α} :
    Antitone (decreasing_rearrangement f μ) := sorry

lemma distribution_decreasing_rearrangement (f : α → ε) (μ : Measure α) (t : ℝ≥0):
  distribution f t μ = distribution (decreasing_rearrangement f μ) t volume := sorry

end decreasing_rearrangement
-/

section Lorentz

variable [ENorm ε] [TopologicalSpace ε'] [ENormedAddMonoid ε'] {p : ℝ≥0∞} {q : ℝ}


/-- The Lorentz norm of a function, for `p < ∞` -/
def eLorentzNorm' (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  p ^ r⁻¹.toReal * eLpNorm (fun (t : ℝ≥0) ↦ t * distribution f t μ ^ p⁻¹.toReal) r
    (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

/-- The Lorentz norm of a function -/
def eLorentzNorm (f : α → ε) (p : ℝ≥0∞) (r : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then (if r = 0 then 0 else if r = ∞ then eLpNormEssSup f μ else ∞ * eLpNormEssSup f μ)
  else eLorentzNorm' f p r μ

variable {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α}

@[simp]
lemma eLorentzNorm_eq_eLorentzNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLorentzNorm f p r μ = eLorentzNorm' f p r μ := by
  unfold eLorentzNorm
  simp [hp_ne_zero, hp_ne_top]

@[simp]
lemma eLorentzNorm_zero (hp : p = 0) : eLorentzNorm f p r μ = 0 := by simp [eLorentzNorm, hp]

@[simp]
lemma eLorentzNorm_zero' (hr : r = 0) : eLorentzNorm f p r μ = 0 := by
  simp [hr, eLorentzNorm, eLorentzNorm']


--TODO: make this an iff, for p, r ≠ 0?
lemma eLorentzNorm_zero_of_ae_zero {f : α → ε'} (h : f =ᵐ[μ] 0) : eLorentzNorm f p r μ = 0 := by
  simp only [eLorentzNorm, ite_eq_left_iff]
  intro p_ne_zero
  rw [eLpNormEssSup_eq_zero_iff.mpr h]
  simp only [mul_zero, ite_self, ite_eq_left_iff]
  intro p_ne_top
  unfold eLorentzNorm'
  conv in ↑t * distribution f _ μ ^ p⁻¹.toReal =>
    rw [distribution_zero h,
    ENNReal.zero_rpow_of_pos (by simp only [ENNReal.toReal_inv, inv_pos]; apply ENNReal.toReal_pos p_ne_zero p_ne_top),
    mul_zero]
  simp


lemma eLorentzNorm'_mono {f g : α → ε'} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : eLorentzNorm' f p r μ ≤ eLorentzNorm' g p r μ := by
  unfold eLorentzNorm'
  gcongr
  apply eLpNorm_mono_enorm
  intro x
  simp only [ENNReal.toReal_inv, enorm_eq_self]
  gcongr
  exact h

lemma eLorentzNorm_mono {f g : α → ε'} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : eLorentzNorm f p r μ ≤ eLorentzNorm g p r μ := by
  unfold eLorentzNorm
  split_ifs
  · trivial
  · trivial
  · exact eLpNormEssSup_mono_enorm_ae h
  · gcongr
    exact eLpNormEssSup_mono_enorm_ae h
  · exact eLorentzNorm'_mono h

/-
/- Alternative definition. Not used at the moment. -/
lemma eLorentzNorm_eq {f : α → ε} {p : ℝ≥0∞} {r : ℝ≥0∞} {μ : Measure α} :
    eLorentzNorm f p r μ
      = eLpNorm (fun t ↦ t ^ p⁻¹.toReal * decreasing_rearrangement f μ t) r
          (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := sorry
-/

@[simp]
lemma eLorentzNorm_top_top {f : α → ε} : eLorentzNorm f ∞ ∞ μ = eLpNormEssSup f μ := by
  simp [eLorentzNorm]

lemma eLorentzNorm_eq_Lp {f : α → ε'} (hf : AEStronglyMeasurable f μ) :
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


--TODO: generalize this?
lemma aeMeasurable_withDensity_inv {f : ℝ≥0 → ℝ≥0∞} (hf : AEMeasurable f) :
    AEMeasurable f (volume.withDensity (fun t ↦ t⁻¹)) := by
  have : AEMeasurable f (volume.withDensity (fun t ↦ ENNReal.ofNNReal t⁻¹)) := by
    rw [aemeasurable_withDensity_ennreal_iff measurable_inv]
    apply AEMeasurable.mul _ hf
    exact measurable_inv.aemeasurable.coe_nnreal_ennreal
  convert this using 1
  rw [withDensity_eq_iff_of_sigmaFinite]
  · rw [Filter.eventuallyEq_iff_exists_mem]
    use {x | x ≠ 0}
    constructor
    · rw [mem_ae_iff]
      simp only [ne_eq, Set.compl_ne_eq_singleton]
      apply measure_singleton
    · intro x hx
      simp only [ne_eq, Set.mem_setOf_eq] at *
      exact Eq.symm (ENNReal.coe_inv hx)
  · apply Measurable.aemeasurable
    measurability
  · exact measurable_inv.aemeasurable.coe_nnreal_ennreal


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
      apply ENNReal.nonempty_open_inter_Ioi u_open hx x_in_u
    _ ≤ volume (f ⁻¹' s) := by
      apply measure_mono u_inter_subset
    _ ≤ volume {y | a < f y} := by
      apply measure_mono
      unfold s Set.preimage
      simp only [Set.mem_Ioi, Set.setOf_subset_setOf]
      intro y h
      exact h

/-
--TODO: move
theorem NNReal.ball_eq_Ioo (x r : ℝ≥0) : Metric.ball x r = Set.Ioo (x - r) (x + r) :=
  Set.ext fun y => by
    rw [Metric.mem_ball, dist_comm, NNReal.dist_eq, abs_sub_lt_iff, Set.mem_Ioo]
    constructor
    · intro h
      constructor
      · rw [NNReal.coe_sub]
-/

/-
lemma helper' {f : ℝ≥0 → ℝ≥0∞} (x : ℝ≥0)
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
      rw [Metric.isOpen_iff] at u_open
      rcases u_open _ x_in_u with ⟨ε, ε_pos, ball_subset⟩
      use x + ε.toNNReal / 2
      simp only [Set.mem_inter_iff, Set.mem_Ioi, lt_add_iff_pos_right, Nat.ofNat_pos,
        div_pos_iff_of_pos_right, Real.toNNReal_pos]
      use ?_, ε_pos
      apply ball_subset
      simp only [Metric.mem_ball]
      rw [NNReal.dist_eq]
      simp only [NNReal.coe_add, NNReal.coe_div, Real.coe_toNNReal', NNReal.coe_ofNat,
        add_sub_cancel_left]
      rw [abs_of_nonneg]
      · rw [div_lt_iff₀ zero_lt_two]
        simp [ε_pos]
      apply div_nonneg (by simp) zero_lt_two.le
    _ ≤ volume (f ⁻¹' s) := by
      apply measure_mono u_inter_subset
    _ ≤ volume {y | a < f y} := by
      apply measure_mono
      unfold s Set.preimage
      simp only [Set.mem_Ioi, Set.setOf_subset_setOf]
      intro y h
      exact h
-/

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


lemma eLorentzNorm_eq_wnorm (hp : p ≠ 0) : eLorentzNorm f p ∞ μ = wnorm f p μ := by
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
    /-
    have : {y : NNReal | a.toNNReal < (y * distribution f (↑y) μ ^ p.toReal⁻¹).toNNReal}
        = {y : NNReal | a < y * distribution f y μ ^ p.toReal⁻¹} := by
      sorry
    rw [← ne_eq] --, NNReal.volume_eq_volume_ennreal
    · rw [← this]
      apply helper'
      · apply ContinuousWithinAt.ennreal_mul continuous_id'.continuousWithinAt ((continuousWithinAt_distribution _).ennrpow_const _)
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
    -/

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
      · apply ContinuousWithinAt.ennreal_mul continuous_id'.continuousWithinAt ((continuousWithinAt_distribution _).ennrpow_const _)
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


lemma eLorentzNorm'_eq_integral_distribution_rpow [TopologicalSpace ε] :
    eLorentzNorm' f p 1 μ = p * ∫⁻ (t : ℝ≥0), distribution f t μ ^ p.toReal⁻¹ := by
  unfold eLorentzNorm'
  simp only [inv_one, ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.toReal_inv]
  congr
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  rw [lintegral_withDensity_eq_lintegral_mul₀' (by measurability)
    (by apply aeMeasurable_withDensity_inv; apply AEMeasurable.pow_const; apply AEStronglyMeasurable.enorm; apply
      aestronglyMeasurable_iff_aemeasurable.mpr; apply Measurable.aemeasurable; measurability)]
  simp only [enorm_eq_self, ENNReal.toReal_one, ENNReal.rpow_one, Pi.mul_apply, ne_eq, one_ne_zero,
    not_false_eq_true, div_self]
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi, lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only
  rw [← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · rw [ENNReal.coe_ne_zero]
    symm
    apply ne_of_lt
    rw [Real.toNNReal_pos]
    exact hx
  · exact ENNReal.coe_ne_top

lemma eLorentzNorm'_indicator {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {a : ε} (ha : ‖a‖ₑ ≠ ⊤)
  {s : Set α} (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) :
    eLorentzNorm' (s.indicator (Function.const α a)) p 1 μ = p * (‖a‖ₑ * μ s ^ p⁻¹.toReal) := by
  rw [eLorentzNorm'_eq_integral_distribution_rpow]
  congr
  simp_rw [distribution_indicator_const (ε := ε) (μ := μ) (s := s) (a := a)]
  unfold Set.indicator
  simp only [ENNReal.toReal_inv, ite_pow]
  --rw [ENNReal.zero_rpow_of_pos (by simp only [inv_pos]; exact ENNReal.toReal_pos p_ne_zero p_ne_top)]
  --rw [← Set.indicator_apply, lintegral_indicator_const measurableSet_Iio, mul_comm]
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



variable [TopologicalSpace ε] [ContinuousENorm ε]
/-- A function is in the Lorentz space L_{pr} if it is (strongly a.e.)-measurable and has finite Lorentz norm. -/
def MemLorentz (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ eLorentzNorm f p r μ < ∞

lemma MemLorentz_iff_MemLp {f : α → ε'} :
    MemLorentz f p p μ ↔ MemLp f p μ := by
  unfold MemLorentz MemLp
  constructor
  · intro h
    rwa [← eLorentzNorm_eq_Lp h.1]
  · intro h
    rwa [eLorentzNorm_eq_Lp h.1]

/-
lemma MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_top {α : Type*} {F : Type*} {m0 : MeasurableSpace α}
  {p q : ENNReal} {μ : Measure α} [NormedAddCommGroup F] {f : α → F} {C : ℝ}
  (hp : 0 < p) (p_le_q : p ≤ q) :
    eLpNorm f q μ ≤ eLpNorm f p μ ^ 1 * eLpNormEssSup f μ ^ 1 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm sorry sorry]
  /-calc _
    _ = 1 := by
      sorry
  -/
  sorry
-/

--instance ENNReal.normedAddCommGroup : NormedAddCommGroup ℝ≥0∞ := ⟨fun _r _y => rfl⟩

-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_of_MemLorentz_ge {ε : Type*} [ENorm ε] [TopologicalSpace ε] [ContinuousENorm ε]
  {f : α → ε} {p r₁ r₂ : ℝ≥0∞} {μ : Measure α}
  (r₁_pos : 0 < r₁) (r₁_le_r₂ : r₁ ≤ r₂) (hf : MemLorentz f p r₁ μ) :
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
      rw [eLpNorm_eq_lintegral_rpow_enorm r₁_pos.ne.symm r₁_top,
          lintegral_withDensity_eq_lintegral_mul₀ (by measurability) (measurable_mul_distribution_rpow.aestronglyMeasurable.enorm.pow_const r₁.toReal),
          lintegral_nnreal_eq_lintegral_toNNReal_Ioi] at norm_lt_top
      simp only [ENNReal.toReal_inv, enorm_eq_self, Pi.mul_apply, one_div] at norm_lt_top
      rw [r₂_top, ← eLorentzNorm_eq_eLorentzNorm' h₀ h₁, eLorentzNorm_eq_wnorm h₀, wnorm_ne_top h₁, wnorm']
      rw [iSup_lt_iff]

      have toReal_r₁_pos := ENNReal.toReal_pos r₁_pos.ne.symm r₁_top
      have : r₁ ^ r₁.toReal⁻¹ < ∞ := ENNReal.rpow_lt_top_of_nonneg (by simp) r₁_top
      have norm_lt_top' := ENNReal.mul_lt_top norm_lt_top this
      exists _, norm_lt_top'
      intro s
      by_cases s_pos : ¬ 0 < NNReal.toReal s
      · simp only [NNReal.coe_pos, not_lt, nonpos_iff_eq_zero] at s_pos
        rw [s_pos]
        simp
      push_neg at s_pos
      rw [← ENNReal.div_le_iff_le_mul (by left; apply (ENNReal.rpow_pos r₁_pos r₁_top).ne.symm) (by left; exact this.ne)] --TODO: improve this
      calc _
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (↑s / r₁ ^ r₁.toReal⁻¹) := by
          rw [mul_comm, mul_div_assoc]
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          rw [ENNReal.div_rpow_of_nonneg,
              ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne.symm, r₁_top⟩)]
          simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          congr 1
          · rw [ENNReal.rpow_mul, ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne.symm, r₁_top⟩)]
          --·
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, ENNReal.ofReal (x ^ (r₁.toReal - 1))) ^ r₁.toReal⁻¹:= by
          congr
          rw [lintegral_rpow_of_gt s_pos (by linarith), ENNReal.ofReal_div_of_pos (by simpa),
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
      rw [eLpNorm_eq_zero_iff measurable_mul_distribution_rpow.aestronglyMeasurable r₁_pos.ne.symm] at norm_zero
      rwa [eLpNorm_eq_zero_iff measurable_mul_distribution_rpow.aestronglyMeasurable (r₁_pos.trans_le r₁_le_r₂).ne.symm]

lemma MemLorentz.memLp {f : α → ε'} (hf : MemLorentz f p r μ) (h : r ∈ Set.Ioc 0 p) :
    MemLp f p μ := by
  rw [← MemLorentz_iff_MemLp]
  apply MemLorentz_of_MemLorentz_ge h.1 h.2 hf


end Lorentz


variable {α' ε₁ ε₂ : Type*} {m : MeasurableSpace α'} [TopologicalSpace ε₁] [ENorm ε₁]
    [TopologicalSpace ε₂] [ENorm ε₂] {f : α → ε} {f₁ : α → ε₁}

/-- An operator has Lorentz type `(p, r, q, s)` if it is bounded as a map
from `L^{q, s}` to `L^{p, r}`. `HasLorentzType T p r q s μ ν c` means that
`T` has Lorentz type `(p, r, q, s)` w.r.t. measures `μ`, `ν` and constant `c`. -/
def HasLorentzType (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧
    eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ


lemma hasStrongType_iff_hasLorentzType {ε₁ ε₂}
  [TopologicalSpace ε₁] [ENormedAddMonoid ε₁] [TopologicalSpace ε₂] [ENormedAddMonoid ε₂]
  {T : (α → ε₁) → (α' → ε₂)}
  {p q : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞} :
    HasStrongType T p q μ ν c ↔ HasLorentzType T p p q q μ ν c := by
  unfold HasStrongType HasLorentzType
  constructor
  · intro h f hf
    unfold MemLp MemLorentz at *
    rw [eLorentzNorm_eq_Lp hf.1] at *
    have := h f hf
    rwa [eLorentzNorm_eq_Lp this.1]
  · intro h f hf
    unfold MemLp MemLorentz at *
    rw [← eLorentzNorm_eq_Lp hf.1] at *
    have := h f hf
    rwa [← eLorentzNorm_eq_Lp this.1]

/-
-- TODO: find better name
lemma HasLorentzType_p_infty_qs {T : (α → ε₁) → (α' → ε₂)} {p q s : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞} (h : 0 < c) (hT : AEStronglyMeasurable (T f) ν) :
  HasLorentzType T p ∞ q s μ ν c := by
  intro f hf
-/

--TODO: what exactly should be the requirements on 𝕂? Actually, we only need a 1 here.
--TODO: This could be more general, it currently assumes T f ≥ 0
variable {β : Type*} [Zero β] [One β] --[NormedField 𝕂] --[ENormedAddMonoid 𝕂] [Field 𝕂] --[TopologicalSpace 𝕂]
  --[TopologicalSpace 𝕂] [ContinuousENorm 𝕂] [NormedField 𝕂]
  --[TopologicalSpace 𝕂] [ENormedAddMonoid 𝕂] --TODO: Actually, these last arguments should probably be infered

/-- Defines when an operator "has restricted weak type". This is an even weaker version
of `HasBoundedWeakType`. -/
def HasRestrictedWeakType (T : (α → β) → (α' → ε₂)) (p p' : ℝ≥0∞)
  (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal

lemma HasRestrictedWeakType.without_finiteness {ε₂} [TopologicalSpace ε₂] [ENormedAddMonoid ε₂]
    {T : (α → β) → (α' → ε₂)} {p p' : ℝ≥0∞}
    (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤) (p'_ne_zero : p' ≠ 0) (p'_ne_top : p' ≠ ⊤)
    {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (c_pos : 0 < c) (hT : HasRestrictedWeakType T p p' μ ν c)
    : --(h_zero : ∀ {f : α → β}, ) :
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (MeasurableSet G) →
    eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
      ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal := by
  intro F G hF hG
  have p_inv_pos : 0 < p⁻¹.toReal := by
    simp only [ENNReal.toReal_inv, inv_pos, ENNReal.toReal_pos p_ne_zero p_ne_top]
  have p'_inv_pos : 0 < p'⁻¹.toReal := by
    simp only [ENNReal.toReal_inv, inv_pos, ENNReal.toReal_pos p'_ne_zero p'_ne_top]
  by_cases hFG : μ F < ∞ ∧ ν G < ∞
  · exact (hT F G hF hFG.1 hG hFG.2).2
  · rw [not_and_or] at hFG
    rcases hFG with hF | hG
    · by_cases G_zero : ν G = 0
      · rw [G_zero, ENNReal.zero_rpow_of_pos p'_inv_pos]
        simp only [ENNReal.toReal_inv, mul_zero, nonpos_iff_eq_zero]
        convert eLpNorm_measure_zero
        simpa
      simp only [not_lt, top_le_iff] at hF
      rw [hF]
      convert le_top
      rw [ENNReal.mul_eq_top]
      right
      constructor
      · rw [ENNReal.top_rpow_of_pos p_inv_pos, ENNReal.mul_top (by simp [c_pos.ne.symm])]
      simp only [ENNReal.toReal_inv, ne_eq, ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', not_or,
        not_and, not_lt, ENNReal.toReal_nonneg, implies_true, and_true]
      intro h
      exfalso
      exact G_zero h
    · by_cases F_zero : μ F = 0
      · rw [F_zero, ENNReal.zero_rpow_of_pos p_inv_pos]
        simp only [mul_zero, ENNReal.toReal_inv, zero_mul, nonpos_iff_eq_zero]
        apply eLpNorm_eq_zero_of_ae_zero
        sorry --TODO: need additional assumption for this!
      simp only [not_lt, top_le_iff] at hG
      rw [hG]
      convert le_top
      rw [ENNReal.mul_eq_top]
      left
      constructor
      · simp only [ENNReal.toReal_inv, ne_eq, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_pos,
        inv_neg'', not_or, not_and, not_lt, ENNReal.toReal_nonneg, implies_true, and_true]
        use (by simp [c_pos.ne.symm])
        intro h
        exfalso
        exact F_zero h
      rw [ENNReal.top_rpow_of_pos p'_inv_pos]


--TODO: Could probably weaken assumption to (h : ∀ᶠ (x : β) in f, u x ≤ v x)
theorem Filter.mono_limsup {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u v : β → α} (h : ∀ (x : β), u x ≤ v x) : Filter.limsup u f ≤ Filter.limsup v f := by
  refine Filter.limsup_le_limsup ?_
  apply Filter.Eventually.of_forall h

--TODO: move?
theorem Filter.limsup_le_of_le' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u : β → α} {a : α} (h : ∀ᶠ (n : β) in f, u n ≤ a) :
  Filter.limsup u f ≤ a := sInf_le h

--TODO: move?
theorem ENNReal.rpow_add_rpow_le_add' {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  calc
    _ = ((a ^ p + b ^ p) ^ (1 / p)) ^ p := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      linarith
    _ ≤ (a + b) ^ p := by
      gcongr
      apply ENNReal.rpow_add_rpow_le_add _ _ hp1



--TODO: move, generalize?, probably need more assumptions
lemma setLIntegral_Ici {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} :
    ∫⁻ (t : ℝ≥0) in Set.Ici a, f t = ∫⁻ (t : ℝ≥0), f (t + a) := by
  --TODO: do something similar as in lintegral_add_right_Ioi
  sorry

--variable [ENorm ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

--TODO: move
theorem ENNReal.limsup_mul_const_of_ne_top {α : Type*} {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    Filter.limsup (fun x ↦ u x * a) f = Filter.limsup u f * a := by
  simp_rw [mul_comm]
  apply ENNReal.limsup_const_mul_of_ne_top ha_top

/-
def WeaklyContinuous [TopologicalSpace ε] (T : (α → ε) → (α' → ε')) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {f : α → ε} {fs : ℕ → SimpleFunc α ε}
  (hfs : ∀ (x : α), Filter.Tendsto (fun (n : ℕ) => (fs n) x) Filter.atTop (nhds (f x))) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop
-/


def WeaklyContinuous [TopologicalSpace ε] [ENorm ε] [ENorm ε'] [SupSet ε] [Preorder ε] (T : (α → ε) → (α' → ε')) (p : ℝ≥0∞) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {fs : ℕ → SimpleFunc α ε} (_ : Monotone fs),
  let f := fun x ↦ ⨆ n, (fs n) x;
  ∀ (_ : MemLorentz f p 1 μ) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T ⇑(fs n)) 1 (ν.restrict G)) Filter.atTop
--TODO: Show that the Carleson operator is weakly continuous in this sense via Fatou's lemma

--lemma carlesonOperator_weaklyContinuous : WeaklyContinuous carlesonOperator

theorem HasRestrictedWeakType.hasLorentzType_helper [Nonempty α] [TopologicalSpace ε'] [ENormedSpace ε']
  {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (c_pos : 0 < c) {T : (α → ℝ≥0) → α' → ε'}
  (hT : HasRestrictedWeakType T p p' μ ν c) --(T_zero : eLpNorm (T 0) 1 ν = 0)
  (hpp' : p.HolderConjugate p')
  (weakly_cont_T : WeaklyContinuous T p μ ν)
  {G : Set α'} (hG : MeasurableSet G) (hG' : ν G < ⊤)
  (T_subadditive : ∀ (f g : α → ℝ≥0), (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    eLpNorm (T (f + g)) 1 (ν.restrict G) ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G))
  (T_submult : ∀ (f : α → ℝ≥0) (a : ℝ≥0), eLpNorm (T (a • f)) 1 (ν.restrict G) ≤ eLpNorm (a • T f) 1 (ν.restrict G))
  {f : α → ℝ≥0} (hf : Measurable f) (hf' : MemLorentz f p 1 μ) :
      eLpNorm (T f) 1 (ν.restrict G) ≤ (c / p) * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal := by
  by_cases p_ne_top : p = ∞
  · sorry --TODO: check whether this works or whether it should be excluded
  by_cases p'_ne_top : p' = ∞
  · sorry --TODO: check whether this works or whether it should be excluded
  have hp : 1 ≤ p := hpp'.one_le --use: should follow from hpp'
  have p_ne_zero : p ≠ 0 := hpp'.ne_zero --TODO: easy
  rw [eLorentzNorm_eq_eLorentzNorm' p_ne_zero p_ne_top] --TODO: assumptions on p
  revert f
  apply @Measurable.nnreal_induction _ m0
  · intro f
    induction f using SimpleFunc.induction''
    · rename_i a s hs
      /-
      by_cases a_ne_top : a = ⊤
      · sorry --TODO: add new lemma what eLorentzNorm does with indicator functions; could also be used for the other part
        --alternative: use that f is bounded in the eLorentzNorm
      -/
      simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
        SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
      have : s.indicator (Function.const α a) = a • (s.indicator (fun _ ↦ 1)) := by
        ext x
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Set.indicator_const_mul]
        congr
        simp
      intro hf'
      calc _
        _ = eLpNorm (T (a • (s.indicator (fun _ ↦ 1)))) 1 (ν.restrict G) := by
          congr 1
          ext x
          congr
        _ ≤ ‖a‖ₑ * eLpNorm (T ((s.indicator (fun _ ↦ 1)))) 1 (ν.restrict G) := by
          rw [← eLpNorm_const_smul']
          --apply eLpNorm_mono_enorm_ae
          apply T_submult
        _ ≤ ‖a‖ₑ * (c * (μ s) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal) := by
          gcongr
          apply hT.without_finiteness p_ne_zero p_ne_top hpp'.symm.ne_zero p'_ne_top c_pos s G hs hG
        _ = c * (‖a‖ₑ * μ s ^ p⁻¹.toReal) * (ν G) ^ p'⁻¹.toReal := by ring
        _ = (c / p) * eLorentzNorm' (s.indicator (Function.const α a)) p 1 μ * ν G ^ p'⁻¹.toReal := by
          rw [eLorentzNorm'_indicator (by simp) p_ne_zero p_ne_top]
          rw [← mul_assoc (c / p), ENNReal.div_mul_cancel p_ne_zero p_ne_top]
    · rename_i f a s hs hfs hf hg
      /-
      by_cases a_ne_top : a = ⊤
      · sorry --TODO: add new lemma what eLorentzNorm does with indicator functions; could also be used for the other part
      --have hf' : MemLorentz f p 1 μ := by sorry --TODO: get this from hfg' and measurability of f and g
      --have hg' : MemLorentz g p 1 μ := by sorry
      -/
      rw [SimpleFunc.coe_add]
      set g := SimpleFunc.piecewise s hs (SimpleFunc.const α a) (SimpleFunc.const α 0) with g_def
      intro hfg'
      have hf' : MemLorentz f p 1 μ := by sorry --TODO: get this from hfg' and measurability of f and g
      have hg' : MemLorentz g p 1 μ := by sorry --TODO: use that g is an indicator function with finite value
      calc _
        _ ≤ eLpNorm (T f) 1 (ν.restrict G) + eLpNorm (T g) 1 (ν.restrict G) := by
          apply T_subadditive f g hf' hg'
        _ ≤ c / p * eLorentzNorm' f p 1 μ * ν G ^ p'⁻¹.toReal + c / p *  eLorentzNorm' g p 1 μ * ν G ^ p'⁻¹.toReal := by
          gcongr
          · exact hf hf'
          · exact hg hg'
        _ = c / p * eLorentzNorm' (f + g) p 1 μ * ν G ^ p'⁻¹.toReal := by
          rw [← add_mul, ← mul_add]
          congr
          rw [eLorentzNorm'_eq_integral_distribution_rpow,
            eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_eq_integral_distribution_rpow]
          rw [← mul_add] --TODO: measurability --← lintegral_add_left sorry
          congr 1
          rw [SimpleFunc.coe_add, g_def]
          simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise,
            SimpleFunc.coe_const, SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
          symm
          calc _
            _ = ∫⁻ (t : ℝ≥0), (if t < a then μ s else distribution f (t - a) μ) ^ p.toReal⁻¹ := by
              congr with t
              rw [distribution_indicator_add_of_support_subset_nnreal (μ := μ) hfs]
              simp only [ENNReal.coe_lt_coe]
            _ = ∫⁻ (t : ℝ≥0), if t < a then μ s ^ p.toReal⁻¹ else distribution f (t - a) μ ^ p.toReal⁻¹ := by
              simp only [ite_pow]
            _ = ∫⁻ (t : ℝ≥0), (Set.Iio a).indicator (fun _ ↦ μ s ^ p.toReal⁻¹) t
                  + (Set.Ici a).indicator (fun t ↦ distribution f (t - a) μ ^ p.toReal⁻¹) t := by
              congr with t
              rw [← Set.compl_Iio, ← Pi.add_apply, Set.indicator_add_compl_eq_piecewise]
              unfold Set.piecewise
              simp
            _ = a * μ s ^ p.toReal⁻¹ + ∫⁻ (t : ℝ≥0), distribution f t μ ^ p.toReal⁻¹ := by
              rw [lintegral_add_left (by measurability)]
              congr 1
              · rw [lintegral_indicator_const measurableSet_Iio, NNReal.volume_Iio, mul_comm]
              · rw [lintegral_indicator measurableSet_Ici, setLIntegral_Ici]
                simp
          rw [add_comm]
          congr
          apply (ENNReal.mul_right_inj p_ne_zero p_ne_top).mp
          rw [← eLorentzNorm'_eq_integral_distribution_rpow, eLorentzNorm'_indicator (by simp) p_ne_zero p_ne_top]
          simp
  · intro f hf h hf'
    rw [← SimpleFunc.iSup_nnapprox hf] at hf'
    --have
    calc _
      _ ≤ Filter.limsup (fun n ↦ eLpNorm (T (SimpleFunc.nnapprox f n)) 1 (ν.restrict G)) Filter.atTop := by
        nth_rw 1 [← SimpleFunc.iSup_nnapprox hf]
        apply weakly_cont_T SimpleFunc.monotone_nnapprox hf' G
      _ ≤ Filter.limsup (fun n ↦ (c / p) * eLorentzNorm' (SimpleFunc.nnapprox f n) p 1 μ * ν G ^ p'⁻¹.toReal) Filter.atTop := by
        apply Filter.mono_limsup
        intro n
        apply h n _
        sorry --use : all of these functions are bounded (by a constant / by f and this is MemLorentz)
      _ ≤ (c / p) * eLorentzNorm' f p 1 μ * ν G ^ p'⁻¹.toReal := by
        simp_rw [mul_assoc]
        rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.div_ne_top (by simp) p_ne_zero)]
        gcongr
        --simp_rw [mul_comm]
        rw [ENNReal.limsup_mul_const_of_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) hG'.ne)]
        gcongr
        apply Filter.limsup_le_of_le'
        apply Filter.Eventually.of_forall
        intro n
        apply eLorentzNorm'_mono
        apply Filter.Eventually.of_forall
        simp only [enorm_NNReal, ENNReal.coe_le_coe]
        intro x
        exact SimpleFunc.approx_le hf bot_eq_zero'
    /-
    intro fs monotone_fs hfs hf
    set f := (fun x ↦ ⨆ n, (fs n) x)
    calc _
      _ ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop := by
        apply weakly_cont_T monotone_fs hf
      _ ≤ Filter.limsup (fun n ↦ (c / p) * eLorentzNorm' (fs n) p 1 μ * ν G ^ p'⁻¹.toReal) Filter.atTop := by
        apply Filter.mono_limsup
        intro n
        apply hfs n _
        sorry --use : every (fs n) is bounded by f and this is MemLorentz
      _ ≤ (c / p) * eLorentzNorm' f p 1 μ * ν G ^ p'⁻¹.toReal := by
        simp_rw [mul_assoc]
        rw [ENNReal.limsup_const_mul_of_ne_top sorry] --use : c_ne_top
        gcongr
        --simp_rw [mul_comm]
        rw [ENNReal.limsup_mul_const_of_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) hG'.ne)]
        gcongr
        sorry --use: monotonicity of fs / def. of f
    -/

theorem RCLike.norm_I {K : Type u_1} [RCLike K] : ‖(RCLike.I : K)‖ = if RCLike.I ≠ (0 : K) then 1 else 0 := by
  split_ifs with h
  · apply RCLike.norm_I_of_ne_zero h
  · push_neg at h
    simpa

lemma HasRestrictedWeakType.hasLorentzType [TopologicalSpace α] [Nonempty α] {𝕂 : Type*} /- [MeasurableSpace ε'] [BorelSpace ε'] -/
  --[ENormedAddMonoid ε']
  [RCLike 𝕂] [TopologicalSpace ε'] [ENormedSpace ε']
  {T : (α → 𝕂) → (α' → ε')} {p p' : ℝ≥0∞}
  {μ : Measure α} [IsLocallyFiniteMeasure μ] {ν : Measure α'} {c : ℝ≥0} (c_pos : 0 < c)
  (hT : HasRestrictedWeakType T p p' μ ν c) (hpp' : p.HolderConjugate p')
  (T_meas : ∀ {f : α → 𝕂}, (MemLorentz f p 1 μ) → AEStronglyMeasurable (T f) ν)
  (T_subadd : ∀ (f g : α → 𝕂) (x : α'), (MemLorentz f p 1 μ) → (MemLorentz g p 1 μ) →
    --‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    ‖T (f + g) x‖ₑ ≤ ‖T f x + T g x‖ₑ)
  (T_submul : ∀ (a : 𝕂) (f : α → 𝕂) (x : α'), ‖T (a • f) x‖ₑ ≤ ‖a‖ₑ • ‖T f x‖ₑ)
  (weakly_cont_T : ∀ {f : α → 𝕂} {fs : ℕ → α → 𝕂}
                     (f_locInt : LocallyIntegrable f μ)
                     (hF_meas : ∀ (n : ℕ), AEStronglyMeasurable (fs n) μ)
                     (h_norm_monotone : ∀ (a : α), Monotone (fun n ↦ ‖fs n a‖))
                     (h_lim : ∀ (a : α), Filter.Tendsto (fun (n : ℕ) => fs n a) Filter.atTop (nhds (f a)))
                     (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop)

    :

  --(weakly_cont_T : WeaklyContinuous T μ ν) : --TODO: correct assumption with modified T
    --TODO: might have to adjust the constant
    HasLorentzType T p 1 p ∞ μ ν (4 * c / p) := by
  intro f hf
  --have hp : 1 ≤ p := by sorry --use: should follow from hpp'
  have claim : ∀ (G : Set α'), (MeasurableSet G) → (ν G < ∞) → eLpNorm (T f) 1 (ν.restrict G)
    ≤ (4 * c / p) * eLorentzNorm f p 1 μ * (ν G) ^ p'⁻¹.toReal := by
      intro G measurable_G G_finite
      rcases hf with ⟨aemeasurable_f, hf⟩
      revert f --TODO: go on here
      apply wlog_stronglymeasurable
      · intro f g stronglyMeasurable_f hfg hf hg
        have : eLorentzNorm f p 1 μ < ⊤ := by
          sorry --use: hg
        have hf := hf this
        sorry --use: hf
      intro g stronglyMeasurable_g hg

      --TODO: decompose g into 4 nonnegative parts with constant coefficients
      set g₁ := fun x ↦ Real.toNNReal (RCLike.re (g x))
      set g₂ := fun x ↦ Real.toNNReal (- RCLike.re (g x))
      set g₃ := fun x ↦ Real.toNNReal (RCLike.im (g x))
      set g₄ := fun x ↦ Real.toNNReal (- RCLike.im (g x))
      have g_decomposition : g = (1 : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₁)
                                + (-1 : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₂)
                                + (RCLike.I : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₃)
                                + (-RCLike.I : 𝕂) • (algebraMap ℝ 𝕂 ∘ NNReal.toReal ∘ g₄) := by
        unfold g₁ g₂ g₃ g₄
        ext x
        simp only [one_smul, neg_smul, Pi.add_apply, Function.comp_apply, Real.coe_toNNReal',
          Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
        rw [algebraMap]
        sorry --TODO: simple algebra
      set T' := T ∘ (fun f ↦ (@RCLike.ofReal 𝕂 _) ∘ NNReal.toReal ∘ f)
      --TODO: use properties for T to get those for T'
      have hT' : HasRestrictedWeakType T' p p' μ ν c := sorry
      have weaklyCont_T' : WeaklyContinuous T' p μ ν := by
        unfold WeaklyContinuous T'
        intro fs hfs f hf G
        simp only [Function.comp_apply]
        apply weakly_cont_T
        · --TODO: get this from (hf : MemLorentz f p 1 μ)
          --TODO: add lemmas for locallyIntegrable
          --unfold LocallyIntegrable IntegrableAtFilter IntegrableOn

          --have : LocallyIntegrable f μ :=
          --apply (hf.memLp _).locallyIntegrable
          sorry
        · --apply Filter.Eventually.of_forall
          intro n
          apply Measurable.aestronglyMeasurable
          apply RCLike.measurable_ofReal.comp
          apply measurable_coe_nnreal_real.comp (SimpleFunc.measurable (fs n))
        · intro x
          simp only [Function.comp_apply, norm_algebraMap', Real.norm_eq_abs, NNReal.abs_eq]
          exact fun ⦃a b⦄ a_1 ↦ hfs a_1 x
        · --apply Filter.Eventually.of_forall
          intro x
          --apply Filter.Tendsto.algebraMap
          --apply Filter.Tendsto.comp _
          --apply Filter.Tendsto.comp _
          sorry --TODO: use that f is the supremum; maybe need to add a condition implying that
          -- the (fs n) are really converging to f


      have T'_subadd : ∀ (f g : α → ℝ≥0),
        MemLorentz f p 1 μ →
          MemLorentz g p 1 μ →
            eLpNorm (T' (f + g)) 1 (ν.restrict G)
              ≤ eLpNorm (T' f) 1 (ν.restrict G) + eLpNorm (T' g) 1 (ν.restrict G) := by
        intro f g hf hg
        unfold T'
        simp only [Function.comp_apply]
        have hf' : MemLorentz ((@RCLike.ofReal 𝕂 _) ∘ NNReal.toReal ∘ f) p 1 μ := by
          constructor
          · apply RCLike.measurable_ofReal.aestronglyMeasurable.comp_aemeasurable
            refine aestronglyMeasurable_iff_aemeasurable.mp ?_
            apply measurable_coe_nnreal_real.aestronglyMeasurable.comp_aemeasurable hf.1.aemeasurable
          · sorry --TODO: get this from hf, maybe write additional lemma
        have hg' : MemLorentz ((@RCLike.ofReal 𝕂 _) ∘ NNReal.toReal ∘ g) p 1 μ := by
          constructor
          · apply RCLike.measurable_ofReal.aestronglyMeasurable.comp_aemeasurable
            refine aestronglyMeasurable_iff_aemeasurable.mp ?_
            apply measurable_coe_nnreal_real.aestronglyMeasurable.comp_aemeasurable hg.1.aemeasurable
          · sorry --TODO: get this from hf, maybe write additional lemma
        apply le_trans _ (eLpNorm_add_le _ _ le_rfl)
        · apply eLpNorm_mono_enorm
          intro x
          simp only [Pi.add_apply]
          apply le_of_eq_of_le _ (T_subadd _ _ _ hf' hg')
          congr with x
          simp
        · apply AEStronglyMeasurable.restrict
          apply T_meas hf'
        · apply AEStronglyMeasurable.restrict
          apply T_meas hg'
      have T'_submul : ∀ (f : α → ℝ≥0) (a : ℝ≥0), eLpNorm (T' (a • f)) 1 (ν.restrict G)
          ≤ eLpNorm (a • T' f) 1 (ν.restrict G) := by
        intro f a
        apply eLpNorm_mono_enorm
        intro x
        unfold T'
        simp only [Function.comp_apply, Pi.smul_apply, enorm_smul_eq_smul]
        have : a • ‖T (RCLike.ofReal ∘ NNReal.toReal ∘ f) x‖ₑ
          = ‖a‖ₑ • ‖T (RCLike.ofReal ∘ NNReal.toReal ∘ f) x‖ₑ := by
          congr
        rw [this]
        convert T_submul (NNReal.toReal a) _ x
        · ext x
          simp
        congr
        simp
      have helper : ∀ {f : α → ℝ≥0} (hf : Measurable f) (hf' : MemLorentz f p 1 μ),
          eLpNorm (T' f) 1 (ν.restrict G) ≤ (c / p) * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal := by
        intro f hf hf'
        apply HasRestrictedWeakType.hasLorentzType_helper c_pos hT' hpp' weaklyCont_T' measurable_G G_finite
          T'_subadd T'_submul hf hf'

      calc _
        _ ≤ eLpNorm (enorm ∘ T' g₁ + enorm ∘ T' g₂ + enorm ∘ T' g₃ + enorm ∘ T' g₄) 1 (ν.restrict G) := by
          have T_subadd' : ∀ (f₁ f₂ f₃ f₄ : α → 𝕂) (x : α'),
            (MemLorentz f₁ p 1 μ) → (MemLorentz f₂ p 1 μ) → (MemLorentz f₃ p 1 μ) → (MemLorentz f₄ p 1 μ) →
              ‖T (f₁ + f₂ + f₃ + f₄) x‖ₑ ≤ ‖T f₁ x‖ₑ + ‖T f₂ x‖ₑ + ‖T f₃ x‖ₑ + ‖T f₄ x‖ₑ := by
            sorry --use: iterate T_subadd
          apply eLpNorm_mono_enorm
          intro x
          rw [g_decomposition]
          simp only [Pi.add_apply, Function.comp_apply, enorm_eq_self]
          apply (T_subadd' _ _ _ _ _ _ _ _ _).trans
          · gcongr
            · apply (T_submul _ _ _).trans
              unfold T'
              simp
            · apply (T_submul _ _ _).trans
              unfold T'
              simp
            · apply (T_submul _ _ _).trans
              rw [← ofReal_norm_eq_enorm]
              rw [RCLike.norm_I]
              unfold T'
              split_ifs <;> simp
            · apply (T_submul _ _ _).trans
              rw [← ofReal_norm_eq_enorm, norm_neg]
              rw [RCLike.norm_I]
              unfold T'
              split_ifs <;> simp
          · sorry --TODO: Do these later when sure that this is the right condition in T_subadd
          · sorry
          · sorry
          · sorry
        _ ≤ eLpNorm (T' g₁) 1 (ν.restrict G) + eLpNorm (T' g₂) 1 (ν.restrict G)
          + eLpNorm (T' g₃) 1 (ν.restrict G) + eLpNorm (T' g₄) 1 (ν.restrict G) := by
          apply (eLpNorm_add_le sorry sorry le_rfl).trans
          gcongr
          apply (eLpNorm_add_le sorry sorry le_rfl).trans
          gcongr
          apply (eLpNorm_add_le sorry sorry le_rfl).trans
          gcongr
          · rw [Function.comp_def, eLpNorm_enorm]
          · rw [Function.comp_def, eLpNorm_enorm]
          · rw [Function.comp_def, eLpNorm_enorm]
          · rw [Function.comp_def, eLpNorm_enorm]
        _ ≤ (c / p) * eLorentzNorm g₁ p 1 μ * ν G ^ p'⁻¹.toReal
           +(c / p) * eLorentzNorm g₂ p 1 μ * ν G ^ p'⁻¹.toReal
           +(c / p) * eLorentzNorm g₃ p 1 μ * ν G ^ p'⁻¹.toReal
           +(c / p) * eLorentzNorm g₄ p 1 μ * ν G ^ p'⁻¹.toReal := by
          gcongr
          · apply helper
            · apply measurable_real_toNNReal.comp (RCLike.measurable_re.comp stronglyMeasurable_g.measurable)
            · sorry
          · sorry --TODO: analogous to the first one, fill in once everything is finalized there
          · sorry
          · sorry

        _ ≤ (4 * c / p) * eLorentzNorm g p 1 μ * ν G ^ p'⁻¹.toReal := by
          have : (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 := by ring
          rw [mul_div_assoc 4, mul_assoc 4, mul_assoc 4, this, add_mul, add_mul, add_mul]
          simp only [one_mul]
          unfold g₁ g₂ g₃ g₄
          gcongr
          · apply eLorentzNorm_mono
            apply Filter.Eventually.of_forall
            intro x
            simp only [enorm_NNReal, ENNReal.coe_le_coe]
            rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm]
            apply RCLike.re_le_norm
          · sorry --TODO: analogous to the first case
          · sorry
          · sorry
  -- Apply claim to a special G
  --let G := {x | ‖T x‖ₑ > }
  --constructor
  use T_meas hf
  by_cases h : p = ⊤
  · rw [h]
    rw [eLorentzNorm_eq_Lp sorry]
    by_cases h' : f =ᵐ[μ] 0
    · sorry
    · sorry
  · rw [eLorentzNorm_eq_wnorm hpp'.ne_zero, wnorm_ne_top h]
    unfold wnorm'
    apply iSup_le
    intro l
    unfold distribution
    set G := {x | ↑l < ‖T f x‖ₑ}
--      set G'
    --rw [div_le_div__right]
    calc _
      _ = ↑l * ν G / ν G ^ p'⁻¹.toReal := by
        rw [mul_div_assoc]
        congr
        rw [ENNReal.holderConjugate_iff] at hpp'
        rw [ENNReal.eq_div_iff sorry sorry, ← ENNReal.rpow_add, ← ENNReal.toReal_inv, ← ENNReal.toReal_add, add_comm, hpp']
        · simp only [ENNReal.toReal_one, ENNReal.rpow_one]
        · rw [ne_eq, ENNReal.inv_eq_top]
          sorry
        · rw [ne_eq, ENNReal.inv_eq_top]
          sorry
        · sorry
        · sorry
      _ ≤ (∫⁻ (x : α') in G, ‖T f x‖ₑ ∂ν) / ν G ^ p'⁻¹.toReal := by
        gcongr
        --rw [setLIntegral]
        rw [← Measure.restrict_eq_self _ (subset_refl G)]
        calc _
          _ ≤ ↑l * (ν.restrict G) {x | ↑l ≤ ‖T f x‖ₑ} := by
            gcongr
            intro x hx
            unfold G at hx
            rw [Set.mem_setOf_eq] at hx ⊢; exact hx.le
        apply mul_meas_ge_le_lintegral₀
        sorry
      _ = eLpNorm (T f) 1 (ν.restrict G) / ν G ^ p'⁻¹.toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ((4 * c / p) * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal) / ν G ^ p'⁻¹.toReal := by
        gcongr
        apply claim
        · sorry
        · sorry
      _ ≤ (4 * c / p) * eLorentzNorm f p 1 μ * 1 := by
        rw [mul_div_assoc]
        gcongr
        exact ENNReal.div_self_le_one
      _ = (4 * c / p) * eLorentzNorm f p 1 μ := by ring

--end Lorentz

end MeasureTheory
