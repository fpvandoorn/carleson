import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
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

--TODO: Weaken to only assume the ineq ae
lemma eLorentzNorm_mono {f g : α → ε'} (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : eLorentzNorm f p r μ ≤ eLorentzNorm g p r μ := by
  unfold eLorentzNorm
  split_ifs
  · trivial
  · trivial
  · exact eLpNormEssSup_mono_enorm_ae h
  · gcongr
    exact eLpNormEssSup_mono_enorm_ae h
  · unfold eLorentzNorm'
    gcongr
    apply eLpNorm_mono_enorm
    intro x
    simp only [ENNReal.toReal_inv, enorm_eq_self]
    gcongr
    exact h

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

lemma eLorentzNorm_eq_wnorm (hp : p ≠ 0) : eLorentzNorm f p ∞ μ = wnorm f p μ := by
  by_cases p_eq_top : p = ∞
  · rw [p_eq_top]
    simp
  rw [eLorentzNorm_eq_eLorentzNorm' hp p_eq_top, wnorm_ne_top p_eq_top]
  unfold eLorentzNorm' wnorm'
  simp only [ENNReal.inv_top, ENNReal.toReal_zero, ENNReal.rpow_zero, ENNReal.toReal_inv,
    eLpNorm_exponent_top, one_mul]
  unfold eLpNormEssSup
  --rw [Continuous.essSup]
  simp only [enorm_eq_self]
  --TODO: somehow use continuity properties of the distribution function here
  sorry

variable [TopologicalSpace ε] [ContinuousENorm ε]
/-- A function is in the Lorentz space L_{pr} if it is (strongly a.e.)-measurable and has finite Lorentz norm. -/
def MemLorentz (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ eLorentzNorm f p r μ < ∞

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

--TODO: generalize this?
lemma aeMeasurable_withDensity_inv {f : ℝ≥0 → ℝ≥0∞} (hf : AEMeasurable f) :
    AEMeasurable f (volume.withDensity (fun t ↦ t⁻¹)) := by
  have : AEMeasurable f (volume.withDensity (fun t ↦ ENNReal.ofNNReal t⁻¹)) := by
    rw [aemeasurable_withDensity_ennreal_iff measurable_inv]
    apply AEMeasurable.mul _ hf
    exact measurable_inv.aemeasurable.coe_nnreal_ennreal
  convert this using 1
  have : SigmaFinite (@volume ℝ≥0 NNReal.MeasureSpace : Measure ℝ≥0) := sorry --TODO: should be infered
  have : NoAtoms (@volume ℝ≥0 NNReal.MeasureSpace : Measure ℝ≥0) := sorry --TODO: should be infered
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


-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_of_MemLorentz_ge {ε : Type*} [ENorm ε] [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p r₁ r₂ : ℝ≥0∞} {μ : Measure α}
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
          exact lintegral_mono_set Set.Ioo_subset_Ioi_self
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




variable {α' ε₁ ε₂ : Type*} {m : MeasurableSpace α'} [TopologicalSpace ε₁] [ENorm ε₁]
    [TopologicalSpace ε₂] [ENorm ε₂] {f : α → ε} {f₁ : α → ε₁}

/-- An operator has Lorentz type `(p, r, q, s)` if it is bounded as a map
from `L^{q, s}` to `L^{p, r}`. `HasLorentzType T p r q s μ ν c` means that
`T` has Lorentz type `(p, r, q, s)` w.r.t. measures `μ`, `ν` and constant `c`. -/
def HasLorentzType (T : (α → ε₁) → (α' → ε₂))
    (p r q s : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, MemLorentz f p r μ → AEStronglyMeasurable (T f) ν ∧
    eLorentzNorm (T f) q s ν ≤ c * eLorentzNorm f p r μ

/-
-- TODO: find better name
lemma HasLorentzType_p_infty_qs {T : (α → ε₁) → (α' → ε₂)} {p q s : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞} (h : 0 < c) (hT : AEStronglyMeasurable (T f) ν) :
  HasLorentzType T p ∞ q s μ ν c := by
  intro f hf
-/

--TODO: what exactly should be the requirements on 𝕂? Actually, we only need a 1 here.
--TODO: This could be more general, it currently assumes T f ≥ 0
variable {𝕂 : Type*} [TopologicalSpace 𝕂] [ENormedAddMonoid 𝕂] [Field 𝕂]
  --[TopologicalSpace 𝕂] [ContinuousENorm 𝕂] [NormedField 𝕂]
  --[TopologicalSpace 𝕂] [ENormedAddMonoid 𝕂] --TODO: Actually, these last arguments should probably be infered

/-- Defines when an operator "has restricted weak type". This is an even weaker version
of `HasBoundedWeakType`. -/
def HasRestrictedWeakType (T : (α → 𝕂) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ (F : Set α) (G : Set α'), (MeasurableSet F) → (μ F < ∞) → (MeasurableSet G) → (ν G < ∞) →
    AEStronglyMeasurable (T (F.indicator (fun _ ↦ 1))) ν ∧
      eLpNorm (T (F.indicator (fun _ ↦ 1))) 1 (ν.restrict G)
        ≤ c * (μ F) ^ p⁻¹.toReal * (ν G) ^ p'⁻¹.toReal

--TODO: Could probably weaken assumption to (h : ∀ᶠ (x : β) in f, u x ≤ v x)
theorem Filter.mono_limsup {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u v : β → α} (h : ∀ (x : β), u x ≤ v x) : Filter.limsup u f ≤ Filter.limsup v f := by
  apply sInf_le_sInf
  intro a ha
  apply ha.mono
  intro x hx
  exact Preorder.le_trans (u x) (v x) a (h x) hx

theorem Filter.limsup_le_of_le' {α : Type*} {β : Type*} [CompleteLattice α] {f : Filter β}
    {u : β → α} {a : α} (h : ∀ᶠ (n : β) in f, u n ≤ a) :
  Filter.limsup u f ≤ a := sInf_le h

theorem MeasureTheory.HasRestrictedWeakType.hasLorentzType_helper
  {T : (α → 𝕂) → α' → ε'} {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞}
  (hT : HasRestrictedWeakType T p p' μ ν c) (hpp' : p.HolderConjugate p') (f : SimpleFunc α 𝕂) --(hf : MemLorentz f p 1 μ)
  (G : Set α') (hG : MeasurableSet G) (hG' : ν G < ⊤) :
    eLpNorm (T f) 1 (ν.restrict G) ≤ c * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal := by
  sorry

def WeaklyContinuous (T : (α → 𝕂) → (α' → ε')) (μ : Measure α) (ν : Measure α') : Prop :=
  ∀ {f : α → 𝕂} {fs : ℕ → SimpleFunc α 𝕂}
  (hfs : ∀ (x : α), Filter.Tendsto (fun (n : ℕ) => (fs n) x) Filter.atTop (nhds (f x))) (G : Set α'),
    eLpNorm (T f) 1 (ν.restrict G) ≤ Filter.limsup (fun n ↦ eLpNorm (T (fs n)) 1 (ν.restrict G)) Filter.atTop

--TODO : generalize?
--TODO : probably could even have a stronger version where the gs are pointwise bounded by g
lemma approx_from_below (μ : Measure α) (p : ℝ≥0∞) {g : α → 𝕂} (hg : StronglyMeasurable g) : ∃ gs : ℕ → SimpleFunc α 𝕂,
    (∀ (x : α), Filter.Tendsto (fun n ↦ (gs n) x) Filter.atTop (nhds (g x)))
    ∧ Filter.limsup (fun n ↦ eLorentzNorm (gs n) p 1 μ) Filter.atTop ≤ eLorentzNorm g p 1 μ := by
  /-
  apply Filter.limsup_le_of_le'
  apply Filter.Eventually.of_forall
  intro n
  gcongr
  apply eLorentzNorm_mono
  --TODO: continue here, ensure approximation from below for g or find better solution
  --have := SimpleFunc.monotone_approx gs g
  sorry --use : better def of gs?
  -/
  sorry

--TODO: Show that the Carleson operator is weakly continuous in this sense via Fatou's lemma

lemma HasRestrictedWeakType.hasLorentzType /- [MeasurableSpace ε'] [BorelSpace ε'] -/
  --[ENormedAddMonoid ε']
  {T : (α → 𝕂) → (α' → ε')} {p p' : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞}
  (hT : HasRestrictedWeakType T p p' μ ν c) (hpp' : p.HolderConjugate p')
  (weakly_cont_T : WeaklyContinuous T μ ν) :
    --TODO: might have to adjust the constant
    HasLorentzType T p 1 p ∞ μ ν c := by
  intro f hf
  by_cases c_ne_top : c = ⊤
  · sorry
  have claim : ∀ (G : Set α'), (MeasurableSet G) → (ν G < ∞) → eLpNorm (T f) 1 (ν.restrict G)
    ≤ c * eLorentzNorm f p 1 μ * (ν G) ^ p'⁻¹.toReal := by
      -- Get this for simple functions first?
      have hg := hf.1.choose_spec
      set g := hf.1.choose
      --have hgs := hg.1.choose_spec
      --set gs := hg.1.choose
      --have hgs := hg.1.tendsto_approx
      --set gs := hg.1.approx
      have hgs := (approx_from_below μ p hg.1).choose_spec
      set gs := (approx_from_below μ p hg.1).choose
      intro G measurable_G G_finite

      calc _
        _ = eLpNorm (T g) 1 (ν.restrict G) := by sorry --use : aeeq
        _ ≤ Filter.limsup (fun n ↦ eLpNorm (T (gs n)) 1 (ν.restrict G)) Filter.atTop := by
          apply weakly_cont_T hgs.1
        _ ≤ Filter.limsup (fun n ↦ c * eLorentzNorm (gs n) p 1 μ * ν G ^ p'⁻¹.toReal) Filter.atTop := by
          apply Filter.mono_limsup
          intro n
          apply MeasureTheory.HasRestrictedWeakType.hasLorentzType_helper hT hpp' (gs n) _ measurable_G G_finite
        _ ≤ c * eLorentzNorm g p 1 μ * ν G ^ p'⁻¹.toReal := by
          simp_rw [mul_assoc]
          rw [ENNReal.limsup_const_mul_of_ne_top c_ne_top]
          gcongr
          simp_rw [mul_comm]
          rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) G_finite.ne)]
          gcongr
          exact hgs.2
        _ = c * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal := by sorry --use : aeeq


  -- Apply claim to a special G
  --let G := {x | ‖T x‖ₑ > }
  constructor
  · sorry
  · by_cases h : p = ⊤
    · rw [h]
      rw [eLorentzNorm_eq_Lp sorry]
      by_cases h' : f =ᵐ[μ] 0
      · sorry
      · sorry
    · rw [eLorentzNorm_eq_wnorm sorry, wnorm_ne_top h]
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
        _ ≤ (c * eLorentzNorm f p 1 μ * ν G ^ p'⁻¹.toReal) / ν G ^ p'⁻¹.toReal := by
          gcongr
          apply claim
          · sorry
          · sorry
        _ ≤ c * eLorentzNorm f p 1 μ * 1 := by
          rw [mul_div_assoc]
          gcongr
          exact ENNReal.div_self_le_one
        _ = c * eLorentzNorm f p 1 μ := by ring

end Lorentz

end MeasureTheory
