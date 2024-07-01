import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.LinearIsometry

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function


variable {α α' 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)
  {f g : α → E} (hf : AEMeasurable f) {t s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}

-- #check meas_ge_le_mul_pow_snorm -- Chebyshev's inequality

namespace MeasureTheory
/- If we need more properties of `E`, we can add `[RCLike E]` *instead of* the above type-classes-/
-- #check _root_.RCLike

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution [NNNorm E] (f : α → E) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖₊ }

@[gcongr] lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    distribution f t μ ≤ distribution g t μ := by
  have h₀ : {x | t < ‖f x‖₊} \ {x | t < ‖g x‖₊} ⊆ {x | ¬ ‖f x‖ ≤ ‖g x‖} := calc
    {x | t < ‖f x‖₊} \ {x | t < ‖g x‖₊}
      = {x | t < ‖f x‖₊ ∧ ¬ t < ‖g x‖₊}         := by rfl
    _ = {x | t < ‖f x‖₊ ∧ ‖g x‖₊ ≤ t}           := by simp
    _ ⊆ {x | ofNNReal ‖g x‖₊ < ofNNReal ‖f x‖₊} := fun x h₁ ↦ lt_of_le_of_lt h₁.right h₁.left
    _ ⊆ {x | ‖g x‖ < ‖f x‖}                     := by intro x; simp; exact fun a ↦ a
    _ = {x | ¬ ‖f x‖ ≤ ‖g x‖}                   := by simp
  have h₁ : μ ({x | t < ‖f x‖₊} \ {x | t < ‖g x‖₊}) = 0 := measure_mono_null h₀ h
  calc
    μ {x | t < ↑‖f x‖₊}
      ≤ μ ({x | t < ↑‖f x‖₊} ∩ {x | t < ‖g x‖₊})
      + μ ({x | t < ↑‖f x‖₊} \ {x | t < ‖g x‖₊}) := by apply measure_le_inter_add_diff
    _ = μ ({x | t < ↑‖f x‖₊} ∩ {x | t < ‖g x‖₊}) := by rw [h₁]; simp
    _ ≤ μ ({x | t < ‖g x‖₊}) := by apply measure_mono; simp

@[gcongr] lemma distribution_mono_right (h : t ≤ s) :
    distribution f s μ ≤ distribution f t μ := by
  apply measure_mono
  exact fun x a ↦ lt_of_le_of_lt h a

@[gcongr] lemma distribution_mono (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) (h : t ≤ s) :
    distribution f s μ ≤ distribution g t μ := calc
  distribution f s μ ≤ distribution g s μ := by apply distribution_mono_left; assumption
  _                  ≤ distribution g t μ := by apply distribution_mono_right; assumption

lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) (hc : c ≠ 0) :
    ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ := by
    refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
    · exact coe_ne_top
    · exact Ne.symm top_ne_coe
    . exact norm_smul c z

lemma ENNNorm_add_le (y z: E):
    ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ := by
    refine (toReal_le_toReal ?_ ?_).mp ?_
    · exact coe_ne_top
    · exact coe_ne_top
    · apply nnnorm_add_le

lemma distribution_smul_left {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖₊) μ := by
  unfold distribution
  have h₀ : ofNNReal ‖c‖₊ ≠ 0 := ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hc)
  have h₁ : ofNNReal ‖c‖₊ ≠ ⊤ := coe_ne_top
  have h₂ : {x | t < ‖(c • f) x‖₊} = {x | t / ‖c‖₊ < ‖f x‖₊} := by
    ext x
    simp
    rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖₊) _ (‖c‖₊) h₀ h₁]
    rw [ENNNorm_absolute_homogeneous _ hc]
    rw [mul_comm]
    rw [ENNReal.div_mul_cancel h₀ h₁]
  rw [h₂]

lemma distribution_add_le :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ := by
  unfold distribution
  have h₀ : {x | t + s < ↑‖(f + g) x‖₊} ⊆ {x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊} := by
    intro x
    intro h₁
    by_contra h₂
    simp at h₂
    have h₃ : (↑‖f x + g x‖₊ ≤ t + s) := calc
      ↑‖f x + g x‖₊ ≤ ↑‖f x‖₊ + ↑‖g x‖₊ := by apply ENNNorm_add_le
      _             ≤ t + s := add_le_add h₂.left h₂.right
    have h₄ : (¬ ↑‖f x + g x‖₊ ≤ t + s) := by
      simp; exact h₁
    contradiction
  calc
    μ {x | t + s < ↑‖(f + g) x‖₊}
      ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := by exact measure_mono h₀
    _ ≤ μ {x | t < ↑‖f x‖₊} + μ {x | s < ↑‖g x‖₊} := by apply measure_union_le

lemma approx_above_superset (t₀ : ℝ≥0∞) :
    ⋃ n, (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ↑‖f x‖₊}) n = {x | t₀ < ‖f x‖₊} := by
  ext y
  constructor
  · intro h
    have h₀ : ∃ n : ℕ, y ∈ {x | t₀ + (↑n)⁻¹ < ↑‖f x‖₊} := exists_exists_eq_and.mp h
    rcases h₀ with ⟨n, wn⟩
    calc
      t₀ ≤ t₀ + (↑n)⁻¹ := le_self_add
      _  < ↑‖f y‖₊     := wn
  · intro h
    have h₁ : Iio (↑‖f y‖₊ - t₀) ∈ 𝓝 0 := Iio_mem_nhds (tsub_pos_of_lt h)
    have h₂ := ENNReal.tendsto_inv_nat_nhds_zero h₁
    simp at h₂
    rcases h₂ with ⟨n, wn⟩
    have h₃ : (↑n)⁻¹ < ↑‖f y‖₊ - t₀ := wn n (Nat.le_refl n)
    simp
    exists n
    exact lt_tsub_iff_left.mp h₃

lemma tendsto_measure_iUnion_distribution (t₀ : ℝ≥0∞) :
    Filter.Tendsto (⇑μ ∘ (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖₊}))
      Filter.atTop (nhds (μ ({x | t₀ < ‖f x‖₊}))) := by
  unfold Filter.Tendsto
  rw [← approx_above_superset]
  apply MeasureTheory.tendsto_measure_iUnion
  intros a b h x h₁
  calc
    t₀ + (↑b)⁻¹
      ≤ t₀ + (↑a)⁻¹ := add_le_add (Preorder.le_refl t₀) (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr h))
    _ < ↑‖f x‖₊     := h₁

lemma select_neighborhood_distribution (t₀ : ℝ≥0∞) (l : ℝ≥0∞) (hu : l < distribution f t₀ μ) :
    ∃ n : ℕ, l < distribution f (t₀ + (↑n)⁻¹) μ := by
  have h₁ : Ioi l ∈ (𝓝 (distribution f t₀ μ)) := Ioi_mem_nhds hu
  have h₂ := (tendsto_measure_iUnion_distribution t₀) h₁
  simp at h₂
  rcases h₂ with ⟨n, wn⟩
  exists n; exact wn n (Nat.le_refl n)

lemma continuousWithinAt_distribution (t₀ : ℝ≥0∞) :
    ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
  rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
  · rw [t₀top]
    apply continuousWithinAt_of_not_mem_closure
    simp
  · unfold ContinuousWithinAt
    rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
    -- Case: distribution f t₀ μ = ⊤
    · simp
      rw [db_top]
      rw [ENNReal.tendsto_nhds_top_iff_nnreal]
      intro b
      have h₀ : ∃ n : ℕ, ↑b < distribution f (t₀ + (↑n)⁻¹) μ := by
        apply select_neighborhood_distribution
        rw [db_top]
        exact coe_lt_top
      rcases h₀ with ⟨n, wn⟩
      apply eventually_mem_set.mpr
      apply mem_inf_iff_superset.mpr
      exists Iio (t₀ + (↑n)⁻¹)
      constructor
      · exact Iio_mem_nhds (lt_add_right (LT.lt.ne_top t₀nottop)
            (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
      · exists Ioi t₀
        constructor
        · simp
        · intros z h₁
          simp at h₁
          have h₂ : z < t₀ + (↑n)⁻¹ := by tauto
          calc
            ↑b < distribution f (t₀ + (↑n)⁻¹) μ := wn
            _  ≤ distribution f z μ := distribution_mono_right (le_of_lt h₂)
    -- Case: distribution f t₀ μ < ⊤
    · apply (ENNReal.tendsto_nhds (LT.lt.ne_top db_not_top)).mpr
      intros ε ε_gt_0
      apply eventually_mem_set.mpr
      apply mem_inf_iff_superset.mpr
      rcases eq_zero_or_pos (distribution f t₀ μ) with db_zero | db_not_zero
      -- Case: distribution f t₀ μ = 0
      · exists Ico 0 (t₀ + 1)
        constructor
        · apply IsOpen.mem_nhds
          · exact isOpen_Ico_zero
          · simp; exact lt_add_right (LT.lt.ne_top t₀nottop) one_ne_zero
        · exists Ioi t₀
          constructor
          · simp
          · intros z hz
            have h₁ : t₀ < z := hz.right
            rw [db_zero]
            simp
            have h₂ : distribution f z μ ≤ distribution f t₀ μ :=
                distribution_mono_right (le_of_lt h₁)
            rw [db_zero] at h₂
            have h₃ : distribution f z μ = 0 := nonpos_iff_eq_zero.mp h₂
            change (Icc 0 ε (distribution f z μ))
            rw [h₃]
            constructor
            · exact zero_le 0
            · exact zero_le ε
      -- Case: 0 < distribution f t₀ μ
      · have h₀ : ∃ n : ℕ, distribution f t₀ μ - ε < μ {x | t₀ + (↑n)⁻¹ < ‖f x‖₊} := by
          apply select_neighborhood_distribution
          apply ENNReal.sub_lt_self
          · exact LT.lt.ne_top db_not_top
          · exact Ne.symm (ne_of_lt db_not_zero)
          · exact Ne.symm (ne_of_lt ε_gt_0)
        rcases h₀ with ⟨n, wn⟩
        exists Iio (t₀ + (↑n)⁻¹)
        constructor
        · exact Iio_mem_nhds (lt_add_right (LT.lt.ne_top t₀nottop)
              (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
        · exists Ioi t₀
          constructor
          · simp
          · intros z h₁
            simp at h₁
            have h₂ : z < t₀ + (↑n)⁻¹ := by tauto
            constructor
            · calc
                distribution f t₀ μ - ε
                  ≤ distribution f (t₀ + (↑n)⁻¹) μ := le_of_lt wn
                _ ≤ distribution f z μ             := distribution_mono_right (le_of_lt h₂)
            · calc
                distribution f z μ
                  ≤ distribution f t₀ μ := distribution_mono_right (le_of_lt h₁.right)
                _ ≤ distribution f t₀ μ + ε := le_self_add

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖₊ * t * s) μ ≤
    distribution f t μ + distribution g s μ := by
  unfold distribution
  have h₀ : {x | ↑‖L‖₊ * t * s < ↑‖(fun x ↦ (L (f x)) (g x)) x‖₊} ⊆
      {x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊} := by
    intros z hz
    simp at hz
    simp
    by_contra h₁
    simp at h₁
    cases h₁
    have h₂ : ↑‖(L (f z)) (g z)‖₊ ≤ ↑‖L‖₊ * t * s := calc
      ofNNReal ↑‖(L (f z)) (g z)‖₊
        ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ := by
          refine (toNNReal_le_toNNReal ?_ ?_).mp ?_
          · exact coe_ne_top
          · exact coe_ne_top
          · calc
              ‖(L (f z)) (g z)‖₊
                ≤ ↑‖L (f z)‖₊ * ↑‖g z‖₊ := ContinuousLinearMap.le_opNNNorm (L (f z)) (g z)
              _ ≤  ↑‖L‖₊ * ‖f z‖₊ * ↑‖g z‖₊ := by
                  apply mul_le_mul'
                  · exact ContinuousLinearMap.le_opNNNorm L (f z)
                  . exact Preorder.le_refl ‖g z‖₊
      _ ≤ ‖L‖₊ * t * s := by
          apply mul_le_mul'
          · apply mul_le_mul'
            · exact Preorder.le_refl (ofNNReal ↑‖L‖₊)
            · assumption
          · assumption
    have _ : (¬ ↑‖(L (f z)) (g z)‖₊ ≤ ↑‖L‖₊ * t * s) := by
      simp; exact hz
    contradiction
  calc
    μ {x | ↑‖L‖₊ * t * s < ↑‖(fun x ↦ (L (f x)) (g x)) x‖₊}
      ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := by apply measure_mono h₀
    _ ≤ distribution f t μ + distribution g s μ := by apply measure_union_le

/- A version of the layer-cake theorem already exists, but the need the versions below. -/
-- #check MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul

/-- The layer-cake theorem, or Cavalieri's principle for functions into `ℝ≥0∞` -/
lemma lintegral_norm_pow_eq_measure_lt {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (f x) ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * μ { x | ENNReal.ofReal t < f x } := by
  sorry

/-- The layer-cake theorem, or Cavalieri's principle for functions into a normed group. -/
lemma lintegral_norm_pow_eq_distribution {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖f x‖₊ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ := sorry

/-- The layer-cake theorem, or Cavalieri's principle, written using `snorm`. -/
lemma snorm_pow_eq_distribution {p : ℝ≥0} (hp : 1 ≤ p) :
    snorm f p μ ^ (p : ℝ) =
    ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
  sorry

lemma lintegral_pow_mul_distribution {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * distribution f (.ofReal t) μ =
    ENNReal.ofReal p⁻¹ * ∫⁻ x, ‖f x‖₊ ^ (p + 1) ∂μ  := sorry


/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' [NNNorm E] (f : α → E) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

lemma wnorm'_le_snorm' {f : α → E} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    wnorm' f p μ ≤ snorm' f p μ := sorry

/-- The weak L^p norm of a function. -/
def wnorm [NNNorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then snormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

lemma wnorm_le_snorm {f : α → E} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wnorm f p μ ≤ snorm f p μ := sorry

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWℒp [NNNorm E] (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma Memℒp.memWℒp {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : Memℒp f p μ) :
    MemWℒp f p μ := sorry

/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from L^p to weak-L^q.
`HasWeakType T p p' μ ν c` means that `T` has weak type (p, q) w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasWeakType (T : (α → E₁) → (α' → E₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0) : Prop :=
  ∀ f : α → E₁, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * snorm f p μ

/-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, q) w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ snorm (T f) p' ν ≤ c * snorm f p μ

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → snorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ snorm (T f) p' ν ≤ c * snorm f p μ


lemma HasStrongType.hasWeakType (hp : 1 ≤ p)
    (h : HasStrongType T p p' μ ν c) : HasWeakType T p p' μ ν c := by
  sorry

lemma HasStrongType.hasBoundedStrongType (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c :=
  fun f hf _ _ ↦ h f hf


end MeasureTheory
