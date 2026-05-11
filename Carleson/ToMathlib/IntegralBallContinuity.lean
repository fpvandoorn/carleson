module

public import Carleson.Defs
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Indexed
public import Carleson.ToMathlib.RealInterpolation.Main
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Average
public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.Field
import Carleson.ToMathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter Pointwise
open ENNReal hiding one_lt_two
open scoped NNReal
noncomputable section

/-! This file contains results about continuity of integrals and averages over balls that were
unused in `HardyLittleWood`, and whose destiny in Mathlib is unclear.
-/

variable {X E : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {f : X → E}

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_of_isBounded [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : IsBounded s) : IntegrableOn f s μ :=
  hf.integrableOn_isCompact hs.isCompact_closure |>.mono_set subset_closure

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_ball [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {x : X} {r : ℝ} : IntegrableOn f (ball x r) μ :=
  hf.integrableOn_of_isBounded isBounded_ball

open scoped Topology in
lemma continuous_integral_ball [OpensMeasurableSpace X]
    (g : X → ℝ≥0∞) (hg : ∀ x : X, ∀ r > (0 : ℝ), ∫⁻ (y : X) in ball x r, g y ∂μ < ⊤)
    (hg2 : AEMeasurable g μ) (hμ : ∀ z : X, ∀ r > (0 : ℝ), μ (sphere z r) = 0 ):
    ContinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, g y ∂μ) (univ ×ˢ Ioi 0) := by
  intro x hx
  have hx_pos : x.2 > 0 := by simp only [mem_prod, mem_univ, mem_Ioi, true_and] at hx; exact hx
  unfold ContinuousWithinAt
  dsimp only
  have : (fun x : X × ℝ ↦ ∫⁻ (y : X) in ball x.1 x.2, g y ∂μ) =
      fun x : X × ℝ ↦ ∫⁻ (y : X), (ball x.1 x.2).indicator g y ∂μ := by
    ext x
    rw [← lintegral_indicator measurableSet_ball]
  rw [this, ← lintegral_indicator measurableSet_ball]
  apply tendsto_of_seq_tendsto
  intro z hz
  have hz' : Tendsto z atTop (𝓝 x) := tendsto_nhds_of_tendsto_nhdsWithin hz
  have := isBounded_range_of_tendsto z hz'
  obtain ⟨r, hr⟩ := Bornology.IsBounded.subset_ball this x
  simp only [range, ball, setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff] at hr
  simp_rw [Prod.dist_eq] at hr
  have hsub (n : ℕ) : ball (z n).1 (z n).2 ⊆ ball x.1 (x.2 + 2 * r) := by
    intro y hy
    simp only [ball, mem_setOf_eq] at hy ⊢
    calc dist y x.1
    _  ≤ dist y (z n).1 + dist (z n).1 x.1 := dist_triangle y (z n).1 x.1
    _ ≤ (z n).2 + dist (z n).1 x.1 := by gcongr
    _ ≤ |(z n).2| + dist (z n).1 x.1 := by gcongr; exact le_abs_self (z n).2
    _ = |(z n).2 - x.2 + x.2| + dist (z n).1 x.1 := by rw [sub_add_cancel]
    _ ≤ |(z n).2 - x.2| + |x.2| + dist (z n).1 x.1 := by gcongr; exact abs_add_le _ _
    _ < r + |x.2| + r := by
      gcongr
      · calc
        _ = dist (z n).2 x.2 := by rw [← Real.dist_eq]
        _ ≤ _ := le_max_right (dist (z n).1 x.1) (dist (z n).2 x.2)
        _ < r := hr _
      · calc
        _ ≤ _ := le_max_left (dist (z n).1 x.1) (dist (z n).2 x.2)
        _ < r := hr _
    _ = r + x.2 + r := by
      congr
      simp only [mem_prod, mem_univ, mem_Ioi, true_and] at hx; rw [abs_of_nonneg hx.le]
    _ = x.2 + 2 * r := by linarith
  let bound := (ball x.1 (x.2 + 2 * r)).indicator g
  apply tendsto_lintegral_of_dominated_convergence' bound
  · exact fun _ ↦ hg2.indicator measurableSet_ball
  · intro n
    filter_upwards with a
    unfold bound indicator
    split_ifs with h₀ h₁
    · simp
    · contrapose! h₁; exact hsub n h₀
    · simp
    · simp
  · unfold bound
    rw [lintegral_indicator measurableSet_ball]
    apply ne_of_lt
    apply hg
    have : 0 < r := by
      calc
      0 ≤ dist (z 0).1 x.1 := dist_nonneg
      _ ≤ max (dist (z 0).1 x.1) (dist (z 0).2 x.2) := le_max_left _ _
      _ < r := hr _
    linarith
  · have : ∀ᵐ z : X ∂μ, dist z x.1 ≠ x.2 := by
      change (μ ({z | ¬ (dist z x.1 ≠ x.2)}) = 0)
      simpa only [ne_eq, Decidable.not_not] using hμ x.1 x.2 hx_pos
    filter_upwards [this] with y hy
    by_cases hy2 : dist y x.1 < x.2
    · simp only [indicator, ball, mem_setOf_eq]
      split_ifs
      apply tendsto_nhds_of_eventually_eq
      have hz2 : ∀ᶠ n : ℕ in atTop, dist y (z n).1 < (z n).2 := by
        let dist_sub (a : X × ℝ) := dist y a.1 - a.2
        have : ContinuousOn dist_sub (univ ×ˢ Ioi 0) := by fun_prop
        have : Tendsto (dist_sub ∘ z) atTop (𝓝 (dist_sub x)) := Tendsto.comp (this x hx) hz
        have : ∀ᶠ (n : ℕ) in atTop, dist y (z n).1 - (z n).2 < 0 := by
          rw [← sub_lt_zero] at hy2; exact Tendsto.eventually_lt_const hy2 this
        filter_upwards [this]; simp
      filter_upwards [hz2]; intro a ha; split_ifs; rfl
    · have hz2 : ∀ᶠ n : ℕ in atTop, dist y (z n).1 > (z n).2 := by
        let dist_sub (a : X × ℝ) := dist y a.1 - a.2
        have : ContinuousOn dist_sub (univ ×ˢ Ioi 0) := by fun_prop
        have hcmp : Tendsto (dist_sub ∘ z) atTop (𝓝 (dist_sub x)) := Tendsto.comp (this x hx) hz
        have hy2 : dist y x.1 > x.2 := by order
        have hy2 : 0 < dist y x.1 - x.2 := sub_pos.mpr hy2
        have : ∀ᶠ (n : ℕ) in atTop, 0 < dist y (z n).1 - (z n).2 := Tendsto.eventually_const_lt hy2 hcmp
        filter_upwards [this]; simp
      simp only [indicator, ball, mem_setOf_eq]
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hz2] with n hn
      have : ¬ (dist y (z n).1 < (z n).2) := by linarith
      split_ifs; rfl

-- unused in Carleson
-- move to separate file (not sure where)
lemma continuous_average_ball [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace X]
    [ProperSpace X] (hf : LocallyIntegrable f μ)
    (hμ : ∀ z : X, ∀ r > (0 : ℝ), μ (sphere z r) = 0) :
    ContinuousOn (fun x : X × ℝ ↦ ⨍⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
  rw [(isOpen_univ.prod isOpen_Ioi).continuousOn_iff]
  intro x hx
  have hx_pos : 0 < x.2 := by simp only [mem_prod, mem_univ, mem_Ioi, true_and] at hx; exact hx
  have : (fun x : X × ℝ ↦ ⨍⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) =
    fun x : X × ℝ ↦ (μ (ball x.1 x.2))⁻¹ * ∫⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ
     := by ext x; simp [laverage]
  rw [this]
  apply ENNReal.Tendsto.mul
  · apply Tendsto.inv
    have : (fun z : X × ℝ ↦ μ (ball z.1 z.2)) =
        (fun z : X × ℝ ↦ ∫⁻ (y : X) in ball z.1 z.2, (1 : ℝ≥0∞) ∂μ) := by simp
    rw [this, (setLIntegral_one (ball x.1 x.2)).symm]
    have : ContinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, (1 : ℝ≥0∞) ∂μ) (univ ×ˢ Ioi 0) := by
      apply continuous_integral_ball _ _ aemeasurable_const hμ
      intro p r hr; rw [setLIntegral_one]; finiteness
    rw [(isOpen_univ.prod isOpen_Ioi).continuousOn_iff] at this
    apply this hx
  · exact Or.inr (hf.integrableOn_ball.right.ne)
  · have : ContinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
      apply continuous_integral_ball _ _ _ hμ
      · exact fun x r hr ↦ hf.integrableOn_ball.right
      · exact hf.aestronglyMeasurable.enorm
    rw [(isOpen_univ.prod isOpen_Ioi).continuousOn_iff] at this
    exact this hx
  · exact Or.inr (inv_ne_top.mpr (measure_ball_pos μ x.1 hx_pos).ne')

open scoped Topology in
-- unused in Carleson
-- move to separate file (not sure where)
lemma lowerSemiContinuousOn_integral_ball [OpensMeasurableSpace X] (hf2 : AEStronglyMeasurable f μ) :
    LowerSemicontinuousOn (fun x : X × ℝ ↦ ∫⁻ y in ball x.1 x.2, ‖f y‖ₑ ∂μ) (univ ×ˢ Ioi 0) := by
  refine lowerSemicontinuousOn_iff_le_liminf.mpr fun x hx ↦ _root_.le_of_forall_pos_le_add ?_
  intro δ hδ
  let M := liminf (fun x ↦ ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ) (𝓝[univ ×ˢ Ioi 0] x) + δ
  by_cases htop : liminf (fun x ↦ ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ) (𝓝[univ ×ˢ Ioi 0] x) = ∞
  · rw [htop]; simp
  have hM : liminf (fun x ↦ ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ)
      (𝓝[univ ×ˢ Ioi 0] x) < M := lt_add_right htop hδ.ne'
  have : ∃ᶠ (z : X × ℝ) in 𝓝[univ ×ˢ Ioi 0] x, ∫⁻ (y : X) in ball z.1 z.2, ‖f y‖ₑ ∂μ < M := by
    refine frequently_lt_of_liminf_lt ?_ hM
    simp only [IsCoboundedUnder, Filter.IsCobounded, ge_iff_le, eventually_map]
    use ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ
    intro a ha; apply Eventually.self_of_nhdsWithin ha hx
  obtain ⟨ns, hns₀, hns₁⟩ :=
    exists_seq_forall_of_frequently (l := 𝓝[univ ×ˢ Ioi 0] x)
        (p := fun z ↦ ∫⁻ (y : X) in ball z.1 z.2, ‖f y‖ₑ ∂μ < M) this
  let g (n : ℕ) := (ball (ns n).1 (ns n).2).indicator (fun y ↦ ‖f y‖ₑ)
  have (z : X) : (ball x.1 x.2).indicator (fun y ↦ ‖f y‖ₑ) z ≤
      liminf (fun n ↦ g n z) atTop := by
    apply le_liminf_of_le (f := atTop)
    unfold g indicator
    split_ifs with hz
    · have hz2 : ∀ᶠ n : ℕ in atTop, z ∈ ball (ns n).1 (ns n).2 := by
        let dist_sub (y : X × ℝ) := dist z y.1 - y.2
        have : ContinuousOn dist_sub (univ ×ˢ Ioi 0) := by fun_prop
        have : Tendsto (dist_sub ∘ ns) atTop (𝓝 (dist_sub x)) := Tendsto.comp (this x hx) hns₀
        have : ∀ᶠ (n : ℕ) in atTop, dist z (ns n).1 - (ns n).2 < 0 := by
          rw [mem_ball, ← sub_lt_zero] at hz; exact Tendsto.eventually_lt_const hz this
        filter_upwards [this]; simp
      filter_upwards [hz2]; intro a ha; split_ifs; rfl
    · simp
  calc
  ∫⁻ (y : X) in ball x.1 x.2, ‖f y‖ₑ ∂μ
    ≤ ∫⁻ y, (ball x.1 x.2).indicator (fun z ↦ ‖f z‖ₑ) y ∂μ := by
    rw [lintegral_indicator]; exact measurableSet_ball
  _ ≤ ∫⁻ y, liminf (fun n ↦ g n y) atTop ∂μ := by gcongr with y; exact this y
  _ ≤ liminf (fun n ↦ ∫⁻ y, g n y ∂μ) atTop := by
    apply lintegral_liminf_le' fun n ↦ by fun_prop (discharger := measurability)
  _ ≤ M := by
    apply liminf_le_of_le (f := atTop)
    intro b hb
    simp only [eventually_atTop, ge_iff_le] at hb
    obtain ⟨a, ha⟩ := hb
    exact le_of_lt <| lt_of_le_of_lt (ha a le_rfl) <|
      by unfold g; rw [lintegral_indicator measurableSet_ball]; exact hns₁ a
