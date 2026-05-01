module

public import Mathlib.Analysis.Normed.Group.Basic
public import Carleson.ToMathlib.HardyLittlewood
public import Carleson.TwoSidedCarleson.Basic

@[expose] public section

open MeasureTheory Set Bornology Function Metric Filter Topology
open ENNReal hiding one_lt_two
open scoped NNReal

noncomputable section

/-- `K` is a two-sided Calderon-Zygmund kernel.
In the formalization `K x y` is defined everywhere, even for `x = y`.
The assumptions on `K` show that `K x x = 0`. -/
class IsTwoSidedKernel {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (a : outParam ℕ)
    (K : X → X → ℂ) extends IsOneSidedKernel a K where
  enorm_K_sub_le' {x x' y : X} (h : 2 * dist x x' ≤ dist x y) :
    ‖K x y - K x' y‖ₑ ≤ (edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)

export IsTwoSidedKernel (enorm_K_sub_le')

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable {f : X → ℂ} {α : ℝ≥0∞}

/-! ## Section 10.2 and Lemma 10.0.3

Question: -/

/-- The constant used in `nontangential_from_simple`.
I(F) think the constant needs to be fixed in the blueprint. -/
irreducible_def C10_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (4 * a)

/-- Lemma 10.2.1, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem maximal_theorem :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  apply HasWeakType.hasBoundedWeakType
  have : C10_2_1 a = C_weakType_globalMaximalFunction (defaultA a) 1 1 := by
    unfold C_weakType_globalMaximalFunction C_weakType_maximalFunction
    split_ifs with h; swap; · simp at h
    simp_rw [C10_2_1_def, defaultA, coe_pow, coe_ofNat, Nat.cast_pow, Nat.cast_ofNat,
      NNReal.coe_one, div_one, rpow_ofNat, pow_mul', ← pow_add, two_add_two_eq_four]; rfl
  rw [this]
  apply hasWeakType_globalMaximalFunction (μ := volume) (p₁ := 1) (p₂ := 1) (by norm_num) le_rfl

-- Lemma 10.2.1, as formulated in the blueprint
variable (α) in
private theorem maximal_theorem' (hf : BoundedFiniteSupport f) :
    α * volume {x | α < ‖globalMaximalFunction volume 1 f x‖ₑ} ≤
    (C10_2_1 a) * eLpNorm f 1 volume := by
  by_cases hα : α = ∞
  · simp [hα]
  have h := (maximal_theorem f hf).2
  simp only [wnorm, one_ne_top, reduceIte, wnorm', toReal_one, inv_one, rpow_one, iSup_le_iff] at h
  exact coe_toNNReal hα ▸ h α.toNNReal

-- Alternate version of `maximal_theorem'`
private theorem maximal_theorem'' (hα : 0 < α) (hf : BoundedFiniteSupport f) :
    volume {x | α < ‖globalMaximalFunction volume 1 f x‖ₑ} ≤
    (C10_2_1 a) * eLpNorm f 1 volume / α := by
  by_cases α_top : α = ∞
  · simp [α_top]
  apply ENNReal.le_div_iff_mul_le (Or.inl hα.ne') (Or.inl α_top) |>.mpr
  exact mul_comm α _ ▸ maximal_theorem' α hf

/-- Lemma 10.2.2. -/
theorem lebesgue_differentiation {f : X → ℂ} (hf : BoundedFiniteSupport f) :
    ∀ᵐ x ∂volume, ∃ (c : ℕ → X) (r : ℕ → ℝ),
    Tendsto (fun i ↦ ⨍ y in ball (c i) (r i), f y ∂volume) atTop (𝓝 (f x)) ∧
    Tendsto r atTop (𝓝[>] 0) ∧
    ∀ i, x ∈ ball (c i) (r i) := by
  -- By the Vitali covering theorem, the conclusion of the theorem is true for closed balls.
  have ineq (x : X) {r : ℝ} (hr : r > 0) :
      volume (closedBall x (3 * r)) ≤ (defaultA a) ^ 2 * volume (closedBall x r) := calc
    _ ≤ volume (ball x (2 ^ 2 * (0.9 * r))) := measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ (defaultA a) ^ 2 * volume (ball x (0.9 * r)) := measure_ball_two_le_same_iterate _ _ 2
    _ ≤ (defaultA a) ^ 2 * volume (closedBall x r) := by
      gcongr; exact ball_subset_closedBall.trans <| closedBall_subset_closedBall <| by linarith
  let v : VitaliFamily volume := Vitali.vitaliFamily volume _
    (fun x ↦ eventually_nhdsWithin_of_forall (s := Ioi 0) (fun r ↦ ineq x) |>.frequently)
  refine (v.ae_tendsto_average hf.integrable.locallyIntegrable).mono (fun x hx ↦ ?_)
  have tendsto_closedBall : Tendsto (closedBall x) (𝓝[>] 0) (v.filterAt x) := by
    rw [v.tendsto_filterAt_iff]
    refine ⟨eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun r hr ↦ ?_), fun ε hε ↦ ?_⟩
    · exact ⟨isClosed_closedBall, ⟨x, mem_interior.mpr ⟨ball x r, ball_subset_closedBall,
        isOpen_ball, mem_ball_self hr⟩⟩, r, by tauto, ineq x hr⟩
    · rw [eventually_nhdsWithin_iff, _root_.eventually_nhds_iff]
      exact ⟨Iio ε, fun y hy _ ↦ closedBall_subset_closedBall hy.le, ⟨isOpen_Iio, hε⟩⟩
  -- We prove a stronger result: we can use any balls centered at x with radii decreasing to 0
  have ⟨r, _, hr0, hr⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine ⟨fun _ ↦ x, r, ?_, hr, (mem_ball_self <| hr0 ·)⟩
  suffices Tendsto (⨍ y in ball x ·, f y) (𝓝[>] 0) (𝓝 (f x)) from this.comp hr
  -- Now we translate the known result about closed balls to the desired result about open balls,
  -- by approximating the average over the open ball by an average over a closed ball within it.
  refine Metric.tendsto_nhds.mpr (fun ε hε ↦ ?_)
  have := Metric.tendsto_nhds.mp (hx.comp tendsto_closedBall) (ε / 2) (half_pos hε)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at this ⊢
  have ⟨δ, δ0, hδ⟩ := this
  refine ⟨δ, δ0, fun r hr hr0 ↦ ?_⟩
  have ⟨ρ, ρ_mono, ρ_lt_r, tendsto_ρ_r⟩ := exists_seq_strictMono_tendsto r
  let cB (n : ℕ) := closedBall x (ρ n)
  suffices ∀ᶠ n in atTop, ρ n > 0 ∧ dist (⨍ y in ball x r, f y) (⨍ y in cB n, f y) < ε / 2 by
    have ⟨n, hn0, hn⟩ := this.exists
    apply lt_of_le_of_lt <| dist_triangle (⨍ y in ball x r, f y) (⨍ y in cB n, f y) (f x)
    rw [← add_halves ε]
    refine add_lt_add hn (hδ ?_ hn0)
    have r_lt_δ : r < δ := by simpa [abs_eq_self.mpr (mem_Ioi.mp hr0).le] using hr
    rw [dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ⟨lt_trans (neg_neg_iff_pos.mpr δ0) hn0, lt_trans (ρ_lt_r n) r_lt_δ⟩
  apply Eventually.and (tendsto_ρ_r.eventually_const_lt hr0)
  -- It remains to confirm that `⨍ y in cB n, f y` estimates `⨍ y in ball x r, f y` for large `n`:
  suffices Tendsto (⨍ y in cB ·, f y) atTop (𝓝 (⨍ y in ball x r, f y)) by
    have := (continuous_dist.uncurry_left (⨍ y in ball x r, f y)).continuousAt.tendsto.comp this
    simpa using Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp this (ε / 2) (half_pos hε))
  -- We first check that `∫ y in cB n, f y` estimates `∫ y in ball x r, f y`:
  have hsm (n : ℕ) : MeasurableSet (cB n) := measurableSet_closedBall
  have h_mono : Monotone cB := fun m n hmn ↦ closedBall_subset_closedBall (ρ_mono.le_iff_le.mpr hmn)
  have := MeasureTheory.tendsto_setIntegral_of_monotone hsm h_mono hf.integrable.integrableOn
  have iUnion_cB : ⋃ n, cB n = ball x r := by
    refine subset_antisymm (iUnion_subset (closedBall_subset_ball <| ρ_lt_r ·)) (fun y hy ↦ ?_)
    have ⟨n, hn⟩ := (tendsto_ρ_r.eventually_const_lt hy).exists
    use closedBall x (ρ n), ⟨n, rfl⟩, hn.le
  -- Finally, we check that this estimate works for averages as well as integrals.
  simp_rw [average, integral_smul_measure]
  refine Tendsto.smul ?_ (iUnion_cB ▸ this)
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, toReal_inv]
  refine (tendsto_inv₀ ?_).comp ?_
  · exact ENNReal.toReal_ne_zero.mpr ⟨(measure_ball_pos volume x hr0).ne', measure_ball_ne_top⟩
  · apply (ENNReal.tendsto_toReal measure_ball_ne_top).comp
    exact iUnion_cB ▸ tendsto_measure_iUnion_atTop h_mono

/-! Lemma 10.2.3 is in Mathlib: `Pairwise.countable_of_isOpen_disjoint`. -/

section Depth

/-- `δ(x)` in the blueprint. The depth of a point `x` in a set `O` is the supremum of radii of
balls centred on `x` that are subsets of `O`. -/
def depth (O : Set X) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ≥0, ⨆ (_ : ball x r ⊆ O), r

variable {O : Set X} {x y : X}

lemma depth_lt_iff_not_disjoint {d : ℝ} :
    depth O x < ENNReal.ofReal d ↔ ¬Disjoint (ball x d) Oᶜ where
  mp hd := by
    simp_rw [depth, iSup_lt_iff, iSup_le_iff] at hd; obtain ⟨d', ld', hd'⟩ := hd
    have ns := (hd' d.toNNReal).mt; rw [not_le] at ns; specialize ns ld'
    rw [not_subset_iff_exists_mem_notMem] at ns; obtain ⟨y, my, ny⟩ := ns
    have pd := zero_le.trans_lt ld'
    rw [ofReal_pos] at pd; replace pd := Real.coe_toNNReal d pd.le
    rw [pd] at my; exact not_disjoint_iff.mpr ⟨y, my, ny⟩
  mpr hd := by
    obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp hd
    simp_rw [depth, iSup_lt_iff, iSup_le_iff]; use edist x y
    rw [mem_ball'] at my₁; simp_rw [edist_lt_ofReal, my₁, true_and]; intro d' sd; by_contra! h
    rw [← ofReal_coe_nnreal, edist_lt_ofReal, ← mem_ball'] at h
    exact my₂ (sd h)

lemma le_depth_iff_subset {d : ℝ} : ENNReal.ofReal d ≤ depth O x ↔ ball x d ⊆ O := by
  rw [← disjoint_compl_right_iff_subset, ← not_iff_not, not_le]
  exact depth_lt_iff_not_disjoint

/-- A point's depth in an open set `O` is positive iff it lies in `O`. -/
lemma depth_pos_iff_mem (hO : IsOpen O) : 0 < depth O x ↔ x ∈ O := by
  constructor <;> intro h
  · contrapose! h; simp_rw [nonpos_iff_eq_zero, depth, iSup_eq_zero]; intro d hd
    by_contra! dpos; apply absurd _ h; rw [coe_ne_zero, ← zero_lt_iff] at dpos
    exact hd (mem_ball_self dpos)
  · obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h)
    lift ε to ℝ≥0 using εpos.le
    calc
      _ < ofNNReal ε := mod_cast εpos
      _ ≤ _ := le_biSup _ hε

lemma depth_eq_zero_iff_notMem (hO : IsOpen O) : depth O x = 0 ↔ x ∉ O := by
  have := (depth_pos_iff_mem hO (x := x)).not
  rwa [not_lt, nonpos_iff_eq_zero] at this

/-- A point has finite depth in `O` iff `O` is not the whole space. -/
lemma depth_lt_top_iff_ne_univ : depth O x < ⊤ ↔ O ≠ univ := by
  constructor <;> intro h
  · contrapose! h; simp_rw [top_le_iff, depth, iSup₂_eq_top, h, subset_univ, exists_const]
    intro r rlt; lift r to ℝ≥0 using rlt.ne
    use r + 1; exact coe_lt_coe_of_lt (lt_add_one r)
  · obtain ⟨p, np⟩ := (ne_univ_iff_exists_notMem _).mp h
    calc
      _ ≤ edist x p := by
        refine iSup₂_le fun r hr ↦ ?_
        contrapose! hr; rw [not_subset]; use p, ?_, np
        rw [coe_nnreal_eq, edist_dist, ofReal_lt_ofReal_iff_of_nonneg dist_nonneg] at hr
        rwa [mem_ball']
      _ < _ := edist_lt_top ..

/-- A "triangle inequality" for depths. -/
lemma depth_le_edist_add_depth : depth O x ≤ edist x y + depth O y := by
  refine iSup₂_le fun d sd ↦ ?_; contrapose! sd
  rw [← lt_tsub_iff_left, coe_nnreal_eq, edist_dist, ← ENNReal.ofReal_sub _ dist_nonneg,
    depth_lt_iff_not_disjoint, not_disjoint_iff] at sd
  obtain ⟨z, mz₁, mz₂⟩ := sd
  rw [mem_ball, lt_tsub_iff_left] at mz₁
  replace mz₁ := mem_ball'.mpr <| (dist_triangle_right ..).trans_lt mz₁
  exact fun w ↦ mz₂ (w mz₁)

lemma depth_bound_1 (hO : O ≠ univ)
    (h : ¬Disjoint (ball x ((depth O x).toReal / 6)) (ball y ((depth O y).toReal / 6))) :
    x ∈ ball y (3 * ((depth O y).toReal / 6)) := by
  rw [mem_ball]
  have dnt {z : X} : depth O z ≠ ⊤ := (depth_lt_top_iff_ne_univ.mpr hO).ne
  have pre : depth O x / 6 + 5 * depth O x / 6 ≤ depth O x / 6 + 7 * depth O y / 6 := by
    calc
      _ = depth O x := by
        rw [← ENNReal.add_div, ← one_add_mul, show (1 : ℝ≥0∞) + 5 = 6 by norm_num, mul_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
      _ ≤ edist x y + depth O y := depth_le_edist_add_depth
      _ ≤ ENNReal.ofReal ((depth O x).toReal / 6 + (depth O y).toReal / 6) + depth O y := by
        rw [edist_dist]
        exact add_le_add_left (ofReal_le_ofReal (dist_lt_of_not_disjoint_ball h).le) _
      _ ≤ depth O x / 6 + depth O y / 6 + depth O y := by
        rw [ofReal_add (by positivity) (by positivity)]
        iterate 2 rw [ofReal_div_of_pos (by norm_num), ofReal_ofNat, ofReal_toReal dnt]
      _ = _ := by
        rw [show (7 : ℝ≥0∞) = 1 + 6 by norm_num, one_add_mul, ENNReal.add_div, mul_comm,
          ENNReal.mul_div_cancel_right (by norm_num) (by norm_num), add_assoc]
  rw [ENNReal.add_le_add_iff_left (div_ne_top dnt (by norm_num)),
    ENNReal.div_le_iff (by norm_num) (by norm_num),
    ENNReal.div_mul_cancel (by norm_num) (by norm_num), mul_comm,
    ← ENNReal.le_div_iff_mul_le (.inl (by norm_num)) (.inl (by norm_num)),
    ENNReal.mul_div_right_comm] at pre
  calc
    _ < (depth O x).toReal / 6 + (depth O y).toReal / 6 := dist_lt_of_not_disjoint_ball h
    _ ≤ (7 / 5 * depth O y).toReal / 6 + (depth O y).toReal / 6 := by
      gcongr; exact mul_ne_top (by finiteness) dnt
    _ ≤ 2 * (depth O y).toReal / 6 + (depth O y).toReal / 6 := by
      nth_rw 3 [← toReal_ofNat]; rw [← toReal_mul]; gcongr
      · exact mul_ne_top (by finiteness) dnt
      · rw [ENNReal.div_le_iff_le_mul (.inl (by norm_num)) (.inl (by norm_num))]
        norm_num
    _ = _ := by rw [mul_div_assoc, ← add_one_mul, two_add_one_eq_three]

lemma depth_bound_2 (hO : O ≠ univ) (h : x ∈ ball y (3 * ((depth O y).toReal / 6))) :
    (depth O x).toReal / 6 + dist x y ≤ 8 * (depth O y).toReal / 6 := by
  rw [mem_ball] at h
  have ent : edist x y ≠ ⊤ := by finiteness
  have dnt {z : X} : depth O z ≠ ⊤ := (depth_lt_top_iff_ne_univ.mpr hO).ne
  calc
    _ ≤ (edist x y + depth O y).toReal / 6 + dist x y := by
      gcongr
      · rw [ENNReal.add_ne_top]; exact ⟨ent, dnt⟩
      · exact depth_le_edist_add_depth
    _ = (depth O y).toReal / 6 + (7 / 6) * dist x y := by
      rw [ENNReal.toReal_add ent dnt, ← dist_edist]; ring
    _ ≤ (depth O y).toReal / 6 + (7 / 6) * (3 * ((depth O y).toReal / 6)) := by gcongr
    _ = (9 / 2) * (depth O y).toReal / 6 := by ring
    _ ≤ _ := by gcongr; norm_num

lemma depth_bound_3 (hO : O ≠ univ) (h : x ∈ ball y (3 * ((depth O y).toReal / 6))) :
    (depth O y).toReal / 6 + dist y x ≤ 8 * (depth O x).toReal / 6 := by
  rw [mem_ball'] at h
  have dnt {z : X} : depth O z ≠ ⊤ := (depth_lt_top_iff_ne_univ.mpr hO).ne
  have dnt2 : depth O y / 2 ≠ ⊤ := ENNReal.div_ne_top dnt (by norm_num)
  have hti : depth O y ≤ 2 * depth O x := by
    rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl (by norm_num)) (.inl (by norm_num)),
      ← ENNReal.add_le_add_iff_left dnt2, ENNReal.add_halves]
    calc
      _ ≤ edist y x + depth O x := depth_le_edist_add_depth
      _ ≤ _ := by
        gcongr; rw [edist_dist]; apply ofReal_le_of_le_toReal
        rw [toReal_div, toReal_ofNat]; linarith
  calc
    _ ≤ (2 * depth O x).toReal / 6 + 3 * ((depth O y).toReal / 6) := by gcongr; have := @dnt x; finiteness
    _ ≤ (2 * depth O x).toReal / 6 + 3 * ((2 * depth O x).toReal / 6) := by gcongr; have := @dnt x; finiteness
    _ = _ := by rw [toReal_mul, toReal_ofNat]; ring

lemma ball_covering_bounded_intersection
    (hO : IsOpen O ∧ O ≠ univ) {U : Set X} (countU : U.Countable)
    (pdU : U.PairwiseDisjoint fun c ↦ ball c ((depth O c).toReal / 6)) {x : X} (mx : x ∈ O) :
    {c ∈ U | x ∈ ball c (3 * ((depth O c).toReal / 6))}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  set V := {c ∈ U | x ∈ ball c (3 * ((depth O c).toReal / 6))}
  have vbpos : 0 < volume (ball x ((depth O x).toReal / 6)) := by
    refine measure_ball_pos volume x (div_pos ?_ (by norm_num))
    rw [toReal_pos_iff, depth_pos_iff_mem hO.1, depth_lt_top_iff_ne_univ]; exact ⟨mx, hO.2⟩
  have vbnt : volume (ball x ((depth O x).toReal / 6)) ≠ ⊤ := by finiteness
  rw [← ENat.toENNReal_le, Nat.cast_pow, Nat.cast_ofNat, ENat.toENNReal_pow, ENat.toENNReal_ofNat,
    ← ENNReal.mul_le_mul_iff_left vbpos.ne' vbnt]
  have Aeq : (2 : ℝ≥0∞) ^ (3 * a) = defaultA a ^ 3 := by
    rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm]
  calc
    _ = ∑' c : V, volume (ball x ((depth O x).toReal / 6)) := (ENNReal.tsum_set_const _ _).symm
    _ ≤ ∑' c : V, volume (ball c.1 (8 * (depth O c.1).toReal / 6)) :=
      ENNReal.tsum_le_tsum fun ⟨u, mu, xu⟩ ↦
        measure_mono (ball_subset_ball' (depth_bound_2 hO.2 xu))
    _ ≤ 2 ^ (3 * a) * ∑' v : V, volume (ball v.1 ((depth O v.1).toReal / 6)) := by
      rw [← ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun ⟨u, mu, xu⟩ ↦ ?_
      rw [mul_div_assoc, show (8 : ℝ) = 2 ^ 3 by norm_num, Aeq]
      apply measure_ball_two_le_same_iterate
    _ = 2 ^ (3 * a) * volume (⋃ v : V, ball v.1 ((depth O v.1).toReal / 6)) := by
      have VsU : V ⊆ U := sep_subset ..
      haveI : Countable V := by rw [countable_coe_iff]; exact countU.mono VsU
      congr 1
      refine (measure_iUnion (fun ⟨v₁, mv₁⟩ ⟨v₂, mv₂⟩ hn ↦ ?_) (fun _ ↦ measurableSet_ball)).symm
      rw [ne_eq, Subtype.mk.injEq] at hn
      exact pdU (VsU mv₁) (VsU mv₂) hn
    _ ≤ 2 ^ (3 * a) * volume (ball x (8 * (depth O x).toReal / 6)) := by
      gcongr; exact iUnion_subset fun ⟨u, mu, xu⟩ ↦ ball_subset_ball' (depth_bound_3 hO.2 xu)
    _ ≤ _ := by
      rw [show 6 * a = 3 * a + 3 * a by lia, pow_add, mul_assoc]; gcongr
      rw [mul_div_assoc, show (8 : ℝ) = 2 ^ 3 by norm_num, Aeq]
      apply measure_ball_two_le_same_iterate

/-- Lemma 10.2.4, but following the blueprint exactly (with a countable set of centres rather than
functions from `ℕ`). -/
lemma ball_covering' (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (U : Set X) (r : X → ℝ), U.Countable ∧ (U.PairwiseDisjoint fun c ↦ ball c (r c)) ∧
      ⋃ c ∈ U, ball c (3 * r c) = O ∧ (∀ c ∈ U, ¬Disjoint (ball c (7 * r c)) Oᶜ) ∧
      ∀ x ∈ O, {c ∈ U | x ∈ ball c (3 * r c)}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  let W : Set (Set X) := {U | U ⊆ O ∧ U.PairwiseDisjoint fun c ↦ ball c ((depth O c).toReal / 6)}
  obtain ⟨U, maxU⟩ : ∃ U, Maximal (· ∈ W) U := by
    refine zorn_subset _ fun U sU cU ↦ ⟨⋃₀ U, ?_, fun _ ↦ subset_sUnion_of_mem⟩
    simp only [W, sUnion_subset_iff, mem_setOf_eq]
    exact ⟨fun u hu ↦ (sU hu).1, (pairwiseDisjoint_sUnion cU.directedOn).2 fun u hu ↦ (sU hu).2⟩
  have countU : U.Countable := by
    refine maxU.1.2.countable_of_isOpen (fun _ _ ↦ isOpen_ball) (fun u mu ↦ ?_)
    rw [nonempty_ball]; refine div_pos (toReal_pos ?_ ?_) (by norm_num)
    · rw [← EReal.coe_ennreal_pos_iff_ne_zero, EReal.coe_ennreal_pos, depth_pos_iff_mem hO.1]
      exact maxU.1.1 mu
    · rw [← lt_top_iff_ne_top, depth_lt_top_iff_ne_univ]; exact hO.2
  refine ⟨U, fun c ↦ (depth O c).toReal / 6, countU, maxU.1.2, ?_, fun c mc ↦ ?_, fun x mx ↦ ?_⟩
  · refine subset_antisymm (fun x mx ↦ ?_) (fun x mx ↦ ?_)
    · simp only [mem_iUnion₂] at mx; obtain ⟨c, mc, mx⟩ := mx
      refine (le_depth_iff_subset.mp ?_) mx
      rw [← mul_comm_div, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_toReal (depth_lt_top_iff_ne_univ.mpr hO.2).ne]
      nth_rw 2 [← one_mul (depth O _)]; gcongr; norm_num
    · rw [mem_iUnion₂]
      by_cases mxU : x ∈ U
      · refine ⟨x, mxU, mem_ball_self ?_⟩
        simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, div_pos_iff_of_pos_right, toReal_pos_iff]
        rw [depth_pos_iff_mem hO.1, depth_lt_top_iff_ne_univ]; exact ⟨mx, hO.2⟩
      obtain ⟨i, mi, hi⟩ : ∃ i ∈ U,
          ¬Disjoint (ball x ((depth O x).toReal / 6)) (ball i ((depth O i).toReal / 6)) := by
        by_contra! h; apply absurd maxU; simp_rw [not_maximal_iff maxU.1]
        exact ⟨insert x U, ⟨insert_subset mx maxU.1.1, maxU.1.2.insert_of_notMem mxU h⟩,
          ssubset_insert mxU⟩
      use i, mi, depth_bound_1 hO.2 hi
  · rw [← depth_lt_iff_not_disjoint, ← mul_comm_div, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_toReal (depth_lt_top_iff_ne_univ.mpr hO.2).ne]
    nth_rw 1 [← one_mul (depth O _)]
    have dpos := (depth_pos_iff_mem hO.1).mpr (maxU.1.1 mc)
    have dlt := (depth_lt_top_iff_ne_univ (x := c)).mpr hO.2
    exact ENNReal.mul_lt_mul_left dpos.ne' dlt.ne (by norm_num)
  · exact ball_covering_bounded_intersection hO countU maxU.1.2 mx

omit [DoublingMeasure X (defaultA a)] in
lemma ball_covering_finite (hO : IsOpen O ∧ O ≠ univ) {U : Set X} {r' : X → ℝ} (fU : U.Finite)
    (pdU : U.PairwiseDisjoint fun c ↦ ball c (r' c)) (U₃ : ⋃ c ∈ U, ball c (3 * r' c) = O)
    (U₇ : ∀ c ∈ U, ¬Disjoint (ball c (7 * r' c)) Oᶜ)
    (Ubi : ∀ x ∈ O, {c ∈ U | x ∈ ball c (3 * r' c)}.encard ≤ (2 ^ (6 * a) : ℕ)) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ ball (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, 0 < r i → ¬Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, {i | x ∈ ball (c i) (3 * r i)}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  lift U to Finset X using fU
  obtain ⟨p, -⟩ := (ne_univ_iff_exists_notMem _).mp hO.2
  let e := U.equivFin
  let c (i : ℕ) : X := if hi : i < U.card then (e.symm ⟨_, hi⟩).1 else p
  let r (i : ℕ) : ℝ := if hi : i < U.card then r' (c i) else 0
  refine ⟨c, r, fun i mi j mj hn ↦ ?_, ?_, fun i hi ↦ ?_, fun x mx ↦ ?_⟩
  · change Disjoint (ball _ _) (ball _ _)
    by_cases hi : i < U.card; swap
    · simp_rw [r, hi, dite_false, ball_zero, empty_disjoint]
    have hic : c i ∈ U := by simp [c, hi]
    by_cases hj : j < U.card; swap
    · simp_rw [r, hj, dite_false, ball_zero, disjoint_empty]
    have hjc : c j ∈ U := by simp [c, hj]
    simp_rw [r, hi, hj, dite_true]; apply pdU hic hjc
    simp_rw [c, hi, hj, dite_true]; contrapose! hn
    rwa [SetCoe.ext_iff, e.symm.apply_eq_iff_eq, Fin.mk.injEq] at hn
  · rw [← U₃]; apply subset_antisymm
    · refine iUnion_subset fun i ↦ ?_
      unfold r; split_ifs with hi
      · convert subset_iUnion₂ (c i) _
        · rfl
        · simp_rw [c, hi, dite_true, Subtype.coe_prop]
      · simp
    · refine iUnion₂_subset fun x mx ↦ ?_
      let i := e ⟨x, mx⟩; convert subset_iUnion _ i.1
      simp_rw [r, c, i.2, dite_true, i, Fin.eta, Equiv.symm_apply_apply]
  · unfold r at hi ⊢; split_ifs with hi'
    · simp_rw [Finset.mem_coe] at U₇
      have mi : c i ∈ U := by simp_rw [c, hi', dite_true]; exact Finset.coe_mem _
      exact U₇ _ mi
    · simp_rw [hi', dite_false, lt_self_iff_false] at hi
  · calc
      _ = {i | ¬i < U.card ∧ x ∈ ball (c i) (3 * r i)}.encard +
          {i | i < U.card ∧ x ∈ ball (c i) (3 * r i)}.encard := by
        have : {i | x ∈ ball (c i) (3 * r i)} =
            {i | ¬ i < U.card ∧ x ∈ ball (c i) (3 * r i)} ∪
                {i | i < U.card ∧ x ∈ ball (c i) (3 * r i)} := by
          ext i; refine ⟨fun hx ↦ ?_, fun h ↦ ?_⟩
          · by_cases hi : i < U.card
            exacts [Or.inr ⟨hi, hx⟩, Or.inl ⟨hi, hx⟩]
          · rcases h with ⟨_, hx⟩ | ⟨_, hx⟩ <;> exact hx
        rw [← encard_union_eq]
        · congr
        · exact disjoint_left.mpr fun i mi₁ mi₂ ↦ mi₁.1 mi₂.1
      _ = 0 + {u ∈ SetLike.coe U | x ∈ ball u (3 * r' u)}.encard := by
        congr
        · simp_rw [encard_eq_zero, eq_empty_iff_forall_notMem, mem_setOf_eq, not_and]; intro i hi
          simp [r, hi]
        · set A := {i | i < U.card ∧ x ∈ ball (c i) (3 * r i)}
          set B := {u ∈ SetLike.coe U | x ∈ ball u (3 * r' u)}
          let f (i : A) : B := ⟨e.symm ⟨i.1, i.2.1⟩, by
            refine ⟨Subtype.coe_prop _, ?_⟩
            have := i.2.2; simp_rw [r, c, i.2.1, dite_true] at this; exact this⟩
          let g (u : B) : A := ⟨e ⟨u.1, u.2.1⟩, by
            simp_rw [A, r, c, mem_setOf_eq, Fin.is_lt, dite_true, Fin.eta, Equiv.symm_apply_apply,
              u.2.2, true_and]⟩
          let eqv : A ≃ B := ⟨f, g, fun i ↦ by simp [f, g], fun u ↦ by simp [f, g]⟩
          exact encard_congr eqv
      _ ≤ _ := by rw [zero_add]; exact Ubi x mx

/-- Lemma 10.2.4. -/
theorem ball_covering (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ ball (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, 0 < r i → ¬Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, {i | x ∈ ball (c i) (3 * r i)}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  obtain ⟨U, r', countU, pdU, U₃, U₇, Ubi⟩ := ball_covering' hO
  obtain fU | iU := U.finite_or_infinite
  · exact ball_covering_finite hO fU pdU U₃ U₇ Ubi
  · let e := (countable_infinite_iff_nonempty_denumerable.mp ⟨countU, iU⟩).some.eqv
    let c (i : ℕ) : X := (e.symm i).1
    let r (i : ℕ) : ℝ := r' (c i)
    refine ⟨c, r, fun i mi j mj hn ↦ ?_, ?_, fun i hi ↦ ?_, fun x mx ↦ ?_⟩
    · have hic : c i ∈ U := by simp [c]
      have hjc : c j ∈ U := by simp [c]
      apply pdU hic hjc; simp_rw [c]; contrapose! hn
      rwa [SetCoe.ext_iff, e.symm.apply_eq_iff_eq] at hn
    · rw [← U₃]; apply subset_antisymm
      · refine iUnion_subset fun i ↦ ?_
        unfold r; convert subset_iUnion₂ (c i) _
        · rfl
        · simp_rw [c, Subtype.coe_prop]
      · refine iUnion₂_subset fun x mx ↦ ?_
        let i := e ⟨x, mx⟩; convert subset_iUnion _ i
        simp_rw [r, c, i, Equiv.symm_apply_apply]
    · unfold r at hi ⊢
      have mi : c i ∈ U := by simp_rw [c, Subtype.coe_prop]
      exact U₇ _ mi
    · calc
        _ = {u ∈ U | x ∈ ball u (3 * r' u)}.encard := by
          set A := {i | x ∈ ball (c i) (3 * r i)}
          set B := {u ∈ U | x ∈ ball u (3 * r' u)}
          let f (i : A) : B := ⟨e.symm i, by
            refine ⟨Subtype.coe_prop _, ?_⟩
            have := i.2; simp_rw [A, mem_setOf_eq, r, c] at this; exact this⟩
          let g (u : B) : A := ⟨e ⟨u.1, u.2.1⟩, by
            simp_rw [A, r, c, mem_setOf_eq, Equiv.symm_apply_apply, u.2.2]⟩
          let eqv : A ≃ B := ⟨f, g, fun i ↦ by simp [f, g], fun u ↦ by simp [f, g]⟩
          exact encard_congr eqv
        _ ≤ _ := Ubi x mx

end Depth

/-! ### Lemma 10.2.5

Lemma 10.2.5 has an annoying case distinction between the case `E_α ≠ X` (general case) and
`E_α = X` (finite case). It isn't easy to get rid of this case distinction.

In the formalization we state most properties of Lemma 10.2.5 twice, once for each case
(in some cases the condition is vacuous in the finite case, and then we omit it)

We could have tried harder to uniformize the cases, but in the finite case there is really only set
`B*_j`, and in the general case it is convenient to index `B*_j` by the natural numbers.
-/

/-- The property specifying whether we are in the "general case". -/
def GeneralCase (f : X → ℂ) (α : ℝ≥0∞) : Prop :=
  ∃ x, α ≥ globalMaximalFunction (X := X) volume 1 f x

/-- In the finite case, the volume of `X` is finite. -/
lemma volume_lt_of_not_GeneralCase
    (hf : BoundedFiniteSupport f) (h : ¬ GeneralCase f α) (hα : 0 < α) :
    volume (univ : Set X) < ∞ := by
  simp only [GeneralCase, not_exists, not_le] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hα.ne'
  refine lt_of_le_of_lt (eq_univ_iff_forall.mpr h ▸ maximal_theorem' α hf) ?_ |>.ne
  exact mul_lt_top coe_lt_top (hf.memLp 1).eLpNorm_lt_top

private lemma isFiniteMeasure_of_not_generalCase
    (hf : BoundedFiniteSupport f) (h : ¬ GeneralCase f α) (hα : 0 < α) :
    IsFiniteMeasure (volume : Measure X) :=
  (isFiniteMeasure_iff _).mpr <| volume_lt_of_not_GeneralCase hf h hα

lemma isOpen_MB_preimage_Ioi (hX : GeneralCase f α) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α) ∧
    globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ :=
  have ⟨x, hx⟩ := hX
  ⟨lowerSemiContinuous_globalMaximalFunction.isOpen_preimage _,
    (ne_univ_iff_exists_notMem _).mpr ⟨x, by simpa using hx⟩⟩

/-- The center of B_j in the proof of Lemma 10.2.5 (general case). -/
def czCenter (hX : GeneralCase f α) (i : ℕ) : X :=
  ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose i

/-- The radius of B_j in the proof of Lemma 10.2.5 (general case). -/
def czRadius (hX : GeneralCase f α) (i : ℕ) : ℝ :=
  ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose i

/-- The ball B_j in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hX i) (czRadius hX i)

/-- The ball B_j' introduced below Lemma 10.2.5 (general case). -/
abbrev czBall6 (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hX i) (6 * czRadius hX i)

/-- The ball B_j* in Lemma 10.2.5 (general case). -/
abbrev czBall3 (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hX i) (3 * czRadius hX i)

/-- The ball B_j** in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall7 (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hX i) (7 * czRadius hX i)

lemma czBall_pairwiseDisjoint {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ ball (czCenter hX i) (czRadius hX i) :=
  ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.1

lemma iUnion_czBall3 {hX : GeneralCase f α} :
    ⋃ i, czBall3 hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_czBall7 {hX : GeneralCase f α} {i : ℕ} (hi : 0 < czRadius hX i) :
    ¬Disjoint (czBall7 hX i) (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ :=
  ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.1 i hi

private lemma czBall_subset_czBall {hX : GeneralCase f α} {i : ℕ} {b c : ℝ}
    (hb : 0 ≤ b := by norm_num) (hbc : b ≤ c := by norm_num) :
    ball (czCenter hX i) (b * czRadius hX i) ⊆ ball (czCenter hX i) (c * czRadius hX i) := by
  by_cases hr : czRadius hX i ≥ 0
  · exact ball_subset_ball <| mul_le_mul_of_nonneg_right hbc hr
  · simp [ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos hb (le_of_not_ge hr)]

/-- Part of Lemma 10.2.5 (general case). -/
lemma encard_czBall3_le {hX : GeneralCase f α} {y : X} :
    {i | y ∈ czBall3 hX i}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  by_cases hy : α < globalMaximalFunction volume 1 f y
  · exact ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.2 y hy
  · suffices ∀ i, i ∉ {i | y ∈ czBall3 hX i} by simp [eq_empty_of_forall_notMem this, -mem_ball]
    simpa [← not_exists, ← mem_iUnion, iUnion_czBall3, -mem_ball] using hy

lemma mem_czBall3_finite {hX : GeneralCase f α} {y : X} :
    {i | y ∈ czBall3 hX i}.Finite :=
  finite_of_encard_le_coe encard_czBall3_le

/-- `Q_i` in the proof of Lemma 10.2.5 (general case). -/
def czPartition (hX : GeneralCase f α) (i : ℕ) : Set X :=
  czBall3 hX i \ ((⋃ j < i, czPartition hX j) ∪ ⋃ j > i, czBall hX j)

@[measurability]
private lemma MeasurableSet.czPartition (hX : GeneralCase f α) (i : ℕ) :
    MeasurableSet (czPartition hX i) := by
  refine i.strong_induction_on (fun j hj ↦ ?_)
  unfold _root_.czPartition
  apply measurableSet_ball.diff ∘ (MeasurableSet.biUnion (to_countable _) hj).union
  exact MeasurableSet.biUnion (to_countable _) (fun _ _ ↦ measurableSet_ball)

lemma czBall_subset_czPartition {hX : GeneralCase f α} {i : ℕ} :
    czBall hX i ⊆ czPartition hX i := by
  intro r hr
  rw [mem_ball] at hr
  unfold czPartition
  apply mem_diff_of_mem (by rw [mem_ball]; linarith [dist_nonneg.trans_lt hr])
  simp only [mem_union, mem_iUnion, mem_ball, not_or, not_exists, not_lt]
  refine ⟨?_, fun j hj ↦ by
    refine le_of_not_gt (disjoint_left.mp (czBall_pairwiseDisjoint ?_ ?_ hj.ne) hr) <;> tauto⟩
  unfold czPartition
  simp only [mem_diff, mem_ball, mem_union, mem_iUnion, not_or, not_and, not_not]
  exact fun _ _ _ _ ↦ by use i

lemma czPartition_subset_czBall3 {hX : GeneralCase f α} {i : ℕ} :
    czPartition hX i ⊆ czBall3 hX i := by
  rw [czPartition]; exact diff_subset

private lemma czPartition_subset_czBall7 {hX : GeneralCase f α} {i : ℕ} :
    czPartition hX i ⊆ czBall7 hX i :=
  le_trans czPartition_subset_czBall3 czBall_subset_czBall

lemma czPartition_pairwiseDisjoint {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ czPartition hX i := by
  simp only [pairwiseDisjoint_iff, mem_univ, forall_const]
  intro i k hik
  have ⟨x, hxi, hxk⟩ := inter_nonempty.mp hik
  have (t d) (hx : x ∈ czPartition hX t) (hd : t < d) : x ∉ czPartition hX d := by
    have : czPartition hX t ⊆ ⋃ j < d, czPartition hX j := subset_biUnion_of_mem hd
    rw [czPartition]
    exact notMem_diff_of_mem <| mem_union_left _ (this hx)
  have : _ ∧ _ := ⟨this i k hxi |>.mt (· hxk), this k i hxk |>.mt (· hxi)⟩
  lia

lemma czPartition_pairwiseDisjoint' {hX : GeneralCase f α}
    {x : X} {i j : ℕ} (hi : x ∈ czPartition hX i) (hj : x ∈ czPartition hX j) :
    i = j := by
  have := czPartition_pairwiseDisjoint (hX := hX)
  apply pairwiseDisjoint_iff.mp this (mem_univ i) (mem_univ j)
  exact inter_nonempty.mp <| .intro x ⟨hi, hj⟩

private lemma czPartition_pairwise_disjoint_on {hX : GeneralCase f α} :
    Pairwise (Disjoint on czPartition hX) :=
  fun i j ↦ czPartition_pairwiseDisjoint (mem_univ i) (mem_univ j)

lemma iUnion_czPartition {hX : GeneralCase f α} :
    ⋃ i, czPartition hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α := by
  rw [← iUnion_czBall3 (hX := hX)]
  refine ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have : ⋃ i, czPartition hX i ⊆ ⋃ i, czBall3 hX i := fun y hy ↦
      have ⟨r, hr⟩ := mem_iUnion.mp hy
      mem_iUnion_of_mem r (czPartition_subset_czBall3 hr)
    exact this hx
  · rw [mem_iUnion] at hx ⊢
    by_contra! hp
    obtain ⟨g, hg⟩ := hx
    have ⟨t, ht⟩ : ∃ i, x ∈ (⋃ j < i, czPartition hX j) ∪ ⋃ j > i, czBall hX j := by
      by_contra! hb
      absurd hp g
      rw [czPartition, mem_diff]
      exact ⟨hg, hb g⟩
    have : ⋃ j > t, czBall hX j ⊆ ⋃ j > t, czPartition hX j :=
      iUnion₂_mono fun i j ↦ czBall_subset_czPartition (i := i)
    have := (mem_or_mem_of_mem_union ht).imp_right (this ·)
    simp_all

private lemma globalMaximalFunction_preimage_finite
    (hα : 0 < α) (hf : BoundedFiniteSupport f) :
    volume (globalMaximalFunction volume 1 f ⁻¹' Ioi α) < ∞ := by
  have := hasStrongType_globalMaximalFunction one_pos one_lt_two f (hf.memLp 2) |>.2.trans_lt <|
    mul_lt_top coe_lt_top (hf.memLp 2).eLpNorm_lt_top
  contrapose! this
  set s := (globalMaximalFunction volume 1 f ⁻¹' Ioi α)
  calc ∞
    _ = (∫⁻ x in s, α ^ 2) ^ (1 / 2 : ℝ) := by simp [top_le_iff.mp this, ENNReal.pow_ne_zero hα.ne']
    _ ≤ (∫⁻ x, ‖globalMaximalFunction volume 1 f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
      refine rpow_le_rpow ?_ (by norm_num)
      refine le_trans (setLIntegral_mono_ae ?_ ?_) (setLIntegral_le_lintegral s _)
      · exact AEStronglyMeasurable.globalMaximalFunction.aemeasurable.pow_const 2 |>.restrict
      · exact Eventually.of_forall fun x hx ↦ pow_le_pow_left' (le_of_lt <| by simpa [s] using hx) 2
    _ = eLpNorm (globalMaximalFunction volume 1 f) 2 volume := by simp [eLpNorm, eLpNorm']

private lemma volume_czPartition_lt_top (hX : GeneralCase f α) (i : ℕ) :
    volume (czPartition hX i) < ∞ :=
  lt_of_le_of_lt (measure_mono czPartition_subset_czBall3) measure_ball_lt_top

private lemma volume_czBall7_le (hX : GeneralCase f α) (i : ℕ) :
    volume (czBall7 hX i) ≤ 2 ^ (3 * a) * volume (czPartition hX i) := calc
  _ ≤ volume (ball (czCenter hX i) (2 ^ 3 * czRadius hX i)) := measure_mono czBall_subset_czBall
  _ ≤ (defaultA a) ^ 3 * volume (ball (czCenter hX i) (czRadius hX i)) :=
    measure_ball_two_le_same_iterate _ _ 3
  _ ≤ _ := by
    rw [Nat.cast_pow, ← pow_mul, mul_comm a 3, Nat.cast_ofNat]
    gcongr; exact czBall_subset_czPartition

private lemma volume_czBall3_le (hX : GeneralCase f α) (i : ℕ) :
    volume (czBall3 hX i) ≤ 2 ^ (2 * a) * volume (czBall hX i) := calc
  _ ≤ volume (ball (czCenter hX i) (2 ^ 2 * czRadius hX i)) := measure_mono czBall_subset_czBall
  _ ≤ 2 ^ (2 * a) * volume (czBall hX i) :=
    le_of_le_of_eq (measure_ball_two_le_same_iterate _ _ 2) <| by simp [← pow_mul, mul_comm a 2]

-- Inequality (10.2.30)
private lemma laverage_czBall7_le (hX : GeneralCase f α) (i : ℕ) :
    ⨍⁻ x in czBall7 hX i, ‖f x‖ₑ ∂volume ≤ α := by
  by_cases hi : czRadius hX i ≤ 0
  · simp [ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 7 by norm_num) hi]
  have ⟨y, hy7, hy⟩ := not_disjoint_iff.mp <| not_disjoint_czBall7 (lt_of_not_ge hi)
  simp only [mem_compl_iff, mem_preimage, Nat.cast_pow, Nat.cast_ofNat, mem_Ioi, not_lt] at hy
  refine le_trans ?_ hy
  simpa using laverage_le_globalMaximalFunction (μ := volume) hy7

open scoped Classical in
variable (f) in
/-- The function `g` in Lemma 10.2.5. (both cases) -/
def czApproximation (α : ℝ≥0∞) (x : X) : ℂ :=
  if hX : GeneralCase f α then
    if hx : ∃ j, x ∈ czPartition hX j then ⨍ y in czPartition hX hx.choose, f y else f x
  else ⨍ y, f y

lemma czApproximation_def_of_mem {hX : GeneralCase f α} {x : X}
    {i : ℕ} (hx : x ∈ czPartition hX i) :
    czApproximation f α x = ⨍ y in czPartition hX i, f y := by
  have : ∃ i, x ∈ czPartition hX i := ⟨i, hx⟩
  simp [czApproximation, hX, this, czPartition_pairwiseDisjoint' this.choose_spec hx]

lemma czApproximation_def_of_notMem {x : X} (hX : GeneralCase f α)
    (hx : x ∉ globalMaximalFunction volume 1 f ⁻¹' Ioi α) :
    czApproximation f α x = f x := by
  rw [← iUnion_czPartition (hX := hX), mem_iUnion, not_exists] at hx
  simp only [czApproximation, hX, ↓reduceDIte, hx, exists_const]

lemma czApproximation_def_of_volume_lt {x : X}
    (hX : ¬ GeneralCase f α) : czApproximation f α x = ⨍ y, f y := by
  simp [czApproximation, hX]

private lemma lintegral_czPartition_le {hX : GeneralCase f α} (i : ℕ) :
    ∫⁻ x in czPartition hX i, ‖czApproximation f α x‖ₑ ≤
    ∫⁻ x in czPartition hX i, ‖f x‖ₑ := calc
  _ = ∫⁻ x in czPartition hX i, ‖⨍ y in czPartition hX i, f y‖ₑ := by
    apply setLIntegral_congr_fun_ae (MeasurableSet.czPartition hX i)
    exact Eventually.of_forall fun x hx ↦ by rw [czApproximation_def_of_mem hx]
  _ = ‖⨍ y in czPartition hX i, f y‖ₑ * volume (czPartition hX i) := setLIntegral_const _ _
  _ ≤ (⨍⁻ y in czPartition hX i, ‖f y‖ₑ ∂volume) * volume (czPartition hX i) :=
    mul_le_mul_left (enorm_integral_le_lintegral_enorm f) _
  _ = _ := by rw [mul_comm, measure_mul_setLAverage _ (volume_czPartition_lt_top hX i).ne]

/-- The function `b_i` in Lemma 10.2.5 (general case). -/
def czRemainder' (hX : GeneralCase f α) (i : ℕ) (x : X) : ℂ :=
  (czPartition hX i).indicator (f - czApproximation f α) x

private lemma czRemainder'_eq_zero (hX : GeneralCase f α) {i : ℕ} (hi : czRadius hX i ≤ 0) :
    czRemainder' hX i = 0 := by
  suffices czPartition hX i ⊆ ∅ by ext; simp [czRemainder', eq_empty_of_subset_empty this]
  apply subset_of_subset_of_eq czPartition_subset_czBall7
  exact ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos (by norm_num) hi

variable (f) in
/-- The function `b = ∑ⱼ bⱼ` introduced below Lemma 10.2.5.
In the finite case, we also use this as the function `b = b₁` in Lemma 10.2.5.
We choose a more convenient definition, but prove in `tsum_czRemainder'` that this is the same. -/
def czRemainder (α : ℝ≥0∞) (x : X) : ℂ :=
  f x - czApproximation f α x

/-- Part of Lemma 10.2.5, this is essentially (10.2.16) (both cases). -/
lemma tsum_czRemainder' (hX : GeneralCase f α) (x : X) :
    ∑' i, czRemainder' hX i x = czRemainder f α x := by
  simp only [czRemainder', czRemainder]
  by_cases hx : ∃ j, x ∈ czPartition hX j
  · have ⟨j, hj⟩ := hx
    rw [tsum_eq_single j, indicator_of_mem hj]
    · rfl
    · refine fun i hi ↦ indicator_of_notMem ?_ _
      exact (czPartition_pairwise_disjoint_on hi).notMem_of_mem_right hj
  · simp only [czApproximation, hX, reduceDIte, hx, sub_self]
    convert tsum_zero with i
    exact indicator_of_notMem (fun hi ↦ hx ⟨i, hi⟩) _

open scoped Classical in
/-- Part of Lemma 10.2.5 (both cases). -/
lemma aemeasurable_czApproximation {hf : AEMeasurable f} : AEMeasurable (czApproximation f α) := by
  by_cases hX : GeneralCase f α; swap
  · unfold czApproximation; simp [hX]
  let czA (x : X) := -- Measurable version of `czApproximation f α`
    if hx : ∃ j, x ∈ czPartition hX j then ⨍ y in czPartition hX hx.choose, f y else hf.mk f x
  refine ⟨czA, fun T hT ↦ ?_, hf.ae_eq_mk.mono fun x h ↦ by simp [czApproximation, czA, hX, h]⟩
  let S := {x : X | ∃ j, x ∈ czPartition hX j}ᶜ ∩ (hf.mk f) ⁻¹' T
  have : czA ⁻¹' T = S ∪ ⋃₀ (czPartition hX '' {i | ⨍ y in czPartition hX i, f y ∈ T}) := by
    refine ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_cases hx : ∃ j, x ∈ czPartition hX j
      · refine Or.inr ⟨czPartition hX hx.choose, ⟨mem_image_of_mem _ ?_, hx.choose_spec⟩⟩
        simpa [czA, hx] using h
      · exact Or.inl ⟨hx, by simpa [czA, hx, hX] using h⟩
    · cases h with
      | inl h => simpa [czA, mem_setOf_eq ▸ mem_setOf_eq ▸ h.1] using h.2
      | inr h => obtain ⟨_, ⟨⟨i, ⟨hi, rfl⟩⟩, hxi⟩⟩ := h
                 have hx : ∃ j, x ∈ czPartition hX j := ⟨i, hxi⟩
                 simpa [czA, hx, czPartition_pairwiseDisjoint' hx.choose_spec hxi] using hi
  rw [this]
  have := Measurable.exists (MeasurableSet.czPartition hX · |>.mem)
  apply MeasurableSet.union (by measurability) ∘ MeasurableSet.sUnion ((to_countable _).image _)
  simp [MeasurableSet.czPartition hX]

protected lemma AEMeasurable.czRemainder' {hf : AEMeasurable f} (hX : GeneralCase f α) (i : ℕ) :
    AEMeasurable (czRemainder' hX i) := by
  unfold czRemainder'
  apply (aemeasurable_indicator_iff (MeasurableSet.czPartition hX i)).mpr
  exact (hf.sub <| aemeasurable_czApproximation (hf := hf)).restrict

/-- Part of Lemma 10.2.5 (both cases). -/
@[fun_prop]
protected lemma BoundedFiniteSupport.czApproximation {α : ℝ≥0∞} (hα : 0 < α)
    (hf : BoundedFiniteSupport f) : BoundedFiniteSupport (czApproximation f α) := by
  by_cases h : Nonempty X; swap
  · have := not_nonempty_iff.mp h; constructor <;> simp
  constructor
  · use (aemeasurable_czApproximation (hf := aemeasurable hf)).aestronglyMeasurable
    refine lt_of_le_of_lt ?_ hf.eLpNorm_lt_top
    apply essSup_le_of_ae_le _ <| (ENNReal.ae_le_essSup (‖f ·‖ₑ)).mono (fun x h ↦ ?_)
    by_cases hX : GeneralCase f α
    · by_cases hx : ∃ j, x ∈ czPartition hX j
      · have ⟨j, hj⟩ := hx
        rw [czApproximation_def_of_mem hj]
        exact (enorm_integral_le_lintegral_enorm _).trans (setLAverage_le_essSup _ _)
      · simp [czApproximation, eLpNormEssSup, hX, hx, h]
    · simp only [czApproximation, hX, reduceDIte]
      exact (enorm_integral_le_lintegral_enorm _).trans (laverage_le_essSup _)
  · by_cases hX : GeneralCase f α; swap
    · exact lt_of_le_of_lt (measure_mono (subset_univ _)) <| volume_lt_of_not_GeneralCase hf hX hα
    calc volume (support (czApproximation f α))
      _ ≤ volume (globalMaximalFunction volume 1 f ⁻¹' Ioi α ∪ support f) := by
        gcongr
        intro x mem_supp
        by_cases hx : ∃ j, x ∈ czPartition hX j
        · left; rw [← iUnion_czPartition (hX := hX)]; exact (mem_iUnion.mpr hx)
        · right; simpa [czApproximation, hX, hx] using mem_supp
      _ ≤ volume _ + volume (support f) := measure_union_le _ _
      _ < ∞ := add_lt_top.mpr ⟨globalMaximalFunction_preimage_finite hα hf, hf.measure_support_lt⟩

@[fun_prop]
protected lemma BoundedFiniteSupport.czRemainder (hα : 0 < α) {hf : BoundedFiniteSupport f} :
    BoundedFiniteSupport (czRemainder f α) :=
  hf.sub (hf.czApproximation hα)

protected lemma BoundedFiniteSupport.czRemainder' (hα : 0 < α) {hf : BoundedFiniteSupport f}
    (hX : GeneralCase f α) (i : ℕ) :
    BoundedFiniteSupport (czRemainder' hX i) :=
  (hf.sub (hf.czApproximation hα)).indicator (MeasurableSet.czPartition hX i)

protected lemma AEMeasurable.czRemainder (hα : 0 < α) {hf : BoundedFiniteSupport f} :
    AEMeasurable (czRemainder f α) := by
  fun_prop (discharger := assumption)

/-- Part of Lemma 10.2.5, equation (10.2.16) (both cases).
This is true by definition, the work lies in `tsum_czRemainder'` -/
lemma czApproximation_add_czRemainder {x : X} :
    czApproximation f α x + czRemainder f α x = f x := by
  simp [czApproximation, czRemainder]

private lemma α_le_mul_α : α ≤ 2 ^ (3 * a) * α := by
  nth_rw 1 [← one_mul α]; gcongr; exact_mod_cast Nat.one_le_two_pow

-- Equation (10.2.17), finite case
private lemma enorm_czApproximation_le_finite
    (hα : ⨍⁻ x, ‖f x‖ₑ ≤ α) (hX : ¬ GeneralCase f α) :
    ∀ᵐ x, ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  simp only [czApproximation, hX, reduceDIte]
  by_cases h : Nonempty X
  · exact eventually_const.mpr <| (enorm_integral_le_lintegral_enorm f).trans (hα.trans α_le_mul_α)
  · exact eventually_of_mem univ_mem (by tauto)

/-- Equation (10.2.17) specialized to the general case. -/
lemma enorm_czApproximation_le_infinite {hf : BoundedFiniteSupport f} (hX : GeneralCase f α) :
    ∀ᵐ x, ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  have h₁ (x : X) (hx : ∃ i, x ∈ czPartition hX i) : ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α :=
    have ⟨i, hi⟩ := hx
    calc ‖czApproximation f α x‖ₑ
      _ = ‖⨍ x in czPartition hX i, f x‖ₑ := by rw [czApproximation_def_of_mem hi]
      _ ≤ ⨍⁻ x in czPartition hX i, ‖f x‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
      _ ≤ (volume (czPartition hX i))⁻¹ * ∫⁻ x in czPartition hX i, ‖f x‖ₑ := by
        simp [laverage]
      _ ≤ 2 ^ (3 * a) * (volume (czBall7 hX i))⁻¹ * ∫⁻ x in czPartition hX i, ‖f x‖ₑ := by
        apply mul_le_mul_left
        have := (ENNReal.inv_mul_le_iff (by simp) (by simp)).mpr <| volume_czBall7_le hX i
        rwa [← ENNReal.inv_le_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv] at this
      _ ≤ 2 ^ (3 * a) * (volume (czBall7 hX i))⁻¹ * ∫⁻ x in czBall7 hX i, ‖f x‖ₑ :=
        mul_le_mul_right (lintegral_mono_set czPartition_subset_czBall7) _
      _ ≤ 2 ^ (3 * a) * α := by
        rw [mul_assoc]; gcongr; simpa [laverage] using laverage_czBall7_le hX i
  have h₂ : ∀ᵐ x, ¬(∃ i, x ∈ czPartition hX i) → ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α :=
    (lebesgue_differentiation hf).mono fun x ⟨c, r, lim, _, x_mem_ball⟩ hx ↦ by
      have le_α := hx
      rw [← mem_iUnion, iUnion_czPartition, mem_preimage, mem_Ioi, not_lt] at le_α
      simp only [czApproximation, hX, reduceDIte, hx]
      refine le_of_tendsto lim.enorm <| Eventually.of_forall fun i ↦ ?_
      apply le_trans (enorm_integral_le_lintegral_enorm f)
      exact le_trans (laverage_le_globalMaximalFunction (x_mem_ball i)) <| le_α.trans α_le_mul_α
  simpa only [← or_imp, em, forall_const] using eventually_and.mpr ⟨Eventually.of_forall h₁, h₂⟩

/-- Part of Lemma 10.2.5, equation (10.2.17) (both cases). -/
lemma enorm_czApproximation_le
    {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ ≤ α) :
    ∀ᵐ x, ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α :=
  by_cases (enorm_czApproximation_le_infinite (hf := hf)) (enorm_czApproximation_le_finite hα)

-- Equation (10.2.18), finite case
private lemma eLpNorm_czApproximation_le_finite
    (hf : BoundedFiniteSupport f) (hα : 0 < α) (hX : ¬ GeneralCase f α) :
    eLpNorm (czApproximation f α) 1 volume ≤ eLpNorm f 1 volume := by
  by_cases h : Nonempty X; swap
  · simp [not_nonempty_iff.mp h]
  calc
    _ = ‖⨍ x, f x‖ₑ * volume univ := by
      unfold czApproximation; simp [hX, eLpNorm_const _ one_pos.ne' (NeZero.ne volume)]
    _ ≤ (⨍⁻ x, ‖f x‖ₑ ∂volume) * volume (univ : Set X) :=
      mul_le_mul_left (enorm_integral_le_lintegral_enorm f) _
    _ = eLpNorm f 1 volume := by
      simp [mul_comm _ (volume univ), eLpNorm, eLpNorm', laverage, ← mul_assoc,
        ENNReal.mul_inv_cancel (NeZero.ne (volume univ)) (volume_lt_of_not_GeneralCase hf hX hα).ne]

-- Equation (10.2.18), infinite case
private lemma eLpNorm_czApproximation_le_infinite (hX : GeneralCase f α) :
    eLpNorm (czApproximation f α) 1 volume ≤ eLpNorm f 1 volume := by
  simp only [eLpNorm, one_ne_zero, reduceIte, one_ne_top, eLpNorm', toReal_one, rpow_one,
    ne_eq, not_false_eq_true, div_self]
  have hmeas : MeasurableSet (univ \ ⋃ i, czPartition hX i) := by measurability
  have := union_univ _ ▸ @union_diff_self X (⋃ i, czPartition hX i) univ
  repeat rw [← setLIntegral_univ (μ := volume), ← this, lintegral_union hmeas disjoint_sdiff_right,
    lintegral_iUnion (MeasurableSet.czPartition hX) <| czPartition_pairwise_disjoint_on]
  -- gcongr tsum ?_ + ?_
  apply add_le_add
  · apply ENNReal.tsum_le_tsum
    intro _
    apply lintegral_czPartition_le
  · simp only [union_diff_self, union_univ]
    apply le_of_eq ∘ setLIntegral_congr_fun_ae (by measurability)
    exact Eventually.of_forall (fun x hx ↦ by simp_all [czApproximation])

/-- Part of Lemma 10.2.5, equation (10.2.18) (both cases). -/
lemma eLpNorm_czApproximation_le
    {hf : BoundedFiniteSupport f} (hα : 0 < α) :
    eLpNorm (czApproximation f α) 1 volume ≤ eLpNorm f 1 volume :=
  by_cases eLpNorm_czApproximation_le_infinite (eLpNorm_czApproximation_le_finite hf hα)

/-- Part of Lemma 10.2.5, equation (10.2.19) (general case). -/
lemma support_czRemainder'_subset {hX : GeneralCase f α} {i : ℕ} :
    support (czRemainder' hX i) ⊆ czBall3 hX i := by
  refine subset_trans (fun x hx ↦ ?_) czPartition_subset_czBall3
  rw [mem_support, czRemainder', ne_eq, indicator_apply_eq_zero, Classical.not_imp] at hx
  exact hx.1

/-- Part of Lemma 10.2.5, equation (10.2.20) (general case). -/
lemma integral_czRemainder' {hX : GeneralCase f α} {i : ℕ} :
    ∫ x, czRemainder' hX i x = 0 := by
  unfold czRemainder'
  rw [integral_indicator (MeasurableSet.czPartition hX i)]
  rw [← setAverage_sub_setAverage (volume_czPartition_lt_top hX i).ne f]
  refine setIntegral_congr_fun (MeasurableSet.czPartition hX i) <| fun x hx ↦ ?_
  rw [Pi.sub_apply, czApproximation_def_of_mem hx]

/-- Part of Lemma 10.2.5, equation (10.2.20) (finite case). -/
lemma integral_czRemainder {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    ∫ x, czRemainder f α x = 0 := by
  have := isFiniteMeasure_of_not_generalCase hf hX hα
  simpa [czRemainder, czApproximation, hX] using integral_sub_average volume f

-- Inequality (10.2.32)
private lemma ineq_10_2_32 (hf : BoundedFiniteSupport f) {hX : GeneralCase f α}
    {i : ℕ} :
    eLpNorm (czRemainder' hX i) 1 volume ≤ 2 * (∫⁻ x in czPartition hX i, ‖f x‖ₑ) := calc
  _ = ∫⁻ x in czPartition hX i, ‖f x - czApproximation f α x‖ₑ := by
    simp [czRemainder', eLpNorm, eLpNorm', enorm_indicator_eq_indicator_enorm,
      lintegral_indicator <| MeasurableSet.czPartition hX i]
  _ ≤ ∫⁻ x in czPartition hX i, ‖f x‖ₑ + ‖czApproximation f α x‖ₑ :=
    lintegral_mono (fun x ↦ enorm_sub_le)
  _ = (∫⁻ x in _, ‖f x‖ₑ) + ∫⁻ x in _, ‖_‖ₑ := lintegral_add_left' hf.aemeasurable.enorm.restrict _
  _ ≤ 2 * (∫⁻ x in czPartition hX i, ‖f x‖ₑ) := by
    rw [two_mul]; exact add_le_add_right (lintegral_czPartition_le i) _

/-- Part of Lemma 10.2.5, equation (10.2.21) (general case). -/
lemma eLpNorm_czRemainder'_le {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {i : ℕ} :
    eLpNorm (czRemainder' hX i) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 hX i) := by
  by_cases hi : czRadius hX i ≤ 0
  · simp [czRemainder'_eq_zero hX hi]
  calc
    _ ≤ 2 * (∫⁻ x in czPartition hX i, ‖f x‖ₑ) := ineq_10_2_32 hf
    _ ≤ 2 * (volume (czBall7 hX i) * α) := by
      apply mul_le_mul_right ∘ (le_trans <| lintegral_mono_set czPartition_subset_czBall7)
      have h : volume (czBall7 hX i) ≠ 0 :=
        measure_ball_pos _ _ (mul_pos Nat.ofNat_pos (lt_of_not_ge hi)) |>.ne'
      simpa [laverage, ENNReal.inv_mul_le_iff h measure_ball_ne_top] using laverage_czBall7_le hX i
    _ ≤ 2 * ((volume (ball (czCenter hX i) (2 ^ 2 * (3 * czRadius hX i)))) * α) := by
      gcongr; convert czBall_subset_czBall (b := 7) (c := 12) using 2; ring
    _ ≤ 2 * (2 ^ (2 * a) * volume (czBall3 hX i) * α) := by
      gcongr;
      exact (measure_ball_two_le_same_iterate _ _ 2).trans_eq <| by simp [pow_mul, mul_comm 2]
    _ = 2 ^ (2 * a + 1) * α * volume (czBall3 hX i) := by ring

-- Weaker version of `eLpNorm_czRemainder'_le` which is used repeatedly below
private lemma eLpNorm_restrict_czRemainder'_le {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {i : ℕ} :
    ∫⁻ y in czBall3 hX i, ‖czRemainder' hX i y‖ₑ ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 hX i) := by
  apply le_trans (setLIntegral_le_lintegral _ _)
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_czRemainder'_le (hf := hf)

-- Used to prove `eLpNorm_czRemainder_le` and `tsum_eLpNorm_czRemainder_le`
private lemma eLpNorm_czRemainder_le'
    (hf : BoundedFiniteSupport f) (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f α) 1 volume ≤ 2 * ∫⁻ x, ‖f x‖ₑ :=
  have := isFiniteMeasure_of_not_generalCase hf hX (lt_of_le_of_lt zero_le hα)
  calc
    _ = ∫⁻ x, ‖f x - ⨍ y, f y‖ₑ := by simp [czRemainder, eLpNorm, eLpNorm', czApproximation, hX]
    _ ≤ ∫⁻ x, (‖f x‖ₑ + ‖⨍ y, f y‖ₑ) := lintegral_mono (fun x ↦ enorm_sub_le)
    _ = (∫⁻ x, ‖f x‖ₑ) + ∫⁻ (x : X), ‖⨍ y, f y‖ₑ := lintegral_add_right' _ aemeasurable_const
    _ ≤ (∫⁻ x, ‖f x‖ₑ) + ∫⁻ (x : X), ⨍⁻ y, ‖f y‖ₑ := by
      gcongr; apply enorm_integral_le_lintegral_enorm
    _ = 2 * ∫⁻ x, ‖f x‖ₑ := by rw [two_mul, lintegral_laverage]

/-- Part of Lemma 10.2.5, equation (10.2.21) (finite case). -/
lemma eLpNorm_czRemainder_le {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f α) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
  by_cases h : Nonempty X; swap
  · have := not_nonempty_iff.mp h; simp
  have := isFiniteMeasure_of_not_generalCase hf hX (lt_of_le_of_lt zero_le hα)
  calc
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ := eLpNorm_czRemainder_le' hf hX hα
    _ ≤ 2 * (α * volume (univ : Set X)) := by
      rw [laverage_eq] at hα
      exact mul_le_mul_right (a := 2) <| ENNReal.div_lt_iff (Or.inl (NeZero.ne _))
        (Or.inl this.measure_univ_lt_top.ne) |>.mp hα |>.le
    _ ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
      rw [← mul_assoc]; gcongr; simpa using pow_le_pow_right' one_le_two (Nat.le_add_left 1 (2 * a))

/-- Part of Lemma 10.2.5, equation (10.2.22) (general case). -/
lemma tsum_volume_czBall3_le (hf : BoundedFiniteSupport f)
    (hX : GeneralCase f α) (hα : 0 < α) :
    ∑' i, volume (czBall3 hX i) ≤ 2 ^ (6 * a) / α * eLpNorm f 1 volume := calc
  _ ≤ ∑' i, 2 ^ (2 * a) * volume (czBall hX i) := ENNReal.tsum_le_tsum (volume_czBall3_le hX)
  _ ≤ 2 ^ (2 * a) * volume (globalMaximalFunction volume 1 f ⁻¹' Ioi α) := by
    simp_rw [← smul_eq_mul, ENNReal.tsum_const_smul]
    gcongr
    rw [← measure_iUnion ?_ (fun i ↦ measurableSet_ball), ← iUnion_czPartition (hX := hX)]
    · exact measure_mono <| iUnion_mono (fun i ↦ czBall_subset_czPartition)
    · refine (pairwise_disjoint_on (czBall hX)).mpr fun i j h ↦ ?_
      exact czBall_pairwiseDisjoint (mem_univ i) (mem_univ j) h.ne
  _ ≤ 2 ^ (2 * a) * ((C10_2_1 a) * eLpNorm f 1 volume / α) :=
    mul_le_mul_right (maximal_theorem'' hα hf) _
  _ = 2 ^ (6 * a) / α * eLpNorm f 1 volume := by
    rw [C10_2_1_def, mul_div_assoc', mul_comm (_ / α), mul_div, ← mul_assoc]; norm_cast; ring_nf

/-- Part of Lemma 10.2.5, equation (10.2.22) (finite case). -/
lemma volume_univ_le (hf : BoundedFiniteSupport f) (hX : ¬GeneralCase f α) (hα : 0 < α) :
    volume (univ : Set X) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  convert maximal_theorem'' hα hf using 1
  · simp_all [GeneralCase]
  · rw [ENNReal.mul_div_right_comm, C10_2_1_def]; rfl

/-- Part of Lemma 10.2.5, equation (10.2.23) (general case). -/
lemma tsum_eLpNorm_czRemainder'_le {hf : BoundedFiniteSupport f} (hX : GeneralCase f α) :
    ∑' i, eLpNorm (czRemainder' hX i) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  apply le_trans <| ENNReal.tsum_le_tsum (fun i ↦ ineq_10_2_32 hf)
  simp_rw [← smul_eq_mul, ENNReal.tsum_const_smul]
  gcongr
  rw [← lintegral_iUnion (MeasurableSet.czPartition hX) czPartition_pairwise_disjoint_on]
  simpa [eLpNorm, eLpNorm'] using (lintegral_mono_set (subset_univ _))

/-- Part of Lemma 10.2.5, equation (10.2.23) (finite case). -/
lemma tsum_eLpNorm_czRemainder_le
    {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f α) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  simpa [eLpNorm, eLpNorm'] using (eLpNorm_czRemainder_le' hf hX hα)

/- ### Lemmas 10.2.6 - 10.2.9 -/

/-- The constant `c` introduced below Lemma 10.2.5. -/
irreducible_def c10_0_3 (a : ℕ) : ℝ≥0 := (2 ^ (a ^ 3 + 12 * a + 4))⁻¹

open scoped Classical in
variable (f) in
/-- The set `Ω` introduced below Lemma 10.2.5. -/
def Ω (α : ℝ≥0∞) : Set X :=
  if hX : GeneralCase f α then ⋃ i, czBall6 hX i else univ

private lemma czBall3_subset_of_mem_Ω (hX : GeneralCase f α) (hx : x ∈ (Ω f α)ᶜ) (j : ℕ) :
    czBall3 hX j ⊆ (ball x (czRadius hX j))ᶜ := by
  by_cases! hr : czRadius hX j ≤ 0
  · simp [ball_eq_empty.mpr hr]
  intro y hy
  simp only [Ω, hX, reduceDIte, compl_iUnion, mem_iInter] at hx
  simp only [czBall3, mem_ball, mem_compl_iff, not_lt] at hx hy ⊢
  linarith [dist_triangle_left x (czCenter hX j) y, hx j]

private lemma six_mul_czRadius_le_of_mem_Ω (hx : x ∈ (Ω f α)ᶜ) (hX : GeneralCase f α) (j : ℕ) :
    6 * czRadius hX j ≤ dist x (czCenter hX j) := by
  revert j; simpa [Ω, hX] using hx

/-- The constant used in `estimate_good`. -/
irreducible_def C10_2_6 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a ^ 3 + 3 * a + 2) * c10_0_3 a

variable (a) in
@[no_expose] private def α' (α : ℝ≥0∞) : ℝ≥0∞ := c10_0_3 a * α

private lemma α'_pos {α : ℝ≥0∞} (hα : 0 < α) : 0 < α' a α :=
  ENNReal.mul_pos (by simp [c10_0_3]) hα.ne'

private lemma div_α'_eq {p : ℝ≥0∞} : p / α' a α = p / c10_0_3 a / α := by
  rcases eq_top_or_lt_top α with rfl | αlt
  · rw [div_top, ENNReal.div_eq_zero_iff]; refine .inr (mul_top ?_)
    rw [c10_0_3]; positivity
  nth_rw 1 [α', ← inv_inv α, ← div_eq_mul_inv, ← ENNReal.div_mul, ← div_eq_mul_inv]
  · left; rw [c10_0_3]; positivity
  · left; rw [c10_0_3]; finiteness

/-- Lemma 10.2.6 -/
private lemma estimate_good (hf : BoundedFiniteSupport f) (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    distribution (czOperator K r (czApproximation f (α' a α))) (α / 2) volume ≤
    C10_2_6 a / α * eLpNorm f 1 volume := by
  by_cases hα_top : α = ∞
  · simp [hα_top, top_div_of_lt_top ENNReal.ofNat_lt_top]
  have ne0 : (c10_0_3 a : ℝ≥0∞) ≠ 0 := by simp [c10_0_3]
  have hα' : 0 < α' a α := α'_pos (pos_of_gt hα)
  have hα'' := (zero_le.trans_lt hα).ne'
  calc distribution ((czOperator K r (czApproximation f (α' a α)))) (α / 2) volume
    _ = distribution ((czOperator K r (czApproximation f (α' a α))) ^ 2) ((α / 2) ^ 2) volume :=
      (distribution_pow _ _ _ _ two_pos.ne').symm
    _ ≤ ((α / 2) ^ 2)⁻¹ * ∫⁻ y, ‖((czOperator K r (czApproximation f (α' a α))) ^ 2) y‖ₑ := by
      apply distribution_le
      · exact ENNReal.pow_ne_zero (ENNReal.div_ne_zero.mpr ⟨hα'', ofNat_ne_top⟩) 2
      · change AEMeasurable (czOperator K r (czApproximation f (α' a α)) · ^ 2) volume
        refine czOperator_aestronglyMeasurable ?_ |>.aemeasurable.pow_const 2
        exact aemeasurable_czApproximation (hf := hf.aemeasurable) |>.aestronglyMeasurable
    _ = 2 ^ 2 / α ^ 2 * ∫⁻ y, ‖czOperator K r (czApproximation f (c10_0_3 a * α)) y‖ₑ ^ 2 := by
      congr
      · calc ((α / 2) ^ 2)⁻¹
          _ = (α ^ 2 / 2 ^ 2)⁻¹ := by congr; exact_mod_cast α.div_rpow_of_nonneg 2 two_pos.le
          _ = 2 ^ 2 / α ^ 2     := ENNReal.inv_div (Or.inl coe_ne_top) (Or.inl (by norm_num))
      · simp [α']
    _ ≤ 2 ^ 2 / α ^ 2 * ((C_Ts a) ^ 2 * ∫⁻ y, ‖czApproximation f (α' a α) y‖ₑ ^ 2) := by
      have half_pos : 0 < (2 : ℝ)⁻¹ := by norm_num
      refine mul_le_mul_right (ENNReal.le_of_rpow_le half_pos ?_) (2 ^ 2 / α ^ 2)
      rw [ENNReal.mul_rpow_of_nonneg _ _ half_pos.le, ← ENNReal.rpow_natCast_mul]
      convert hT _ (hf.czApproximation hα') |>.2
      all_goals simp [eLpNorm, eLpNorm', α']
    _ ≤ 2^2/α^2 * ((C_Ts a) ^ 2 * ∫⁻ y, 2^(3*a) * c10_0_3 a * α * ‖czApproximation f _ y‖ₑ) := by
      gcongr _ * (_ * ?_)
      suffices ∀ᵐ x, ‖czApproximation f (α' a α) x‖ₑ ≤ 2 ^ (3 * a) * c10_0_3 a * α by
        apply lintegral_mono_ae ∘ this.mono; intros; · rw [sq]; gcongr
      simp_rw [ENNReal.div_eq_inv_mul] at hα
      rw [← laverage_const_mul (inv_ne_top.mpr ne0), ← ENNReal.div_eq_inv_mul] at hα
      refine mul_assoc _ _ α ▸ enorm_czApproximation_le ?_ (hf := hf)
      exact mul_comm α _ ▸ (ENNReal.div_lt_iff (Or.inl ne0) (Or.inl coe_ne_top)).mp hα |>.le
    _ = 2^2/α^2 * ((C_Ts a)^2 * (2^(3*a) * c10_0_3 a * α * ∫⁻ y, ‖czApproximation f _ y‖ₑ)) := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ 2 ^ 2 / α ^ 2 * ((C_Ts a) ^ 2 * (2 ^ (3 * a) * c10_0_3 a * α * eLpNorm f 1 volume)) := by
      gcongr; simpa [eLpNorm, eLpNorm'] using eLpNorm_czApproximation_le (hf := hf) hα'
    _ = 2 ^ 2 / α^2 * ((C_Ts a) ^ 2 * (2 ^ (3 * a) * c10_0_3 a * α)) * eLpNorm f 1 volume := by ring
    _ = (2 ^ 2 * (C_Ts a) ^ 2 * 2 ^ (3 * a) * c10_0_3 a * α) / α ^ 2 * eLpNorm f 1 volume := by
      rw [ENNReal.mul_comm_div, mul_div]; ring_nf
    _ = (2 ^ 2 * (C_Ts a) ^ 2 * 2 ^ (3 * a) * c10_0_3 a) / α * eLpNorm f 1 volume := by
      rw [sq α, ENNReal.mul_div_mul_right _ _ hα'' hα_top]
    _ = (C10_2_6 a) / α * eLpNorm f 1 volume := by simp only [C_Ts, C10_2_6]; norm_cast; ring_nf

/-- The constant used in `czOperatorBound`. -/
irreducible_def C10_2_7 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1) * c10_0_3 a

private abbrev czOperatorBoundSummand (hX : GeneralCase f (α' a α)) (i : ℕ) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * (((3 * czRadius hX i).toNNReal / nndist x (czCenter hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 hX i)) / volume (ball x (dist x (czCenter hX i)))

/-- The function `F` defined in Lemma 10.2.7. -/
private def czOperatorBound (hX : GeneralCase f (α' a α)) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * ∑' i, ((3 * czRadius hX i).toNNReal / nndist x (czCenter hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 hX i) / volume (ball x (dist x (czCenter hX i)))

private lemma czOperatorBound_eq (hX : GeneralCase f (α' a α)) (x : X) :
    czOperatorBound hX x = ∑' i, czOperatorBoundSummand hX i x := by
  simp_rw [czOperatorBound, czOperatorBoundSummand, ← ENNReal.tsum_mul_left, mul_div]

private def 𝒥₁ (r : ℝ) (x : X) (hX : GeneralCase f (α' a α)) : Set ℕ :=
  {j | r + 3 * czRadius hX j ≤ dist x (czCenter hX j) }

private def 𝒥₂ (r : ℝ) (x : X) (hX : GeneralCase f (α' a α)) : Set ℕ :=
  {j | r - 3*czRadius hX j ≤ dist x (czCenter hX j) ∧ dist x (czCenter hX j) < r + 3*czRadius hX j }

private def 𝒥₃ (r : ℝ) (x : X) (hX : GeneralCase f (α' a α)) : Set ℕ :=
  {j | dist x (czCenter hX j) < r - 3*czRadius hX j }

private lemma union_𝒥 (r : ℝ) (x : X) (hX : GeneralCase f (α' a α)) :
    𝒥₁ r x hX ∪ 𝒥₂ r x hX ∪ 𝒥₃ r x hX = univ := by
  refine eq_univ_iff_forall.mpr (fun j ↦ ?_)
  by_cases h₃ : dist x (czCenter hX j) < r - 3 * czRadius hX j
  · exact Or.inr h₃
  by_cases h₁ : r + 3 * czRadius hX j ≤ dist x (czCenter hX j)
  · exact Or.inl (Or.inl h₁)
  simp_all [𝒥₂]

-- Auxiliary bound used to prove `lemma_10_2_7_bound`
private lemma lemma_10_2_7_bound' (hx : x ∈ (Ω f (α' a α))ᶜ) (hX : GeneralCase f (α' a α)) (j : ℕ)
    {g : X → ℂ} (g_aemeas : AEMeasurable g (volume.restrict (czBall3 hX j)))
    (hg : ∫⁻ y in czBall3 hX j, ‖g y‖ₑ ≤ 2 ^ (2 * a + 1) * (α' a α) * volume (czBall3 hX j)) :
    ∫⁻ y in czBall3 hX j, ‖K x y - K x (czCenter hX j)‖ₑ * ‖g y‖ₑ ≤
    czOperatorBoundSummand hX j x := calc
  _ ≤ ∫⁻ y in czBall3 hX j, (edist (czCenter hX j) y / edist x (czCenter hX j)) ^ (a : ℝ)⁻¹ *
        (C_K a / vol x (czCenter hX j)) * ‖g y‖ₑ := by
    refine setLIntegral_mono' measurableSet_ball fun y hy ↦ mul_le_mul_left ?_ _
    rw [enorm_sub_rev]
    exact enorm_K_sub_le <| calc 2 * dist (czCenter hX j) y
      _ ≤ 2 * (3 * czRadius hX j) := (mul_le_mul_iff_of_pos_left two_pos).mpr (mem_ball'.mp hy).le
      _ ≤ dist x (czCenter hX j)  := le_of_eq_of_le (by ring) (six_mul_czRadius_le_of_mem_Ω hx hX j)
  _ ≤ ∫⁻ y in czBall3 hX j, (.ofReal (3 * czRadius hX j) / edist x (czCenter hX j)) ^ (a : ℝ)⁻¹ *
        (C_K a / vol x (czCenter hX j)) * ‖g y‖ₑ := by
    refine setLIntegral_mono' measurableSet_ball fun y hy ↦ mul_le_mul_left ?_ _
    gcongr
    exact edist_dist (czCenter hX j) y ▸ ENNReal.ofReal_le_ofReal (mem_ball'.mp hy).le
  _ = _ := lintegral_const_mul'' _ g_aemeas.enorm
  _ ≤ (.ofReal (3 * czRadius hX j) / edist x (czCenter hX j)) ^ (a : ℝ)⁻¹ *
        (C_K a / vol x (czCenter hX j)) * (2 ^ (2 * a + 1) * (α' a α) * volume (czBall3 hX j)) :=
    mul_right_mono hg
  _ = 2 ^ (2 * a + 1) * ((c10_0_3 a) * α) * volume (czBall3 hX j) * ((.ofReal (3 * czRadius hX j) /
        edist x (czCenter hX j)) ^ (a : ℝ)⁻¹ * C_K a) / vol x (czCenter hX j) := by
    unfold α'; rw [mul_div, mul_comm, mul_div]
  _ = 2 ^ a ^ 3 * 2 ^ (2 * a + 1) * c10_0_3 a * α * ((ENNReal.ofReal (3 * czRadius hX j) /
        edist x (czCenter hX j)) ^ (a : ℝ)⁻¹ * volume (czBall3 hX j)) / vol x (czCenter hX j) := by
    rw [C_K, show ENNReal.ofNNReal (2 ^ (a : ℝ) ^ 3) = 2 ^ (a ^ 3) by norm_cast]; ring_nf
  _ = _ := by rw [czOperatorBoundSummand, C10_2_7_def, add_assoc, ← pow_add]; norm_cast

-- Bound used twice in the proof of Lemma 10.2.7
private lemma lemma_10_2_7_bound (hx : x ∈ (Ω f (α' a α))ᶜ) (hX : GeneralCase f (α' a α)) (j : ℕ)
    {g : X → ℂ} (g_int : IntegrableOn g (czBall3 hX j)) (hg0 : ∫ y in czBall3 hX j, g y = 0)
    (hg : ∫⁻ y in czBall3 hX j, ‖g y‖ₑ ≤ 2 ^ (2 * a + 1) * (α' a α) * volume (czBall3 hX j)) :
    ‖∫ y in czBall3 hX j, K x y * g y‖ₑ ≤ czOperatorBoundSummand hX j x := by
  by_cases! hj : czRadius hX j ≤ 0
  · simp [Metric.ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos three_pos.le hj]
  calc
    _ = ‖(∫ y in czBall3 hX j, K x y * g y) - ∫ y in czBall3 hX j, K x (czCenter hX j) * g y‖ₑ := by
      rw [integral_const_mul_of_integrable (IntegrableOn.integrable g_int), hg0, mul_zero, sub_zero]
    _ = ‖∫ y in czBall3 hX j, (K x y - K x (czCenter hX j)) * g y‖ₑ := by
      simp_rw [sub_mul]
      rw [integral_sub ?_ (g_int.const_mul _)]
      exact integrableOn_K_mul g_int x hj (czBall3_subset_of_mem_Ω hX hx j)
    _ ≤ _ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in czBall3 hX j, ‖K x y - K x (czCenter hX j)‖ₑ * ‖g y‖ₑ := by simp
    _ ≤ _ := lemma_10_2_7_bound' hx hX j g_int.aemeasurable hg

private lemma 𝒥₁_bound (hf : BoundedFiniteSupport f) (hα : 0 < α) (hx : x ∈ (Ω f (α' a α))ᶜ)
    (hX : GeneralCase f (α' a α)) {j : ℕ} (hj : j ∈ 𝒥₁ r x hX) :
    ‖czOperator K r (czRemainder' hX j) x‖ₑ ≤ czOperatorBoundSummand hX j x := calc
  _ = ‖∫ y in czBall3 hX j, K x y * (czRemainder' hX j y)‖ₑ := by
    apply congrArg
    apply setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_ball.compl.nullMeasurableSet
    · intro y hy
      simp only [𝒥₁, mem_setOf_eq, mem_ball, mem_compl_iff] at hj hy ⊢
      linarith [dist_triangle_left x (czCenter hX j) y]
    · refine Eventually.of_forall (fun y hy ↦ mul_eq_zero_of_right (K x y) ?_)
      exact notMem_support.mp <| notMem_subset support_czRemainder'_subset (notMem_of_mem_diff hy)
  _ ≤ _ := by
    apply lemma_10_2_7_bound hx hX j (hf.czRemainder' (α'_pos hα) hX j).integrable.restrict
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_czRemainder']
      intro y hy
      exact notMem_support.mp <| notMem_subset support_czRemainder'_subset hy
    · exact eLpNorm_restrict_czRemainder'_le (hf := hf)

private lemma tsum_𝒥₁ (hf : BoundedFiniteSupport f) (hα : 0 < α)
    (hX : GeneralCase f (α' a α)) (hx : x ∈ (Ω f (α' a α))ᶜ) :
    ∑' (j : ↑(𝒥₁ r x hX)), ‖czOperator K r (czRemainder' hX ↑j) x‖ₑ ≤ czOperatorBound hX x := by
  apply le_trans <| ENNReal.tsum_le_tsum (𝒥₁_bound hf hα hx hX <| Subtype.coe_prop ·)
  apply le_of_le_of_eq <| ENNReal.tsum_mono_subtype (czOperatorBoundSummand hX · x) (subset_univ _)
  rw [czOperatorBound_eq, tsum_univ (czOperatorBoundSummand hX · x)]

-- The value dⱼ defined below inequality (10.2.48)
variable (r) (x) in
private def d (hX : GeneralCase f (α' a α)) (j : ℕ) :=
  ⨍ y in czBall3 hX j, (ball x r)ᶜ.indicator (czRemainder' hX j) y

private lemma integrableOn_d (hX : GeneralCase f (α' a α)) (j : ℕ) :
    Integrable (fun _ ↦ d r x hX j) (volume.restrict (czBall3 hX j)) := by
  suffices IsFiniteMeasure (volume.restrict (czBall3 hX j)) by apply integrable_const
  exact isFiniteMeasure_restrict.mpr measure_ball_ne_top

private lemma enorm_d_le (hf : BoundedFiniteSupport f) (hX : GeneralCase f (α' a α)) (j : ℕ) :
    ‖d r x hX j‖ₑ ≤ 2 ^ (2 * a + 1) * α' a α := by
  by_cases! hr : czRadius hX j ≤ 0
  · simp [d, Metric.ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos three_pos.le hr]
  calc
    _ ≤ _ := enorm_integral_le_lintegral_enorm _
    _ ≤ (volume (czBall3 hX j))⁻¹ * ∫⁻ y in czBall3 hX j,
          (ball x r)ᶜ.indicator (‖czRemainder' hX j ·‖ₑ) y := by
      simp [enorm_indicator_eq_indicator_enorm]
    _ ≤ (volume (czBall3 hX j))⁻¹ * ∫⁻ y in czBall3 hX j, ‖czRemainder' hX j y‖ₑ := by
      gcongr; exact indicator_enorm_le_enorm_self _ _
    _ ≤ (volume (czBall3 hX j))⁻¹ * (2 ^ (2 * a + 1) * (α' a α) * volume (czBall3 hX j)) :=
      mul_le_mul_right (eLpNorm_restrict_czRemainder'_le (hf := hf) ) _
    _ ≤ _ := by
      rw [mul_comm (volume _)⁻¹, mul_assoc]
      have : volume (czBall3 hX j) ≠ 0 :=
        isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (mul_pos three_pos hr))
      simp [ENNReal.mul_inv_cancel this measure_ball_ne_top]

-- The next two functions are integrands involved in the 𝒥₂ section of the proof of Lemma 10.2.7
variable (r) (x) in
private abbrev g₀ (hX : GeneralCase f (α' a α)) (j : ℕ) (y : X) :=
  (ball x r)ᶜ.indicator (czRemainder' hX j) y

variable (r) (x) in
private abbrev g (hX : GeneralCase f (α' a α)) (j : ℕ) (y : X) :=
  g₀ r x hX j y - d r x hX j

private lemma integrableOn_g₀ (hf : BoundedFiniteSupport f) (hα : 0 < α)
    (hX : GeneralCase f (α' a α)) (j : ℕ) : IntegrableOn (g₀ r x hX j) (czBall3 hX j) :=
  (hf.czRemainder' (α'_pos hα) hX j).integrable.restrict.indicator measurableSet_ball.compl

private lemma lintegral_enorm_g₀_le (hf : BoundedFiniteSupport f)
    (hX : GeneralCase f (α' a α)) (j : ℕ) :
    ∫⁻ y in czBall3 hX j, ‖g₀ r x hX j y‖ₑ ≤ 2 ^ (2*a + 1) * α' a α * volume (czBall3 hX j) := by
  simp_rw [g₀, enorm_indicator_eq_indicator_enorm]
  apply le_trans (lintegral_mono (fun y ↦ indicator_enorm_le_enorm_self _ _))
  exact eLpNorm_restrict_czRemainder'_le (hf := hf)

variable (r) (x) in
private lemma integrableOn_g (hα : 0 < α) (hf : BoundedFiniteSupport f)
    (hX : GeneralCase f (α' a α)) (j : ℕ) : IntegrableOn (g r x hX j) (czBall3 hX j) :=
  (integrableOn_g₀ hf hα hX j).sub (integrableOn_d hX j)

private lemma integral_g (hf : BoundedFiniteSupport f) (hα : 0 < α) (hX : GeneralCase f (α' a α))
    (j : ℕ) : ∫ y in czBall3 hX j, g r x hX j y = 0 := by
  by_cases! hj : czRadius hX j ≤ 0
  · simp [Metric.ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos three_pos.le hj]
  rw [integral_sub (integrableOn_g₀ hf hα hX j) (integrableOn_d hX j)]
  simp only [d, setAverage_eq, Complex.real_smul, Complex.ofReal_inv, integral_const,
    MeasurableSet.univ, measureReal_restrict_apply, univ_inter, ← mul_assoc]
  have : volume.real (czBall3 hX j) ≠ 0 := (measureReal_ball_pos (czCenter hX j) (mul_pos three_pos hj)).ne'
  rw [mul_inv_cancel₀ (by simpa)]
  simp

private lemma lintegral_enorm_half_g (hf : BoundedFiniteSupport f) (hα : 0 < α)
    (hX : GeneralCase f (α' a α)) (j : ℕ) :
    ∫⁻ y in czBall3 hX j, ‖2⁻¹ * g r x hX j y‖ₑ ≤
    2 ^ (2 * a + 1) * α' a α * volume (czBall3 hX j) := calc
  _ = 2⁻¹ * ∫⁻ y in czBall3 hX j, ‖g r x hX j y‖ₑ := by
    simp_rw [enorm_mul]
    rw [lintegral_const_mul' _ _ enorm_ne_top, enorm_inv (NeZero.ne 2), ← ofReal_norm_eq_enorm]
    simp
  _ ≤ 2⁻¹ * ∫⁻ y in czBall3 hX j, ‖g₀ r x hX j y‖ₑ + ‖d r x hX j‖ₑ := by gcongr; exact enorm_sub_le
  _ = _ := by rw [lintegral_add_left' (integrableOn_g₀ hf hα hX j).aemeasurable.enorm]
  _ ≤ 2 ^ (2 * a + 1) * α' a α * volume (czBall3 hX j) := by
    rw [← one_mul (_ * _ * _), ← ENNReal.inv_mul_cancel two_pos.ne' ENNReal.ofNat_ne_top,
      mul_assoc, two_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    gcongr 2⁻¹ * (?_ + ?_ * volume (czBall3 hX j))
    · exact lintegral_enorm_g₀_le hf hX j
    · exact enorm_d_le hf hX j

-- The bounds on `‖czOperator K r (czRemainder' hX j) x‖ₑ` used for the `𝒥₂` estimate (even
-- though this part of the estimate doesn't require j ∈ 𝒥₂).
private lemma 𝒥₂_bound (hf : BoundedFiniteSupport f) (hα : 0 < α) (hx : x ∈ (Ω f (α' a α))ᶜ)
    (hX : GeneralCase f (α' a α)) {j : ℕ} :
    ‖czOperator K r (czRemainder' hX j) x‖ₑ ≤ 2 * czOperatorBoundSummand hX j x +
      2 ^ (2 * a + 1) * (α' a α) * ∫⁻ y in czBall3 hX j, ‖K x y‖ₑ := calc
  _ = ‖∫ y, K x y * (ball x r)ᶜ.indicator (czRemainder' hX j) y‖ₑ := by
    simp_rw [czOperator, ← integral_indicator measurableSet_ball.compl, indicator_mul_right]
  _ = ‖∫ y in czBall3 hX j, K x y * ((ball x r)ᶜ.indicator (czRemainder' hX j) y)‖ₑ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    refine mul_eq_zero_of_right _ <| indicator_apply_eq_zero.mpr fun _ ↦ ?_
    exact notMem_support.mp <| notMem_subset support_czRemainder'_subset hy
  _ = ‖∫ y in czBall3 hX j, K x y * (g r x hX j y + d r x hX j)‖ₑ := by simp
  _ = ‖(∫ y in czBall3 hX j, K x y * (g r x hX j y)) +
        ∫ y in czBall3 hX j, K x y * d r x hX j‖ₑ := by
    by_cases! hj : czRadius hX j ≤ 0
    · simp [Metric.ball_eq_empty.mpr <| mul_nonpos_of_nonneg_of_nonpos three_pos.le hj]
    simp_rw [mul_add]
    have subset : czBall3 hX j ⊆
        {y | dist x y ∈ Icc (czRadius hX j) (dist x (czCenter hX j) + 3 * czRadius hX j)} := by
      intro y hy
      have := czBall3_subset_of_mem_Ω hX hx j hy
      simp only [mem_ball, dist_comm y, mem_compl_iff, not_lt, mem_Icc] at hy this ⊢
      exact ⟨this, by linarith [dist_triangle x (czCenter hX j) y]⟩
    rw [integral_add]
    · apply integrableOn_K_mul (integrableOn_g r x hα hf hX j) x hj
      exact subset.trans (fun y ↦ by simp [dist_comm y]; tauto)
    · exact (integrableOn_K_Icc hj).mono_set subset |>.mul_const _
  _ ≤ ‖_‖ₑ + ‖_‖ₑ := enorm_add_le _ _
  _ = ‖2 * (2⁻¹ * ∫ y in czBall3 hX j, K x y * g r x hX j y)‖ₑ + ‖_‖ₑ := by
    congr
    ring
  _ = ‖2 * ∫ y in czBall3 hX j, K x y * (2⁻¹ * g r x hX j y)‖ₑ + ‖_‖ₑ := by
    congr
    have h : ∀ y, K x y * (2⁻¹ * g r x hX j y) = 2⁻¹ * (K x y * g r x hX j y) := by
      intro y
      exact mul_left_comm ..
    simp_rw [h]
    exact (integral_const_mul ..).symm
  _ = ‖(2 : ℂ)‖ₑ * ‖∫ y in czBall3 hX j, K x y * (2⁻¹ * g r x hX j y)‖ₑ + ‖_‖ₑ := by
    rw [← enorm_mul]
  _ ≤ _ := by
    gcongr
    · simp [← ofReal_norm_eq_enorm]
    · apply lemma_10_2_7_bound hx hX j ((integrableOn_g r x hα hf hX j).const_mul 2⁻¹)
      · have h :
          ∫ (y : X) in czBall3 hX j, 2⁻¹ * g r x hX j y =
          2⁻¹ * ∫ (y : X) in czBall3 hX j, g r x hX j y :=
          integral_const_mul ..
        simp_rw [h, integral_g hf hα hX, mul_zero]
      · apply lintegral_enorm_half_g hf hα hX
    · apply le_trans (enorm_integral_le_lintegral_enorm _)
      simp_rw [enorm_mul, lintegral_mul_const _ (measurable_K_right x).enorm, ← mul_comm ‖_‖ₑ]
      exact mul_le_mul_left (enorm_d_le hf hX j) _

-- The set `A` defined between (10.2.51) and (10.2.52)
variable (r) (x) in
private def A (hX : GeneralCase f (α' a α)) : Set X := ⋃ (j : ↑(𝒥₂ r x hX)), czBall3 hX j

-- (10.2.52)
private lemma A_subset (hx : x ∈ (Ω f (α' a α))ᶜ) (hX : GeneralCase f (α' a α)) :
    A r x hX ⊆ Annulus.co x (r / 3) (3 * r) := by
  refine iUnion_subset (fun j y hy ↦ ?_)
  rw [mem_ball'] at hy
  have : 6 * czRadius hX j ≤ dist x (czCenter hX j) := six_mul_czRadius_le_of_mem_Ω hx hX j
  have hj := Subtype.coe_prop j
  simp only [𝒥₂, tsub_le_iff_right, mem_setOf_eq] at hj
  constructor
  · linarith [dist_triangle_right x (czCenter hX j) y]
  · linarith [dist_triangle x (czCenter hX j) y]

private lemma sum_volume_restrict_le (hX : GeneralCase f (α' a α)) :
    Measure.sum (fun (j : 𝒥₂ r x hX) ↦ volume.restrict (czBall3 hX j)) ≤
    2 ^ (6 * a) • volume.restrict (A r x hX) :=
  Measure.sum_restrict_le (fun _ ↦ measurableSet_ball) <| fun y ↦
    le_trans (encard_preimage_val_le_encard_right _ {i | y ∈ czBall3 hX i}) encard_czBall3_le

-- Long calculation toward the end of Lemma 10.2.7
private lemma tsum_integral_K_le (hx : x ∈ (Ω f (α' a α))ᶜ) (hX : GeneralCase f (α' a α)) :
    ∑' (j : 𝒥₂ r x hX), ∫⁻ y in czBall3 hX j, ‖K x y‖ₑ ≤ 2 ^ (a ^ 3 + 10 * a) := calc
  _ ≤ ∫⁻ (a : X), ‖K x a‖ₑ ∂(2 ^ (6 * a) • volume.restrict (A r x hX)) := by
    rw [← lintegral_sum_measure]
    exact lintegral_mono' (sum_volume_restrict_le hX) (le_refl _)
  _ = 2 ^ (6 * a) * ∫⁻ y in A r x hX, ‖K x y‖ₑ := by
    simp only [lintegral_smul_measure, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  _ ≤ 2 ^ (6 * a) * ∫⁻ y in Annulus.co x (r / 3) (3 * r), ‖K x y‖ₑ :=
    mul_le_mul_right (lintegral_mono_set (A_subset hx hX)) _
  _ ≤ 2 ^ (6 * a) * ∫⁻ y in Annulus.co x (r / 3) (3 * r),
        2 ^ (a ^ 3) / volume (ball x (r / 3)) := by
    refine mul_le_mul_right (setLIntegral_mono' Annulus.measurableSet_co (fun y hy ↦ ?_)) _
    trans 2 ^ (a ^ 3) / volume (ball x (dist x y))
    · have := enorm_K_le_vol_inv (K := K) x y; unfold C_K at this; exact_mod_cast this
    · gcongr; exact hy.1
  _ = 2 ^ (6*a) * (2 ^ (a^3) / volume (ball x (r/3)) * volume (Annulus.co x (r/3) (3*r))) := by
    simp [lintegral_const]
  _ ≤ 2 ^ (6*a) * (2 ^ (a^3) / volume (ball x (r/3)) * (2 ^ (4*a) * volume (ball x (r/3)))) := by
    gcongr
    apply le_trans (measure_mono Annulus.co_subset_ball)
    trans volume (ball x (2 ^ 4 * (r / 3)))
    · by_cases hr : r ≤ 0
      · simp [ball_eq_empty.mpr (mul_nonpos_of_nonneg_of_nonpos three_pos.le hr)]
      · exact measure_mono <| ball_subset_ball (by linarith)
    · rw [mul_comm 4, pow_mul]
      exact_mod_cast measure_ball_two_le_same_iterate x (r / 3) 4 (μ := volume)
  _ = 2 ^ a ^ 3 * 2 ^ (6 * a) * 2 ^ (4 * a) *
        ((volume (ball x (r / 3)))⁻¹ * volume (ball x (r / 3))) := by
    rw [div_eq_mul_inv]; ring
  _ ≤ 2 ^ a ^ 3 * 2 ^ (6 * a) * 2 ^ (4 * a) * 1 := by gcongr; apply ENNReal.inv_mul_le_one
  _ = 2 ^ (a ^3 + 10 * a) := by rw [mul_one, ← pow_add, ← pow_add]; ring_nf

private lemma tsum_𝒥₂ (hf : BoundedFiniteSupport f) (hα : 0 < α) (hx : x ∈ (Ω f (α' a α))ᶜ)
    (hX : GeneralCase f (α' a α)) :
    ∑' (j : 𝒥₂ r x hX), ‖czOperator K r (czRemainder' hX j) x‖ₑ ≤
    2 * czOperatorBound hX x + α / 8 := calc
  _ ≤ ∑' (j : 𝒥₂ r x hX), (2 * (czOperatorBoundSummand hX j x) +
        2 ^ (2 * a + 1) * (α' a α) * ∫⁻ y in czBall3 hX j, ‖K x y‖ₑ) :=
    ENNReal.tsum_le_tsum (fun j ↦ 𝒥₂_bound hf hα hx hX)
  _ = ∑' (j : 𝒥₂ r x hX), _ + ∑' (j : 𝒥₂ r x hX), _ := ENNReal.tsum_add
  _ ≤ _ := by
    refine add_le_add ?_ ?_
    · rw [ENNReal.tsum_mul_left, czOperatorBound_eq, ← tsum_univ (β := ℕ)]
      apply mul_le_mul_right
      exact ENNReal.tsum_mono_subtype (czOperatorBoundSummand hX · x) (subset_univ _)
    · calc
        _ = _ * ∑' (j : 𝒥₂ r x hX), _ := by rw [ENNReal.tsum_mul_left]
        _ ≤ _ * 2 ^ (a^3 + 10*a) := mul_le_mul_right (tsum_integral_K_le hx hX) _
        _ = 2 ^ (2*a + 1 : ℝ) * ((2 ^ (a^3 + 12*a + 4 : ℝ))⁻¹ * α) * 2 ^ (a^3 + 10*a : ℝ) := by
          norm_cast
          simp [α', c10_0_3]
        _ = 2 ^ (2*a + 1 : ℝ) * 2 ^ (- (a^3 + 12*a + 4 : ℝ)) * 2 ^ (a^3 + 10*a : ℝ) * α := by
          rw [rpow_neg]; ring
        _ = 2 ^ ((2 * a + 1) + -(a ^ 3 + 12 * a + 4 : ℝ) + (a ^ 3 + 10 * a)) * α := by
          repeat rw [rpow_add _ _ two_pos.ne' ofNat_ne_top]
        _ = α / 8 := by ring_nf; rw [rpow_neg, ← ENNReal.div_eq_inv_mul]; norm_num

omit [IsTwoSidedKernel a K] in
private lemma tsum_𝒥₃ (hX : GeneralCase f (α' a α)) :
    ∑' (j : 𝒥₃ r x hX), ‖czOperator K r (czRemainder' hX j) x‖ₑ = 0 := by
  refine ENNReal.tsum_eq_zero.mpr (fun j ↦ enorm_eq_zero.mpr ?_)
  have hj := Subtype.coe_prop j
  simp_rw [𝒥₃, dist_comm x, lt_sub_iff_add_lt'] at hj
  refine setIntegral_eq_zero_of_forall_eq_zero (fun y hy ↦ ?_)
  apply mul_eq_zero_of_right _ ∘ notMem_support.mp
  exact notMem_subset (support_czRemainder'_subset.trans (ball_subset_ball' hj.le)) hy

omit [IsTwoSidedKernel a K] in
private lemma czOperator_czRemainder' (hX : GeneralCase f α) (i : ℕ) :
    czOperator K r (czRemainder' hX i) x =
    ∫ y in (ball x r)ᶜ ∩ czPartition hX i, K x y * czRemainder f α y := by
  have h_meas := MeasurableSet.czPartition hX i
  simp [czOperator, czRemainder', czRemainder, ← indicator_mul_right, setIntegral_indicator h_meas]

private lemma czOperator_czRemainder (hf : BoundedFiniteSupport f) (hr : 0 < r) (hα : 0 < α)
    (hX : GeneralCase f α) :
    czOperator K r (czRemainder f α) x = ∑' i, czOperator K r (czRemainder' hX i) x := by
  simp_rw [czOperator_czRemainder', czOperator]
  rw [← integral_iUnion, ← inter_iUnion, ← setIntegral_indicator]
  · congr with y
    by_cases hy : y ∈ ⋃ i, czPartition hX i <;>
      simp [hy, ← tsum_czRemainder' hX, czRemainder', not_exists.mp (mem_iUnion.mpr.mt _)]
  · exact MeasurableSet.iUnion (MeasurableSet.czPartition hX)
  · measurability
  · exact pairwise_disjoint_mono czPartition_pairwise_disjoint_on (fun _ _ ↦ mem_of_mem_inter_right)
  · exact integrableOn_K_mul (hf.czRemainder hα).integrable.integrableOn x hr (by simp)

/-- Lemma 10.2.7.
Note that `hx` implies `hX`, but we keep the superfluous hypothesis to shorten the statement. -/
private lemma estimate_bad_partial (hf : BoundedFiniteSupport f) (hr : 0 < r)
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hx : x ∈ (Ω f (α' a α))ᶜ) (hX : GeneralCase f (α' a α)) :
    ‖czOperator K r (czRemainder f (α' a α)) x‖ₑ ≤ 3 * czOperatorBound hX x + α / 8 := calc
  _ = ‖∑' j, czOperator K r _ x‖ₑ := by rw [czOperator_czRemainder hf hr (α'_pos (pos_of_gt hα)) hX]
  _ ≤ ∑' j, ‖czOperator K r (czRemainder' hX j) x‖ₑ := enorm_tsum_le_tsum_enorm
  _ = ∑' (j : ↑(𝒥₁ r x hX ∪ 𝒥₂ r x hX ∪ 𝒥₃ r x hX)), _ := by rw [← tsum_univ, ← union_𝒥 r x hX]
  _ ≤ _ + _ := ENNReal.tsum_union_le (fun i ↦ ‖czOperator K r (czRemainder' hX i) x‖ₑ) _ _
  _ = ∑' (j : ↑(𝒥₁ r x hX ∪ 𝒥₂ r x hX)), _ := by rw [tsum_𝒥₃, add_zero]
  _ ≤ _ + _ := (ENNReal.tsum_union_le (fun i ↦ ‖czOperator K r (czRemainder' hX i) x‖ₑ) _ _)
  _ ≤ _ + _ := add_le_add (tsum_𝒥₁ hf (pos_of_gt hα) hX hx) (tsum_𝒥₂ hf (pos_of_gt hα) hx hX)
  _ = 3 * czOperatorBound hX x + α / 8 := by ring

private lemma czOperatorBound_inner_le (ha : 4 ≤ a) (hX : GeneralCase f (α' a α)) {i : ℕ} :
    ∫⁻ x in (Ω f (α' a α))ᶜ, ((3 * czRadius hX i).toNNReal / edist x (czCenter hX i)) ^ (a : ℝ)⁻¹ /
      volume (ball x (dist x (czCenter hX i))) ≤ 2 ^ (3 * a) := by
  set r := 3 * czRadius hX i
  set c := czCenter hX i
  rcases le_or_gt r 0 with hr | hr
  · simp_rw [Real.toNNReal_of_nonpos hr, coe_zero, ENNReal.zero_div]
    rw [ENNReal.zero_rpow_of_pos (by rw [inv_pos, Nat.cast_pos]; exact zero_lt_four.trans_le ha)]
    simp_rw [ENNReal.zero_div, lintegral_zero]; exact zero_le
  calc
    _ ≤ ∫⁻ x in (czBall6 hX i)ᶜ,
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball x (dist x c)) := by
      apply lintegral_mono_set; simp_rw [compl_subset_compl, Ω, hX, dite_true]
      exact subset_iUnion ..
    _ ≤ ∫⁻ x in (czBall6 hX i)ᶜ,
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / (volume (ball c (dist x c)) / 2 ^ a) := by
      gcongr with x; apply div_le_of_le_mul
      calc
        _ ≤ volume (ball x (2 * dist x c)) :=
          measure_mono (ball_subset_ball' (by rw [dist_comm, two_mul]))
        _ ≤ _ := by
          rw [mul_comm _ (2 ^ a)]
          convert measure_ball_two_le_same (μ := volume) x (dist x c)
          unfold defaultA; norm_cast
    _ = 2 ^ a * ∫⁻ x in (czBall6 hX i)ᶜ,
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball c (dist x c)) := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]; congr! 2 with x
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (.inl (by finiteness)) (.inl (by positivity)),
        ENNReal.mul_comm_div]
    _ ≤ 2 ^ a * ∫⁻ x in ⋃ n, ball c (2 ^ (n + 1) * r) \ ball c (2 ^ n * r),
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball c (dist x c)) := by
      gcongr _ * ?_; refine lintegral_mono_set fun x mx ↦ ?_
      rw [czBall6, mem_compl_iff, mem_ball, not_lt, show (6 : ℝ) = 2 * 3 by norm_num,
        mul_assoc] at mx
      change 2 * r ≤ dist x c at mx
      rw [mem_iUnion]; use ⌊Real.logb 2 (dist x c / r)⌋₊; simp_rw [mem_diff, mem_ball, not_lt]
      have dxcpos : 0 < dist x c := lt_of_lt_of_le (by positivity) mx
      have dxceq : dist x c = 2 ^ (Real.logb 2 (dist x c / r)) * r := by
        rw [Real.rpow_logb zero_lt_two (by norm_num) (by positivity), div_mul_cancel₀ _ hr.ne']
      constructor
      · nth_rw 1 [dxceq, ← Real.rpow_natCast]; push_cast; gcongr
        exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (Nat.lt_floor_add_one _)
      · nth_rw 2 [dxceq]; rw [← Real.rpow_natCast]; gcongr
        · exact one_le_two
        · refine Nat.floor_le (Real.logb_nonneg one_lt_two ((one_le_div₀ hr).mpr ?_))
          linarith only [hr, mx]
    _ ≤ 2 ^ a * ∑' n, ∫⁻ x in ball c (2 ^ (n + 1) * r) \ ball c (2 ^ n * r),
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball c (dist x c)) := by
      gcongr; exact lintegral_iUnion_le _ _
    _ ≤ 2 ^ a * ∑' n, ∫⁻ x in ball c (2 ^ (n + 1) * r) \ ball c (2 ^ n * r),
        (2 ^ n)⁻¹ ^ (a : ℝ)⁻¹ / volume (ball c (2 ^ n * r)) := by
      gcongr 2 ^ a * ∑' n, ?_ with n
      refine setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun x mx ↦ ?_
      simp_rw [mem_diff, mem_ball, not_lt] at mx
      gcongr
      · change ENNReal.ofReal r / _ ≤ _
        have dxcpos : 0 < dist x c := lt_of_lt_of_le (by positivity) mx.2
        rw [le_inv_iff_mul_le, mul_comm, ← mul_div_assoc, show 2 = ENNReal.ofReal 2 by simp,
          ← ofReal_pow zero_le_two, ← ofReal_mul (by positivity), edist_dist,
          ← ofReal_div_of_pos dxcpos, ← ofReal_one]
        apply ofReal_le_ofReal; rw [div_le_one dxcpos]; exact mx.2
      · exact mx.2
    _ = 2 ^ a * ∑' n : ℕ, 2 ^ (-n / a : ℝ) *
        (volume (ball c (2 ^ (n + 1) * r) \ ball c (2 ^ n * r)) / volume (ball c (2 ^ n * r))) := by
      congr! 3 with n; rw [setLIntegral_const, ← ENNReal.mul_div_right_comm, ← mul_div_assoc]
      congr 2; rw [← rpow_natCast, ← rpow_neg, ← rpow_mul, ← div_eq_mul_inv]
    _ ≤ 2 ^ a * ∑' n : ℕ, 2 ^ (-n / a : ℝ) * 2 ^ a := by
      gcongr with n; apply div_le_of_le_mul
      calc
        _ ≤ volume (ball c (2 * (2 ^ n * r))) := by
          rw [← mul_assoc 2, ← pow_succ']; exact measure_mono diff_subset
        _ ≤ _ := by
          convert measure_ball_two_le_same (μ := volume) c (2 ^ n * r)
          unfold defaultA; norm_cast
    _ ≤ 2 ^ a * 2 ^ a * 2 ^ a := by
      rw [ENNReal.tsum_mul_right, ← mul_assoc]; gcongr
      rw [← rpow_natCast]; exact geometric_series_estimate (by norm_cast; lia)
    _ = _ := by norm_cast; ring

/-- The constant used in `distribution_czOperatorBound`. -/
@[no_expose] def C10_2_8 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 11 * a + 4)

/-- Lemma 10.2.8 -/
private lemma distribution_czOperatorBound (ha : 4 ≤ a) (hf : BoundedFiniteSupport f)
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f (α' a α)) :
    volume ((Ω f (α' a α))ᶜ ∩ czOperatorBound hX ⁻¹' Ioi (α / 8)) ≤
    C10_2_8 a / α * eLpNorm f 1 volume := by
  rcases eq_zero_or_pos α with rfl | αpos; · simp at hα
  rcases eq_top_or_lt_top α with rfl | αlt
  · have : czOperatorBound hX ⁻¹' Ioi (⊤ / 8) = ∅ := by
      rw [top_div_of_ne_top (by norm_num), isMax_top.Ioi_eq, preimage_empty]
    rw [this, inter_empty, measure_empty]; exact zero_le
  calc
    _ ≤ (volume.restrict (Ω f (α' a α))ᶜ) {x | α / 8 ≤ czOperatorBound hX x} := by
      rw [inter_comm, ← Measure.restrict_apply']; swap
      · apply MeasurableSet.compl; simp_rw [Ω, hX, dite_true]
        exact MeasurableSet.iUnion fun _ ↦ measurableSet_ball
      gcongr; intro x mx; simp only [mem_preimage, mem_Ioi, mem_setOf_eq] at mx ⊢; exact mx.le
    _ ≤ (∫⁻ x in (Ω f (α' a α))ᶜ, czOperatorBound hX x) / (α / 8) := by
      apply meas_ge_le_lintegral_div
      · refine ((AEMeasurable.ennreal_tsum fun i ↦ ?_).const_mul _).restrict
        refine AEMeasurable.div ?_ measurable_vol₁.aemeasurable
        refine ((AEMeasurable.const_div ?_ _).pow_const _).mul_const _
        simp only [coe_nnreal_ennreal_nndist]
        exact aemeasurable_id'.edist aemeasurable_const
      · simp [αpos.ne']
      · finiteness
    _ ≤ 8 * C10_2_7 a * ∑' i, volume (czBall3 hX i) * ∫⁻ x in (Ω f (α' a α))ᶜ,
        ((3 * czRadius hX i).toNNReal / edist x (czCenter hX i)) ^ (a : ℝ)⁻¹ /
        volume (ball x (dist x (czCenter hX i))) := by
      unfold czOperatorBound
      rw [lintegral_const_mul' _ _ (by finiteness), ENNReal.div_eq_inv_mul,
        ENNReal.inv_div (.inr αlt.ne) (.inr αpos.ne'), ← mul_assoc, ← mul_assoc,
        ← ENNReal.mul_div_right_comm, ENNReal.div_mul_cancel αpos.ne' αlt.ne]
      simp only [coe_nnreal_ennreal_nndist]
      rw [lintegral_tsum]; swap
      · refine fun i ↦ (AEMeasurable.div ?_ measurable_vol₁.aemeasurable).restrict
        refine ((AEMeasurable.const_div ?_ _).pow_const _).mul_const _
        exact aemeasurable_id'.edist aemeasurable_const
      congr! 3 with i
      rw [← lintegral_const_mul' _ _ (by finiteness)]; congr 2 with x
      rw [← ENNReal.mul_comm_div, mul_div_assoc, mul_comm]
    _ ≤ 8 * C10_2_7 a * ∑' i, volume (czBall3 hX i) * 2 ^ (3 * a) := by
      gcongr with i; exact czOperatorBound_inner_le ha hX
    _ ≤ 8 * C10_2_7 a * 2 ^ (3 * a) * (2 ^ (6 * a) / α' a α * eLpNorm f 1 volume) := by
      rw [ENNReal.tsum_mul_right, mul_comm _ (2 ^ _), ← mul_assoc]; gcongr
      exact tsum_volume_czBall3_le hf hX (α'_pos αpos)
    _ = _ := by
      rw [← mul_assoc, ← mul_div_assoc, show (8 : ℝ≥0∞) * C10_2_7 a * 2 ^ (3 * a) * 2 ^ (6 * a) =
        2 ^ (9 * a + 3) * C10_2_7 a by ring, C10_2_7, coe_mul, ← mul_assoc, div_α'_eq,
        ENNReal.mul_div_cancel_right (by rw [c10_0_3]; positivity) (by rw [c10_0_3]; finiteness),
        show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← coe_pow, ← coe_mul, ← pow_add, C10_2_8]
      congr 4; ring

/-- The constant used in `estimate_bad`. -/
@[no_expose] def C10_2_9 (a : ℕ) : ℝ≥0 := 2 ^ (7 * a) / c10_0_3 a + C10_2_8 a

/-- Lemma 10.2.9 -/
private lemma estimate_bad (ha : 4 ≤ a) (hr : 0 < r)
    (hf : BoundedFiniteSupport f) (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) :
    distribution (czOperator K r (czRemainder f (α' a α))) (α / 2) volume ≤
    C10_2_9 a / α * eLpNorm f 1 volume := by
  rcases eq_zero_or_pos α with rfl | αpos; · simp only [not_lt_zero] at hα
  by_cases hX : GeneralCase f (α' a α)
  · calc
      _ ≤ volume (Ω f (α' a α) ∪
          {x ∈ (Ω f (α' a α))ᶜ | α / 2 < ‖czOperator K r (czRemainder f (α' a α)) x‖ₑ}) := by
        refine measure_mono fun x mx ↦ ?_
        rw [mem_setOf_eq] at mx
        simp_rw [mem_union, mem_setOf_eq, mx, and_true, mem_compl_iff]; tauto
      _ ≤ volume (Ω f (α' a α)) +
          volume {x ∈ (Ω f (α' a α))ᶜ | α / 2 < ‖czOperator K r (czRemainder f (α' a α)) x‖ₑ} :=
        measure_union_le _ _
      _ ≤ ∑' i, volume (czBall6 hX i) +
          volume ((Ω f (α' a α))ᶜ ∩ czOperatorBound hX ⁻¹' Ioi (α / 8)) := by
        gcongr
        · simp_rw [Ω, hX, dite_true]; exact measure_iUnion_le _
        · intro x mx; simp_rw [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi] at mx ⊢
          obtain ⟨mx₁, mx₂⟩ := mx; refine ⟨mx₁, ?_⟩; contrapose! mx₂
          calc
            _ ≤ 3 * czOperatorBound hX x + α / 8 := estimate_bad_partial hf hr hα mx₁ hX
            _ ≤ 3 * (α / 8) + α / 8 := by gcongr
            _ = _ := by
              rw [← add_one_mul, show (3 : ℝ≥0∞) + 1 = 4 by norm_num,
                show (8 : ℝ≥0∞) = 4 * 2 by norm_num, ← mul_div_assoc,
                ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
      _ ≤ 2 ^ a * ∑' i, volume (czBall3 hX i) + C10_2_8 a / α * eLpNorm f 1 volume := by
        rw [← ENNReal.tsum_mul_left]; gcongr with i
        · rw [czBall6, czBall3, show (6 : ℝ) = 2 * 3 by norm_num, mul_assoc]
          convert measure_ball_two_le_same (μ := volume) (czCenter hX i) (3 * czRadius hX i)
          unfold defaultA; norm_cast
        · exact distribution_czOperatorBound ha hf hα hX
      _ ≤ 2 ^ (7 * a) / α' a α * eLpNorm f 1 volume + C10_2_8 a / α * eLpNorm f 1 volume := by
        rw [show 7 * a = a + 6 * a by ring, pow_add, mul_div_assoc, mul_assoc]; gcongr
        exact tsum_volume_czBall3_le hf hX (α'_pos αpos)
      _ = _ := by
        nth_rw 1 [← add_mul, div_α'_eq, ← ENNReal.add_div, show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl,
          ← coe_pow, ← coe_div (by rw [c10_0_3]; positivity), ← coe_add, C10_2_9]
  · calc
      _ ≤ volume (univ : Set X) := measure_mono (subset_univ _)
      _ ≤ 2 ^ (4 * a) / α' a α * eLpNorm f 1 volume := volume_univ_le hf hX (α'_pos αpos)
      _ ≤ 2 ^ (7 * a) / c10_0_3 a / α * eLpNorm f 1 volume := by rw [div_α'_eq]; gcongr <;> norm_num
      _ ≤ _ := by
        rw [show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← coe_pow, ← coe_div (by rw [c10_0_3]; positivity),
          C10_2_9]
        gcongr; exact le_self_add

/- ### Lemma 10.0.3 -/

/-- The constant used in `czOperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 21 * a)

/-- Lemma 10.0.3, blueprint form. -/
lemma estimate_czOperator (ha : 4 ≤ a) (hr : 0 < r) (hf : BoundedFiniteSupport f)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    distribution (czOperator K r f) α volume ≤ C10_0_3 a / α * eLpNorm f 1 volume := by
  rcases le_or_gt α (⨍⁻ x, ‖f x‖ₑ / c10_0_3 a) with hα | hα
  · rw [laverage_eq] at hα
    rcases eq_zero_or_pos (eLpNorm f 1) with hf₂ | hf₂
    · rw [eLpNorm_eq_zero_iff hf.aestronglyMeasurable one_ne_zero] at hf₂
      have op0 : czOperator K r f = 0 := by
        ext x; rw [czOperator, integral_eq_zero_of_ae]; swap
        · have := (EventuallyEq.rfl (f := (K x ·))).mul hf₂
          simp only [mul_zero] at this; exact this.restrict
        simp
      simp_rw [op0, distribution, Pi.zero_apply, enorm_zero, not_lt_zero, setOf_false,
        measure_empty, zero_le]
    conv_rhs at hα =>
      enter [1, 2, x]; rw [div_eq_mul_inv, c10_0_3, coe_inv (by positivity), inv_inv]
    rw [lintegral_mul_const' _ _ (by finiteness), ← eLpNorm_one_eq_lintegral_enorm] at hα
    replace hα := mul_le_of_le_div' hα
    rw [← ENNReal.le_div_iff_mul_le] at hα; rotate_left
    · right; positivity
    · have hf₃ := (hf.memLp 1).eLpNorm_lt_top
      right; finiteness
    rw [mul_comm, ENNReal.mul_div_right_comm] at hα
    refine (measure_mono (subset_univ _)).trans (hα.trans ?_)
    rw [C10_0_3, add_assoc]; gcongr; exacts [one_le_two, by lia]
  rcases eq_zero_or_pos α with rfl | αpos; · simp only [_root_.not_lt_zero] at hα
  have α'pos : 0 < c10_0_3 a * α := by rw [c10_0_3]; positivity
  calc
    _ ≤ distribution (czOperator K r (czApproximation f (α' a α))) (α / 2) volume +
        distribution (czOperator K r (czRemainder f (α' a α))) (α / 2) volume := by
      refine le_trans (measure_mono fun x mx ↦ ?_) (measure_union_le _ _)
      simp only [mem_union, mem_setOf_eq] at mx ⊢; contrapose! mx
      calc
        _ = ‖czOperator K r (czApproximation f (α' a α)) x +
            czOperator K r (czRemainder f (α' a α)) x‖ₑ := by
          congr 1; rw [← sub_eq_iff_eq_add']
          have key := congrFun (czOperator_sub (K := K) hf (hf.czApproximation α'pos) hr) x
          rw [Pi.sub_apply] at key; exact key.symm
        _ ≤ _ := enorm_add_le _ _
        _ ≤ _ := add_le_add mx.1 mx.2
        _ = _ := ENNReal.add_halves α
    _ ≤ C10_2_6 a / α * eLpNorm f 1 volume + C10_2_9 a / α * eLpNorm f 1 volume :=
      add_le_add (estimate_good hf hα hT) (estimate_bad ha hr hf hα)
    _ ≤ _ := by
      rw [← add_mul, ← ENNReal.add_div, ← coe_add]; gcongr
      calc
        _ = 2 ^ (a ^ 3 - 9 * a - 2 : ℤ) + C10_2_9 a := by
          rw [C10_2_6, c10_0_3, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ two_ne_zero]
          congr 2; push_cast; ring
        _ ≤ 2 ^ a ^ 3 + 2 ^ (7 * a) * 2 ^ (a ^ 3 + 12 * a + 4) + 2 ^ (a ^ 3 + 11 * a + 4) := by
          rw [C10_2_9, ← add_assoc, c10_0_3, div_inv_eq_mul, C10_2_8]; gcongr
          rw [← zpow_natCast, Nat.cast_pow]
          gcongr
          · exact one_le_two
          · lia
        _ ≤ 3 * 2 ^ (a ^ 3 + 19 * a + 4) := by
          rw [← pow_add, show 7 * a + (a ^ 3 + 12 * a + 4) = a ^ 3 + 19 * a + 4 by ring,
            show (3 : ℝ≥0) = 1 + 1 + 1 by norm_num]
          simp_rw [add_mul, one_mul]; gcongr
          · exact one_le_two
          · linarith
          · exact one_le_two
          · norm_num
        _ ≤ 2 ^ (a ^ 3 + 19 * a + 6) := by
          rw [show a ^ 3 + 19 * a + 6 = 2 + (a ^ 3 + 19 * a + 4) by ring, pow_add _ 2]
          gcongr; norm_num
        _ ≤ _ := by rw [C10_0_3, add_assoc]; gcongr; exacts [one_le_two, by lia]

/-- Lemma 10.0.3, formulated differently. The blueprint version is basically this after
unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`. -/
theorem czOperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := fun f hf ↦ by
  refine ⟨czOperator_aestronglyMeasurable hf.aestronglyMeasurable, ?_⟩
  simp_rw [wnorm, one_ne_top, ite_false, wnorm', toReal_one, inv_one, rpow_one, iSup_le_iff]
  intro α; apply mul_le_of_le_div'; rw [ENNReal.mul_div_right_comm]
  exact estimate_czOperator ha hr hf hT

end
