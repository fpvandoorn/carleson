import Carleson.ToMathlib.HardyLittlewood
import Carleson.TwoSidedCarleson.Basic

open MeasureTheory Set Bornology Function ENNReal Metric Filter Topology
open scoped NNReal

noncomputable section

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
theorem maximal_theorem [Nonempty X] :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  apply HasWeakType.hasBoundedWeakType
  have : C10_2_1 a = C_weakType_globalMaximalFunction (defaultA a) 1 1 := by
    unfold C_weakType_globalMaximalFunction C_weakType_maximalFunction
    split_ifs with h; swap; simp at h
    simp_rw [C10_2_1_def, defaultA, coe_pow, coe_ofNat, Nat.cast_pow, Nat.cast_ofNat,
        NNReal.coe_one, div_one, rpow_ofNat, pow_mul', ← npow_add,
        two_add_two_eq_four]; rfl
  rw [this]
  apply hasWeakType_globalMaximalFunction (μ := volume) (p₁ := 1) (p₂ := 1) (by norm_num) le_rfl

-- Lemma 10.2.1, as formulated in the blueprint
variable (α) in
private theorem maximal_theorem' [Nonempty X] (hf : BoundedFiniteSupport f) :
    α * volume {x | α < ‖globalMaximalFunction volume 1 f x‖ₑ} ≤
    (C10_2_1 a) * eLpNorm f 1 volume := by
  by_cases hα : α = ∞
  · simp [hα]
  have h := (maximal_theorem f hf).2
  simp only [wnorm, one_ne_top, reduceIte, wnorm', toReal_one, inv_one, rpow_one, iSup_le_iff] at h
  exact coe_toNNReal hα ▸ h α.toNNReal

-- Alternate version of `maximal_theorem'`
private theorem maximal_theorem'' [Nonempty X] (hα : α > 0) (hf : BoundedFiniteSupport f) :
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
    have pd := (zero_le _).trans_lt ld'
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
  · contrapose! h; simp_rw [le_zero_iff, depth, iSup_eq_zero]; intro d hd
    by_contra! dpos; apply absurd _ h; rw [coe_ne_zero, ← zero_lt_iff] at dpos
    exact hd (mem_ball_self dpos)
  · obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h)
    lift ε to ℝ≥0 using εpos.le
    calc
      _ < ofNNReal ε := mod_cast εpos
      _ ≤ _ := le_biSup _ hε

lemma depth_eq_zero_iff_notMem (hO : IsOpen O) : depth O x = 0 ↔ x ∉ O := by
  have := (depth_pos_iff_mem hO (x := x)).not
  rwa [not_lt, le_zero_iff] at this

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
        exact add_le_add_right (ofReal_le_ofReal (dist_lt_of_not_disjoint_ball h).le) _
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
    _ ≤ (2 * depth O x).toReal / 6 + 3 * ((depth O y).toReal / 6) := by
      gcongr; exact mul_ne_top ofNat_ne_top dnt
    _ ≤ (2 * depth O x).toReal / 6 + 3 * ((2 * depth O x).toReal / 6) := by
      gcongr; exact mul_ne_top ofNat_ne_top dnt
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
    ← ENNReal.mul_le_mul_right vbpos.ne' vbnt]
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
      rw [show 6 * a = 3 * a + 3 * a by omega, pow_add, mul_assoc]; gcongr
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
    · rw [← zero_lt_iff, depth_pos_iff_mem hO.1]; exact maxU.1.1 mu
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
    exact ENNReal.mul_lt_mul_right' dpos.ne' dlt.ne (by norm_num)
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
    have hic : c i ∈ U.toSet := by simp [c, hi]
    by_cases hj : j < U.card; swap
    · simp_rw [r, hj, dite_false, ball_zero, disjoint_empty]
    have hjc : c j ∈ U.toSet := by simp [c, hj]
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
        rw [← encard_union_eq]; swap
        · exact disjoint_left.mpr fun i mi₁ mi₂ ↦ mi₁.1 mi₂.1
        congr; ext i; simp only [mem_setOf_eq, mem_union]; tauto
      _ = 0 + {u ∈ U.toSet | x ∈ ball u (3 * r' u)}.encard := by
        congr
        · simp_rw [encard_eq_zero, eq_empty_iff_forall_notMem, mem_setOf_eq, not_and]; intro i hi
          simp [r, hi]
        · set A := {i | i < U.card ∧ x ∈ ball (c i) (3 * r i)}
          set B := {u ∈ U.toSet | x ∈ ball u (3 * r' u)}
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
lemma volume_lt_of_not_GeneralCase [Nonempty X]
    (hf : BoundedFiniteSupport f) (h : ¬ GeneralCase f α) (hα : 0 < α) :
    volume (univ : Set X) < ∞ := by
  simp only [GeneralCase, not_exists, not_le] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hα.ne'
  refine lt_of_le_of_lt (eq_univ_iff_forall.mpr h ▸ maximal_theorem' α hf) ?_ |>.ne
  exact mul_lt_top coe_lt_top (hf.memLp 1).eLpNorm_lt_top

private lemma isFiniteMeasure_finite [Nonempty X]
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
abbrev czBall2 (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter hX i) (2 * czRadius hX i)

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
lemma encard_czBall3_le {hX : GeneralCase f α}
    {y : X} (hy : α < globalMaximalFunction volume 1 f y) :
    {i | y ∈ czBall3 hX i}.encard ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.2 y hy

lemma mem_czBall3_finite {hX : GeneralCase f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    {i | y ∈ czBall3 hX i}.Finite :=
  finite_of_encard_le_coe (encard_czBall3_le hy)

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
  refine mem_diff_of_mem ?_ ?_
  · rw [mem_ball]; linarith [lt_of_le_of_lt dist_nonneg hr]
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
  omega

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

private lemma globalMaximalFunction_preimage_finite [Nonempty X]
    (hα : α > 0) (hf : BoundedFiniteSupport f) :
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
  _ ≤ _ := by rw [Nat.cast_pow, ← pow_mul, mul_comm a 3]; gcongr; exact czBall_subset_czPartition

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
    mul_le_mul_right' (enorm_integral_le_lintegral_enorm f) _
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
def tsum_czRemainder' (hX : GeneralCase f α) (x : X) :
    ∑ᶠ i, czRemainder' hX i x = czRemainder f α x := by
  simp only [czRemainder', czRemainder]
  by_cases hx : ∃ j, x ∈ czPartition hX j
  · have ⟨j, hj⟩ := hx
    rw [finsum_eq_single _ j, indicator_of_mem hj]
    · rfl
    · refine fun i hi ↦ indicator_of_notMem ?_ _
      exact (czPartition_pairwise_disjoint_on hi).notMem_of_mem_right hj
  · simp only [czApproximation, hX, reduceDIte, hx, sub_self]
    exact finsum_eq_zero_of_forall_eq_zero fun i ↦ indicator_of_notMem (fun hi ↦ hx ⟨i, hi⟩) _

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

/-- Part of Lemma 10.2.5 (both cases). -/
lemma BoundedFiniteSupport.czApproximation [Nonempty X]
    (α : ℝ≥0∞) (hα : 0 < α) (hf : BoundedFiniteSupport f) :
    BoundedFiniteSupport (czApproximation f α) where
  memLp_top := by
    use (aemeasurable_czApproximation (hf := aemeasurable hf)).aestronglyMeasurable
    refine lt_of_le_of_lt ?_ (eLpNorm_lt_top hf)
    apply essSup_le_of_ae_le _ <| (ENNReal.ae_le_essSup (‖f ·‖ₑ)).mono (fun x h ↦ ?_)
    by_cases hX : GeneralCase f α
    · by_cases hx : ∃ j, x ∈ czPartition hX j
      · have ⟨j, hj⟩ := hx
        rw [czApproximation_def_of_mem hj]
        exact le_trans (enorm_integral_le_lintegral_enorm _) (setLAverage_le_essSup _)
      · simp [_root_.czApproximation, eLpNormEssSup, hX, hx, h]
    · simp only [_root_.czApproximation, hX, reduceDIte]
      exact le_trans (enorm_integral_le_lintegral_enorm _) (laverage_le_essSup _)
  measure_support_lt := by
    by_cases hX : GeneralCase f α; swap
    · exact lt_of_le_of_lt (measure_mono (subset_univ _)) <| volume_lt_of_not_GeneralCase hf hX hα
    calc volume (support (_root_.czApproximation f α))
      _ ≤ volume (globalMaximalFunction volume 1 f ⁻¹' Ioi α ∪ support f) := by
        refine measure_mono (fun x mem_supp ↦ ?_)
        by_cases hx : ∃ j, x ∈ czPartition hX j
        · left; rw [← iUnion_czPartition (hX := hX)]; exact (mem_iUnion.mpr hx)
        · right; simpa [_root_.czApproximation, hX, hx] using mem_supp
      _ ≤ volume _ + volume (support f) := measure_union_le _ _
      _ < ∞ := add_lt_top.mpr ⟨globalMaximalFunction_preimage_finite hα hf, hf.measure_support_lt⟩

/-- Part of Lemma 10.2.5, equation (10.2.16) (both cases).
This is true by definition, the work lies in `tsum_czRemainder'` -/
lemma czApproximation_add_czRemainder {x : X} :
    czApproximation f α x + czRemainder f α x = f x := by
  simp [czApproximation, czRemainder]

private lemma α_le_mul_α : α ≤ 2 ^ (3 * a) * α := by
  nth_rw 1 [← one_mul α]; gcongr; exact_mod_cast Nat.one_le_two_pow

-- Equation (10.2.17), finite case
private lemma enorm_czApproximation_le_finite [Nonempty X]
    (hα : ⨍⁻ x, ‖f x‖ₑ ≤ α) (hX : ¬ GeneralCase f α) :
    ∀ᵐ x, ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  simp only [czApproximation, hX, reduceDIte, eventually_const]
  exact le_trans (enorm_integral_le_lintegral_enorm f) <| hα.trans α_le_mul_α

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
        apply mul_le_mul_right'
        have := (ENNReal.inv_mul_le_iff (by simp) (by simp)).mpr <| volume_czBall7_le hX i
        rwa [← ENNReal.inv_le_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv] at this
      _ ≤ 2 ^ (3 * a) * (volume (czBall7 hX i))⁻¹ * ∫⁻ x in czBall7 hX i, ‖f x‖ₑ :=
        mul_le_mul_left' (lintegral_mono_set czPartition_subset_czBall7) _
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
lemma enorm_czApproximation_le [Nonempty X]
    {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ ≤ α) :
    ∀ᵐ x, ‖czApproximation f α x‖ₑ ≤ 2 ^ (3 * a) * α :=
  by_cases (enorm_czApproximation_le_infinite (hf := hf)) (enorm_czApproximation_le_finite hα)

-- Equation (10.2.18), finite case
private lemma eLpNorm_czApproximation_le_finite [Nonempty X]
    (hf : BoundedFiniteSupport f) (hα : 0 < α) (hX : ¬ GeneralCase f α) :
    eLpNorm (czApproximation f α) 1 volume ≤ eLpNorm f 1 volume := calc
  _ = ‖⨍ x, f x‖ₑ * volume univ := by
    unfold czApproximation; simp [hX, eLpNorm_const _ one_pos.ne' (NeZero.ne volume)]
  _ ≤ (⨍⁻ x, ‖f x‖ₑ ∂volume) * volume (univ : Set X) :=
    mul_le_mul_right' (enorm_integral_le_lintegral_enorm f) _
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
  gcongr tsum ?_ + ?_
  · apply lintegral_czPartition_le
  · simp only [union_diff_self, union_univ]
    apply le_of_eq ∘ setLIntegral_congr_fun_ae (by measurability)
    exact Eventually.of_forall (fun x hx ↦ by simp_all [czApproximation, hX])

/-- Part of Lemma 10.2.5, equation (10.2.18) (both cases). -/
lemma eLpNorm_czApproximation_le [Nonempty X]
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
lemma integral_czRemainder [Nonempty X] {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    ∫ x, czRemainder f α x = 0 := by
  have := isFiniteMeasure_finite hf hX hα
  simpa [czRemainder, czApproximation, hX] using integral_sub_average volume f

-- Inequality (10.2.32)
private lemma ineq_10_2_32 (hf : BoundedFiniteSupport f) {hX : GeneralCase f α}
    {i : ℕ} :
    eLpNorm (czRemainder' hX i) 1 volume ≤ 2 * (∫⁻ x in czPartition hX i, ‖f x‖ₑ) := calc
  _ = ∫⁻ x in czPartition hX i, ‖f x - czApproximation f α x‖ₑ := by
    simp [czRemainder', eLpNorm, eLpNorm', enorm_indicator_eq_indicator_enorm,
      lintegral_indicator <| MeasurableSet.czPartition hX i]
  _ ≤ ∫⁻ x in czPartition hX i, ‖f x‖ₑ + ‖czApproximation f α x‖ₑ :=
    lintegral_mono_fn (fun x ↦ enorm_sub_le)
  _ = (∫⁻ x in _, ‖f x‖ₑ) + ∫⁻ x in _, ‖_‖ₑ := lintegral_add_left' hf.aemeasurable.enorm.restrict _
  _ ≤ 2 * (∫⁻ x in czPartition hX i, ‖f x‖ₑ) := by
    rw [two_mul]; exact add_le_add_left (lintegral_czPartition_le i) _

/-- Part of Lemma 10.2.5, equation (10.2.21) (general case). -/
lemma eLpNorm_czRemainder'_le {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {i : ℕ} :
    eLpNorm (czRemainder' hX i) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 hX i) := by
  by_cases hi : czRadius hX i ≤ 0
  · simp [czRemainder'_eq_zero hX hi]
  calc
    _ ≤ 2 * (∫⁻ x in czPartition hX i, ‖f x‖ₑ) := ineq_10_2_32 hf
    _ ≤ 2 * (volume (czBall7 hX i) * α) := by
      apply mul_le_mul_left' ∘ (le_trans <| lintegral_mono_set czPartition_subset_czBall7)
      have h : volume (czBall7 hX i) ≠ 0 :=
        measure_ball_pos _ _ (mul_pos Nat.ofNat_pos (lt_of_not_ge hi)) |>.ne'
      simpa [laverage, ENNReal.inv_mul_le_iff h measure_ball_ne_top] using laverage_czBall7_le hX i
    _ ≤ 2 * ((volume (ball (czCenter hX i) (2 ^ 2 * (3 * czRadius hX i)))) * α) := by
      gcongr; convert czBall_subset_czBall (b := 7) (c := 12) using 2; ring
    _ ≤ 2 * (2 ^ (2 * a) * volume (czBall3 hX i) * α) := by
      gcongr;
      exact (measure_ball_two_le_same_iterate _ _ 2).trans_eq <| by simp [pow_mul, mul_comm 2]
    _ = 2 ^ (2 * a + 1) * α * volume (czBall3 hX i) := by ring

-- Used to prove `eLpNorm_czRemainder_le` and `tsum_eLpNorm_czRemainder_le`
private lemma eLpNorm_czRemainder_le' [Nonempty X]
    (hf : BoundedFiniteSupport f) (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f α) 1 volume ≤ 2 * ∫⁻ x, ‖f x‖ₑ :=
  have := isFiniteMeasure_finite hf hX (lt_of_le_of_lt (zero_le _) hα)
  calc
    _ = ∫⁻ x, ‖f x - ⨍ y, f y‖ₑ := by simp [czRemainder, eLpNorm, eLpNorm', czApproximation, hX]
    _ ≤ ∫⁻ x, (‖f x‖ₑ + ‖⨍ y, f y‖ₑ) := lintegral_mono (fun x ↦ enorm_sub_le)
    _ = (∫⁻ x, ‖f x‖ₑ) + ∫⁻ (x : X), ‖⨍ y, f y‖ₑ := lintegral_add_right' _ aemeasurable_const
    _ ≤ (∫⁻ x, ‖f x‖ₑ) + ∫⁻ (x : X), ⨍⁻ y, ‖f y‖ₑ := by
      gcongr; apply enorm_integral_le_lintegral_enorm
    _ = 2 * ∫⁻ x, ‖f x‖ₑ := by rw [two_mul, lintegral_laverage]

/-- Part of Lemma 10.2.5, equation (10.2.21) (finite case). -/
lemma eLpNorm_czRemainder_le [Nonempty X] {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    eLpNorm (czRemainder f α) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
  have := isFiniteMeasure_finite hf hX (lt_of_le_of_lt (zero_le _) hα)
  calc
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ := eLpNorm_czRemainder_le' hf hX hα
    _ ≤ 2 * (α * volume (univ : Set X)) := by
      rw [laverage_eq] at hα
      exact mul_le_mul_left' (a := 2) <| ENNReal.div_lt_iff (Or.inl (NeZero.ne _))
        (Or.inl this.measure_univ_lt_top.ne) |>.mp hα |>.le
    _ ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
      rw [← mul_assoc]; gcongr; simpa using pow_le_pow_right' one_le_two (Nat.le_add_left 1 (2 * a))

/-- Part of Lemma 10.2.5, equation (10.2.22) (general case). -/
lemma tsum_volume_czBall3_le [Nonempty X] (hf : BoundedFiniteSupport f)
    (hX : GeneralCase f α) (hα : 0 < α) :
    ∑' i, volume (czBall3 hX i) ≤ 2 ^ (6 * a) / α * eLpNorm f 1 volume := calc
  _ ≤ ∑' i, 2 ^ (2 * a) * volume (czBall hX i) := ENNReal.tsum_le_tsum (volume_czBall3_le hX)
  _ ≤ 2 ^ (2 * a) * volume (globalMaximalFunction volume 1 f ⁻¹' Ioi α) := by
    simp_rw [← smul_eq_mul, ENNReal.tsum_const_smul]
    gcongr
    rw [← measure_iUnion ?_ (fun i ↦ measurableSet_ball), ← iUnion_czPartition]
    · exact measure_mono <| iUnion_mono (fun i ↦ czBall_subset_czPartition)
    · refine (pairwise_disjoint_on (czBall hX)).mpr fun i j h ↦ ?_
      exact czBall_pairwiseDisjoint (mem_univ i) (mem_univ j) h.ne
  _ ≤ 2 ^ (2 * a) * ((C10_2_1 a) * eLpNorm f 1 volume / α) :=
    mul_le_mul_left' (maximal_theorem'' hα hf) _
  _ = 2 ^ (6 * a) / α * eLpNorm f 1 volume := by
    rw [C10_2_1_def, mul_div_assoc', mul_comm (_ / α), mul_div, ← mul_assoc]; norm_cast; ring_nf

/-- Part of Lemma 10.2.5, equation (10.2.22) (finite case). -/
lemma volume_univ_le [Nonempty X] {hf : BoundedFiniteSupport f}
    (hX : ¬ GeneralCase f α) (hα : 0 < α) :
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
lemma tsum_eLpNorm_czRemainder_le [Nonempty X]
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
  if hX : GeneralCase f α then ⋃ i, czBall2 hX i else univ

/-- The constant used in `estimate_good`. -/
irreducible_def C10_2_6 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a ^ 3 + 3 * a + 2) * c10_0_3 a

/-- Lemma 10.2.6 -/
lemma estimate_good [Nonempty X] {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    distribution (czOperator K r (czApproximation f (c10_0_3 a * α))) (α / 2) volume ≤
    C10_2_6 a / α * eLpNorm f 1 volume := by
  by_cases hα_top : α = ∞
  · simp [hα_top, top_div_of_lt_top ENNReal.ofNat_lt_top]
  have ne0 : (c10_0_3 a : ℝ≥0∞) ≠ 0 := by simp [c10_0_3]
  have hα' : 0 < c10_0_3 a * α := ENNReal.mul_pos ne0 hα.pos.ne'
  calc distribution ((czOperator K r (czApproximation f _))) (α / 2) volume
    _ = distribution ((czOperator K r (czApproximation f _)) ^ 2) ((α / 2) ^ 2) volume :=
      (distribution_pow _ _ _ _ two_pos.ne').symm
    _ ≤ ((α / 2) ^ 2)⁻¹ * ∫⁻ y, ‖((czOperator K r (czApproximation f _)) ^ 2) y‖ₑ := by
      apply distribution_le
      · exact ENNReal.pow_ne_zero (ENNReal.div_ne_zero.mpr ⟨ne_zero_of_lt hα, ofNat_ne_top⟩) 2
      · change AEMeasurable (czOperator K r (czApproximation f _) · ^ 2) volume
        refine czOperator_aestronglyMeasurable' ?_ |>.aemeasurable.pow_const 2
        exact aemeasurable_czApproximation (hf := hf.aemeasurable) |>.aestronglyMeasurable
    _ = 2 ^ 2 / α ^ 2 * ∫⁻ y, ‖czOperator K r (czApproximation f (c10_0_3 a * α)) y‖ₑ ^ 2 := by
      congr
      · calc ((α / 2) ^ 2)⁻¹
          _ = (α ^ 2 / 2 ^ 2)⁻¹ := by congr; exact_mod_cast α.div_rpow_of_nonneg 2 two_pos.le
          _ = 2 ^ 2 / α ^ 2     := ENNReal.inv_div (Or.inl coe_ne_top) (Or.inl (by norm_num))
      · simp
    _ ≤ 2 ^ 2 / α ^ 2 * ((C_Ts a) ^ 2 * ∫⁻ y, ‖czApproximation f (c10_0_3 a * α) y‖ₑ ^ 2) := by
      have half_pos : 0 < (2 : ℝ)⁻¹ := by norm_num
      refine mul_le_mul_left' (ENNReal.le_of_rpow_le half_pos ?_) (2 ^ 2 / α ^ 2)
      rw [ENNReal.mul_rpow_of_nonneg _ _ half_pos.le, ← ENNReal.rpow_natCast_mul]
      convert hT _ (BoundedFiniteSupport.czApproximation (c10_0_3 a * α) hα' hf) |>.2
      all_goals simp [eLpNorm, eLpNorm']
    _ ≤ 2^2/α^2 * ((C_Ts a) ^ 2 * ∫⁻ y, 2^(3*a) * c10_0_3 a * α * ‖czApproximation f _ y‖ₑ) := by
      gcongr _ * (_ * ?_)
      suffices ∀ᵐ x, ‖czApproximation f (c10_0_3 a * α) x‖ₑ ≤ 2 ^ (3 * a) * c10_0_3 a * α by
        apply lintegral_mono_ae ∘ this.mono; intros; rw [sq]; gcongr
      simp_rw [ENNReal.div_eq_inv_mul] at hα
      rw [← laverage_const_mul (inv_ne_top.mpr ne0), ← ENNReal.div_eq_inv_mul] at hα
      refine mul_assoc _ _ α ▸ enorm_czApproximation_le ?_ (hf := hf)
      exact mul_comm α _ ▸ (ENNReal.div_lt_iff (Or.inl ne0) (Or.inl coe_ne_top)).mp hα |>.le
    _ = 2^2/α^2 * ((C_Ts a)^2 * (2^(3*a) * c10_0_3 a * α * ∫⁻ y, ‖czApproximation f _ y‖ₑ)) := by
      have : 2 ^ (3*a) * c10_0_3 a * α ≠ ∞ := mul_ne_top (mul_ne_top coe_ne_top coe_ne_top) hα_top
      rw [lintegral_const_mul' _ _ this]
    _ ≤ 2 ^ 2 / α ^ 2 * ((C_Ts a) ^ 2 * (2 ^ (3 * a) * c10_0_3 a * α * eLpNorm f 1 volume)) := by
      gcongr; simpa [eLpNorm, eLpNorm'] using eLpNorm_czApproximation_le (hf := hf) hα'
    _ = 2 ^ 2 / α^2 * ((C_Ts a) ^ 2 * (2 ^ (3 * a) * c10_0_3 a * α)) * eLpNorm f 1 volume := by ring
    _ = (2 ^ 2 * (C_Ts a) ^ 2 * 2 ^ (3 * a) * c10_0_3 a * α) / α ^ 2 * eLpNorm f 1 volume := by
      rw [ENNReal.mul_comm_div, mul_div]; ring_nf
    _ = (2 ^ 2 * (C_Ts a) ^ 2 * 2 ^ (3 * a) * c10_0_3 a) / α * eLpNorm f 1 volume := by
      rw [sq α, ENNReal.mul_div_mul_right _ _ (ne_zero_of_lt hα) hα_top]
    _ = (C10_2_6 a) / α * eLpNorm f 1 volume := by simp only [C_Ts, C10_2_6]; norm_cast; ring_nf

/-- The constant used in `czOperatorBound`. -/
irreducible_def C10_2_7 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1) * c10_0_3 a

/-- The function `F` defined in Lemma 10.2.7. -/
def czOperatorBound (hX : GeneralCase f α) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * ∑' i, ((czRadius hX i).toNNReal / nndist x (czCenter hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 hX i) / volume (ball x (dist x (czCenter hX i)))

/-- Lemma 10.2.7.
Note that `hx` implies `hX`, but we keep the superfluous hypothesis to shorten the statement. -/
lemma estimate_bad_partial (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hx : x ∈ (Ω f α)ᶜ) (hX : GeneralCase f α) :
    ‖czOperator K r (czRemainder f α) x‖ₑ ≤ 3 * czOperatorBound hX x + α / 8 := by
  sorry

lemma aemeasurable_V {y : X} :
    AEMeasurable (fun x ↦ volume (ball x (dist x y))) volume := by
  sorry

lemma czOperatorBound_inner_le (ha : 4 ≤ a) (hX : GeneralCase f α) {i : ℕ} :
    ∫⁻ x in (Ω f α)ᶜ, ((czRadius hX i).toNNReal / edist x (czCenter hX i)) ^ (a : ℝ)⁻¹ /
      volume (ball x (dist x (czCenter hX i))) ≤ 2 ^ (3 * a) := by
  set r := czRadius hX i
  set c := czCenter hX i
  rcases le_or_gt r 0 with hr | hr
  · simp_rw [Real.toNNReal_of_nonpos hr, coe_zero, ENNReal.zero_div]
    rw [ENNReal.zero_rpow_of_pos (by rw [inv_pos, Nat.cast_pos]; exact zero_lt_four.trans_le ha)]
    simp_rw [ENNReal.zero_div, lintegral_zero]; exact zero_le _
  calc
    _ ≤ ∫⁻ x in (czBall2 hX i)ᶜ,
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball x (dist x c)) := by
      apply lintegral_mono_set; simp_rw [compl_subset_compl, Ω, hX, dite_true]
      exact subset_iUnion ..
    _ ≤ ∫⁻ x in (czBall2 hX i)ᶜ,
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / (volume (ball c (dist x c)) / 2 ^ a) := by
      gcongr with x; apply div_le_of_le_mul
      calc
        _ ≤ volume (ball x (2 * dist x c)) :=
          measure_mono (ball_subset_ball' (by rw [dist_comm, two_mul]))
        _ ≤ _ := by
          rw [mul_comm _ (2 ^ a)]
          convert measure_ball_two_le_same (μ := volume) x (dist x c)
          unfold defaultA; norm_cast
    _ = 2 ^ a * ∫⁻ x in (czBall2 hX i)ᶜ,
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball c (dist x c)) := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]; congr! 2 with x
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (.inl (by finiteness)) (.inl (by positivity)),
        ENNReal.mul_comm_div]
    _ ≤ 2 ^ a * ∫⁻ x in ⋃ n, ball c (2 ^ (n + 1) * r) \ ball c (2 ^ n * r),
        (r.toNNReal / edist x c) ^ (a : ℝ)⁻¹ / volume (ball c (dist x c)) := by
      gcongr; refine lintegral_mono_set fun x mx ↦ ?_
      rw [czBall2, mem_compl_iff, mem_ball, not_lt] at mx; change 2 * r ≤ dist x c at mx
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
          rw [← mul_assoc, ← pow_succ']; exact measure_mono diff_subset
        _ ≤ _ := by
          convert measure_ball_two_le_same (μ := volume) c (2 ^ n * r)
          unfold defaultA; norm_cast
    _ ≤ 2 ^ a * 2 ^ a * 2 ^ a := by
      rw [ENNReal.tsum_mul_right, ← mul_assoc]; gcongr
      rw [← rpow_natCast]; exact geometric_series_estimate (by norm_cast; omega)
    _ = _ := by norm_cast; ring

variable [CompatibleFunctions ℝ X (defaultA a)]

/-- Lemma 10.2.8 -/
lemma distribution_czOperatorBound (ha : 4 ≤ a) (hf : BoundedFiniteSupport f)
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    volume ((Ω f α)ᶜ ∩ czOperatorBound hX ⁻¹' Ioi (α / 8)) ≤
    (2 ^ a)⁻¹ / α * eLpNorm f 1 volume := by
  rcases eq_zero_or_pos α with rfl | αpos; · simp at hα
  rcases eq_top_or_lt_top α with rfl | αlt
  · have : czOperatorBound hX ⁻¹' Ioi (⊤ / 8) = ∅ := by
      rw [top_div_of_ne_top (by norm_num), isMax_top.Ioi_eq, preimage_empty]
    rw [this, inter_empty, measure_empty]; exact zero_le _
  calc
    _ ≤ (volume.restrict (Ω f α)ᶜ) {x | α / 8 ≤ czOperatorBound hX x} := by
      rw [inter_comm, ← Measure.restrict_apply']; swap
      · apply MeasurableSet.compl; simp_rw [Ω, hX, dite_true]
        exact MeasurableSet.iUnion fun _ ↦ measurableSet_ball
      gcongr; intro x mx; simp only [mem_preimage, mem_Ioi, mem_setOf_eq] at mx ⊢; exact mx.le
    _ ≤ (∫⁻ x in (Ω f α)ᶜ, czOperatorBound hX x) / (α / 8) := by
      apply meas_ge_le_lintegral_div
      · refine ((AEMeasurable.ennreal_tsum fun i ↦ ?_).const_mul _).restrict
        refine AEMeasurable.div ?_ aemeasurable_V
        refine ((AEMeasurable.const_div ?_ _).pow_const _).mul_const _
        simp only [coe_nnreal_ennreal_nndist]
        exact aemeasurable_id'.edist aemeasurable_const
      · simp [αpos.ne']
      · exact ENNReal.div_ne_top αlt.ne (by norm_num)
    _ ≤ 8 * C10_2_7 a * ∑' i, volume (czBall3 hX i) * ∫⁻ x in (Ω f α)ᶜ,
        ((czRadius hX i).toNNReal / edist x (czCenter hX i)) ^ (a : ℝ)⁻¹ /
        volume (ball x (dist x (czCenter hX i))) := by
      unfold czOperatorBound
      rw [lintegral_const_mul' _ _ (by finiteness), ENNReal.div_eq_inv_mul,
        ENNReal.inv_div (.inr αlt.ne) (.inr αpos.ne'), ← mul_assoc, ← mul_assoc,
        ← ENNReal.mul_div_right_comm, ENNReal.div_mul_cancel αpos.ne' αlt.ne]
      simp only [coe_nnreal_ennreal_nndist]
      rw [lintegral_tsum]; swap
      · refine fun i ↦ (AEMeasurable.div ?_ aemeasurable_V).restrict
        refine ((AEMeasurable.const_div ?_ _).pow_const _).mul_const _
        exact aemeasurable_id'.edist aemeasurable_const
      congr! 3 with i
      rw [← lintegral_const_mul' _ _ (by finiteness)]; congr 2 with x
      rw [← ENNReal.mul_comm_div, mul_div_assoc, mul_comm]
    _ ≤ 8 * C10_2_7 a * ∑' i, volume (czBall3 hX i) * 2 ^ (3 * a) := by
      gcongr with i; exact czOperatorBound_inner_le ha hX
    _ ≤ 8 * C10_2_7 a * 2 ^ (3 * a) * (2 ^ (6 * a) / α * eLpNorm f 1 volume) := by
      rw [ENNReal.tsum_mul_right, mul_comm _ (2 ^ _), ← mul_assoc]; gcongr
      exact tsum_volume_czBall3_le hf hX αpos
    _ = _ := by
      rw [← mul_assoc, ← mul_div_assoc, show (8 : ℝ≥0∞) = 2 ^ 3 by norm_num,
        show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl]
      simp_rw [← coe_pow, ← coe_mul]; rw [← coe_inv (by positivity)]; congr
      rw [C10_2_7, ← mul_assoc, ← pow_add, mul_rotate, ← pow_add, ← mul_assoc,
        ← pow_add, show 3 * a + 6 * a + (3 + (a ^ 3 + 2 * a + 1)) = a ^ 3 + 11 * a + 4 by ring,
        c10_0_3, show a ^ 3 + 12 * a + 4 = a ^ 3 + 11 * a + 4 + a by ring, pow_add _ _ a,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

variable [IsCancellative X (defaultτ a)]

/-- The constant used in `estimate_bad`. -/
irreducible_def C10_2_9 (a : ℕ) : ℝ≥0 := 2 ^ (5 * a) / c10_0_3 a + 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.9 -/
-- In the proof, case on `GeneralCase f α`, noting in the finite case that `Ω = univ`
lemma estimate_bad (ha : 4 ≤ a) (hf : BoundedFiniteSupport f)
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) :
    distribution (czOperator K r (czRemainder f α)) (α / 2) volume ≤
    C10_2_9 a / α * eLpNorm f 1 volume := by
  sorry

/- ### Lemmas 10.0.3 -/

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
-- in proof: do cases on `α ≤ ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a`.
-- If true, use the argument directly below (10.2.37)
theorem czoperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
