import Carleson.Defs

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {K : X → X → ℂ}

namespace MetricΘ

variable [CompatibleFunctions ℝ X (defaultA a)]

/-- We choose as metric space instance on `Θ` one given by an arbitrary ball.
The metric given by all other balls are equivalent. -/
instance : PseudoMetricSpace (Θ X) :=
  inferInstanceAs <| PseudoMetricSpace <| WithFunctionDistance o 1

instance : TopologicalSpace (Θ X) := inferInstance

lemma dist_eq_cdist {f g : Θ X} : dist f g = dist_{o, 1} f g := rfl

/-!
The following two lemmas state that the distance could be equivalently given by any other cdist.
-/

lemma dist_le_cdist {f g : Θ X} {x : X} {r : ℝ} (hr : 0 < r) :
    dist f g ≤ As (defaultA a) ((1 + dist o x) / r) * dist_{x, r} f g :=
  cdist_le_mul_cdist hr (by norm_num) f g

lemma cdist_le_dist {f g : Θ X} {x : X} {r : ℝ} (hr : 0 < r) :
    dist_{x, r} f g ≤ As (defaultA a) (r + dist o x) * dist f g := by
  rw [← div_one (_ + _), dist_comm o]
  exact cdist_le_mul_cdist (by norm_num) hr f g

instance : SecondCountableTopology (Θ X) :=
  CompatibleFunctions.allBallsCoverBalls.secondCountableTopology one_lt_two

end MetricΘ

open MetricΘ

variable [KernelProofData a K] {θ ϑ : Θ X} {Q : SimpleFunc X (Θ X)} {R₁ R₂ : ℝ} {f : X → ℂ} {x : X}

lemma measurable_carlesonOperatorIntegrand (mf : Measurable f) :
    Measurable (fun x ↦ carlesonOperatorIntegrand K (Q x) R₁ R₂ f x) := by
  unfold carlesonOperatorIntegrand
  rw [← stronglyMeasurable_iff_measurable]
  conv => enter [1, x]; rw [← integral_indicator Annulus.measurableSet_oo]
  apply StronglyMeasurable.integral_prod_right
  rw [stronglyMeasurable_iff_measurable]
  refine Measurable.indicator ?_ (measurable_dist.comp measurable_id measurableSet_Ioo)
  apply (measurable_K.mul (mf.comp measurable_snd)).mul
  exact ((Complex.measurable_ofReal.comp measurable_Q₂).const_mul I).cexp

open Annulus in
/-- Let `f` be integrable over an annulus with fixed radii `R₁, R₂`.
Then `fun R ↦ ∫ y in oo x R R₂, f y` is right-continuous at `R₁`. -/
lemma rightContinuous_integral_annulus (iof : IntegrableOn f (oo x R₁ R₂)) :
    ContinuousWithinAt (fun R ↦ ∫ y in oo x R R₂, f y) (Ici R₁) R₁ := by
  -- If `R₁ ≥ R₂` the proof is easy
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · simp_rw [continuousWithinAt_iff, mem_Ici]; intro ε εpos
    use 1, zero_lt_one; intro R' hR' _
    rw [oo_eq_empty (hR₂.trans hR'), oo_eq_empty hR₂, setIntegral_empty, dist_self]
    exact εpos
  -- Reduce to showing that the volumes of annuli `oc x R₁ R` can be arbitrarily small
  suffices Tendsto (volume.restrict (oo x R₁ R₂) ∘ (oc x R₁ ·)) (𝓝[≥] R₁) (nhds 0) by
    simp_rw [continuousWithinAt_iff, mem_Ici]; intro ε εpos
    have key := iof.tendsto_setIntegral_nhds_zero this
    simp_rw [← integral_indicator measurableSet_oc, ← integral_indicator measurableSet_oo,
      indicator_indicator, tendsto_nhdsWithin_nhds, mem_Ici] at key
    specialize key _ εpos; obtain ⟨δ, δpos, nb⟩ := key
    use min δ (R₂ - R₁), lt_min_iff.mpr ⟨δpos, sub_pos.mpr hR₂⟩; intro y ly dy
    rw [lt_min_iff] at dy; specialize nb ly dy.1
    rw [dist_eq_norm, Real.norm_of_nonneg (sub_nonneg.mpr ly), sub_lt_sub_iff_right] at dy
    rw [dist_eq_norm, sub_zero, inter_eq_self_of_subset_right (oc_subset_oo le_rfl dy.2),
      integral_indicator measurableSet_oc] at nb
    rw [dist_eq_norm']; convert nb
    rw [sub_eq_iff_eq_add, ← setIntegral_union _ measurableSet_oo]; rotate_left
    · exact iof.mono_set (oc_subset_oo le_rfl dy.2)
    · exact iof.mono_set (oo_subset_oo ly le_rfl)
    · simp_rw [disjoint_left, oc, oo, mem_setOf, mem_Ioc, mem_Ioo, not_and_or, not_lt]
      exact fun z mz ↦ .inl mz.2
    rw [oc_union_oo ly dy.2]
  -- Obtain a strictly antitone sequence of numbers less than `R₂` and converging to `R₁`.
  -- By monotone convergence we reduce to showing that the volumes of annuli `oc x R₁ R`
  -- along this sequence can be arbitrarily small
  obtain ⟨u, sau, mu, ttu⟩ := exists_seq_strictAnti_tendsto' hR₂
  suffices Tendsto (fun n ↦ volume (oc x R₁ (u n))) atTop (nhds 0) by
    rw [ENNReal.tendsto_nhds_zero]; intro ε εpos
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    rw [ENNReal.tendsto_atTop_zero] at this
    specialize this _ εpos; obtain ⟨n, hn⟩ := this; specialize hn _ le_rfl
    use u n - R₁, sub_pos.mpr (mu n).1; intro y dy ly
    rw [dist_eq_norm, Real.norm_of_nonneg (sub_nonneg.mpr ly), sub_lt_sub_iff_right] at dy
    rw [Function.comp_apply, Measure.restrict_apply measurableSet_oc,
      inter_eq_self_of_subset_left (oc_subset_oo le_rfl (dy.trans (mu n).2))]
    exact (measure_mono (oc_subset_oc le_rfl dy.le)).trans hn
  -- Split the annulus along the `u n`...
  let s (n : ℕ) := oc x (u (n + 1)) (u n)
  have us (k : ℕ) : ⋃ n, s (k + n) = oc x R₁ (u k) := by
    ext y; simp_rw [mem_iUnion, s, oc, mem_setOf, mem_Ioc]; constructor <;> intro h
    · obtain ⟨n, hn₁, hn₂⟩ := h
      exact ⟨(mu (k + n + 1)).1.trans hn₁, hn₂.trans (sau.antitone (Nat.le_add_right ..))⟩
    · let T : Set ℕ := {n | u (k + n) < dist x y}
      have neT : T.Nonempty := by
        rw [Metric.tendsto_atTop] at ttu
        specialize ttu (dist x y - R₁) (by linarith only [h.1]); obtain ⟨N, hN⟩ := ttu
        specialize hN (k + N) (Nat.le_add_left ..)
        rw [dist_eq_norm, Real.norm_of_nonneg (by linarith only [(mu (k + N)).1]),
          sub_lt_sub_iff_right] at hN; use N, hN
      have wfT : T.IsWF := IsWF.of_wellFoundedLT T
      use wfT.min neT - 1
      have minT_mem := wfT.min_mem neT; simp_rw [T, mem_setOf] at minT_mem
      have minT_pos : wfT.min neT ≠ 0 := by
        by_contra! h'; rw [h'] at minT_mem; exact absurd h.2 (not_le.mpr minT_mem)
      nth_rw 1 [← Nat.add_sub_assoc (by omega), Nat.sub_add_cancel (by omega), ← not_lt]
      refine ⟨minT_mem, ?_⟩; change wfT.min neT - 1 ∉ T; contrapose! minT_pos
      replace minT_pos := wfT.min_le neT minT_pos; omega
  have ds (k : ℕ) : Pairwise (Function.onFun Disjoint fun n ↦ s (k + n)) := fun i j hn ↦ by
    change Disjoint (s (k + i)) (s (k + j))
    wlog hl : i < j generalizing i j; · exact (this j i hn.symm (by omega)).symm
    simp_rw [s, disjoint_left, oc, mem_setOf, mem_Ioc]; intro y my
    rw [not_and_or, not_le]; right
    exact (sau.antitone (show k + i + 1 ≤ k + j by omega)).trans_lt my.1
  -- ...and appeal to `ENNReal.tendsto_sum_nat_add`
  conv =>
    enter [1, n]; rw [← us, measure_iUnion (ds n) (fun _ ↦ measurableSet_oc)]
    enter [1, k]; rw [add_comm]
  specialize us 0; specialize ds 0; simp_rw [zero_add] at us ds
  apply tendsto_sum_nat_add fun n ↦ volume (s n)
  rw [← measure_iUnion ds (fun _ ↦ measurableSet_oc), us, ← lt_top_iff_ne_top]
  calc
    _ ≤ volume (closedBall x (u 0)) := by
      refine measure_mono fun y my ↦ ?_; rw [oc_eq] at my; exact my.1
    _ < _ := measure_closedBall_lt_top

open Annulus in
/-- Let `f` be integrable over an annulus with fixed radii `R₁, R₂`.
Then `fun R ↦ ∫ y in oo x R₁ R, f y` is left-continuous at `R₂`. -/
lemma leftContinuous_integral_annulus (iof : IntegrableOn f (oo x R₁ R₂)) :
    ContinuousWithinAt (fun R ↦ ∫ y in oo x R₁ R, f y) (Iic R₂) R₂ := by
  -- If `R₁ ≥ R₂` the proof is easy
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · simp_rw [continuousWithinAt_iff, mem_Iic]; intro ε εpos
    use 1, zero_lt_one; intro R' hR' _
    rw [oo_eq_empty (hR'.trans hR₂), oo_eq_empty hR₂, setIntegral_empty, dist_self]
    exact εpos
  -- Reduce to showing that the volumes of annuli `co x R R₂` can be arbitrarily small
  suffices Tendsto (volume.restrict (oo x R₁ R₂) ∘ (co x · R₂)) (𝓝[≤] R₂) (nhds 0) by
    simp_rw [continuousWithinAt_iff, mem_Iic]; intro ε εpos
    have key := iof.tendsto_setIntegral_nhds_zero this
    simp_rw [← integral_indicator measurableSet_co, ← integral_indicator measurableSet_oo,
      indicator_indicator, tendsto_nhdsWithin_nhds, mem_Iic] at key
    specialize key _ εpos; obtain ⟨δ, δpos, nb⟩ := key
    use min δ (R₂ - R₁), lt_min_iff.mpr ⟨δpos, sub_pos.mpr hR₂⟩; intro y ly dy
    rw [lt_min_iff] at dy; specialize nb ly dy.1
    rw [dist_eq_norm', Real.norm_of_nonneg (sub_nonneg.mpr ly), sub_lt_sub_iff_left] at dy
    rw [dist_eq_norm, sub_zero, inter_eq_self_of_subset_right (co_subset_oo dy.2 le_rfl),
      integral_indicator measurableSet_co] at nb
    rw [dist_eq_norm']; convert nb
    rw [sub_eq_iff_eq_add', ← setIntegral_union _ measurableSet_co]; rotate_left
    · exact iof.mono_set (oo_subset_oo le_rfl ly)
    · exact iof.mono_set (co_subset_oo dy.2 le_rfl)
    · simp_rw [disjoint_left, co, oo, mem_setOf, mem_Ico, mem_Ioo, not_and_or, not_le]
      exact fun z mz ↦ .inl mz.2
    rw [oo_union_co dy.2 ly]
  -- Obtain a strictly monotone sequence of numbers greater than `R₁` and converging to `R₂`.
  -- By monotone convergence we reduce to showing that the volumes of annuli `co x R R₂`
  -- along this sequence can be arbitrarily small
  obtain ⟨u, smu, mu, ttu⟩ := exists_seq_strictMono_tendsto' hR₂
  suffices Tendsto (fun n ↦ volume (co x (u n) R₂)) atTop (nhds 0) by
    rw [ENNReal.tendsto_nhds_zero]; intro ε εpos
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    rw [ENNReal.tendsto_atTop_zero] at this
    specialize this _ εpos; obtain ⟨n, hn⟩ := this; specialize hn _ le_rfl
    use R₂ - u n, sub_pos.mpr (mu n).2; intro y dy ly
    rw [dist_eq_norm', Real.norm_of_nonneg (sub_nonneg.mpr ly), sub_lt_sub_iff_left] at dy
    rw [Function.comp_apply, Measure.restrict_apply measurableSet_co,
      inter_eq_self_of_subset_left (co_subset_oo ((mu n).1.trans dy) le_rfl)]
    exact (measure_mono (co_subset_co dy.le le_rfl)).trans hn
  -- Split the annulus along the `u n`...
  let s (n : ℕ) := co x (u n) (u (n + 1))
  have us (k : ℕ) : ⋃ n, s (k + n) = co x (u k) R₂ := by
    ext y; simp_rw [mem_iUnion, s, co, mem_setOf, mem_Ico]; constructor <;> intro h
    · obtain ⟨n, hn₁, hn₂⟩ := h
      exact ⟨(smu.monotone (Nat.le_add_right ..)).trans hn₁, hn₂.trans (mu (k + n + 1)).2⟩
    · let T : Set ℕ := {n | dist x y < u (k + n)}
      have neT : T.Nonempty := by
        rw [Metric.tendsto_atTop] at ttu
        specialize ttu (R₂ - dist x y) (by linarith only [h.2]); obtain ⟨N, hN⟩ := ttu
        specialize hN (k + N) (Nat.le_add_left ..)
        rw [dist_eq_norm', Real.norm_of_nonneg (by linarith only [(mu (k + N)).2]),
          sub_lt_sub_iff_left] at hN; use N, hN
      have wfT : T.IsWF := IsWF.of_wellFoundedLT T
      use wfT.min neT - 1
      have minT_mem := wfT.min_mem neT; simp_rw [T, mem_setOf] at minT_mem
      have minT_pos : wfT.min neT ≠ 0 := by
        by_contra! h'; rw [h'] at minT_mem; exact absurd h.1 (not_le.mpr minT_mem)
      nth_rw 2 [← Nat.add_sub_assoc (by omega)]; rw [Nat.sub_add_cancel (by omega), ← not_lt]
      refine ⟨?_, minT_mem⟩; change wfT.min neT - 1 ∉ T; contrapose! minT_pos
      replace minT_pos := wfT.min_le neT minT_pos; omega
  have ds (k : ℕ) : Pairwise (Function.onFun Disjoint fun n ↦ s (k + n)) := fun i j hn ↦ by
    change Disjoint (s (k + i)) (s (k + j))
    wlog hl : i < j generalizing i j; · exact (this j i hn.symm (by omega)).symm
    simp_rw [s, disjoint_left, co, mem_setOf, mem_Ico]; intro y my
    rw [not_and_or, not_le]; left
    exact my.2.trans_le (smu.monotone (show k + i + 1 ≤ k + j by omega))
  -- ...and appeal to `ENNReal.tendsto_sum_nat_add`
  conv =>
    enter [1, n]; rw [← us, measure_iUnion (ds n) (fun _ ↦ measurableSet_co)]
    enter [1, k]; rw [add_comm]
  specialize us 0; specialize ds 0; simp_rw [zero_add] at us ds
  apply tendsto_sum_nat_add fun n ↦ volume (s n)
  rw [← measure_iUnion ds (fun _ ↦ measurableSet_co), us, ← lt_top_iff_ne_top]
  calc
    _ ≤ volume (ball x R₂) := by
      refine measure_mono fun y my ↦ ?_; rw [co_eq] at my; exact my.1
    _ < _ := measure_ball_lt_top

/-- The integrand of `carlesonOperatorIntegrand` is integrable over the `R₁, R₂` annulus. -/
lemma integrableOn_coi_inner_annulus (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    IntegrableOn (fun y ↦ K x y * f y * exp (I * θ y)) (Annulus.oo x R₁ R₂) := by
  simp_rw [mul_assoc]; refine integrableOn_K_mul ?_ _ hR₁ fun y my ↦ ?_
  · refine Integrable.bdd_mul ?_ mf.aestronglyMeasurable.restrict ⟨_, nf⟩
    apply Measure.integrableOn_of_bounded (M := 1)
    · rw [← lt_top_iff_ne_top]
      calc
        _ ≤ volume (ball x R₂) := by
          refine measure_mono fun y my ↦ ?_
          rw [Annulus.oo, mem_setOf, mem_Ioo] at my; rw [mem_ball']; exact my.2
        _ < _ := measure_ball_lt_top
    · exact ((Complex.measurable_ofReal.comp (by fun_prop)).const_mul I).cexp.aestronglyMeasurable
    · refine Eventually.of_forall fun y ↦ ?_
      rw [mul_comm, norm_exp_ofReal_mul_I]
  · rw [Annulus.oo, mem_setOf, mem_Ioo] at my
    rw [mem_compl_iff, mem_ball', not_lt]; exact my.1.le

lemma rightContinuous_carlesonOperatorIntegrand
    (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ · R₂ f x) (Ici R₁) R₁ :=
  rightContinuous_integral_annulus (integrableOn_coi_inner_annulus mf nf hR₁)

lemma leftContinuous_carlesonOperatorIntegrand
    (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ R₁ · f x) (Iic R₂) R₂ :=
  leftContinuous_integral_annulus (integrableOn_coi_inner_annulus mf nf hR₁)

variable (θ x) in
/-- Given `0 < R₁ < R₂`, move `(R₁, R₂)` to rational `(q₁, q₂)` where `R₁ < q₁ < q₂ < R₂`
and the norm of `carlesonOperatorIntegrand` changes by at most `ε`. -/
lemma exists_rat_near_carlesonOperatorIntegrand
    (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂) {ε : ℝ} (εpos : 0 < ε) :
    ∃ q₁ q₂ : ℚ, R₁ < q₁ ∧ q₁ < q₂ ∧ q₂ < R₂ ∧
    dist (carlesonOperatorIntegrand K θ q₁ q₂ f x)
    (carlesonOperatorIntegrand K θ R₁ R₂ f x) < ε := by
  -- Shift `R₁` to a larger rational with error less than `ε / 2`
  have rcon := @rightContinuous_carlesonOperatorIntegrand _ _ _ _ _ θ R₁ R₂ _ x mf nf hR₁
  rw [Metric.continuousWithinAt_iff] at rcon; specialize rcon _ (half_pos εpos)
  obtain ⟨δ₁, δ₁pos, hq₁⟩ := rcon
  have lt₁ : R₁ < min (R₁ + δ₁) R₂ := by rw [lt_min_iff]; constructor <;> linarith
  obtain ⟨q₁, lbq₁, ubq₁⟩ := exists_rat_btwn lt₁
  rw [lt_min_iff, ← sub_lt_iff_lt_add'] at ubq₁; obtain ⟨ubq₁, lR₂⟩ := ubq₁
  have dq₁ : dist ↑q₁ R₁ < δ₁ := by rwa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr lbq₁.le)]
  specialize hq₁ lbq₁.le dq₁
  -- Shift `R₂` to a smaller rational with error less than `ε / 2`
  have q₁pos : (0 : ℝ) < q₁ := hR₁.trans lbq₁
  have lcon := @leftContinuous_carlesonOperatorIntegrand _ _ _ _ _ θ q₁ R₂ _ x mf nf q₁pos
  rw [Metric.continuousWithinAt_iff] at lcon; specialize lcon _ (half_pos εpos)
  obtain ⟨δ₂, δ₂pos, hq₂⟩ := lcon
  have lt₂ : max (R₂ - δ₂) q₁ < R₂ := by rw [max_lt_iff]; constructor <;> linarith
  obtain ⟨q₂, lbq₂, ubq₂⟩ := exists_rat_btwn lt₂
  rw [max_lt_iff, sub_lt_comm] at lbq₂; obtain ⟨lbq₂, lq⟩ := lbq₂
  have dq₂ : dist ↑q₂ R₂ < δ₂ := by
    rwa [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ubq₂.le)]
  specialize hq₂ ubq₂.le dq₂
  -- The rest is just the triangle inequality
  use q₁, q₂, lbq₁, Rat.cast_lt.mp lq, ubq₂
  have final_bound := (dist_triangle ..).trans_lt (add_lt_add hq₂ hq₁)
  rwa [add_halves] at final_bound

/-- The constant used in the proof of `int-continuous`. -/
irreducible_def C3_0_1 (a : ℕ) (R₁ R₂ : ℝ≥0) : ℝ≥0 :=
  2 ^ (a ^ 3) * (2 * R₂ / R₁) ^ a

lemma lintegral_inv_vol_le {R₁ R₂ : ℝ≥0} (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂) :
    ∫⁻ y in Annulus.oo x R₁ R₂, (vol x y)⁻¹ ≤ ↑((2 * R₂ / R₁) ^ a) := by
  -- rw [coe_pow, coe_div hR₁.ne', coe_mul, coe_ofNat]
  suffices ∀ y ∈ Annulus.oo x R₁ R₂, volume (ball x R₂) / ↑((2 * R₂ / R₁) ^ a) ≤ vol x y by
    calc
      _ ≤ ∫⁻ y in Annulus.oo x R₁ R₂, ↑((2 * R₂ / R₁) ^ a) / volume (ball x R₂) := by
        refine setLIntegral_mono' Annulus.measurableSet_oo fun y my ↦ ?_
        rw [← ENNReal.inv_div (.inr measure_ball_ne_top)]; swap
        · exact .inr (measure_ball_pos _ _ (hR₁.trans hR₂)).ne'
        rw [ENNReal.inv_le_inv]; exact this y my
      _ ≤ ↑((2 * R₂ / R₁) ^ a) / volume (ball x R₂) * volume (ball x R₂) := by
        rw [setLIntegral_const]; gcongr; intro y my; rw [Annulus.oo_eq] at my; exact my.1
      _ = _ :=
        ENNReal.div_mul_cancel (measure_ball_pos _ _ (hR₁.trans hR₂)).ne' measure_ball_ne_top
  intro y my
  obtain ⟨n, _, _⟩ : ∃ n, R₂ ≤ 2 ^ n * dist x y ∧ 2 ^ n ≤ 2 * R₂ / R₁ := by
    have : 1 ≤ R₂ / R₁ := by rw [one_le_div hR₁]; exact hR₂.le
    obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near this one_lt_two; use n + 1; constructor
    · rw [div_lt_iff₀ hR₁, ← NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_ofNat] at hn₂
      rw [Annulus.oo, mem_setOf, mem_Ioo] at my; apply hn₂.le.trans; gcongr; exact my.1.le
    · rw [pow_succ', mul_div_assoc]; gcongr
  calc
    _ ≤ volume (ball x (2 ^ n * dist x y)) / (2 ^ a) ^ n := by
      rw [← pow_mul, show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← coe_pow, mul_comm a, pow_mul]; gcongr
    _ ≤ _ := by
      apply ENNReal.div_le_of_le_mul'
      convert measure_ball_two_le_same_iterate (μ := volume) x (dist x y) n; norm_cast

lemma edist_carlesonOperatorIntegrand_le
    {R₁ R₂ : ℝ≥0} (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    edist (carlesonOperatorIntegrand K θ R₁ R₂ f x) (carlesonOperatorIntegrand K ϑ R₁ R₂ f x) ≤
    C3_0_1 a R₁ R₂ * edist_{x, dist o x + R₂} θ ϑ := by
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · iterate 2 rw [carlesonOperatorIntegrand, Annulus.oo_eq_empty (by simp [hR₂]), setIntegral_empty]
    rw [edist_self]; exact zero_le _
  calc
    _ = ‖∫ y in Annulus.oo x R₁ R₂, K x y * f y * (exp (I * θ y) - exp (I * ϑ y))‖ₑ := by
      rw [edist_eq_enorm_sub, carlesonOperatorIntegrand, carlesonOperatorIntegrand, ← integral_sub]
      rotate_left
      · exact integrableOn_coi_inner_annulus mf nf hR₁
      · exact integrableOn_coi_inner_annulus mf nf hR₁
      congr! 3 with y; rw [mul_sub]
    _ ≤ ∫⁻ y in Annulus.oo x R₁ R₂, ‖K x y‖ₑ * ‖f y‖ₑ * ‖exp (I * θ y) - exp (I * ϑ y)‖ₑ := by
      simp_rw [← enorm_mul]; exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in Annulus.oo x R₁ R₂, C_K a / vol x y * edist_{x, dist o x + R₂} θ ϑ := by
      refine setLIntegral_mono' Annulus.measurableSet_oo fun y my ↦ ?_
      rw [mul_assoc]; refine mul_le_mul' (enorm_K_le_vol_inv _ _) ?_
      rw [← one_mul (edist_{x, dist o x + R₂} θ ϑ)]; gcongr
      · rw [← enorm_norm, ← enorm_one (G := ℝ)]; exact Real.enorm_le_enorm (norm_nonneg _) (nf y)
      · rw [edist_dist, le_ofReal_iff_toReal_le (by finiteness) dist_nonneg, toReal_enorm]
        calc
          _ = ‖exp (I * (θ y - ϑ y - θ o + ϑ o : ℝ)) - 1‖ := by
            rw [cancelPt_eq_zero, sub_zero, cancelPt_eq_zero, add_zero, Complex.ofReal_sub,
              ← mul_one ‖_ - 1‖, ← norm_exp_I_mul_ofReal (ϑ y), ← norm_mul, sub_one_mul,
              ← Complex.exp_add, ← mul_add, sub_add_cancel]
          _ ≤ ‖θ y - ϑ y - θ o + ϑ o‖ := norm_exp_I_mul_ofReal_sub_one_le
          _ ≤ _ := by
            rw [Annulus.oo, mem_setOf, mem_Ioo] at my
            apply oscillation_le_cdist
            · rw [mem_ball']; exact my.2.trans_le (le_add_of_nonneg_left dist_nonneg)
            · rw [mem_ball, lt_add_iff_pos_right]; exact hR₁.trans hR₂
    _ = C_K a * edist_{x, dist o x + R₂} θ ϑ * ∫⁻ y in Annulus.oo x R₁ R₂, (vol x y)⁻¹ := by
      simp_rw [ENNReal.div_eq_inv_mul]
      iterate 2 rw [lintegral_mul_const' _ _ (by finiteness)]
      rw [mul_rotate]
    _ ≤ C_K a * edist_{x, dist o x + R₂} θ ϑ * ↑((2 * R₂ / R₁) ^ a) := by
      gcongr; exact lintegral_inv_vol_le hR₁ hR₂
    _ = _ := by
      rw [← mul_rotate, ← coe_mul, mul_comm (_ ^ _), C3_0_1, C_K, ← Nat.cast_pow,
        NNReal.rpow_natCast]

lemma dist_carlesonOperatorIntegrand_le
    {R₁ R₂ : ℝ≥0} (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    dist (carlesonOperatorIntegrand K θ R₁ R₂ f x) (carlesonOperatorIntegrand K ϑ R₁ R₂ f x) ≤
    C3_0_1 a R₁ R₂ * dist_{x, dist o x + R₂} θ ϑ := by
  rw [← ofReal_le_ofReal_iff (by positivity), ← edist_dist, ENNReal.ofReal_mul NNReal.zero_le_coe,
    ofReal_coe_nnreal, ← edist_dist]
  exact edist_carlesonOperatorIntegrand_le mf nf hR₁

lemma continuous_carlesonOperatorIntegrand (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    Continuous (carlesonOperatorIntegrand K · R₁ R₂ f x) := by
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · unfold carlesonOperatorIntegrand; rw [Annulus.oo_eq_empty (by simp [hR₂])]
    simp_rw [setIntegral_empty]; exact continuous_const
  lift R₁ to ℝ≥0 using hR₁.le
  lift R₂ to ℝ≥0 using (hR₁.trans hR₂).le
  rw [NNReal.coe_pos] at hR₁; rw [NNReal.coe_lt_coe] at hR₂
  have R₂pos := hR₁.trans hR₂
  rw [continuous_iff]; intro ϑ ε εpos
  let C₁ := As (defaultA a) (dist o x + R₂ + dist o x)
  have C₁pos : 0 < C₁ := by unfold C₁ As; norm_cast; positivity
  have C₂pos : 0 < C3_0_1 a R₁ R₂ := by rw [C3_0_1]; positivity
  refine ⟨ε / (C₁ * C3_0_1 a R₁ R₂), by positivity, fun θ db ↦ ?_⟩
  calc
    _ ≤ _ := dist_carlesonOperatorIntegrand_le mf nf hR₁
    _ ≤ C3_0_1 a R₁ R₂ * C₁ * dist θ ϑ := by rw [mul_assoc]; gcongr; apply cdist_le_dist; positivity
    _ < _ := by rwa [← lt_div_iff₀' (by positivity), mul_comm]

-- not sure if this is the best phrasing
lemma enorm_carlesonOperatorIntegrand_le {R₁ R₂ : ℝ≥0} (nf : (‖f ·‖) ≤ 1) (hR₁ : 0 < R₁) :
    ‖carlesonOperatorIntegrand K θ R₁ R₂ f x‖ₑ ≤ C3_0_1 a R₁ R₂ := by
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · unfold carlesonOperatorIntegrand; rw [Annulus.oo_eq_empty (by simp [hR₂])]
    rw [setIntegral_empty, enorm_zero]; exact zero_le _
  calc
    _ ≤ ∫⁻ y in Annulus.oo x R₁ R₂, ‖K x y‖ₑ * ‖f y‖ₑ * ‖exp (I * θ y)‖ₑ := by
      simp_rw [← enorm_mul]; exact enorm_integral_le_lintegral_enorm _
    _ ≤ C_K a * ∫⁻ y in Annulus.oo x R₁ R₂, (vol x y)⁻¹ := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]; simp_rw [← div_eq_mul_inv]
      refine setLIntegral_mono' Annulus.measurableSet_oo fun y my ↦ ?_
      rw [enorm_exp_I_mul_ofReal, mul_one, ← mul_one (_ / _)]
      apply mul_le_mul' (enorm_K_le_vol_inv _ _)
      rw [← enorm_norm, ← enorm_one (G := ℝ)]; exact Real.enorm_le_enorm (norm_nonneg _) (nf y)
    _ ≤ C_K a * ↑((2 * R₂ / R₁) ^ a) := by gcongr; exact lintegral_inv_vol_le hR₁ hR₂
    _ = _ := by rw [← coe_mul, C3_0_1, C_K, ← Nat.cast_pow, NNReal.rpow_natCast]
