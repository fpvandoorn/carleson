import Carleson.Defs
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {K : X → X → ℂ}

namespace MetricΘ

variable [CompatibleFunctions ℝ X (defaultA a)]

/-- We choose as metric space instance on `Θ` one given by an arbitrary ball.
The metric given by all other balls are equivalent. -/
scoped instance : PseudoMetricSpace (Θ X) :=
  inferInstanceAs <| PseudoMetricSpace <| WithFunctionDistance o 1

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

variable [KernelProofData a K] {θ : Θ X} {Q : SimpleFunc X (Θ X)} {R₁ R₂ : ℝ} {f : X → ℂ} {x : X}
-- [IsCancellative X (defaultτ a)]

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
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ly), sub_lt_sub_iff_right] at dy
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
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ly), sub_lt_sub_iff_right] at dy
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
      refine measure_mono fun y my ↦ ?_
      rw [oc, mem_setOf, mem_Ioc] at my; rw [mem_closedBall']; exact my.2
    _ < _ := measure_closedBall_lt_top

#exit

lemma rightContinuous_carlesonOperatorIntegrand
    (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) (mθ : Measurable θ) (hR₁ : 0 < R₁) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ · R₂ f x) (Ici R₁) R₁ := by
  simp_rw [carlesonOperatorIntegrand, continuousWithinAt_iff, mem_Ici]; intro ε εpos
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · use 1, zero_lt_one; intro R' hR' _
    rw [Annulus.oo_eq_empty (hR₂.trans hR'), Annulus.oo_eq_empty hR₂, setIntegral_empty, dist_self]
    exact εpos
  obtain ⟨u, sau, mu, ttu⟩ := exists_seq_strictAnti_tendsto' hR₂
  -- R₁ < ... < u (n + 1) < u n < ... < u 1 < u 0 < R₂
  let s (n : ℕ) := Annulus.oc x (u (n + 1)) (u n)
  have union_s : ⋃ i, s i = Annulus.oc x R₁ (u 0) := by
    ext y; simp_rw [mem_iUnion, s, Annulus.oc, mem_setOf, mem_Ioc]; constructor <;> intro h
    · obtain ⟨n, hn₁, hn₂⟩ := h
      exact ⟨(mu (n + 1)).1.trans hn₁, hn₂.trans (sau.antitone (zero_le n))⟩
    · let T : Set ℕ := {n | u n < dist x y}
      have neT : T.Nonempty := by
        rw [Metric.tendsto_atTop] at ttu
        specialize ttu (dist x y - R₁) (by linarith only [h.1]); obtain ⟨N, hN⟩ := ttu
        specialize hN N le_rfl
        rw [dist_eq_norm, Real.norm_of_nonneg (by linarith only [(mu N).1]),
          sub_lt_sub_iff_right] at hN; use N, hN
      have wfT : T.IsWF := IsWF.of_wellFoundedLT T
      use wfT.min neT - 1
      have minT_mem := wfT.min_mem neT; simp_rw [T, mem_setOf] at minT_mem
      have minT_pos : wfT.min neT ≠ 0 := by
        by_contra! h'; rw [h'] at minT_mem; exact absurd h.2 (not_le.mpr minT_mem)
      rw [Nat.sub_one_add_one minT_pos, ← not_lt]; refine ⟨minT_mem, ?_⟩
      change wfT.min neT - 1 ∉ T; contrapose! minT_pos
      replace minT_pos := wfT.min_le neT minT_pos; omega
  have disjoint_s : Pairwise (Function.onFun Disjoint s) := fun i j hn ↦ by
    change Disjoint (s i) (s j)
    wlog hl : i < j generalizing i j; · exact (this j i hn.symm (by omega)).symm
    simp_rw [s, disjoint_left, Annulus.oc, mem_setOf, mem_Ioc]; intro y my
    rw [not_and_or, not_le]; right
    exact (sau.antitone (show i + 1 ≤ j by omega)).trans_lt my.1
  let f' (y : X) := K x y * f y * cexp (I * θ y)
  have integrableOn_f' : IntegrableOn f' (⋃ i, s i) := by
    simp_rw [union_s, f', mul_assoc]
    refine integrableOn_K_mul ?_ _ hR₁ fun y my ↦ ?_
    · refine Integrable.bdd_mul ?_ mf.aestronglyMeasurable.restrict ⟨_, nf⟩
      apply Measure.integrableOn_of_bounded (M := 1)
      · rw [← lt_top_iff_ne_top]
        calc
          _ ≤ volume (ball x R₂) := by
            refine measure_mono fun y my ↦ ?_
            rw [Annulus.oc, mem_setOf, mem_Ioc] at my; rw [mem_ball']; exact my.2.trans_lt (mu 0).2
          _ < _ := measure_ball_lt_top
      · exact ((Complex.measurable_ofReal.comp mθ).const_mul I).cexp.aestronglyMeasurable
      · refine Eventually.of_forall fun y ↦ ?_
        rw [mul_comm, norm_exp_ofReal_mul_I]
    · rw [Annulus.oc, mem_setOf, mem_Ioc] at my
      rw [mem_compl_iff, mem_ball', not_lt]; exact my.1.le
  have hsiu := hasSum_integral_iUnion (fun _ ↦ Annulus.measurableSet_oc) disjoint_s integrableOn_f'
  have pstt := hsiu.summable.tendsto_sum_tsum_nat
  rw [hsiu.tsum_eq, union_s, Metric.tendsto_atTop] at pstt
  sorry

lemma leftContinuous_carlesonOperatorIntegrand (mf : Measurable f) (hR₁ : 0 < R₁) :
    ContinuousWithinAt (carlesonOperatorIntegrand K θ R₁ · f x) (Iic R₂) R₂ := by
  simp_rw [carlesonOperatorIntegrand, continuousWithinAt_iff, mem_Iic, Real.dist_eq]; intro ε εpos
  rcases le_or_gt R₂ R₁ with hR₂ | hR₂
  · use 1, zero_lt_one; intro R' hR'₁ hR'₂
    rw [Annulus.oo_eq_empty (hR'₁.trans hR₂), Annulus.oo_eq_empty hR₂, setIntegral_empty, dist_self]
    exact εpos
  sorry

lemma continuous_carlesonOperatorIntegrand (nf : (‖f ·‖) ≤ 1) :
    Continuous (carlesonOperatorIntegrand K · R₁ R₂ f x) := by
  sorry

/-- The constant used in the proof of `int-continuous`. -/
irreducible_def C3_0_1 (a : ℕ) (R₁ R₂ : ℝ≥0) : ℝ≥0 :=
  2 ^ (a ^ 3) * (2 * R₂ / R₁) ^ a

-- not sure if this is the best phrasing
lemma isBounded_carlesonOperatorIntegrand {R₁ R₂ : ℝ≥0} (nf : (‖f ·‖) ≤ 1) :
    ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ₑ ≤ C3_0_1 a R₁ R₂ := by
  sorry
