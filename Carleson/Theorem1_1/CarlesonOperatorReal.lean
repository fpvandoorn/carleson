import Carleson.Theorem1_1.Hilbert_kernel

noncomputable section

--TODO: avoid this extra definition?
def CarlesonOperatorReal (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1),
  ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * Complex.exp (Complex.I * n * y)‖₊


lemma annulus_real_eq {x r R: ℝ} (r_nonneg : 0 ≤ r) : {y | dist x y ∈ Set.Ioo r R} = Set.Ioo (x - R) (x - r) ∪ Set.Ioo (x + r) (x + R) := by
  ext y
  simp only [Real.dist_eq, Set.mem_Ioo, lt_abs, neg_sub, abs_lt, neg_lt_sub_iff_lt_add,
    Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨(h₀ | h₀), h₁, h₂⟩
    · left
      constructor <;> linarith
    · right
      constructor <;> linarith
  · rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    · constructor
      · left
        linarith
      · constructor <;> linarith
    · constructor
      · right
        linarith
      · constructor <;> linarith

lemma annulus_real_volume {x r R : ℝ} (hr : r ∈ Set.Icc 0 R) : MeasureTheory.volume {y | dist x y ∈ Set.Ioo r R} = ENNReal.ofReal (2 * (R - r)) := by
  rw [annulus_real_eq hr.1, MeasureTheory.measure_union _ measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith [hr.2]) (by linarith [hr.2])]
  ring_nf
  rw [Set.disjoint_iff]
  intro y hy
  linarith [hy.1.2, hy.2.1, hr.1]


lemma annulus_measurableSet {x r R : ℝ} : MeasurableSet {y | dist x y ∈ Set.Ioo r R} := measurableSet_preimage (Measurable.dist measurable_const measurable_id) measurableSet_Ioo

lemma sup_eq_sup_dense_of_continuous {f : ℝ → ENNReal} {S : Set ℝ} (D : Set ℝ) (hS : IsOpen S) (hD: Dense D) (hf : ContinuousOn f S) :
    ⨆ r ∈ S, f r = ⨆ r ∈ (S ∩ D), f r := by
  --Show two inequalities, one is trivial
  apply le_antisymm _ (biSup_mono Set.inter_subset_left)
  apply le_of_forall_ge_of_dense
  intro c hc
  rw [lt_iSup_iff] at hc
  rcases hc with ⟨x, hx⟩
  rw [lt_iSup_iff] at hx
  rcases hx with ⟨xS, hx⟩
  have : IsOpen (S ∩ f ⁻¹' (Set.Ioi c)) := hf.isOpen_inter_preimage hS isOpen_Ioi
  have : Set.Nonempty ((S ∩ f ⁻¹' (Set.Ioi c)) ∩ D) := by
    apply hD.inter_open_nonempty
    exact this
    use x, xS
    simpa
  rcases this with ⟨y, hy⟩
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi] at hy
  apply hy.1.2.le.trans
  apply le_biSup
  exact ⟨hy.1.1, hy.2⟩

lemma helper {n : ℤ} {f : ℝ → ℂ} (hf : Measurable f) : Measurable (Function.uncurry fun x y ↦ f y * K x y * (Complex.I * n * y).exp) := by
  apply Measurable.mul
  apply Measurable.mul
  apply hf.comp measurable_snd
  exact Hilbert_kernel_measurable
  apply Measurable.cexp
  apply Measurable.mul measurable_const
  apply Complex.measurable_ofReal.comp measurable_snd

local notation "T" => CarlesonOperatorReal K


lemma CarlesonOperatorReal_measurable {f : ℝ → ℂ} (f_measurable : Measurable f) {B : ℝ} (f_bounded : ∀ x, ‖f x‖ ≤ B) : Measurable (T f):= by
  --TODO: clean up proof
  apply measurable_iSup
  intro n
  set F : ℝ → ℝ → ℝ → ℂ := fun x r y ↦ {y | dist x y ∈ Set.Ioo r 1}.indicator (fun t ↦ f t * K x t * (Complex.I * ↑n * ↑t).exp) y with Fdef
  set G : ℝ → ℝ → ENNReal := fun x r ↦ ↑‖∫ (y : ℝ), F x r y‖₊ with Gdef
  have : (fun x ↦ ⨆ r, ⨆ (_ : 0 < r), ⨆ (_ : r < 1), ↑‖∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * (Complex.I * ↑n * ↑y).exp‖₊)
        = fun x ↦ ⨆ (r : ℝ) (_ : r ∈ Set.Ioo 0 1), G x r := by
    ext x
    congr with r
    rw [iSup_and, Gdef, Fdef]
    congr with _
    congr with _
    congr 2
    rw [← MeasureTheory.integral_indicator annulus_measurableSet]
  rw [this]
  set Q : Set ℝ := Rat.cast '' Set.univ with Qdef
  have hQ : Dense Q ∧ Countable Q := by
    constructor
    . rw [Rat.denseEmbedding_coe_real.dense_image]
      exact dense_univ
    . rw [Set.countable_coe_iff, Qdef, Set.image_univ]
      apply Set.countable_range
  have : (fun x ↦ ⨆ (r ∈ Set.Ioo 0 1), G x r) = (fun x ↦ ⨆ (r ∈ (Set.Ioo 0 1) ∩ Q), G x r) := by
    ext x
    rw [sup_eq_sup_dense_of_continuous Q isOpen_Ioo hQ.1]
    intro r hr
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp
    . apply Continuous.continuousAt
      apply EReal.continuous_coe_ennreal_iff.mp
      apply EReal.continuous_coe_iff.mpr (continuous_iff_le_induced.mpr fun U a ↦ a)
    apply ContinuousAt.nnnorm
    set S := Set.Ioo (r / 2) (2 * r) with Sdef
    set bound := fun y ↦ ‖F x (r / 2) y‖ with bound_def
    have h_bound : ∀ᶠ (s : ℝ) in nhds r, ∀ᵐ (a : ℝ), ‖F x s a‖ ≤ bound a := by
      rw [eventually_nhds_iff]
      use S
      constructor
      . intro s hs
        apply Filter.eventually_of_forall
        intro y
        rw [bound_def, Fdef, norm_indicator_eq_indicator_norm]
        simp only
        rw [norm_indicator_eq_indicator_norm]
        apply Set.indicator_le_indicator_of_subset
        . intro y hy
          constructor <;> linarith [hy.1, hy.2, hs.1]
        . intro y
          apply norm_nonneg
      constructor
      . apply isOpen_Ioo
      . rw [Sdef]
        constructor <;> linarith [hr.1]
    apply MeasureTheory.continuousAt_of_dominated _  h_bound
    . have F_bound_on_set :  ∀ a ∈ {y | dist x y ∈ Set.Ioo (r / 2) 1},  ‖f a * K x a * (Complex.I * ↑n * ↑a).exp‖ ≤ B * ‖2 ^ (2 : ℝ) / (2 * (r / 2))‖ := by
        intro a ha
        rw [norm_mul, norm_mul, mul_assoc Complex.I, mul_comm Complex.I]
        norm_cast
        rw [Complex.norm_exp_ofReal_mul_I, mul_one]
        gcongr
        . linarith [f_bounded 0, norm_nonneg (f 0)]
        . exact f_bounded a
        . rw [Set.mem_setOf_eq] at ha
          rw [Real.norm_eq_abs, abs_of_nonneg (by apply div_nonneg (by norm_num); linarith [hr.1])]
          calc _
            _ ≤ 2 ^ (2 : ℝ) / (2 * |x - a|) := Hilbert_kernel_bound
            _ ≤ 4 / (2 * (r / 2)) := by
              gcongr
              . linarith [hr.1]
              . norm_num
              . rw [← Real.dist_eq]
                exact ha.1.le
      rw [bound_def, Fdef]
      conv => pattern ‖_‖; rw [norm_indicator_eq_indicator_norm]
      rw [MeasureTheory.integrable_indicator_iff annulus_measurableSet]
      apply MeasureTheory.Measure.integrableOn_of_bounded
      . rw [annulus_real_volume (by constructor <;> linarith [hr.1, hr.2])]
        exact ENNReal.ofReal_ne_top
      . --measurability
        apply Measurable.aestronglyMeasurable
        apply Measurable.norm (Measurable.of_uncurry_left (helper f_measurable))
      . --interesting part
        rw [MeasureTheory.ae_restrict_iff' annulus_measurableSet]
        simp_rw [norm_norm]
        apply Filter.eventually_of_forall
        apply F_bound_on_set
    . have contOn1 : ∀ (y : ℝ), ContinuousOn (fun s ↦ F x s y) (Set.Iio (dist x y)) := by
        intro y
        rw [continuousOn_iff_continuous_restrict]
        apply continuous_of_const
        simp only [Set.restrict_apply, Subtype.forall]
        intro s hs t ht
        rw [Fdef]
        simp only [Set.mem_Ioo]
        by_cases h : dist x y < 1
        . rw [Set.indicator_apply, ite_cond_eq_true, Set.indicator_apply, ite_cond_eq_true]
          . simp
            use ht
          . simp
            use hs
        . push_neg at h
          rw [Set.indicator_apply, ite_cond_eq_false, Set.indicator_apply, ite_cond_eq_false]
          all_goals
            simp
            intro _
            exact h
      have contOn2 : ∀ (y : ℝ), ContinuousOn (fun s ↦ F x s y) (Set.Ioi (min (dist x y) 1)) := by
        intro y
        rw [continuousOn_iff_continuous_restrict]
        apply continuous_of_const
        simp only [Set.restrict_apply, Subtype.forall]
        intro s hs t ht
        rw [Fdef]
        simp
        rw [Set.indicator_apply, ite_cond_eq_false, Set.indicator_apply, ite_cond_eq_false]
        . rw [Set.mem_Ioi, min_lt_iff] at ht
          simp
          intro h
          rcases ht with h' | h'
          . exfalso
            exact (lt_self_iff_false _).mp (h'.trans h)
          . exact (h'.trans h).le
        . rw [Set.mem_Ioi, min_lt_iff] at hs
          simp
          intro h
          rcases hs with h' | h'
          . exfalso
            exact (lt_self_iff_false _).mp (h'.trans h)
          . exact (h'.trans h).le
      have contOn : ∀ y, ∀ t ≠ dist x y, ContinuousAt (fun s ↦ F x s y) t := by
        intro y t ht
        by_cases h : t < dist x y
        . apply (contOn1 y).continuousAt (Iio_mem_nhds h)
        . push_neg at h
          apply ContinuousOn.continuousAt (contOn2 y)
          exact Ioi_mem_nhds ((min_le_left _ _).trans_lt (lt_of_le_of_ne h ht.symm))
      have subset_finite : {y | ¬ContinuousAt (fun s ↦ F x s y) r} ⊆ ({x - r, x + r} : Finset ℝ) := by
        intro y hy
        have : dist x y = r := by
          contrapose! hy
          rw [Set.mem_setOf_eq, not_not]
          exact contOn y r hy.symm
        rw [Real.dist_eq, abs_eq hr.1.le] at this
        simp
        rcases this with h | h
        . left; linarith
        . right; linarith
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null subset_finite
      apply Finset.measure_zero
    . apply Filter.eventually_of_forall
      intro r
      apply ((Measurable.of_uncurry_left (helper f_measurable)).indicator annulus_measurableSet).aestronglyMeasurable
  rw [this]
  apply measurable_biSup
  apply Set.Countable.mono Set.inter_subset_right hQ.2
  intro r _
  --measurability
  apply measurable_coe_nnreal_ennreal.comp
  apply measurable_nnnorm.comp
  rw [← stronglyMeasurable_iff_measurable]
  apply MeasureTheory.StronglyMeasurable.integral_prod_right
  rw [stronglyMeasurable_iff_measurable, Fdef]
  apply Measurable.indicator (helper f_measurable) (measurable_dist measurableSet_Ioo)



lemma CarlesonOperatorReal_mul {f : ℝ → ℂ} {x : ℝ} {a : ℝ} (ha : 0 < a) : T f x = a.toNNReal * T (fun x ↦ 1 / a * f x) x := by
  rw [CarlesonOperatorReal, CarlesonOperatorReal, ENNReal.mul_iSup]
  congr with n
  rw [ENNReal.mul_iSup]
  congr with r
  rw [ENNReal.mul_iSup]
  congr
  ext rpos
  rw [ENNReal.mul_iSup]
  congr with rle1
  norm_cast
  apply NNReal.eq
  simp only [coe_nnnorm, NNReal.coe_mul]
  rw [← Real.norm_of_nonneg (@NNReal.zero_le_coe a.toNNReal), ← Complex.norm_real, ← norm_mul,
    ← MeasureTheory.integral_mul_left, Real.coe_toNNReal a ha.le]
  congr with y
  field_simp
  rw [mul_div_cancel_left₀]
  norm_cast
  exact ha.ne.symm


lemma CarlesonOperatorReal_eq_of_restrict_interval {f : ℝ → ℂ} {a b : ℝ} {x : ℝ} (hx : x ∈ Set.Icc a b) : T f x = T ((Set.Ioo (a - 1) (b + 1)).indicator f) x := by
  rw [CarlesonOperatorReal, CarlesonOperatorReal]
  congr with n
  congr with _
  congr with _
  congr with _
  congr with y
  rw [mul_eq_mul_right_iff, mul_eq_mul_right_iff]
  left
  rw [Set.indicator]
  split_ifs with hy
  . left; rfl
  . right
    apply k_of_one_le_abs
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hy
    rw [le_abs]
    rcases hy with hy | hy
    . left; linarith [hx.1]
    . right; linarith [hx.2]
