/- This file contains the definition and basic properties of the Carleson operator on the real line.
-/

import Carleson.Classical.HilbertKernel

noncomputable section

open MeasureTheory

--TODO: avoid this extra definition?
def carlesonOperatorReal (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1),
  ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * Complex.exp (Complex.I * n * y)‖₊


lemma annulus_real_eq {x r R: ℝ} (r_nonneg : 0 ≤ r) : {y | dist x y ∈ Set.Ioo r R} = Set.Ioo (x - R) (x - r) ∪ Set.Ioo (x + r) (x + R) := by
  ext y
  simp only [Real.dist_eq, Set.mem_Ioo, lt_abs, neg_sub, abs_lt, neg_lt_sub_iff_lt_add,
    Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨(h₀ | h₀), h₁, h₂⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    · exact ⟨by left; linarith, by constructor <;> linarith⟩
    · exact ⟨by right; linarith, by constructor <;> linarith⟩

lemma annulus_real_volume {x r R : ℝ} (hr : r ∈ Set.Icc 0 R) :
    volume {y | dist x y ∈ Set.Ioo r R} = ENNReal.ofReal (2 * (R - r)) := by
  rw [annulus_real_eq hr.1, measure_union _ measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith [hr.2]) (by linarith [hr.2])]
  · ring_nf
  rw [Set.disjoint_iff]
  intro y hy
  linarith [hy.1.2, hy.2.1, hr.1]

lemma annulus_measurableSet {x r R : ℝ} : MeasurableSet {y | dist x y ∈ Set.Ioo r R} := measurableSet_preimage (measurable_const.dist measurable_id) measurableSet_Ioo

lemma sup_eq_sup_dense_of_continuous {f : ℝ → ENNReal} {S : Set ℝ} (D : Set ℝ) (hS : IsOpen S) (hD: Dense D) (hf : ContinuousOn f S) :
    ⨆ r ∈ S, f r = ⨆ r ∈ (S ∩ D), f r := by
  -- Show two inequalities, one is trivial
  refine le_antisymm (le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_) (biSup_mono Set.inter_subset_left)
  rw [lt_iSup_iff] at hc
  rcases hc with ⟨x, hx⟩
  rw [lt_iSup_iff] at hx
  rcases hx with ⟨xS, hx⟩
  have : IsOpen (S ∩ f ⁻¹' (Set.Ioi c)) := hf.isOpen_inter_preimage hS isOpen_Ioi
  have : Set.Nonempty ((S ∩ f ⁻¹' (Set.Ioi c)) ∩ D) :=
    hD.inter_open_nonempty _ this ⟨x, xS, by simpa⟩
  rcases this with ⟨y, hy⟩
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi] at hy
  exact hy.1.2.le.trans (le_biSup _ ⟨hy.1.1, hy.2⟩)

lemma measurable_mul_kernel {n : ℤ} {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (Function.uncurry fun x y ↦ f y * K x y * (Complex.I * n * y).exp) :=
      ((hf.comp measurable_snd).mul Hilbert_kernel_measurable).mul
  (measurable_const.mul (Complex.measurable_ofReal.comp measurable_snd)).cexp

/-- Rationals as a set of real numbers. -/
private def Qᵣ : Set ℝ := Rat.cast '' Set.univ

/-- Rationals are dense in reals. -/
private lemma Qᵣ_dense : Dense Qᵣ :=
  Rat.isDenseEmbedding_coe_real.dense_image.mpr dense_univ

/-- Rationals are countable after conversion to reals, too. -/
private lemma Qᵣ_countable : Countable Qᵣ :=
  propext Set.countable_coe_iff ▸ congr_arg Set.Countable Set.image_univ ▸
    Set.countable_range Rat.cast

local notation "T" => carlesonOperatorReal K

lemma carlesonOperatorReal_measurable {f : ℝ → ℂ} (f_measurable : Measurable f)
    {B : ℝ} (f_bounded : ∀ x, ‖f x‖ ≤ B) :
    Measurable (T f) := by
  apply Measurable.iSup
  intro n
  set F : ℝ → ℝ → ℝ → ℂ :=
    fun x r y ↦
      {y | dist x y ∈ Set.Ioo r 1}.indicator (fun t ↦ f t * K x t * (Complex.I * ↑n * ↑t).exp) y
    with Fdef
  set G : ℝ → ℝ → ENNReal := fun x r ↦ ↑‖∫ (y : ℝ), F x r y‖₊ with Gdef
  have hFG : (fun x ↦ ⨆ r, ⨆ (_ : 0 < r), ⨆ (_ : r < 1), ↑‖∫ (y : ℝ) in
                {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * (Complex.I * ↑n * ↑y).exp‖₊)
             = fun x ↦ ⨆ (r : ℝ) (_ : r ∈ Set.Ioo 0 1), G x r := by
    ext
    congr with r
    rw [iSup_and, Gdef, Fdef]
    congr
    rw [← integral_indicator annulus_measurableSet]
  rw [hFG]
  have hGr : (⨆ (r ∈ Set.Ioo 0 1), G · r) = (⨆ (r ∈ (Set.Ioo 0 1) ∩ Qᵣ), G · r) := by
    ext x
    rw [sup_eq_sup_dense_of_continuous Qᵣ isOpen_Ioo Qᵣ_dense]
    refine fun r ⟨hr, _⟩ ↦
      ContinuousAt.continuousWithinAt (ContinuousAt.comp (Continuous.continuousAt
        (EReal.continuous_coe_ennreal_iff.mp (EReal.continuous_coe_iff.mpr
          (continuous_iff_le_induced.mpr fun U a ↦ a)))) (ContinuousAt.nnnorm ?_))
    set S := Set.Ioo (r / 2) (2 * r) with Sdef
    set bound := fun y ↦ ‖F x (r / 2) y‖ with bound_def
    have h_bound : ∀ᶠ (s : ℝ) in nhds r, ∀ᵐ (a : ℝ), ‖F x s a‖ ≤ bound a := by
      rw [eventually_nhds_iff]
      use S
      constructor
      · intro s ⟨_, _⟩
        apply Filter.Eventually.of_forall
        intro y
        rw [bound_def, Fdef, norm_indicator_eq_indicator_norm]
        simp only
        rw [norm_indicator_eq_indicator_norm]
        apply Set.indicator_le_indicator_of_subset
        · intro y ⟨_, _⟩
          constructor <;> linarith
        · intro y
          apply norm_nonneg
      constructor
      · apply isOpen_Ioo
      · rw [Sdef]
        constructor <;> linarith
    apply continuousAt_of_dominated _  h_bound
    · have F_bound_on_set : ∀ a ∈ {y | dist x y ∈ Set.Ioo (r / 2) 1},
          ‖f a * K x a * (Complex.I * ↑n * ↑a).exp‖ ≤ B * ‖2 ^ (2 : ℝ) / (2 * (r / 2))‖ := by
        intro a ha
        rw [norm_mul, norm_mul, mul_assoc Complex.I, mul_comm Complex.I]
        norm_cast
        rw [Complex.norm_exp_ofReal_mul_I, mul_one]
        gcongr
        · linarith [f_bounded 0, norm_nonneg (f 0)]
        · exact f_bounded a
        · rw [Set.mem_setOf_eq] at ha
          rw [Real.norm_eq_abs, abs_of_nonneg (by apply div_nonneg (by norm_num); linarith)]
          calc _
            _ ≤ 2 ^ (2 : ℝ) / (2 * |x - a|) := Hilbert_kernel_bound
            _ ≤ 4 / (2 * (r / 2)) := by
              gcongr
              · linarith
              · rw [← Real.dist_eq]
                exact ha.1.le
      rw [bound_def, Fdef]
      conv => pattern ‖_‖; rw [norm_indicator_eq_indicator_norm]
      rw [integrable_indicator_iff annulus_measurableSet]
      apply Measure.integrableOn_of_bounded
      · rw [annulus_real_volume (by constructor <;> linarith)]
        exact ENNReal.ofReal_ne_top
      · apply ((Measurable.of_uncurry_left (measurable_mul_kernel f_measurable)).norm).aestronglyMeasurable
      · --interesting part
        rw [ae_restrict_iff' annulus_measurableSet]
        simp_rw [norm_norm]
        apply Filter.Eventually.of_forall
        apply F_bound_on_set
    · have contOn1 : ∀ (y : ℝ), ContinuousOn (F x · y) (Set.Iio (dist x y)) := by
        intro y
        rw [continuousOn_iff_continuous_restrict]
        apply continuous_of_const
        simp only [Set.restrict_apply, Subtype.forall]
        intro s hs t ht
        rw [Fdef]
        simp only [Set.mem_Ioo]
        by_cases h : dist x y < 1
        · rw [Set.indicator_apply, ite_cond_eq_true, Set.indicator_apply, ite_cond_eq_true]
          · simp only [Set.mem_setOf_eq, eq_iff_iff, iff_true]
            use ht
          · simp only [Set.mem_setOf_eq, eq_iff_iff, iff_true]
            use hs
        · push_neg at h
          rw [Set.indicator_apply, ite_cond_eq_false, Set.indicator_apply, ite_cond_eq_false]
          all_goals
            simp only [Set.mem_setOf_eq, eq_iff_iff, iff_false, not_and, not_lt]
            exact fun _ ↦ h
      have contOn2 : ∀ (y : ℝ), ContinuousOn (fun s ↦ F x s y) (Set.Ioi (min (dist x y) 1)) := by
        intro y
        rw [continuousOn_iff_continuous_restrict]
        apply continuous_of_const
        simp only [Set.restrict_apply, Subtype.forall]
        intro s hs t ht
        rw [Fdef]
        simp only [Set.mem_Ioo]
        rw [Set.indicator_apply, ite_cond_eq_false, Set.indicator_apply, ite_cond_eq_false]
        · rw [Set.mem_Ioi, min_lt_iff] at ht
          simp only [Set.mem_setOf_eq, eq_iff_iff, iff_false, not_and, not_lt]
          intro h
          rcases ht with h' | h'
          · exfalso
            exact (lt_self_iff_false _).mp (h'.trans h)
          · exact (h'.trans h).le
        · rw [Set.mem_Ioi, min_lt_iff] at hs
          simp only [Set.mem_setOf_eq, eq_iff_iff, iff_false, not_and, not_lt]
          intro h
          rcases hs with h' | h'
          · exfalso
            exact (lt_self_iff_false _).mp (h'.trans h)
          · exact (h'.trans h).le
      have contOn : ∀ y, ∀ t ≠ dist x y, ContinuousAt (F x · y) t := by
        intro y t ht
        by_cases h : t < dist x y
        · exact_mod_cast (contOn1 y).continuousAt (Iio_mem_nhds h)
        · push_neg at h
          exact ContinuousOn.continuousAt (contOn2 y) (Ioi_mem_nhds
            ((min_le_left _ _).trans_lt (lt_of_le_of_ne h ht.symm)))
      have subset_finite :
          {y | ¬ContinuousAt (F x · y) r} ⊆ ({x - r, x + r} : Finset ℝ) := by
        intro y hy
        have hxy : dist x y = r := by
          contrapose! hy
          rw [Set.mem_setOf_eq, not_not]
          exact contOn y r hy.symm
        rw [Real.dist_eq, abs_eq hr.le] at hxy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        cases hxy
        · left; linarith
        · right; linarith
      rw [ae_iff]
      exact measure_mono_null subset_finite (Finset.measure_zero _ _)
    · exact Filter.Eventually.of_forall fun r ↦ ((Measurable.of_uncurry_left
        (measurable_mul_kernel f_measurable)).indicator annulus_measurableSet).aestronglyMeasurable
  rw [hGr]
  refine Measurable.biSup _ (Set.Countable.mono Set.inter_subset_right Qᵣ_countable) (fun r _ ↦ ?_)
  apply measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp _)
  rw [← stronglyMeasurable_iff_measurable]
  apply StronglyMeasurable.integral_prod_right
  rw [stronglyMeasurable_iff_measurable, Fdef]
  exact (measurable_mul_kernel f_measurable).indicator (measurable_dist measurableSet_Ioo)

--TODO: Refactor the measurability proof to use the following.

/-
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open TopologicalSpace MeasureTheory Set

variable {α β : Type*} [MeasurableSpace α]
  [MeasurableSpace β]
  {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [SecondCountableTopology ι]
  {f : ι → α → β} [ConditionallyCompleteLattice β]
  [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β]
  [BorelSpace β]

-- lemma Measurable_iSup_gt {s : Set ι} [OrdConnected s]
--     (h1f : ∀ x i, ContinuousWithinAt (f · x) s i)
--     (h2f : ∀ i, Measurable (f i)) :
--     Measurable (⨆ i ∈ s, f i ·) := sorry
  -- use SecondCountableTopology to rewrite the sup as a sup over the countable dense set (or similar)
  -- then use measurable_iSup
-/


lemma carlesonOperatorReal_mul {f : ℝ → ℂ} {x : ℝ} {a : ℝ} (ha : 0 < a) : T f x = a.toNNReal * T (fun x ↦ 1 / a * f x) x := by
  rw [carlesonOperatorReal, carlesonOperatorReal, ENNReal.mul_iSup]
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
  rw [← Real.norm_of_nonneg NNReal.zero_le_coe, ← Complex.norm_real, ← norm_mul,
    ← integral_const_mul, Real.coe_toNNReal a ha.le]
  congr with y
  field_simp
  rw [mul_div_cancel_left₀]
  norm_cast
  exact ha.ne.symm


lemma carlesonOperatorReal_eq_of_restrict_interval {f : ℝ → ℂ} {a b : ℝ} {x : ℝ} (hx : x ∈ Set.Icc a b) : T f x = T ((Set.Ioo (a - 1) (b + 1)).indicator f) x := by
  simp_rw [carlesonOperatorReal]
  congr with n
  congr with _
  congr with _
  congr with _
  congr with y
  rw [mul_eq_mul_right_iff, mul_eq_mul_right_iff]
  left
  rw [Set.indicator]
  split_ifs with hy
  · left; rfl
  · right
    apply k_of_one_le_abs
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hy
    rw [le_abs]
    rcases hy with hy | hy
    · left; linarith [hx.1]
    · right; linarith [hx.2]
