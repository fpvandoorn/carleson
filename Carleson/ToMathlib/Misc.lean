import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Carleson.ToMathlib.MeasureReal

/-
* This file can import all ToMathlib files.
* If adding more than a few result, please put them in a more appropriate file in ToMathlib.
-/

open Function Set
open scoped ENNReal

section Metric

attribute [gcongr] Metric.ball_subset_ball


lemma Metric.dense_iff_iUnion_ball {X : Type*} [PseudoMetricSpace X] (s : Set X) :
    Dense s ↔ ∀ r > 0, ⋃ c ∈ s, ball c r = univ := by
  simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop, mem_ball, Dense, Metric.mem_closure_iff,
    forall_comm (α := X)]

theorem PseudoMetricSpace.dist_eq_of_dist_zero {X : Type*} [PseudoMetricSpace X] (x : X) {y y' : X}
    (hyy' : dist y y' = 0) : dist x y = dist x y' :=
  dist_comm y x ▸ dist_comm y' x ▸ sub_eq_zero.1 (abs_nonpos_iff.1 (hyy' ▸ abs_dist_sub_le y y' x))

end Metric

section Order

lemma IsTop.isMax_iff {α} [PartialOrder α] {i j : α} (h : IsTop i) : IsMax j ↔ j = i := by
  simp_rw [le_antisymm_iff, h j, true_and]
  refine ⟨(· (h j)), swap (fun _ ↦ h · |>.trans ·)⟩

end Order

section Int

theorem Int.floor_le_iff (c : ℝ) (z : ℤ) : ⌊c⌋ ≤ z ↔ c < z + 1 := by
  rw_mod_cast [← Int.floor_le_sub_one_iff, add_sub_cancel_right]

theorem Int.Icc_of_eq_sub_1 {a b : ℤ} (h : a = b - 1) : Finset.Icc a b = {a, b} := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · rw [h, Finset.mem_Icc] at ht
    by_cases hta : t = b - 1
    · rw [hta, ← h]; exact Finset.mem_insert_self a {b}
    · suffices b = t from this ▸ Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 rfl))
      exact le_antisymm (sub_add_cancel b 1 ▸ (ne_eq t (b - 1) ▸ hta).symm.lt_of_le ht.1) ht.2
  · have hab : a ≤ b := h ▸ sub_le_self b one_pos.le
    rcases Finset.mem_insert.1 ht with rfl | hb
    · exact Finset.mem_Icc.2 ⟨le_refl t, hab⟩
    · rw [Finset.mem_singleton.1 hb]; exact Finset.mem_Icc.2 ⟨hab, le_refl b⟩

end Int

section ENNReal

lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
  if hfin : s.Finite then
    have hfin' : Finite s := hfin
    rw [tsum_def]
    simp only [ENNReal.summable, ↓reduceDIte]
    have hsup: support (fun (_ : s) ↦ (1 : ℝ≥0∞)) = Set.univ := by
      ext i
      simp only [mem_support, ne_eq, one_ne_zero, not_false_eq_true, mem_univ]
    have hsupfin: (Set.univ : Set s).Finite := finite_univ
    rw [← hsup] at hsupfin
    rw [if_pos hsupfin]
    rw [hfin.encard_eq_coe_toFinset_card]
    simp only [ENat.toENNReal_coe]
    rw [Finset.card_eq_sum_ones]
    rw [finsum_eq_sum (fun (_ : s) ↦ (1 :ℝ≥0∞)) hsupfin]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_inj]
    apply Finset.card_bij (fun a _ => a.val)
    · intro a
      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
        Subtype.coe_prop, imp_self]
    · intro a _ a' _ heq
      ext
      exact heq
    · intro a ha
      use ⟨a,by
        simp only [Finite.mem_toFinset] at ha
        exact ha⟩
      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
        exists_const]
  else
  have : Infinite s := infinite_coe_iff.mpr hfin
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)]
  rw [Set.encard_eq_top_iff.mpr hfin]
  simp only [ENat.toENNReal_top]


lemma ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ℝ≥0∞) :
    ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
  nth_rw 1 [← one_mul c]
  rw [ENNReal.tsum_mul_right,tsum_one_eq']

/-! ## `ENNReal` manipulation lemmas -/

lemma ENNReal.sum_geometric_two_pow_toNNReal {k : ℕ} (hk : k > 0) :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-k * n : ℤ) = (1 / (1 - 1 / 2 ^ k) : ℝ).toNNReal := by
  conv_lhs =>
    enter [1, n]
    rw [← rpow_intCast, show (-k * n : ℤ) = (-k * n : ℝ) by simp, rpow_mul, rpow_natCast]
  rw [tsum_geometric, show (2 : ℝ≥0∞) = (2 : ℝ).toNNReal by simp,
    ← coe_rpow_of_ne_zero (by simp), ← Real.toNNReal_rpow_of_nonneg zero_le_two,
    ← coe_one, ← Real.toNNReal_one, ← coe_sub, NNReal.sub_def,
    Real.toNNReal_one, NNReal.coe_one, Real.coe_toNNReal', max_eq_left (by positivity),
    Real.rpow_neg zero_le_two, Real.rpow_natCast, one_div]
  have : ((1 : ℝ) - (2 ^ k)⁻¹).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add, not_le, inv_lt_one_iff]
    right; exact one_lt_pow (R := ℝ) _root_.one_lt_two hk.ne'
  rw [← coe_inv this, coe_inj, Real.toNNReal_inv, one_div]

lemma ENNReal.sum_geometric_two_pow_neg_one : ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-n : ℤ) = 2 := by
  conv_lhs => enter [1, n]; rw [← one_mul (n : ℤ), ← neg_mul, ← Nat.cast_one]
  rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one]; norm_num

lemma ENNReal.sum_geometric_two_pow_neg_two :
    ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-2 * n : ℤ) = ((4 : ℝ) / 3).toNNReal := by
  conv_lhs => enter [1, n, 2]; rw [← Nat.cast_two]
  rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_two]; norm_num

lemma tsum_geometric_ite_eq_tsum_geometric {k c : ℕ} :
    (∑' (n : ℕ), if k ≤ n then (2 : ℝ≥0∞) ^ (-c * (n - k) : ℤ) else 0) =
    ∑' (n : ℕ), 2 ^ (-c * n : ℤ) := by
  convert (Injective.tsum_eq (f := fun n ↦ if k ≤ n then (2 : ℝ≥0∞) ^ (-c * (n - k) : ℤ) else 0)
    (add_left_injective k) (fun n mn ↦ _)).symm
  · simp
  · rw [mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at mn
    use n - k, Nat.sub_add_cancel mn.1

end ENNReal

section Indicator
attribute [gcongr] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
end Indicator


namespace MeasureTheory

/-! ## Partitioning an interval -/


lemma lintegral_Ioc_partition {a b : ℕ} {c : ℝ} {f : ℝ → ℝ≥0∞} (hc : 0 ≤ c) :
    ∫⁻ t in Ioc (a * c) (b * c), f t =
    ∑ l ∈ Finset.Ico a b, ∫⁻ t in Ioc (l * c) ((l + 1 : ℕ) * c), f t := by
  rcases lt_or_le b a with h | h
  · rw [Finset.Ico_eq_empty (by omega), Ioc_eq_empty (by rw [not_lt]; gcongr),
      setLIntegral_empty, Finset.sum_empty]
  induction b, h using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Ioc_self, setLIntegral_empty, Finset.sum_empty]
  | succ b h ih =>
    have li : a * c ≤ b * c := by gcongr
    rw [← Ioc_union_Ioc_eq_Ioc li (by gcongr; omega),
      lintegral_union measurableSet_Ioc Ioc_disjoint_Ioc_same,
      Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert Finset.right_not_mem_Ico,
      add_comm (lintegral ..), ih]

/-! ## Averaging -/

-- Named for consistency with `lintegral_add_left'`
-- Maybe add laverage/laverage theorems for all the other lintegral_add statements?
lemma laverage_add_left {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {f g : α → ENNReal} (hf : AEMeasurable f μ) :
    ⨍⁻ x, (f x + g x) ∂μ = ⨍⁻ x, f x ∂μ + ⨍⁻ x, g x ∂μ := by
  simp_rw [laverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf]

-- Named for consistency with `lintegral_mono'`
lemma laverage_mono {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {f g : α → ENNReal} (h : ∀ x, f x ≤ g x) :
    ⨍⁻ x, f x ∂μ ≤ ⨍⁻ x, g x ∂μ := by
  simp_rw [laverage_eq]
  exact ENNReal.div_le_div_right (lintegral_mono h) (μ univ)

lemma laverage_const_mul {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {f : α → ENNReal} {c : ENNReal} (hc : c ≠ ⊤) :
    c * ⨍⁻ x, f x ∂μ = ⨍⁻ x, c * f x ∂μ := by
  simp_rw [laverage_eq, ← mul_div_assoc c, lintegral_const_mul' c f hc]

-- The following two lemmas are unused

-- Named for consistency with `lintegral_add_left'`
-- Maybe add laverage/setLaverage theorems for all the other lintegral_add statements?
lemma setLaverage_add_left' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {s : Set α} {f g : α → ENNReal} (hf : AEMeasurable f μ) :
    ⨍⁻ x in s, (f x + g x) ∂μ = ⨍⁻ x in s, f x ∂μ + ⨍⁻ x in s, g x ∂μ := by
  simp_rw [setLaverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]

-- Named for consistency with `setLintegral_mono'`
lemma setLaverage_mono' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f g : α → ENNReal} (h : ∀ x ∈ s, f x ≤ g x) :
    ⨍⁻ x in s, f x ∂μ ≤ ⨍⁻ x in s, g x ∂μ := by
  simp_rw [setLaverage_eq]
  exact ENNReal.div_le_div_right (setLIntegral_mono' hs h) (μ s)

end MeasureTheory

namespace MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
  {F : Type*} [NormedAddCommGroup F]

theorem AEStronglyMeasurable.ennreal_toReal {u : α → ℝ≥0∞} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x ↦ (u x).toReal) μ := by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable

lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ := by
  exact lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

lemma setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ := by
  refine laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self

lemma setLaverage_const_le {c : ℝ≥0∞} : ⨍⁻ _x in s, c ∂μ ≤ c := by
  simp_rw [setLaverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc]
  conv_rhs => rw [← mul_one c]
  gcongr
  exact ENNReal.mul_inv_le_one (μ s)

theorem eLpNormEssSup_lt_top_of_ae_ennnorm_bound {f : α → F} {C : ℝ≥0∞}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : eLpNormEssSup f μ ≤ C := essSup_le_of_ae_le C hfC

@[simp]
lemma ENNReal.nnorm_toReal {x : ℝ≥0∞} : ‖x.toReal‖₊ = x.toNNReal := by
  ext; simp [ENNReal.toReal]

end MeasureTheory

/-! ## `EquivalenceOn` -/

/-- An equivalence relation on the set `s`. -/
structure EquivalenceOn {α : Type*} (r : α → α → Prop) (s : Set α) : Prop where
  /-- An equivalence relation is reflexive: `x ~ x` -/
  refl  : ∀ x ∈ s, r x x
  /-- An equivalence relation is symmetric: `x ~ y` implies `y ~ x` -/
  symm  : ∀ {x y}, x ∈ s → y ∈ s → r x y → r y x
  /-- An equivalence relation is transitive: `x ~ y` and `y ~ z` implies `x ~ z` -/
  trans : ∀ {x y z}, x ∈ s → y ∈ s → z ∈ s → r x y → r y z → r x z


namespace EquivalenceOn

variable {α : Type*} {r : α → α → Prop} {s : Set α} {hr : EquivalenceOn r s} {x y : α}

variable (hr) in
protected def setoid : Setoid s where
  r x y := r x y
  iseqv := {
    refl := fun x ↦ hr.refl x x.2
    symm := fun {x y} ↦ hr.symm x.2 y.2
    trans := fun {x y z} ↦ hr.trans x.2 y.2 z.2
  }

include hr in
lemma exists_rep (x : α) : ∃ y, x ∈ s → y ∈ s ∧ r x y :=
  ⟨x, fun hx ↦ ⟨hx, hr.refl x hx⟩⟩

open Classical in
variable (hr) in
/-- An arbitrary representative of `x` w.r.t. the equivalence relation `r`. -/
protected noncomputable def out (x : α) : α :=
  if hx : x ∈ s then (Quotient.out (s := hr.setoid) ⟦⟨x, hx⟩⟧ : s) else x

lemma out_mem (hx : x ∈ s) : hr.out x ∈ s := by
  rw [EquivalenceOn.out, dif_pos hx]
  apply Subtype.prop

@[simp]
lemma out_mem_iff : hr.out x ∈ s ↔ x ∈ s := by
  refine ⟨fun h ↦ ?_, out_mem⟩
  by_contra hx
  rw [EquivalenceOn.out, dif_neg hx] at h
  exact hx h

lemma out_rel (hx : x ∈ s) : r (hr.out x) x := by
  rw [EquivalenceOn.out, dif_pos hx]
  exact @Quotient.mk_out _ (hr.setoid) ⟨x, hx⟩

lemma rel_out (hx : x ∈ s) : r x (hr.out x) := hr.symm (out_mem hx) hx (out_rel hx)

lemma out_inj (hx : x ∈ s) (hy : y ∈ s) (h : r x y) : hr.out x = hr.out y := by
  simp_rw [EquivalenceOn.out, dif_pos hx, dif_pos hy]
  congr 1
  simp_rw [Quotient.out_inj, Quotient.eq]
  exact h

lemma out_inj' (hx : x ∈ s) (hy : y ∈ s) (h : r (hr.out x) (hr.out y)) : hr.out x = hr.out y := by
  apply out_inj hx hy
  refine hr.trans hx ?_ hy (rel_out hx) <| hr.trans ?_ ?_ hy h <| out_rel hy
  all_goals simpa

variable (hr) in
/-- The set of representatives. -/
def reprs : Set α := hr.out '' s

lemma out_mem_reprs (hx : x ∈ s) : hr.out x ∈ hr.reprs := ⟨x, hx, rfl⟩

lemma reprs_subset : hr.reprs ⊆ s := by
  rintro _ ⟨x, hx, rfl⟩
  exact out_mem hx

lemma reprs_inj (hx : x ∈ hr.reprs) (hy : y ∈ hr.reprs) (h : r x y) : x = y := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact out_inj' hx hy h

end EquivalenceOn

namespace Set.Finite

lemma biSup_eq {α : Type*} {ι : Type*} [CompleteLinearOrder α] {s : Set ι}
    (hs : s.Finite) (hs' : s.Nonempty) (f : ι → α) :
    ∃ i ∈ s, ⨆ j ∈ s, f j = f i := by
  induction' s, hs using dinduction_on with a s _ _ ihs hf
  · simp at hs'
  rw [iSup_insert]
  by_cases hs : s.Nonempty
  · by_cases ha : f a ⊔ ⨆ x ∈ s, f x = f a
    · use a, mem_insert a s
    · obtain ⟨i, hi⟩ := ihs hs
      use i, Set.mem_insert_of_mem a hi.1
      rw [← hi.2, sup_eq_right]
      simp only [sup_eq_left, not_le] at ha
      exact ha.le
  · simpa using Or.inl fun i hi ↦ (hs (nonempty_of_mem hi)).elim

end Set.Finite

lemma Real.self_lt_two_rpow (x : ℝ) : x < 2 ^ x := by
  rcases lt_or_le x 0 with h | h
  · exact h.trans (rpow_pos_of_pos zero_lt_two x)
  · calc
      _ < (⌊x⌋₊.succ : ℝ) := Nat.lt_succ_floor x
      _ ≤ 2 ^ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.lt_pow_self one_lt_two _
      _ ≤ _ := rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le h)
