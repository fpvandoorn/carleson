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
* If adding more than a few results, please put them in a more appropriate file in ToMathlib.
-/

open Function Set
open scoped ENNReal

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
    rw [ne_eq, Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add, not_le, inv_lt_one_iff₀]
    right; exact one_lt_pow₀ (M₀ := ℝ) _root_.one_lt_two hk.ne'
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

lemma ENNReal.toReal_zpow (x : ℝ≥0∞) (z : ℤ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [← rpow_intCast, ← toReal_rpow, Real.rpow_intCast]

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

attribute [fun_prop] Continuous.comp_aestronglyMeasurable
  AEStronglyMeasurable.mul AEStronglyMeasurable.prod_mk
attribute [gcongr] Measure.AbsolutelyContinuous.prod -- todo: also add one-sided versions for gcongr


theorem AEStronglyMeasurable.ennreal_toReal {u : α → ℝ≥0∞} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x ↦ (u x).toReal) μ := by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable

lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ := by
  exact lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]
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

theorem restrict_absolutelyContinuous : μ.restrict s ≪ μ :=
  fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| zero_le _

end MeasureTheory

section

open MeasureTheory Bornology
variable {E X : Type*} {p : ℝ≥0∞} [NormedAddCommGroup E] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E}

---- now obsolete -> `BoundedCompactSupport.memℒp`
-- lemma _root_.HasCompactSupport.memℒp_of_isBounded (hf : HasCompactSupport f)
--     (h2f : IsBounded (range f))
--     (h3f : AEStronglyMeasurable f μ) {p : ℝ≥0∞} : Memℒp f p μ := by
--   obtain ⟨C, hC⟩ := h2f.exists_norm_le
--   simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
--   exact hf.memℒp_of_bound h3f C <| .of_forall hC

end

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
/-- The setoid defined from an equivalence relation on a set. -/
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
/-- The set of representatives of an equivalence relation on a set. -/
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
  simpa [sSup_image, eq_comm] using hs'.image f |>.csSup_mem (hs.image f)

end Set.Finite

lemma Real.self_lt_two_rpow (x : ℝ) : x < 2 ^ x := by
  rcases lt_or_le x 0 with h | h
  · exact h.trans (rpow_pos_of_pos zero_lt_two x)
  · calc
      _ < (⌊x⌋₊.succ : ℝ) := Nat.lt_succ_floor x
      _ ≤ 2 ^ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.lt_pow_self one_lt_two
      _ ≤ _ := rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le h)

namespace Set

open ComplexConjugate

lemma indicator_eq_indicator_one_mul {ι M:Type*} [MulZeroOneClass M]
    (s : Set ι) (f : ι → M) (x : ι) : s.indicator f x = s.indicator 1 x * f x := by
  simp only [indicator]; split_ifs <;> simp

lemma conj_indicator {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (s : Set α) (x : α):
    conj (s.indicator f x) = s.indicator (conj f) x := by
  simp only [indicator]; split_ifs <;> simp

end Set

section Norm

open Complex

-- for mathlib?
lemma norm_indicator_one_le {α E}
    [SeminormedAddCommGroup E] [One E] [NormOneClass E] {s : Set α} (x : α) :
    ‖s.indicator (1 : α → E) x‖ ≤ 1 :=
  Trans.trans (norm_indicator_le_norm_self 1 x) norm_one

lemma norm_exp_I_mul_ofReal (x : ℝ) : ‖exp (.I * x)‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_I_mul_sub_ofReal (x y: ℝ) : ‖exp (.I * (x - y))‖ = 1 := by
  rw [mul_comm, ← ofReal_sub, Complex.norm_exp_ofReal_mul_I]

end Norm

namespace MeasureTheory

open Metric Bornology
variable {𝕜: Type*}
variable [RCLike 𝕜]

variable {X α: Type*}

namespace HasCompactSupport

variable [Zero α] {f : X → α}

variable [PseudoMetricSpace X] [ProperSpace X]

theorem of_support_subset_closedBall {x : X}
    {r : ℝ} (hf : support f ⊆ closedBall x r) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall ..) hf

theorem of_support_subset_isBounded {s : Set X}
    (hs : IsBounded s) (hf : support f ⊆ s) :
    HasCompactSupport f :=
  IsCompact.closure_of_subset hs.isCompact_closure <| Trans.trans hf subset_closure

end HasCompactSupport

namespace Integrable

variable [MeasureSpace X]

-- must be in mathlib but can't find it
theorem indicator_const {c : ℝ} {s: Set X}
    (hs: MeasurableSet s) (h2s : volume s < ⊤) : Integrable (s.indicator (fun _ ↦ c)) :=
  (integrable_indicator_iff hs).mpr <| integrableOn_const.mpr <| Or.inr h2s

end Integrable

-- Currently unused.
-- The assumption `int_f` can likely be removed, as otherwise the integral is zero.
open Classical in
theorem setIntegral_biUnion_le_sum_setIntegral {X : Type*} {ι : Type*} [MeasurableSpace X]
    {f : X → ℝ} (s : Finset ι) {S : ι → Set X} {μ : Measure X}
    (f_ae_nonneg : ∀ᵐ (x : X) ∂μ.restrict (⋃ i ∈ s, S i), 0 ≤ f x)
    (int_f : IntegrableOn f (⋃ i ∈ s, S i) μ) :
    ∫ x in (⋃ i ∈ s, S i), f x ∂μ ≤ ∑ i ∈ s, ∫ x in S i, f x ∂μ := by
  have res_res : ∀ i ∈ s, (μ.restrict (⋃ i ∈ s, S i)).restrict (S i) = μ.restrict (S i) :=
    fun i hi ↦ by rw [Measure.restrict_restrict_of_subset]; exact (subset_biUnion_of_mem hi)
  -- Show that it suffices to prove the result in the case where the integrand is measurable
  set g := AEMeasurable.mk f int_f.aemeasurable with hg
  have g_ae_nonneg : ∀ᵐ (x : X) ∂μ.restrict (⋃ i ∈ s, S i), 0 ≤ g x := by
    apply f_ae_nonneg.congr ∘ int_f.aemeasurable.ae_eq_mk.mp
    exact Filter.Eventually.of_forall (fun _ h ↦ by rw [h])
  have int_g : ∀ i ∈ s, Integrable g (μ.restrict (S i)) := by
    intro i hi
    have := (int_f.congr int_f.aemeasurable.ae_eq_mk).restrict (s := S i)
    rwa [res_res i hi] at this
  have : ∑ i ∈ s, ∫ (x : X) in S i, f x ∂μ = ∑ i ∈ s, ∫ (x : X) in S i, g x ∂μ := by
    refine Finset.sum_congr rfl (fun i hi ↦ integral_congr_ae ?_)
    convert int_f.aemeasurable.ae_eq_mk.restrict (s := S i) using 2
    rw [Measure.restrict_restrict_of_subset]
    exact (subset_biUnion_of_mem hi)
  rw [this, integral_congr_ae int_f.aemeasurable.ae_eq_mk]
  -- Now prove the result for the measurable integrand `g`
  have meas : MeasurableSet {x | 0 ≤ g x} :=
    have : {x | 0 ≤ g x} = g ⁻¹' (Ici 0) := by simp [preimage, mem_Ici]
    this ▸ (AEMeasurable.measurable_mk int_f.aemeasurable) measurableSet_Ici
  rw [← integral_finset_sum_measure int_g]
  set μ₀ : ι → Measure X := fun i ↦ ite (i ∈ s) (μ.restrict (S i)) 0
  refine integral_mono_measure ?_ ?_ (integrable_finset_sum_measure.mpr int_g)
  · refine Measure.le_iff.mpr (fun T hT ↦ ?_)
    simp_rw [μ.restrict_apply hT, Measure.coe_finset_sum, s.sum_apply, inter_iUnion]
    apply le_trans <| measure_biUnion_finset_le s (T ∩ S ·)
    exact s.sum_le_sum (fun _ _ ↦ ge_of_eq (μ.restrict_apply hT))
  · have : ∑ i ∈ s, μ.restrict (S i) = Measure.sum μ₀ := by
      ext T hT
      simp only [Measure.sum_apply (hs := hT), Measure.coe_finset_sum, s.sum_apply, μ₀]
      rw [tsum_eq_sum (s := s) (fun b hb ↦ by simp [hb])]
      exact Finset.sum_congr rfl (fun i hi ↦ by simp [hi, res_res])
    rw [Filter.EventuallyLE, this, Measure.ae_sum_iff' (by exact meas)]
    intro i
    by_cases hi : i ∈ s
    · simp only [Pi.zero_apply, hi, reduceIte, μ₀, ← res_res i hi, ae_restrict_iff meas, ← hg]
      exact g_ae_nonneg.mono (fun _ h _ ↦ h)
    · simp [hi, μ₀]

-- Analogous to `MeasureTheory.integral_smul_const` in Mathlib
theorem average_smul_const {X : Type*} {E : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*}
    [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E] (f : X → 𝕜) (c : E) :
    ⨍ (x : X), f x • c ∂μ = (⨍ (x : X), f x ∂μ) • c :=
  integral_smul_const f c

end MeasureTheory

namespace ENNReal

theorem lintegral_Lp_smul {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : p > 0) (c : NNReal) :
    (∫⁻ x : α, (c • f) x ^ p ∂μ) ^ (1 / p) = c • (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) := by
  simp_rw [smul_def, Pi.smul_apply, smul_eq_mul, mul_rpow_of_nonneg _ _ hp.le,
    MeasureTheory.lintegral_const_mul'' _ (hf.pow_const p),
    mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le), ← rpow_mul, mul_one_div_cancel hp.ne.symm,
    rpow_one]

-- Analogous to `ENNReal.ofReal_pow` in Mathlib
theorem ofReal_zpow {p : ℝ} (hp : 0 < p) (n : ℤ) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  rw [ofReal_eq_coe_nnreal hp.le, ← coe_zpow, ← ofReal_coe_nnreal, NNReal.coe_zpow, NNReal.coe_mk]
  exact NNReal.coe_ne_zero.mp hp.ne.symm

end ENNReal
