import Carleson.ToMathlib.ENorm
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-
* This file can import all ToMathlib files.
* If adding more than a few results, please put them in a more appropriate file in ToMathlib.

Upstreaming status: need to split up this file (according to the lemmas' future location)
Most lemmas look ready to be upstreamed; some will require small tweaks.
-/

open Function Set
open scoped ENNReal

-- todo: rename and protect `Real.RCLike`

namespace Real
-- to Mathlib.Analysis.SpecialFunctions.Log.Base
lemma le_pow_natCeil_logb {b x : ℝ} (hb : 1 < b) (hx : 0 < x) :
    x ≤ b ^ ⌈Real.logb b x⌉₊ := by
  calc
    x = b ^ Real.logb b x := by rw [Real.rpow_logb (by linarith) hb.ne' hx]
    _ ≤ b ^ ⌈Real.logb b x⌉₊ := by
      rw [← Real.rpow_natCast]
      gcongr
      · exact hb.le
      apply Nat.le_ceil

end Real

section ENNReal

open ENNReal

lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
  by_cases hfin : s.Finite
  · lift s to Finset α using hfin
    simp
  have : Infinite s := infinite_coe_iff.mpr hfin
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num), Set.encard_eq_top_iff.mpr hfin]
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
  conv_lhs => enter [1, n]; rw [← one_mul (n : ℤ), ← neg_mul, ← Nat.cast_one (R := ℤ)]
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

-- TODO: this helper lemma may be useful in other places to, for instance in `HardyLittlewood.lean`
lemma iSup_rpow {f : ℕ → ℝ≥0∞} {p : ℝ} (hp : 0 < p) :
    (⨆ n, f n) ^ p = ⨆ n, f n ^ p := by
  apply le_antisymm
  · rw [← rpow_le_rpow_iff (z := p⁻¹) (by positivity), rpow_rpow_inv (by positivity)]
    refine iSup_le fun i ↦ ?_
    rw [← rpow_le_rpow_iff (z := p) (by positivity), rpow_inv_rpow (by positivity)]
    apply le_iSup _ i
  · apply iSup_le; intro i; gcongr; apply le_iSup _ i

end ENNReal

section NNReal


@[simp]
lemma _root_.ENNReal.nnorm_toReal {x : ℝ≥0∞} : ‖x.toReal‖₊ = x.toNNReal := by
  ext; simp [ENNReal.toReal]

end NNReal


namespace Function
section support

lemma support_rpow_of_pos {α : Type*} {f : α → ℝ≥0∞} {p : ℝ} (p_pos : 0 < p) :
    support (fun x ↦ f x ^ p) = support f := by
  ext x
  simp [ENNReal.rpow_eq_zero_iff_of_pos p_pos]

lemma support_rpow_of_neg {α : Type*} {f : α → ℝ≥0∞} {p : ℝ} (p_neg : p < 0) :
    support (fun x ↦ f x ^ p) = {x | f x ≠ ⊤} := by
  ext x
  simp [p_neg]
  grind

@[simp] lemma support_ofNNReal : Function.support ENNReal.ofNNReal = Set.Ioi 0 := by
  ext x
  simp

end support
end Function

namespace MeasureTheory

set_option linter.style.refine false in
variable {α : Type*} {β : Type*} {s : Set α} {f g : α → β}
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} in
@[measurability, fun_prop]
protected theorem _root_.AEMeasurable.piecewise {d : DecidablePred (· ∈ s)} (hs : MeasurableSet s)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (piecewise s f g) μ := by
  refine' ⟨_, hf.measurable_mk.piecewise hs hg.measurable_mk, ?_⟩
  · assumption
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  simp_rw [Set.piecewise, ← hfx, ← hgx]

variable {α : Type*} {β : Type*} {p : α → Prop} {f g : α → β}
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} in
@[measurability, fun_prop]
protected theorem _root_.AEMeasurable.ite {d : DecidablePred p} (hp : MeasurableSet {a | p a})
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => ite (p x) (f x) (g x)) μ :=
  hf.piecewise hp hg


/-! ## Partitioning an interval -/


lemma lintegral_Ioc_partition {a b : ℕ} {c : ℝ} {f : ℝ → ℝ≥0∞} (hc : 0 ≤ c) :
    ∫⁻ t in Ioc (a * c) (b * c), f t =
    ∑ l ∈ Finset.Ico a b, ∫⁻ t in Ioc (l * c) ((l + 1 : ℕ) * c), f t := by
  rcases lt_or_ge b a with h | h
  · rw [Finset.Ico_eq_empty (by lia), Ioc_eq_empty (by rw [not_lt]; gcongr),
      setLIntegral_empty, Finset.sum_empty]
  induction b, h using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Ioc_self, setLIntegral_empty, Finset.sum_empty]
  | succ b h ih =>
    have li : a * c ≤ b * c := by gcongr
    rw [← Ioc_union_Ioc_eq_Ioc li (by gcongr; lia),
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      ← Order.succ_eq_add_one, ← Finset.insert_Ico_right_eq_Ico_succ h,
      Finset.sum_insert Finset.right_notMem_Ico,
      add_comm (lintegral ..), ih, Order.succ_eq_add_one]

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
  simp_rw [setLAverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]

-- Named for consistency with `setLintegral_mono'`
lemma setLaverage_mono' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f g : α → ENNReal} (h : ∀ x ∈ s, f x ≤ g x) :
    ⨍⁻ x in s, f x ∂μ ≤ ⨍⁻ x in s, g x ∂μ := by
  simp_rw [setLAverage_eq]
  exact ENNReal.div_le_div_right (setLIntegral_mono' hs h) (μ s)

lemma AEStronglyMeasurable_continuousMap_coe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace.PseudoMetrizableSpace Y]
    [SecondCountableTopologyEither X Y]
    (f : C(X, Y)) : StronglyMeasurable f :=
  (map_continuous _).stronglyMeasurable

end MeasureTheory

namespace MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
  {F : Type*} [NormedAddCommGroup F]

attribute [fun_prop] Continuous.comp_aestronglyMeasurable
  AEStronglyMeasurable.mul AEStronglyMeasurable.prodMk
  AEMeasurable.restrict AEStronglyMeasurable.restrict
  AEStronglyMeasurable.const_smul AEStronglyMeasurable.const_smul'
  AEStronglyMeasurable.smul_const
  AEStronglyMeasurable.mul AEStronglyMeasurable.add
  AEStronglyMeasurable.mul_const AEStronglyMeasurable.const_mul
  AEStronglyMeasurable.inv AEStronglyMeasurable.div
attribute [gcongr] Measure.AbsolutelyContinuous.prod -- todo: also add one-sided versions for gcongr
attribute [fun_prop] AEStronglyMeasurable.comp_measurable
attribute [fun_prop] StronglyMeasurable.measurable

lemma measure_mono_ae' {A B : Set α} (h : μ (B \ A) = 0) : μ B ≤ μ A := by
  apply measure_mono_ae
  change μ {x | ¬ B x ≤ A x} = 0
  simpa only [le_Prop_eq, Classical.not_imp]

theorem AEStronglyMeasurable.ennreal_toReal {u : α → ℝ≥0∞} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x ↦ (u x).toReal) μ := by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable

lemma setLaverage_const_le {c : ℝ≥0∞} : ⨍⁻ _x in s, c ∂μ ≤ c := by
  simp_rw [setLAverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc]
  conv_rhs => rw [← mul_one c]
  gcongr
  exact ENNReal.mul_inv_le_one (μ s)

theorem eLpNormEssSup_lt_top_of_ae_ennnorm_bound {f : α → F} {C : ℝ≥0∞}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : eLpNormEssSup f μ ≤ C := essSup_le_of_ae_le C hfC

theorem restrict_absolutelyContinuous : μ.restrict s ≪ μ :=
  fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| zero_le _

section eLpNorm

variable {p : ℝ≥0∞}

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

lemma eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  apply essSup_mono_ae _
  apply Eventually.of_forall (by simp)

lemma eLpNormEssSup_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  apply essSup_congr_ae
  filter_upwards [hf] with x hx
  simp [hx]

lemma eLpNorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ ≤ eLpNorm' f p μ := by
  simp_rw [eLpNorm', enorm_eq_self]
  gcongr
  simp

lemma eLpNorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ = eLpNorm' f p μ := by
  simp_rw [eLpNorm', enorm_eq_self]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hf] with x hx
  simp [hx]

lemma eLpNorm_toReal_le {f : α → ℝ≥0∞} :
    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ := by
  simp_rw [eLpNorm]
  split_ifs
  · rfl
  · exact eLpNormEssSup_toReal_le
  · exact eLpNorm'_toReal_le toReal_nonneg

lemma eLpNorm_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm (ENNReal.toReal ∘ f) p μ = eLpNorm f p μ := by
  simp_rw [eLpNorm]
  split_ifs
  · rfl
  · exact eLpNormEssSup_toReal_eq hf
  · exact eLpNorm'_toReal_eq hf

lemma sq_eLpNorm_two {ε : Type*} [ENorm ε] {f : α → ε} :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (f := f) two_ne_zero

open ComplexConjugate in
/-- One of the very few cases where a norm can be moved _out of_ an integral. -/
lemma eLpNorm_two_eq_enorm_integral_mul_conj {f : α → ℂ} (lpf : MemLp f 2 μ) :
    eLpNorm f 2 μ ^ 2 = ‖∫ x, f x * conj (f x) ∂μ‖ₑ := by
  conv_rhs => enter [1, 2, x]; rw [RCLike.mul_conj, ← RCLike.ofReal_pow]
  erw [integral_ofReal]
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ by simp)]; swap
  · exact lpf.aestronglyMeasurable.norm.pow 2
  conv_rhs => enter [1, 1, 1, 2, x]; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← sq_eLpNorm_two, ← enorm_norm]
  simp_rw [Complex.coe_algebraMap, Complex.norm_real, enorm_norm]
  rw [toReal_pow, enorm_pow, enorm_toReal lpf.eLpNorm_ne_top]

end eLpNorm

namespace MemLp

variable {p : ℝ≥0∞}
theorem toReal {f : α → ℝ≥0∞} (hf : MemLp f p μ) : MemLp (f · |>.toReal) p μ :=
  ⟨hf.aestronglyMeasurable.aemeasurable.ennreal_toReal.aestronglyMeasurable,
    eLpNorm_toReal_le.trans_lt hf.eLpNorm_lt_top⟩

end MemLp

theorem Integrable.toReal {f : α → ℝ≥0∞} (hf : Integrable f μ) : Integrable (f · |>.toReal) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.toReal

end MeasureTheory

section

open MeasureTheory Bornology
variable {E X : Type*} {p : ℝ≥0∞} [NormedAddCommGroup E] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E}

---- now obsolete -> `BoundedCompactSupport.memLp`
-- lemma _root_.HasCompactSupport.memLp_of_isBounded (hf : HasCompactSupport f)
--     (h2f : IsBounded (range f))
--     (h3f : AEStronglyMeasurable f μ) {p : ℝ≥0∞} : MemLp f p μ := by
--   obtain ⟨C, hC⟩ := h2f.exists_norm_le
--   simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
--   exact hf.memLp_of_bound h3f C <| .of_forall hC

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
  rcases lt_or_ge x 0 with h | h
  · exact h.trans (rpow_pos_of_pos zero_lt_two x)
  · calc
      _ < (⌊x⌋₊.succ : ℝ) := Nat.lt_succ_floor x
      _ ≤ 2 ^ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.lt_pow_self one_lt_two
      _ ≤ _ := rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le h)

@[fun_prop]
lemma Complex.measurable_starRingEnd : Measurable (starRingEnd ℂ) :=
   Complex.continuous_conj.measurable

namespace ENNReal

lemma rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (hz : z ≤ 0) (h : x ≤ y) :
    y ^ z ≤ x ^ z := by
  rw [← neg_neg z, rpow_neg y, rpow_neg x, ← inv_rpow, ← inv_rpow]
  exact rpow_le_rpow (ENNReal.inv_le_inv.mpr h) (neg_nonneg.mpr hz)

lemma rpow_lt_rpow_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) (h : x < y) :
    y ^ z < x ^ z := by
  rw [← neg_neg z, ENNReal.rpow_neg y, ENNReal.rpow_neg x, ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
  exact ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.mpr h) (neg_pos.mpr hz)

lemma rpow_lt_rpow_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) :
    x ^ z < y ^ z ↔ y < x :=
  ⟨lt_imp_lt_of_le_imp_le (fun h ↦ ENNReal.rpow_le_rpow_of_nonpos (le_of_lt hz) h),
    fun h ↦ ENNReal.rpow_lt_rpow_of_neg hz h⟩

lemma rpow_le_rpow_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) :
    x ^ z ≤ y ^ z ↔ y ≤ x :=
  le_iff_le_iff_lt_iff_lt.2 <| ENNReal.rpow_lt_rpow_iff_of_neg hz

theorem rpow_le_self_of_one_le {x : ℝ≥0∞} {y : ℝ} (hx : 1 ≤ x) (hy : y ≤ 1) :
    x ^ y ≤ x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx hy

end ENNReal

namespace Set

section Indicator

open ComplexConjugate

attribute [gcongr] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset

lemma indicator_eq_indicator' {α : Type*} {M : Type*} [Zero M] {s : Set α} {f g : α → M} (h : ∀ x ∈ s, f x = g x) :
    s.indicator f = s.indicator g := by
  ext x
  unfold indicator
  split
  · rename_i hxs
    exact h x hxs
  · rfl

lemma indicator_eq_indicator_one_mul {ι M : Type*} [MulZeroOneClass M]
    (s : Set ι) (f : ι → M) (x : ι) : s.indicator f x = s.indicator 1 x * f x := by
  simp only [indicator]; split_ifs <;> simp

lemma conj_indicator {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (s : Set α) (x : α) :
    conj (s.indicator f x) = s.indicator (conj f) x := by
  simp only [indicator]; split_ifs <;> simp

lemma eq_indicator_one_mul_of_norm_le {X : Type*} {F : Set X} {f : X → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    f = (F.indicator 1) * f := by
  ext y
  simp only [Pi.mul_apply, indicator, Pi.one_apply, ite_mul, one_mul, zero_mul]
  split_ifs with hy
  · rfl
  · specialize hf y
    simp only [indicator, hy, ↓reduceIte] at hf
    rw [← norm_eq_zero]
    exact le_antisymm hf (norm_nonneg _)

lemma indicator_one_le_one {X : Type*} {G : Set X} (x : X) :
    G.indicator (1 : X → ℝ) x ≤ 1 := by
  classical
  exact le_trans (ite_le_sup _ _ _) (by simp)

end Indicator

end Set

section Norm

open Complex

-- TODO: add enorm analogues of these lemmas when not present yet;
-- the first one will require a new class `ENormOneClass` (and maybe generalising much of
-- mathlib's lemmas to that class, as appropriate).

-- for mathlib?
lemma norm_indicator_one_le {α E}
    [SeminormedAddCommGroup E] [One E] [NormOneClass E] {s : Set α} (x : α) :
    ‖s.indicator (1 : α → E) x‖ ≤ 1 :=
  Trans.trans (norm_indicator_le_norm_self 1 x) norm_one

-- TODO: which of these lemmas have been upstreamed to mathlib already?

lemma norm_one_sub_exp_neg_I_mul_ofReal (x : ℝ) : ‖1 - exp (-(I * x))‖ = ‖1 - exp (I * x)‖ := by
  have : 1 - exp (I * x) = - exp (I * x) * (1 - exp (I * (-x))) := by
    simp [mul_sub, ← exp_add]; ring
  simp [this]

open Real in
lemma exp_I_mul_eq_one_iff_of_lt_of_lt (x : ℝ) (hx : -(2 * π) < x) (h'x : x < 2 * π) :
    exp (I * x) = 1 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have : Real.cos x = 1 := by simpa [mul_comm I x] using congr(($h).re)
  rwa [Real.cos_eq_one_iff_of_lt_of_lt hx h'x] at this

end Norm

section BddAbove
-- move near BddAbove.range_add if that imports Finset.sum

variable {ι ι' α M : Type*} [Preorder M]

@[simp]
theorem BddAbove.range_const {c : M} : BddAbove (range (fun _ : ι ↦ c)) :=
  bddAbove_singleton.mono Set.range_const_subset

variable [One M] in
@[to_additive (attr := simp)]
theorem BddAbove.range_one : BddAbove (range (1 : ι → M)) :=
  .range_const

variable [AddCommMonoid M] [AddLeftMono M] [AddRightMono M] in
theorem BddAbove.range_finsetSum {s : Finset ι} {f : ι → ι' → M}
    (hf : ∀ i ∈ s, BddAbove (range (f i))) :
    BddAbove (range (fun x ↦ ∑ i ∈ s, f i x)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hjs IH =>
    simp_rw [Finset.sum_insert hjs]
    apply BddAbove.range_add
    · exact hf _ (Finset.mem_insert_self j s)
    · exact IH fun _ hi ↦ hf _ (Finset.mem_insert_of_mem hi)

-- TODO: should there be enorm versions of these lemmas?

open Bornology
@[to_additive isBounded_iff_bddAbove_norm]
lemma isBounded_iff_bddAbove_norm' {E} [SeminormedCommGroup E] {s : Set E} :
    IsBounded s ↔ BddAbove (Norm.norm '' s) := by
  simp [isBounded_iff_forall_norm_le', bddAbove_def]

lemma isBounded_range_iff_bddAbove_norm' {ι E} [SeminormedAddCommGroup E] {f : ι → E} :
    IsBounded (range f) ↔ BddAbove (range (‖f ·‖)) := by
  rw [isBounded_iff_bddAbove_norm, ← range_comp, Function.comp_def]

lemma isBounded_image_iff_bddAbove_norm' {ι E} [SeminormedAddCommGroup E] {f : ι → E} {s : Set ι} :
    IsBounded (f '' s) ↔ BddAbove ((‖f ·‖) '' s) := by
  rw [isBounded_iff_bddAbove_norm, ← image_comp, Function.comp_def]

end BddAbove

namespace MeasureTheory

open Metric Bornology
variable {𝕜 : Type*} [RCLike 𝕜] {X α : Type*}

-- TODO: can this be moved to HasCompactSupport? should it move there, when upstreaming?
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
theorem indicator_const {c : ℝ} {s : Set X}
    (hs : MeasurableSet s) (h2s : volume s < ⊤) : Integrable (s.indicator (fun _ ↦ c)) :=
  (integrable_indicator_iff hs).mpr <| integrableOn_const h2s.ne

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
      exact Finset.sum_congr rfl (fun i hi ↦ by simp [hi])
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

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_Lp_smul {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : p > 0) (c : NNReal) :
    (∫⁻ x : α, (c • f) x ^ p ∂μ) ^ (1 / p) = c • (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) := by
  simp_rw [smul_def, Pi.smul_apply, smul_eq_mul, mul_rpow_of_nonneg _ _ hp.le,
    MeasureTheory.lintegral_const_mul'' _ (hf.pow_const p),
    mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le), ← rpow_mul, mul_one_div_cancel hp.ne.symm,
    rpow_one]

-- Analogous to `ENNReal.ofReal_pow` in Mathlib
-- Currently unused
theorem ofReal_zpow {p : ℝ} (hp : 0 < p) (n : ℤ) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  rw [ofReal_eq_coe_nnreal hp.le, ← coe_zpow, ← ofReal_coe_nnreal, NNReal.coe_zpow, NNReal.coe_mk]
  exact NNReal.coe_ne_zero.mp hp.ne.symm

end ENNReal


--TODO: to mathlib
@[to_additive (attr := simp)]
theorem prod_attach_insert {α β : Type*} {s : Finset α} {a : α} [DecidableEq α] [CommMonoid β]
    {f : { i // i ∈ insert a s } → β} (ha : a ∉ s) :
    ∏ x ∈ (insert a s).attach, f x =
    f ⟨a, Finset.mem_insert_self a s⟩ * ∏ x ∈ s.attach, f ⟨x, Finset.mem_insert_of_mem x.2⟩ := by
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · intros x hx y hy h
    ext
    simpa using h
  · simp [ha]

@[to_additive]
lemma Finset.prod_finset_product_filter_right {α β γ : Type*} {s : Finset α} {t : Finset β}
    {p : α → Prop} {q : α → β → Prop} [DecidablePred p] [DecidableRel q]
    [DecidablePred fun r : α × β ↦ p r.1 ∧ q r.1 r.2] {f : α → β → γ} [CommMonoid γ] :
    ∏ x ∈ s with p x, ∏ y ∈ t with q x y, f x y =
    ∏ r ∈ s ×ˢ t with p r.1 ∧ q r.1 r.2, f r.1 r.2 := by
  convert (prod_finset_product_right' ((t ×ˢ s).filter fun r ↦ p r.2 ∧ q r.2 r.1) _ _ _).symm
  · refine Finset.prod_equiv (Equiv.prodComm α β) (fun r ↦ ?_) (by simp)
    simp_rw [mem_filter, mem_product, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    tauto
  · intro r; simp only [mem_filter, mem_product]; tauto

open Classical ComplexConjugate in
lemma Finset.sum_range_mul_conj_sum_range {α : Type*} {s : Finset α} {f : α → ℂ} :
    ∑ j ∈ s, f j * conj (f j) + ∑ j ∈ s, ∑ j' ∈ s with j ≠ j', f j * conj (f j') =
    (∑ j ∈ s, f j) * conj (∑ j' ∈ s, f j') := by
  calc
    _ = ∑ j ∈ s, ∑ j' ∈ s with j = j', f j * conj (f j') +
        ∑ j ∈ s, ∑ j' ∈ s with j ≠ j', f j * conj (f j') := by
      rw [add_left_inj]
      congr! with j mj; simp_rw [filter_eq, mj, ite_true, sum_singleton]
    _ = _ := by
      conv_lhs =>
        rw [← sum_add_distrib]; enter [2, j]; rw [sum_filter_add_sum_filter_not, ← mul_sum]
      rw [sum_mul, map_sum]

lemma Finset.pow_sum_comm {ι R : Type*} [Semiring R] {s : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ s, f i) ^ n = ∑ i ∈ s, f i ^ n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    simp_rw [pow_succ, ih, sum_mul, mul_sum]
    congr! 1 with x mx
    refine Finset.sum_eq_single _ (fun y my hn ↦ ?_) (fun _ ↦ by contradiction)
    rw [← Nat.sub_one_add_one (show n ≠ 0 by lia), pow_succ, mul_assoc, hf _ mx _ my hn.symm,
      mul_zero]

namespace MeasureTheory

lemma sum_sq_eLpNorm_indicator_le_of_pairwiseDisjoint
    {α ι F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    {s : Finset ι} {f : α → F} {t : ι → Set α} (meast : ∀ i, MeasurableSet (t i))
    (hpd : PairwiseDisjoint s t) :
    ∑ i ∈ s, eLpNorm ((t i).indicator f) 2 μ ^ 2 ≤ eLpNorm f 2 μ ^ 2 := by
  simp_rw [sq_eLpNorm_two]
  conv_lhs =>
    enter [2, i, 2, x]
    rw [enorm_indicator_eq_indicator_enorm, sq, ← inter_indicator_mul, inter_self]
    enter [2, y]; rw [← sq]
  conv_lhs => enter [2, i]; rw [lintegral_indicator (meast i)]
  rw [← lintegral_biUnion_finset hpd fun _ _ ↦ meast _]
  exact setLIntegral_le_lintegral _ _

theorem measurable_measure_ball {α : Type*} [PseudoMetricSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [SFinite μ] :
    Measurable fun (a, r) ↦ μ (Metric.ball a r) := by
  let s : Set (α × α × ℝ) := setOf fun (b, a, r) ↦ b ∈ Metric.ball a r
  apply measurable_measure_prodMk_right (s := s)
  unfold s Metric.ball
  simp_rw [mem_setOf]
  apply measurableSet_lt
  · fun_prop
  · fun_prop

end MeasureTheory
