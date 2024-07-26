import Carleson.WeakType
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Sign

noncomputable section

section computations_pq

open Real Set

variable {p q t : ℝ} (hp : p > 0) (hq : q > 0) (ht : t ∈ Ioo 0 1)

lemma preservation_positivity : 0 < (1 - t) * p⁻¹ + t * q⁻¹ :=
  add_pos (mul_pos (sub_pos.mpr ht.2) (inv_pos_of_pos hp))
      (mul_pos ht.1 (inv_pos_of_pos hq))

end computations_pq

section computations

open Real Set

variable {p₀ q₀ p₁ q₁ p q t : ℝ} (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
  (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
  (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)

lemma test (a b : ℝ) (ha : a > 0) (hb : b > 0) : a < b ↔ b⁻¹ < a⁻¹ := by
  exact Iff.symm (inv_lt_inv hb ha)

def σ :=
  (((1 - t) * p₀⁻¹ + t * p₁⁻¹) * (q₁⁻¹ - q₀⁻¹)) / (((1 - t) * q₀⁻¹ + t * q₁⁻¹) * (p₁⁻¹ - p₀⁻¹))

lemma test_ (a b c : ℝ) (hc : c > 0) : c * a < c * b ↔ a < b := by exact mul_lt_mul_left hc

lemma inv_of_interpolated_pos : 0 < p⁻¹ := by
  rw [hp]; exact preservation_positivity hp₀ hp₁ ht

lemma test' (a : ℝ) (h : 0 < a⁻¹) : 0 < a := by exact inv_pos.mp h

lemma interpolated_pos : 0 < p := inv_pos.mp (inv_of_interpolated_pos hp₀ hp₁ ht hp)

lemma exp_lt_iff : p < p₀ ↔ p₁ < p₀ := by
  rw [← inv_lt_inv hp₀ (interpolated_pos hp₀ hp₁ ht hp), ← inv_lt_inv (b := p₁) hp₀ hp₁, hp]
  rw [sub_mul, one_mul]
  nth_rewrite 2 [← mul_lt_mul_left ht.1]; rw [← Real.add_lt_add_iff_left (t * p₀⁻¹ -p₀⁻¹)]; ring_nf

lemma ex_gt_iff : p₀ < p ↔ p₀ < p₁ := by
  rw [← inv_lt_inv (interpolated_pos hp₀ hp₁ ht hp) hp₀, ← inv_lt_inv hp₁ hp₀, hp]
  rw [sub_mul, one_mul]
  nth_rewrite 2 [← mul_lt_mul_left ht.1]; rw [← Real.add_lt_add_iff_left (t * p₀⁻¹ -p₀⁻¹)]; ring_nf

lemma ne_exponents : q ≠ q₀ := by
  have obs : q⁻¹ ≠ q₀⁻¹ := by
    rw [hq, ← sub_ne_zero, sub_mul, one_mul, add_comm_sub, add_sub_cancel_left, ← mul_sub]
    exact mul_ne_zero (ne_of_gt ht.1) (sub_ne_zero_of_ne (Ne.symm (fun h ↦ hq₀q₁ (inv_inj.mp h))))
  exact fun h ↦ obs (inv_inj.mpr h)

lemma σ_equality_1 :
    @σ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹ + t * p₁⁻¹) * ((1 - t) * q₀⁻¹ + t * q₁⁻¹ - q₀⁻¹)) /
    (((1 - t) * q₀⁻¹ + t * q₁⁻¹) * ((1 - t) * p₀⁻¹ + t * p₁⁻¹ - p₀⁻¹)) := by
  unfold σ
  have t_pos : 0 < t := ht.1
  rw [← mul_div_mul_right _ _ (ne_of_gt t_pos), mul_assoc _ _ t, mul_assoc _ _ t]
  congr <;> ring

lemma σ_equality_2 :
    @σ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹ + t * p₁⁻¹) * ((1 - t) * q₀⁻¹ + t * q₁⁻¹ - q₁⁻¹)) /
    (((1 - t) * q₀⁻¹ + t * q₁⁻¹) * ((1 - t) * p₀⁻¹ + t * p₁⁻¹ - p₁⁻¹)) := by
  unfold σ
  have : - (1 - t) < 0 := neg_neg_iff_pos.mpr (sub_pos.mpr ht.2)
  rw [← mul_div_mul_right _ _ (ne_of_lt this), mul_assoc _ _ (-(1 - t)), mul_assoc _ _ (-(1 - t))]
  congr <;> ring

lemma σ_symm :
    @σ p₀ q₀ p₁ q₁ t = @σ p₁ q₁ p₀ q₀ (1 - t) := by
  unfold σ
  rw [← mul_div_mul_right (c := - 1), mul_assoc _ _ (-1), mul_assoc _ _ (-1)]; swap; positivity
  simp only [mul_neg, mul_one, neg_sub, _root_.sub_sub_cancel]
  nth_rewrite 1 [add_comm]; nth_rw 2 [add_comm]

lemma σ_equality_4 :
    @σ p₀ q₀ p₁ q₁ t =
    (p₀ * (q₀ - q)) / (q₀ * (p₀ - p)) := by
  rw [σ_equality_1 ht, ← hp, ← hq]
  have t_pos : 0 < t := ht.1
  have ineq : 0 < 1 - t := (Ioo.one_sub_mem ht).1
  have q_inv_pos : 0 < q⁻¹ := by rw [hq]; positivity
  have p_inv_pos : 0 < p⁻¹ := by rw [hp]; positivity
  have q_pos : 0 < q := by exact inv_pos.mp q_inv_pos
  have p_pos : 0 < p := by exact inv_pos.mp p_inv_pos
  have hne : p * q * p₀ * q₀ ≠ 0 := by positivity
  rw [← mul_div_mul_right _ _ hne]
  have eq₁ : p⁻¹ * (q⁻¹ - q₀⁻¹) * (p * q * p₀ * q₀) =
      p₀ * (p⁻¹ * p) * ((q⁻¹ * q) * q₀ - (q₀⁻¹ * q₀) * q) := by ring
  have eq₂ : q⁻¹ * (p⁻¹ - p₀⁻¹) * (p * q * p₀ * q₀) =
      q₀ * (q⁻¹ * q) * ((p⁻¹ * p) * p₀ - (p₀⁻¹ * p₀) * p) := by ring
  rw [eq₁, eq₂, inv_mul_cancel, inv_mul_cancel, inv_mul_cancel, inv_mul_cancel] <;> try positivity
  simp only [mul_one, one_mul]

lemma σ_equality_5 :
    @σ p₀ q₀ p₁ q₁ t =
    (p₁ * (q₁ - q)) / (q₁ * (p₁ - p)) := by
  rw [σ_symm]
  have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
  rw [σ_equality_4 hp₁ hq₁ hp₀ hq₀ one_sub_mem]
  · rw [hp]; ring
  · rw [hq]; ring

lemma σ_equality_6 :
    p₀ + (@σ p₀ q₀ p₁ q₁ t)⁻¹ * (q - q₀) * (p₀ / q₀) = p := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  simp only [inv_div]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  have : q₀ - q ≠ 0 := sub_ne_zero_of_ne (id (Ne.symm (ne_exponents ht hq₀q₁ hq)))
  calc
  _ = p₀ - (q₀⁻¹ * q₀) * (p₀ - p) * (p₀⁻¹ * p₀) * ((q₀ - q)⁻¹ * (q₀ - q)) := by ring
  _ = _ := by
    rw [inv_mul_cancel (ne_of_gt hq₀), inv_mul_cancel (ne_of_gt hp₀),
        inv_mul_cancel (by positivity)]; ring

lemma σ_pos_iff_aux : ( 0 < p₀ * (q₀ - q) / (q₀ * (p₀ - p))) ↔
    ((q - q₀ < 0) ∧ (p - p₀ < 0)) ∨ ((0 < q - q₀) ∧ (0 < p - p₀))  := by
  rw [div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  -- from here, field_simp would also work
  rw [mul_pos_iff_of_pos_left hp₀, mul_pos_iff_of_pos_left hp₀,
      mul_pos_iff_of_pos_left hq₀, mul_pos_iff_of_pos_left hq₀, neg_sub, neg_sub]
  simp only [sub_pos, sub_neg]

lemma σ_pos_iff₀ : (0 < @σ p₀ q₀ p₁ q₁ t) ↔
    ((q - q₀ < 0) ∧ (p - p₀ < 0)) ∨ ((0 < q - q₀) ∧ (0 < p - p₀)) := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_pos_iff_aux hp₀ hq₀

lemma σ_pos_iff₁ : (0 < @σ p₀ q₀ p₁ q₁ t) ↔
    ((q - q₁ < 0) ∧ (p - p₁ < 0)) ∨ ((0 < q - q₁) ∧ (0 < p - p₁)) := by
  rw [σ_equality_5 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_pos_iff_aux hp₁ hq₁

lemma σ_neg_iff_aux : (p₀ * (q₀ - q) / (q₀ * (p₀ - p)) < 0) ↔
    ((q - q₀ < 0) ∧ (0 < p - p₀)) ∨ ((0 < q - q₀) ∧ (p - p₀ < 0)) := by
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  -- field_simp
  rw [mul_pos_iff_of_pos_left hp₀, mul_pos_iff_of_pos_left hp₀,
      mul_pos_iff_of_pos_left hq₀, mul_pos_iff_of_pos_left hq₀, neg_sub, neg_sub]
  simp only [sub_pos, sub_neg]

lemma σ_neg_iff₀ : (@σ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q - q₀ < 0) ∧ (0 < p - p₀)) ∨ ((0 < q - q₀) ∧ (p - p₀ < 0)) := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_neg_iff_aux hp₀ hq₀

lemma σ_neg_iff₁ : (@σ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q - q₁ < 0) ∧ (0 < p - p₁)) ∨ ((0 < q - q₁) ∧ (p - p₁ < 0)) := by
  rw [σ_equality_5 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  apply σ_neg_iff_aux hp₁ hq₁

-- TODO: there is some dependence on hp which is unnecessary, but should it be removed?
lemma σ_ne_zero : (@σ p₀ q₀ p₁ q₁ t ≠ 0) := by
  rw [σ_equality_4 hp₀ hq₀ hp₁ hq₁ ht hp hq]
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero (ne_of_gt hp₀) ?_
    refine sub_ne_zero_of_ne (Ne.symm ?_)
    exact ne_exponents ht hq₀q₁ hq
  · refine mul_ne_zero (ne_of_gt hq₀) ?_
    refine sub_ne_zero_of_ne (Ne.symm ?_)
    exact ne_exponents ht hp₀p₁ hp

-- hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1



end computations

end

noncomputable section

open Real Set

structure ScaledPowerFunction where
  σ : ℝ
  d : ℝ
  hd : d > 0
  hσ : (σ > 0) ∨ (σ < 0)

structure ToneCouple where
  ton : ℝ → ℝ
  inv : ℝ → ℝ
  mon : Bool
  ton_is_ton : if mon then StrictMonoOn ton (Ioi 0) else StrictAntiOn ton (Ioi 0)
  ran_ton : ∀ t ∈ Ioi (0 : ℝ), ton t ∈ Ioi 0
  ran_inv : ∀ t ∈ Ioi (0 : ℝ), inv t ∈ Ioi 0
  inv_pf : if mon
      then ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ s < inv t) ∧ (t < ton s ↔ inv t < s)
      else ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ inv t < s) ∧ (t < ton s ↔ s < inv t)

instance spf_to_tc (spf : ScaledPowerFunction) : ToneCouple where
  ton := fun s : ℝ ↦ (s / spf.d) ^ spf.σ
  inv := fun t : ℝ ↦ spf.d * t ^ spf.σ⁻¹
  mon := if (spf.σ > 0) then true else false
  ran_ton := fun t ht ↦ rpow_pos_of_pos (div_pos ht spf.hd) _
  ran_inv := fun t ht ↦ Real.mul_pos spf.hd (rpow_pos_of_pos ht spf.σ⁻¹)
  ton_is_ton := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte]
      intro s (hs : s > 0) t (ht : t > 0) hst
      refine (rpow_lt_rpow_iff ?_ ?_ sgn_σ).mpr ?_
      · apply le_of_lt (div_pos hs spf.hd)
      · apply le_of_lt (div_pos ht spf.hd)
      · exact div_lt_div_of_pos_right hst spf.hd
    · simp only [↓reduceIte]
      intro s (hs : s > 0) t (ht : t > 0) hst
      rcases spf.hσ with σ_pos | σ_neg
      · exact False.elim (sgn_σ σ_pos)
      · simp only
        refine (Real.rpow_lt_rpow_iff_of_neg (div_pos ht spf.hd)
            (div_pos hs spf.hd) σ_neg).mpr (div_lt_div_of_pos_right hst spf.hd)
  inv_pf := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte, mem_Ioi]
      intro s hs t ht
      constructor
      · rw [← Real.lt_rpow_inv_iff_of_pos
            (div_nonneg (le_of_lt hs) (le_of_lt spf.hd)) (le_of_lt ht) sgn_σ ]
        rw [← _root_.mul_lt_mul_left spf.hd]
        rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
      · rw [← Real.rpow_inv_lt_iff_of_pos (le_of_lt ht)
            (div_nonneg (le_of_lt hs) (le_of_lt spf.hd)) sgn_σ ]
        rw [← _root_.mul_lt_mul_left spf.hd]
        rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
    · simp only [↓reduceIte, mem_Ioi]
      intro s hs t ht
      rcases spf.hσ with σ_pos | σ_neg
      · contradiction
      · constructor
        · rw [← Real.rpow_inv_lt_iff_of_neg ht (div_pos hs spf.hd) σ_neg]
          rw [← _root_.mul_lt_mul_left spf.hd]
          rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]
        · rw [← Real.lt_rpow_inv_iff_of_neg (div_pos hs spf.hd) ht σ_neg]
          rw [← _root_.mul_lt_mul_left spf.hd]
          rw [mul_div_cancel₀ _ (ne_of_gt spf.hd)]

end

noncomputable section

open Real Set

variable {p₀ q₀ p₁ q₁ p q t : ℝ} (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
  (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
  (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)

/-- A particular choice of scaled power function needed in the real interpolation theorem
    when `q₀` and `q₁` are not equal to infinity -/
instance spfI : ScaledPowerFunction where
  σ := @σ p₀ q₀ p₁ q₁ t
  d := 1
  hd := zero_lt_one
  hσ := lt_or_gt_of_ne <| Ne.symm <| σ_ne_zero hp₀ hq₀ hp₁ hq₁ ht hp₀p₁ hq₀q₁ hp hq

-- (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :



end

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'}
  [NormedAddCommGroup E] [NormedSpace ℝ E] -- [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] -- [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] -- [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] -- [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)
  {f g : α → E} {t : ℝ} {s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}


namespace MeasureTheory

-- TODO: move this to a better place

lemma coe_pow_ne_top {a : ℝ} {q : ℝ} (hq : q ≥ 0): ENNReal.ofReal a ^ q ≠ ⊤ := by
  refine rpow_ne_top_of_nonneg hq coe_ne_top

-- Note this lemma can directly be applied to elements of `ℝ≥0` as well
lemma coe_pow_ne_top' {a : ℝ} {q : ℝ} (hq : q ≥ 1): ENNReal.ofReal a ^ q ≠ ⊤ := by
  exact coe_pow_ne_top (le_trans zero_le_one hq)

lemma coe_pow_pos {a : ℝ} {q : ℝ} (ha : a > 0) : ENNReal.ofReal a ^ q > 0 := by
  refine ENNReal.rpow_pos (ofReal_pos.mpr ha) coe_ne_top

-- TODO: could use easier definition of truncation

def trunc' (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

def trunc'' (f : α → E) (t : ℝ) :=
  {x | ¬ ‖f x‖ ≤ t}.indicator (fun x ↦ if 0 < t then (t * (max t ‖f x‖)⁻¹) • f x else 0)

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else
    if 0 < t then (t * ‖f x‖⁻¹) • f x else 0

def trnc (j : Bool) (f : α → E) (t : ℝ)  : α → E :=
  match j with
  | false => f - trunc f t
  | true => trunc f t

lemma trunc_buildup : trunc f t = trunc' f t + trunc'' f t := by
  ext x
  unfold trunc trunc' trunc''
  simp
  split <;> rename_i h₀
  · simp
    intro h
    have _ : ¬ t < ‖f x‖ := by exact not_lt.mpr h₀
    contradiction
  · have h₁ : max t ‖f x‖ = ‖f x‖ := by
      apply max_eq_right_of_lt
      exact lt_of_not_ge h₀
    unfold indicator
    simp
    split
    · rewrite [h₁]
      split <;> rename_i h₂
      · rfl
      · have _ : ‖f x‖ ≤ t := by exact le_of_not_lt h₂
        contradiction
    · exact Eq.symm (ite_self 0)

lemma stronglyMeasurable_inv (hf : StronglyMeasurable f) (ht : 0 < t):
    StronglyMeasurable (fun y ↦ (max t ‖f y‖)⁻¹):= by
  apply Continuous.comp_stronglyMeasurable (g := fun z ↦ (max t ‖z‖)⁻¹) (hf := hf)
  · apply Continuous.inv₀
    · apply Continuous.max
      · exact continuous_const
      · exact continuous_norm
    · intro z
      exact Ne.symm (ne_of_lt (lt_max_of_lt_left ht))

lemma aestronglyMeasurable_trunc' (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc' f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc' g t)
  constructor
  · apply MeasureTheory.StronglyMeasurable.indicator (s := {x | ‖g x‖ ≤ t})
    · exact wg1
    · apply StronglyMeasurable.measurableSet_le
      apply StronglyMeasurable.norm
      · exact wg1
      · exact stronglyMeasurable_const
  apply measure_mono_null ?_ wg2
  intro x
  contrapose
  simp
  intro h₂
  unfold trunc'
  rewrite [h₂]
  rfl

lemma aestronglyMeasurable_trunc'' (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc'' f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc'' g t)
  constructor
  · apply MeasureTheory.StronglyMeasurable.indicator
    · split <;> rename_i h₀
      · apply StronglyMeasurable.smul
        · apply StronglyMeasurable.mul
          · exact stronglyMeasurable_const
          · apply stronglyMeasurable_inv wg1 h₀
        · exact wg1
      · exact stronglyMeasurable_const
    · have h₂ : {x | ¬ ‖g x‖ ≤ t} = { x | t < ‖g x‖ } := by
        ext x
        exact not_le
      rewrite [h₂]
      apply StronglyMeasurable.measurableSet_lt
      · exact stronglyMeasurable_const
      · apply StronglyMeasurable.norm
        exact wg1

  apply measure_mono_null ?_ wg2
  intro x
  contrapose
  simp
  intro h₂
  unfold trunc''
  unfold indicator
  simp
  rewrite [h₂]
  rfl

lemma aestronglyMeasurable_trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := by
  rewrite [trunc_buildup]
  apply AEStronglyMeasurable.add
  · exact aestronglyMeasurable_trunc' hf
  · exact aestronglyMeasurable_trunc'' hf

lemma aestronglyMeasurable_trunc_compl (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (f - trunc f t) μ :=
  AEStronglyMeasurable.sub hf (aestronglyMeasurable_trunc hf)

/-- The norm of the truncation is monotone in the truncation parameter -/
lemma norm_trunc_mono :
  Monotone (fun s ↦ snorm (trunc f s) p μ) := sorry

/-- The norm of the complement of the truncation is antitone in the truncation parameter -/
lemma norm_trunc_compl_anti :
  Antitone (fun s ↦ snorm (f - trunc f s) p μ) := sorry

/-- The norm of the truncation is meaurable in the truncation parameter -/
@[measurability]
lemma norm_trunc_measurable :
    Measurable (fun s ↦ snorm (trunc f s) p μ) :=
  Monotone.measurable norm_trunc_mono

/-- The norm of the complement of the truncation is measurable in the truncation parameter -/
@[measurability]
lemma norm_trunc_compl_measurable :
    Measurable (fun s ↦ snorm (f - trunc f s) p μ) :=
  Antitone.measurable norm_trunc_compl_anti

-- TODO: change lhs and rhs?
-- TODO: rewrite the condition in filter form?
lemma lintegral_double_restrict_set {A B: Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := setLIntegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]

-- TODO: check which assumption is really needed on q
lemma weakℒp_interpolate_lower {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ico 1 p) {f : α → E₁}
    (hf : MemWℒp f p μ) (hμf : μ (Function.support f) < ⊤) :
    Memℒp f q μ := by
  let q' := q.toReal
  have coe_q : ENNReal.ofReal (q') = q := ofReal_toReal_eq_iff.mpr (LT.lt.ne_top hq.2)
  have one_le_q' : 1 ≤ q' := one_le_ofReal.mp (le_of_le_of_eq hq.1 (Eq.symm coe_q))
  have q'min_1 : 0 ≤ q' - 1 := by linarith
  have q'pos : q' > 0 := by linarith
  have obs_distr : distribution f 0 μ < ⊤ := by
    refine lt_of_eq_of_lt ?_ hμf; unfold distribution; apply congr_arg; unfold Function.support
    simp
  refine ⟨hf.1, ?_⟩
  rw [← coe_q]
  rw [snorm_pow_eq_distribution' (AEStronglyMeasurable.aemeasurable hf.1) q'pos]
  · refine (rpow_lt_top_iff_of_pos ?hy).mpr ?_
    · exact inv_pos_of_pos (lt_of_lt_of_le Real.zero_lt_one one_le_q')
    · refine mul_lt_top coe_ne_top ?_
      refine (ne_of_lt ?_)
      have est := hf.2
      unfold wnorm at est
      split_ifs at est with is_ptop
      · let M := (snormEssSup f μ).toReal
        have coe_M : ENNReal.ofReal M = (snormEssSup f μ) :=
            ofReal_toReal_eq_iff.mpr (ne_of_lt est)
        rw [lintegral_double_restrict_set (B := Ioo (0 : ℝ) (snormEssSup f μ).toReal)
            measurableSet_Ioi measurableSet_Ioo]
        · rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
          calc
          _ ≤ ∫⁻ (_ : ℝ) in Ioo 0 M,
              distribution f 0 μ * .ofReal (M ^ (q' - 1)) := by
            apply setLIntegral_mono' measurableSet_Ioo
            intro x hx
            apply mul_le_mul'
            · exact distribution_mono_right (zero_le _)
            · exact ofReal_le_ofReal <|
                  Real.rpow_le_rpow (le_of_lt hx.1) (le_of_lt hx.2) (by linarith)
          _ = distribution f 0 μ * .ofReal (M ^ (q' - 1)) * volume (Ioo 0 M) :=
            setLIntegral_const (Ioo 0 M) (distribution f 0 μ * ENNReal.ofReal (M ^ (q' - 1)))
          _ = distribution f 0 μ * .ofReal (M ^ (q' - 1)) * .ofReal M := by
            rw [@Real.volume_Ioo]; simp
          _ < _ := mul_lt_top (mul_ne_top (LT.lt.ne_top obs_distr) coe_ne_top) coe_ne_top
        · apply ae_of_all
          intro t ht; simp at ht
          have := ht.2 ht.1
          have : distribution f (ENNReal.ofReal t) μ ≤ distribution f (.ofReal M) μ := by
            apply distribution_mono_right'
            apply ofReal_le_ofReal (by linarith)
          have : distribution f (.ofReal M) μ = 0 := by
            rw [coe_M]; exact meas_snormEssSup_lt
          calc
          _ ≤ distribution f (.ofReal M) μ * ENNReal.ofReal (t ^ (q' - 1)) := by
            exact mul_le_mul_right' (distribution_mono_right' (ofReal_le_ofReal (by linarith))) _
          _ = 0 * ENNReal.ofReal (t ^ (q' - 1)) := by rw[coe_M, distribution_snormEssSup]
          _ = _ := by exact zero_mul _
      · let M := (wnorm' f p.toReal μ).toReal
        have coe_M : ENNReal.ofReal M = (wnorm' f p.toReal μ) :=
            ofReal_toReal_eq_iff.mpr (ne_of_lt est)
        let p' := p.toReal
        have coe_p : ENNReal.ofReal p' = p := by
          exact ofReal_toReal_eq_iff.mpr is_ptop
        have p_pos : p > 0 := lt_of_lt_of_le zero_lt_one hp
        have p'pos : p' > 0 := toReal_pos_iff.mpr ⟨p_pos, Ne.lt_top is_ptop⟩
        have one_le_p' : 1 ≤ p' := by refine one_le_ofReal.mp ?_; rw [coe_p]; exact hp
        have q'lt_p': q' < p' := toReal_strict_mono is_ptop hq.2
        have obs : ∀ t : ℝ,
            (.ofReal t) * distribution f (.ofReal t) μ ^ p'⁻¹ ≤ (ENNReal.ofReal M) := by
          intro t
          have coe_t : (.ofReal t) = (ofNNReal t.toNNReal) := rfl
          rw [coe_t, coe_M]
          exact le_iSup (fun t : ℝ≥0 ↦ ↑t * distribution f (↑t) μ ^ p'⁻¹) t.toNNReal
        have : ∀ t ∈ Ioi (0 : ℝ), distribution f (.ofReal t) μ ^ p'⁻¹ ≤
            (.ofReal t)⁻¹ * (ENNReal.ofReal M) := by
          intro t ht
          refine (ENNReal.mul_le_iff_le_inv ?hr₀ ?hr₁).mp (obs t)
          · exact ne_of_gt (ofReal_pos.mpr ht)
          · exact coe_ne_top
        have : ∀ t ∈ Ioi (0 : ℝ), distribution f (.ofReal t) μ ≤
            ((.ofReal t)⁻¹ * (ENNReal.ofReal M)) ^ p' := by
          intro t ht
          refine (ENNReal.rpow_one_div_le_iff ?hz).mp ?_
          · exact p'pos
          · rw [one_div]
            exact this t ht
        calc
        _ = ∫⁻ t : ℝ in Ioc 0 1 ∪ Ioi 1, distribution f (.ofReal t) μ *
            ENNReal.ofReal (t ^ (q' - 1)) := by
          rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt Real.zero_lt_one)]
        _ ≤ _ := lintegral_union_le _ (Ioc (0 : ℝ) (1 : ℝ)) (Ioi (1 : ℝ))
        _ < ⊤ := by
          refine add_lt_top.mpr ⟨?_, ?_⟩
          · calc
            _ ≤ _ := by
              apply setLIntegral_mono' measurableSet_Ioc
              intro t ht
              apply mul_le_mul' (distribution_mono_right (zero_le (.ofReal t)))
              apply ofReal_le_ofReal
              apply Real.rpow_le_rpow (le_of_lt ht.1) ht.2 q'min_1
            _ = distribution f 0 μ * ENNReal.ofReal (1 ^ (q' - 1)) * volume (Ioc (0 : ℝ) 1) :=
              setLIntegral_const (Ioc 0 1) (distribution f 0 μ * ENNReal.ofReal (1 ^ (q' - 1)))
            _ = distribution f 0 μ * ENNReal.ofReal (1 ^ (q' - 1)) := by
              rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
            _ < ⊤ := by
              apply mul_lt_top (ne_of_lt obs_distr) coe_ne_top
          · calc
            _ ≤ ∫⁻ t : ℝ in Ioi 1,
                ((ENNReal.ofReal t)⁻¹ * ENNReal.ofReal M) ^ p' * ENNReal.ofReal (t ^ (q' - 1))
                := by
              apply setLIntegral_mono' measurableSet_Ioi
              intro t ht
              apply mul_le_mul'
              · refine this t (lt_trans Real.zero_lt_one ht)
              · exact Preorder.le_refl (ENNReal.ofReal (t ^ (q' - 1)))
            _ = ∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal M ^ p' * ‖t ^ (-p' + q' - 1)‖₊ := by
              apply lintegral_congr_ae
              filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
              intro t ht
              have t_pos : t > 0 := lt_trans Real.zero_lt_one ht
              have h₀ : 0 ≤ t ^ (-p') := Real.rpow_nonneg (le_of_lt t_pos) (-p')
              rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt p'pos),
                  mul_comm _ (ENNReal.ofReal M ^ p')]
              rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, neg_one_mul,
                  ENNReal.ofReal_rpow_of_pos t_pos, mul_assoc, ← ofReal_mul h₀,
                  ← Real.rpow_add t_pos, add_sub]
              have tpp : t ^ (-p' + q' - 1) > 0 := Real.rpow_pos_of_pos t_pos (-p' + q' - 1)
              nth_rewrite 1 [← abs_of_pos tpp, ← Real.norm_eq_abs, ← norm_toNNReal]; rfl
            _ = ENNReal.ofReal M ^ p' * ∫⁻ t : ℝ in Ioi 1, ‖t ^ (-p' + q' - 1)‖₊ := by
              rw [← lintegral_const_mul']
              refine rpow_ne_top_of_nonneg (le_of_lt p'pos) coe_ne_top
            _ < ⊤ := by
              refine mul_lt_top ?_ ?_
              · exact LT.lt.ne_top (rpow_lt_top_of_nonneg
                    (le_of_lt (lt_of_lt_of_le Real.zero_lt_one one_le_p')) coe_ne_top)
              · have hpq : (-p' + q' - 1) < -1 := by linarith
                exact LT.lt.ne_top (integrableOn_Ioi_rpow_of_lt hpq Real.zero_lt_one).2

-- lemma computation_for_interpolation {t : ℝ} {M : ℝ} (ht : t ∈ Ioo 0 M) {p q : ℝ} (hpq : p < q) :
--     t ^ q < t ^ p * M⁻¹ ^ p * M ^ q := by
--   have t_pos := ht.1
--   have t_lt_M := ht.2
--   have M_pos := lt_trans t_pos t_lt_M
--   have Mq_pos : M ^ q > 0 := Real.rpow_pos_of_pos M_pos q
--   have key : (t * M⁻¹) ^ q < (t * M⁻¹) ^ p := by
--     refine (Real.rpow_lt_rpow_left_iff_of_base_lt_one ?_ ?_).mpr ?_
--     · refine Real.mul_pos t_pos ?_
--       refine inv_pos_of_pos (lt_trans t_pos t_lt_M)
--     · refine (mul_inv_lt_iff ?_).mpr ?_
--       · exact lt_trans t_pos t_lt_M
--       · rw [mul_one]; exact ht.2
--     · exact hpq
--   rw [← mul_one (t ^ q), ← inv_mul_cancel (a := M ^ q) (ne_of_gt Mq_pos), ← mul_assoc]
--   rw [← Real.mul_rpow (le_of_lt t_pos) (le_of_lt (inv_pos_of_pos M_pos))]
--   nth_rewrite 1 [← Real.rpow_neg_one]
--   rw  [← Real.rpow_mul (le_of_lt M_pos), mul_comm q,
--       Real.rpow_mul (le_of_lt M_pos), ← Real.mul_rpow (le_of_lt t_pos),
--       Real.rpow_neg_one]; swap
--   · rw [Real.rpow_neg_one]; exact le_of_lt (inv_pos_of_pos M_pos)
--   · refine mul_lt_mul_of_le_of_lt' ?_ ?_ ?_ Mq_pos
--     · exact key
--     · exact Preorder.le_refl (M ^ q)
--     · apply le_of_lt
--       apply Real.rpow_pos_of_pos
--       refine Real.mul_pos t_pos (inv_pos_of_pos M_pos)

-- TODO: the proof below has quite some duplication with the proof above
lemma weakℒp_interpolate_higher {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q ∈ Ioi p) {f : α → E₁}
    (hf : MemWℒp f p μ) (hfinf : snormEssSup f μ < ⊤) :
    Memℒp f q μ := by
  refine ⟨hf.1, ?_⟩
  rcases (eq_top_or_lt_top q) with q_eq_top | q_ne_top
  · rw [q_eq_top]
    simp; exact hfinf
  · let q' := q.toReal
    have coe_q : ENNReal.ofReal (q') = q := ofReal_toReal_eq_iff.mpr (LT.lt.ne_top q_ne_top)
    have p_lt_q : p < q := hq
    have p_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have q_pos : 0 < q := lt_trans p_pos p_lt_q
    have q'pos : 0 < q':= by
      apply toReal_pos_iff.mpr; exact ⟨q_pos, q_ne_top⟩
    have q'inv_pos : 0 < q'⁻¹ := inv_pos_of_pos q'pos
    rw [← coe_q]
    rw [snorm_pow_eq_distribution' (AEStronglyMeasurable.aemeasurable hf.1) q'pos]
    · apply rpow_lt_top_of_nonneg
      · exact le_of_lt q'inv_pos
      · refine ne_of_lt ?_
        have est := hf.2
        unfold wnorm at est
        let M := (snormEssSup f μ).toReal
        have M_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
        have coe_M : ENNReal.ofReal M = (snormEssSup f μ) :=
          ofReal_toReal_eq_iff.mpr (ne_of_lt hfinf)
        split_ifs at est with is_ptop
        · rw [is_ptop] at p_lt_q
          simp only [not_top_lt] at p_lt_q
        · rw [lintegral_double_restrict_set (B := Ioo (0 : ℝ) (M + 1)) measurableSet_Ioi
              measurableSet_Ioo]
          · rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
            let L := (wnorm' f p.toReal μ).toReal
            have L_nonneg : 0 ≤ L := toReal_nonneg
            have coe_L : ENNReal.ofReal L = (wnorm' f p.toReal μ) :=
                ofReal_toReal_eq_iff.mpr (ne_of_lt est)
            let p' := p.toReal
            have p'pos : p' > 0 := toReal_pos_iff.mpr ⟨p_pos, Ne.lt_top is_ptop⟩
            have q'lt_p': p' < q' := by
              refine toReal_strict_mono (LT.lt.ne_top q_ne_top) p_lt_q
            calc
            _ ≤ ENNReal.ofReal (q' * L ^ p') * ∫⁻ (t : ℝ) in Ioo 0 (M + 1),
                ‖t ^ (q' - p' - 1)‖₊ := by
              rw [ofReal_mul (le_of_lt q'pos)]
              rw [mul_assoc (ENNReal.ofReal q')]
              nth_rewrite 2 [← lintegral_const_mul']; swap; exact coe_ne_top
              apply mul_le_mul'
              · exact Preorder.le_refl (ENNReal.ofReal q')
              · apply setLIntegral_mono' measurableSet_Ioo
                intro t ht
                have t_pos := ht.1
                have : q' - 1 = p' + (q'- p' - 1) := by linarith
                rw [this, Real.rpow_add t_pos,
                    ofReal_mul (le_of_lt (Real.rpow_pos_of_pos t_pos p')), ← mul_assoc]
                apply mul_le_mul'
                · rw [← ENNReal.ofReal_rpow_of_nonneg L_nonneg (le_of_lt p'pos)]
                  rw [coe_L]
                  unfold wnorm'
                  have coe_t : (.ofReal t) = (ofNNReal t.toNNReal) := rfl
                  have tp_pos : 0 < t ^ p' := Real.rpow_pos_of_pos t_pos p'
                  refine (ENNReal.rpow_one_div_le_iff p'pos).mp ?_
                  rw [mul_comm, one_div,
                      ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (inv_pos_of_pos p'pos)),
                      ENNReal.ofReal_rpow_of_nonneg (le_of_lt tp_pos)
                        (le_of_lt (inv_pos_of_pos p'pos)),
                      Real.rpow_rpow_inv (le_of_lt t_pos) (ne_of_gt p'pos), coe_t]
                  refine le_iSup (fun t : ℝ≥0 ↦ ↑t * distribution f (↑t) μ ^ p'⁻¹) t.toNNReal
                · have tpp : t ^ (q' - p' - 1) > 0 := Real.rpow_pos_of_pos t_pos (q' - p' - 1)
                  rw [← norm_toNNReal, Real.norm_eq_abs, abs_of_pos tpp]
                  apply Preorder.le_refl
            _ < ⊤ := by
              apply mul_lt_top coe_ne_top
              have zero_lt_Mp1 : 0 < M + 1 := by linarith
              have hqp2 : -1 < q' - p' - 1 := by linarith
              exact LT.lt.ne_top
                  ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_Mp1).mpr hqp2).2
          · -- TODO do something with this code duplication from the other proof
            apply ae_of_all
            intro t ht; simp at ht
            have := ht.2 ht.1
            have : distribution f (ENNReal.ofReal t) μ ≤ distribution f (ENNReal.ofReal M) μ := by
              apply distribution_mono_right'
              apply ofReal_le_ofReal (by linarith)
            have : distribution f (ENNReal.ofReal M) μ = 0 := by
              rw [coe_M]; exact meas_snormEssSup_lt
            calc
            _ ≤ distribution f (ENNReal.ofReal M) μ * ENNReal.ofReal (t ^ (q' - 1)) := by
              exact mul_le_mul_right' (distribution_mono_right' (ofReal_le_ofReal (by linarith))) _
            _ = 0 * ENNReal.ofReal (t ^ (q' - 1)) := by rw[coe_M, distribution_snormEssSup]
            _ = _ := by exact zero_mul _

lemma computation_smul_norms {t : ℝ} {f : α → E} (x : α) (hfx : ‖f x‖ > 0) :
    ‖(t * ‖f x‖⁻¹) • f x‖ = |t| := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hfx), mul_assoc,
      inv_mul_cancel (ne_of_gt hfx), mul_one]

lemma trunc_bdd {f : α → E₁} {a : ℝ} (x : α) : ‖trunc f a x‖ ≤ |a| := by
  unfold trunc
  split_ifs with h
  · refine le_trans h (le_abs_self a)
  · simp at h
    rw [computation_smul_norms]; linarith
  · simp

/-- A small lemma that is helpful for rewriting -/
lemma coe_coe_eq_ofReal (a : ℝ) : ofNNReal a.toNNReal = ENNReal.ofReal a := by rfl

lemma trunc_snormEssSup_le {f : α → E₁} {a : ℝ} : snormEssSup (trunc f a) μ ≤
    ENNReal.ofReal |a| := by
  apply essSup_le_of_ae_le
  apply ae_of_all
  intro x
  simp only [← norm_toNNReal, coe_coe_eq_ofReal]
  exact  ofReal_le_ofReal <| trunc_bdd x

lemma trunc_preserves_Lp {p : ℝ≥0∞} {a : ℝ} (hf : Memℒp f p μ) :
    Memℒp (trunc f a) p μ := by
  refine ⟨aestronglyMeasurable_trunc hf.1, ?_⟩
  refine lt_of_le_of_lt ?_ hf.2
  apply snorm_mono_ae
  apply ae_of_all
  intro x
  unfold trunc
  split_ifs with is_fx_le_a is_a_pos
  · exact le_refl _
  · have fx_t_0 : ‖f x‖ > 0 := by linarith
    rw [computation_smul_norms]; swap; exact fx_t_0
    rw [abs_of_pos is_a_pos]; simp at is_fx_le_a; linarith
  · simp

lemma trunc_compl_preserves_Lp {p : ℝ≥0∞} {a : ℝ} (hf : Memℒp f p μ) :
    Memℒp (f - trunc f a) p μ := by
  have truncLp : Memℒp (trunc f a) p μ := trunc_preserves_Lp hf
  apply Memℒp.sub hf truncLp

lemma trunc_Lp_MemLq_higher {p q : ℝ≥0∞} (hp : p ≥ 1) (hq : q > p) {f : α → E₁}
    (hf : Memℒp f p μ) (a : ℝ) : Memℒp (trunc f a) q μ := by
  have : MemWℒp f p μ := by
    apply Memℒp.memWℒp hp hf
  apply weakℒp_interpolate_higher hp hq
  · apply Memℒp.memWℒp hp
    apply trunc_preserves_Lp hf
  · have coe_a_lt_top : ENNReal.ofReal |a| < ⊤ := coe_lt_top
    refine lt_of_le_of_lt ?_ coe_a_lt_top
    apply trunc_snormEssSup_le

lemma distribution_finite_for_finite_snorm {f : α → E₁} {p : ℝ} (hp : 0 < p)
    (hf : AEMeasurable f μ) (f_fin : snorm' f  p μ < ⊤) {t : ℝ} (ht : t > 0) :
    distribution f (.ofReal t) μ < ⊤ := by
  unfold snorm' at f_fin
  have obs : ∫⁻ (a : α), ↑‖f a‖₊ ^ p ∂μ < ⊤ := by
    exact lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hp f_fin
  rw [lintegral_norm_pow_eq_distribution' hf hp] at obs
  have p_ne_0 : ENNReal.ofReal p ≠ 0 := (ne_of_gt (ofReal_pos.mpr hp))
  have : ∫⁻ (t : ℝ) in Ioi 0,
      distribution f (ENNReal.ofReal t) μ * ENNReal.ofReal (t ^ (p - 1)) < ⊤ := by
    contrapose obs
    simp
    simp at obs
    rw [obs]
    exact mul_top p_ne_0
  have : volume {t : ℝ | t ∈ Ioi 0 ∧ distribution f (ENNReal.ofReal t) μ *
      ENNReal.ofReal (t ^ (p - 1)) = ⊤} = 0 := by
    apply measure_eq_top_of_setLintegral_ne_top
    · -- TODO: extract as lemma
      apply Measurable.aemeasurable
      apply Measurable.mul
      · apply distribution_measurable_from_real
      · refine Measurable.ennreal_ofReal ?_
        exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) (p - 1)
    · exact LT.lt.ne_top this
  contrapose this
  have ttop : (distribution f (ENNReal.ofReal t) μ = ⊤) := by
    exact not_lt_top.mp this
  apply ne_of_gt
  calc
  0 < ENNReal.ofReal t := ofReal_pos.mpr ht
  _ = ENNReal.ofReal (t - 0) := by rw [sub_zero]
  _ = volume (Ioo 0 t) := by exact Eq.symm Real.volume_Ioo
  _ ≤ _ := by
    apply measure_mono
    intro s hs
    refine ⟨hs.1, ?_⟩
    have dbtop : distribution f (ENNReal.ofReal s) μ = ⊤ := by
      apply eq_top_iff.mpr
      refine le_of_eq_of_le (Eq.symm ttop) ?_
      apply distribution_mono_right
      apply ofReal_le_ofReal
      exact (le_of_lt hs.2)
    rw [dbtop]
    apply top_mul
    apply ne_of_gt
    refine ofReal_pos.mpr ?_
    exact Real.rpow_pos_of_pos hs.1 (p - 1)

lemma distribution_shift_trunc (t : ℝ) (s : ℝ≥0∞) :
    distribution (f - (trunc f t)) s μ = distribution f (s + t.toNNReal) μ := by
  -- TODO: clean up
  unfold distribution trunc
  split <;> rename_i h₀
  · have h₁ :
        {x | s < ↑‖(f - fun x ↦ if ‖f x‖ ≤ t then f x else (t * ‖f x‖⁻¹) • f x) x‖₊}
        = {x | (t.toNNReal + s) < ↑‖f x‖₊} := by
      ext x
      simp
      split <;> rename_i h₂
      · simp
        calc
        ‖f x‖₊ ≤ ofNNReal t.toNNReal := by
          refine ENNReal.coe_le_coe.mpr (le_toNNReal_of_coe_le h₂)
        _      ≤ t.toNNReal + s := le_self_add
      · rcases (eq_or_ne s ⊤) with s_eq_top | s_ne_top
        · constructor
          · intro h
            have h₃ : ofNNReal ↑‖f x - (t * ‖f x‖⁻¹) • f x‖₊ < ⊤ := by
              exact coe_lt_top
            have h₄ : s < ⊤ := gt_trans h₃ h
            have _ : ¬ (s < ⊤) := by exact not_lt_top.mpr s_eq_top
            contradiction
          · intro h
            have h₅ : s < ⊤ := by exact gt_trans coe_lt_top (lt_of_le_of_lt le_add_self h)
            have _ : ¬ (s < ⊤) := by exact not_lt_top.mpr s_eq_top
            contradiction
        · rewrite [Iff.symm (toNNReal_lt_toNNReal s_ne_top coe_ne_top)]
          have h_sum_ne_top : ofNNReal t.toNNReal + s ≠ ⊤ :=
            add_ne_top.mpr (ite_ne_left_iff.mp (id (Ne.symm s_ne_top)))
          rewrite [Iff.symm (toNNReal_lt_toNNReal h_sum_ne_top coe_ne_top)]
          change (s.toNNReal.toReal < ‖f x - (t * ‖f x‖⁻¹) • f x‖ ↔
              (↑t.toNNReal + s).toNNReal.toReal < ‖f x‖)
          nth_rewrite 1 [← MulAction.one_smul (α := ℝ) (f x)]
          rewrite [← (sub_smul), norm_smul]
          have h₄ : ‖f x‖⁻¹ < t⁻¹ := inv_lt_inv_of_lt h₀ (lt_of_not_ge h₂)
          have h₅ : t * ‖f x‖⁻¹ < t * t⁻¹ := (_root_.mul_lt_mul_left h₀).mpr h₄
          rewrite [((mul_inv_eq_one₀ (Ne.symm (ne_of_lt h₀))).mpr rfl)] at h₅
          have h₆ : 1 - t * ‖f x‖⁻¹ > 0 := sub_pos.mpr h₅
          rewrite [Real.norm_of_nonneg (le_of_lt h₆)]
          have h₁₁ : (1 - t * ‖f x‖⁻¹)*‖f x‖ = ‖f x‖ - t * (‖f x‖*‖f x‖⁻¹) := by linarith
          have h₁₂ : ‖f x‖*‖f x‖⁻¹ = 1 := by
            apply mul_inv_cancel
            linarith
          rewrite [h₁₂] at h₁₁
          rewrite [h₁₁]
          simp
          rewrite [toNNReal_add coe_ne_top s_ne_top]
          simp
          rewrite [max_eq_left_of_lt h₀]
          constructor
          · intro h
            linarith
          · intro h
            linarith
    rewrite [h₁]
    rw [add_comm]
  · have h₂ : (fun x ↦ if ‖f x‖ ≤ t then f x else 0) = (fun x ↦ 0) := by
      ext x
      split
      · have _ : ‖f x‖ ≥ 0 := norm_nonneg (f x)
        have h₃ : ‖f x‖ = 0 := by linarith
        exact norm_eq_zero.mp h₃
      · rfl
    rw [h₂]
    simp
    rw [Real.toNNReal_of_nonpos (le_of_not_lt h₀)]
    simp

lemma trunc_compl_Lp_Lq_lower {p q : ℝ≥0∞} (hp : p ∈ Ico 1 ⊤) (hq : q ∈ Ico 1 p) {f : α → E₁}
    (hf : Memℒp f p μ) {a : ℝ} (ha : a > 0) : Memℒp (f - trunc f a) q μ := by
  apply weakℒp_interpolate_lower hp.1 hq
  · apply Memℒp.memWℒp hp.1
    apply trunc_compl_preserves_Lp hf
  · unfold Function.support
    have key : distribution (f - trunc f a) 0 μ < ⊤ := by
      rw [distribution_shift_trunc]
      rw [coe_coe_eq_ofReal]
      rw [← ofReal_zero]
      rw [← ofReal_add]
      · have p_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp.1
        let p' := p.toReal
        have coe_p : ENNReal.ofReal p' = p := by
          refine ofReal_toReal_eq_iff.mpr ?_
          apply LT.lt.ne_top
          exact hp.2
        have p'pos : 0 < p' := by
          apply toReal_pos_iff.mpr
          exact ⟨p_pos, hp.2⟩
        apply distribution_finite_for_finite_snorm p'pos
        · exact (AEStronglyMeasurable.aemeasurable hf.1)
        · have est := hf.2
          unfold snorm at est
          split_ifs at est with is_p_0 is_p_top
          · exact False.elim <| ne_of_gt p_pos is_p_0
          · exact False.elim <| ofReal_toReal_eq_iff.mp coe_p is_p_top
          · exact est
        · linarith
      · exact Preorder.le_refl 0
      · exact (le_of_lt ha)
    refine lt_of_eq_of_lt ?_ key; apply congr_arg; ext x; simp

lemma distribution_trunc (t : ℝ) :
    distribution (trunc f t) s μ =
    if s < ENNReal.ofReal t then distribution f s μ else 0 := by
  have simp_norm : ∀ x, t > 0 → ¬ ‖f x‖ ≤  t → ‖(t * ‖f x‖⁻¹) • f x‖.toNNReal = t.toNNReal := by
    intro x t_pos ne_norm_le_t
    have norm_pos := (lt_trans t_pos (not_le.mp ne_norm_le_t))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (le_of_lt t_pos) (le_of_lt (inv_pos_of_pos norm_pos))),
        mul_assoc, mul_comm ‖f x‖⁻¹, mul_inv_cancel (ne_of_gt norm_pos), mul_one]
  split <;> rename_i h₀
  · apply congrArg μ
    ext x
    simp
    unfold trunc
    rw [← norm_toNNReal, ← norm_toNNReal]
    split <;> rename_i h₁
    · rfl
    · split <;> rename_i h₂
      · have coe_t_lt_norm : ENNReal.ofReal t < ENNReal.ofReal ‖f x‖ :=
          (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₂)).mpr (not_le.mp h₁)
        rw [simp_norm x h₂ h₁]
        exact { mp := fun _ ↦ lt_trans h₀ coe_t_lt_norm, mpr := fun _ ↦ h₀ }
      · rw [norm_zero, Real.toNNReal_zero, ENNReal.coe_zero]
        exact
          { mp := fun h ↦ False.elim (not_lt_zero h),
            mpr := False.elim
              (not_lt_zero (lt_of_lt_of_le h₀ (ofReal_le_of_le_toReal (not_lt.mp h₂)))) }
  · unfold distribution trunc
    refine measure_mono_null ?_ (OuterMeasureClass.measure_empty μ)
    intro x
    simp
    rw [← norm_toNNReal]
    split <;> rename_i h₁
    · exact le_trans (ofReal_le_ofReal h₁) (not_lt.mp h₀)
    · split <;> rename_i h₂
      · rw [simp_norm x h₂ h₁]
        exact not_lt.mp h₀
      · rw [norm_zero, Real.toNNReal_zero, ENNReal.coe_zero]
        exact zero_le s

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (MeasureTheory.trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

def Subadditive (T : (α → E₁) → α' → E₂) : Prop :=
  ∃ A > 0, ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

def Subadditive' (T : (α → E₁) → α' → E₂) (A : ℝ) : Prop :=
  ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

def Sublinear (T : (α → E₁) → α' → E₂) : Prop :=
  Subadditive T ∧ ∀ (f : α → E₁) (c : ℝ), T (c • f) = c • T f

/-- Proposition that expresses that the map `T` map between function spaces preserves
    AE strong measurability on L^p. -/
def PreservesAEStrongMeasurability (T : (α → E₁) → α' → E₂) (p : ℝ≥0∞) : Prop :=
    ∀ (f : α → E₁), Memℒp f p μ → AEStronglyMeasurable (T f) ν

/-- A collection of small lemmas to help with integral manipulations -/

lemma measure_preserving_shift {a : ℝ} :
    MeasurePreserving (fun x ↦ a + x) volume volume := by
  exact measurePreserving_add_left volume a

lemma measureable_embedding_shift {a : ℝ} :
    MeasurableEmbedding (fun x ↦ a + x) := by
  exact measurableEmbedding_addLeft a

lemma measure_preserving_scaling {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun x ↦ a * x) volume ((ENNReal.ofReal |a⁻¹|) • volume) := by
  refine { measurable := ?measurable, map_eq := ?map_eq }
  · exact measurable_const_mul a
  · exact Real.map_volume_mul_left ha

lemma lintegral_shift (f : ℝ → ENNReal) {a : ℝ} :
    ∫⁻ x : ℝ, (f (x + a)) = ∫⁻ x : ℝ, f x :=
  by exact lintegral_add_right_eq_self f a

lemma lintegral_shift' (f : ℝ → ENNReal) {a : ℝ} {s : Set ℝ}:
    ∫⁻ (x : ℝ) in (fun z : ℝ ↦ z + a)⁻¹' s, f (x + a) = ∫⁻ (x : ℝ) in s, f x := by
  rw [MeasurePreserving.setLIntegral_comp_preimage_emb
      (measurePreserving_add_right volume a) (measurableEmbedding_addRight a)]

lemma lintegral_add_right_Ioi (f : ℝ → ENNReal) {a b : ℝ} :
    ∫⁻ (x : ℝ) in Ioi (b - a), f (x + a) = ∫⁻ (x : ℝ) in Ioi b, f x := by
  nth_rewrite 2 [← lintegral_shift' (a := a)]
  simp

lemma lintegral_scale_constant (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0):
    ∫⁻ x : ℝ, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x := by
  rw [← @lintegral_smul_measure]
  rw [MeasurePreserving.lintegral_comp_emb]
  · exact measure_preserving_scaling h
  · exact measurableEmbedding_mulLeft₀ h

lemma lintegral_scale_constant_preimage (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0)
    {s : Set ℝ}:
    ∫⁻ x : ℝ in (fun z : ℝ ↦ a * z)⁻¹' s, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in s, f x := by
  rw [← @lintegral_smul_measure]
  -- TODO: note that the function below has been renamed recently
  rw [MeasurePreserving.setLIntegral_comp_preimage_emb (measure_preserving_scaling h)
      (measurableEmbedding_mulLeft₀ h)]
  rw [@Measure.restrict_smul]

lemma lintegral_scale_constant_halfspace (f: ℝ → ENNReal) {a : ℝ} (h : 0 < a) :
    ∫⁻ x : ℝ in Ioi 0, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [← lintegral_scale_constant_preimage f (Ne.symm (ne_of_lt h))]
  have h₀ : (fun z ↦ a * z) ⁻¹' Ioi 0 = Ioi 0 := by
    unfold preimage
    ext x
    simp
    constructor
    · intro h₁
      exact (pos_iff_pos_of_mul_pos h₁).mp h
    · intro h₁
      exact Real.mul_pos h h₁
  rw [h₀]

lemma lintegral_scale_constant_halfspace' {f: ℝ → ENNReal} {a : ℝ} (h : 0 < a) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ in Ioi 0, f (a*x) = ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [lintegral_scale_constant_halfspace f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a),
      @abs_inv, mul_inv_cancel (abs_ne_zero.mpr (Ne.symm (ne_of_lt h)))]
  simp

lemma lintegral_scale_constant' {f: ℝ → ENNReal} {a : ℝ} (h : a ≠ 0):
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a), @abs_inv,
      mul_inv_cancel (abs_ne_zero.mpr h)]
  simp


/-- Estimate the strong norm of the complement of the truncation by an integral involving
  the distribution function-/

lemma estimate_snorm_trunc_compl_ {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (hf : AEStronglyMeasurable f μ) {a : ℝ}
    (ha : 0 ≤ a) :
  snorm (f - trunc f a) (ENNReal.ofReal p₀) μ =
  (∫⁻ s : ℝ in Ioi (a : ℝ), ENNReal.ofReal p₀ * ENNReal.ofReal ((s - a) ^ (p₀ - 1)) *
    distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
  rewrite [← lintegral_add_right_Ioi (a := a), sub_self]
  simp only [add_sub_cancel_right]
  rw [snorm_pow_eq_distribution']
  rw [← lintegral_const_mul']
  refine congrFun (congrArg ?_ ?_) p₀⁻¹
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro t ht
    rw [distribution_shift_trunc]
    rw [mul_comm _ (ENNReal.ofReal (t ^ (p₀ - 1))), ← mul_assoc]
    congr
    · rw [ofReal_add]
      · rw [coe_coe_eq_ofReal]
      · exact (le_of_lt ht)
      · exact ha
  · exact coe_ne_top
  · apply AEStronglyMeasurable.aemeasurable
    apply aestronglyMeasurable_trunc_compl hf
  · linarith

lemma estimate_snorm_trunc_compl {p₀ : ℝ} {a : ℝ}
    (hp₀ : 1 ≤ p₀) (hf : AEStronglyMeasurable f μ) (ha : 0 ≤ a) :
    snorm (f - trunc f a) (ENNReal.ofReal p₀) μ ≤
    (∫⁻ s : ℝ in Ioi a, ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
    distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
  rw [estimate_snorm_trunc_compl_ hp₀ hf ha]
  refine (ENNReal.rpow_one_div_le_iff (inv_pos_of_pos (by linarith))).mp ?_
  simp
  rw [ENNReal.rpow_inv_rpow (by linarith)]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t t_gt_a
  rw [mem_Ioi] at t_gt_a
  refine mul_le_mul_three (le_of_eq rfl) ?_ (le_of_eq rfl)
  rw [ofReal_rpow_of_pos (lt_of_le_of_lt ha t_gt_a)]
  apply ofReal_le_ofReal_iff'.mpr; left; apply Real.rpow_le_rpow <;> linarith

lemma estimate_distribution_subadditive {f : α → E₁} {t : ℝ}
    (ht : t > 0) {a : ℝ} {A : ℝ} (hA : A > 0) (h : Subadditive' T A) :
    distribution (T f) (ENNReal.ofReal ((2 : ℝ) * t)) ν ≤
    distribution (T (trunc f a)) (ENNReal.ofReal (t / A)) ν +
    distribution (T (f - trunc f a)) (ENNReal.ofReal (t / A)) ν := by
  rw [ofReal_div_of_pos hA, ← Real.ennnorm_eq_ofReal (le_of_lt hA)]
  rw [← distribution_smul_left (ne_of_gt hA), ← distribution_smul_left (ne_of_gt hA)]
  have : ENNReal.ofReal (2 * t) = ENNReal.ofReal t + ENNReal.ofReal t := by
    rw [← ofReal_add, two_mul] <;> try positivity
  rewrite [this]
  apply distribution_add_le'
  apply ae_of_all
  intro x
  rw [@Pi.smul_apply, @Pi.smul_apply, norm_smul, norm_smul, ← mul_add]
  simp [abs_of_pos hA]
  nth_rewrite 1 [← add_sub_cancel (trunc f a) f]
  apply h

lemma estimate_distribution_subadditive' {f : α → E₁} {t : ℝ}
    (ht : t > 0) (a : ℝ) {A : ℝ} (hA : A > 0) (h : Subadditive' T A) :
    distribution (T f) (ENNReal.ofReal (2 * A * t)) ν ≤
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν +
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν := by
  rw [mul_assoc]
  nth_rewrite 2 [← one_mul t]
  nth_rewrite 3 [← one_mul t]
  rw [← inv_mul_cancel (ne_of_gt hA)]
  rw [mul_rotate]
  rw [← div_eq_mul_inv]
  apply estimate_distribution_subadditive
  · exact Real.mul_pos hA ht
  · exact hA
  · exact h

lemma _rewrite_norm_func {q : ℝ} {g : α' → E} (hq : 1 ≤ q) {A : ℝ} (hA : A > 0)
    (hg : AEMeasurable g ν):
    ∫⁻ x, ‖g x‖₊ ^q ∂ν =
    ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s in Ioi (0 : ℝ),
    distribution g ((ENNReal.ofReal (2 * A * s)))  ν * (ENNReal.ofReal (s^(q - 1))) := by
  rewrite [lintegral_norm_pow_eq_distribution' hg (by linarith)]
  · nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := (2*A)) (by linarith)]
    have h₄ : ENNReal.ofReal |2 * A| ≠ ⊤ := coe_ne_top
    have h₅ : ENNReal.ofReal ((2 * A)^q * q) ≠ ⊤ := coe_ne_top
    have h₆ : ENNReal.ofReal q ≠ ⊤ := coe_ne_top
    rewrite [← lintegral_const_mul' (hr := h₄), ← lintegral_const_mul' (hr := h₅),
        ← lintegral_const_mul' (hr := h₆)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro t zero_lt_t
    rw [Real.mul_rpow]
    · rw [ofReal_mul' (q := t ^ (q - 1))]
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      rw [ofReal_mul' (q := t)]
      · rw [mul_assoc _ _ (ENNReal.ofReal ((2 * A) ^ (q - 1)))]
        rw [mul_comm _ (ENNReal.ofReal ((2 * A) ^ (q - 1)))]
        rw [← mul_assoc]
        refine congrFun (congrArg ?_ ?_) ?_
        rw [abs_of_nonneg (by linarith), ← ofReal_mul (by linarith), ← ofReal_mul]; swap;
            refine Left.mul_nonneg ?_ ?_ <;> linarith
        apply congr_arg
        rw [mul_assoc]
        nth_rewrite 1 [← Real.rpow_one (2 * A), ← Real.rpow_add (by linarith), add_sub_cancel,
            mul_comm]; rfl
      · exact (le_of_lt zero_lt_t)
      · exact Real.rpow_nonneg (le_of_lt zero_lt_t) (q - 1)
    · linarith
    · exact (le_of_lt zero_lt_t)

-- lemma _rewrite_norm_func' {q : ℝ} {f : α → E₁} (hq : 1 ≤ q) (a : ℝ) {A : ℝ} (hA : A > 0)
--     (hT : Subadditive' T hA) :
--     ∫⁻ s in Ioi (0 : ℝ),
--     distribution (T f) ((ENNReal.ofReal (2 * A * s)))  ν * (ENNReal.ofReal (s^(q - 1))) ≤
--     (∫⁻ s in Ioi (0 : ℝ),
--     distribution (T (trunc f a)) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1))) +
--     ∫⁻ s in Ioi (0 : ℝ),
--     distribution (T (f - trunc f a)) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) := by
--   rw [← lintegral_add_left]
--   · rw [← funext fun _ ↦ add_mul _ _ _]
--     apply setLIntegral_mono' measurableSet_Ioi
--     intro s s_pos
--     apply mul_le_mul'
--     · apply estimate_distribution_subadditive' hq s_pos a hA hT
--     · exact Preorder.le_refl _
--   · apply Measurable.mul
--     · apply distribution_measurable_from_real
--     · exact Measurable.ennreal_ofReal <| Measurable.pow_const (fun ⦃t⦄ a ↦ a) (q - 1)

lemma weaktype_estimate {C₀ : ℝ} {p : ℝ} {q : ℝ} (hq : 1 ≤ q)
  {f : α → E₁} (hf : Memℒp f (ENNReal.ofReal p) μ)
    (h₀T : HasWeakType T (ENNReal.ofReal p) (ENNReal.ofReal q) μ ν C₀.toNNReal) {t : ℝ} (ht : t > 0) :
    distribution (T f) (ENNReal.ofReal t) ν ≤ ENNReal.ofReal C₀ ^ q *
        snorm f (ENNReal.ofReal p) μ ^ q * ENNReal.ofReal (t ^ (-q)) := by
  -- rw [mul_comm (ofNNReal C₀)]
  have wt_est := (h₀T f hf).2 -- the weaktype estimate
  -- have one_le_q : q.toReal ≥ 1 := by exact hq
  have q_pos : q > 0 := by linarith
  have q_nonneg := le_of_lt q_pos
  have tq_pos : ENNReal.ofReal t ^ q > 0 := coe_pow_pos ht -- rpow_pos_of_nonneg (ofReal_pos.mpr ht) q_nonneg
  have tq_ne_top : (ENNReal.ofReal t) ^ q ≠ ⊤ := coe_pow_ne_top' hq
  have hq₁ : (ENNReal.ofReal q).toReal = q := by exact toReal_ofReal q_nonneg
  unfold wnorm wnorm' at wt_est; simp at wt_est
  have wt_est_t := wt_est t.toNNReal -- this is the weaktype estimate applied to t
  rw [← ENNReal.mul_le_mul_right (c := (ENNReal.ofReal t) ^ q) _ tq_ne_top,
      ofReal_rpow_of_pos, mul_assoc _ _ (ENNReal.ofReal (t ^ q)), ← ofReal_mul',
      ← Real.rpow_add, neg_add_self, Real.rpow_zero, ofReal_one, mul_one, mul_comm,
      ← ENNReal.mul_rpow_of_nonneg _ _ q_nonneg] <;> try positivity
  refine (ENNReal.rpow_one_div_le_iff q_pos).mp ?_
  rw [ENNReal.mul_rpow_of_nonneg, one_div, ENNReal.ofReal_rpow_of_pos,
      Real.rpow_rpow_inv] <;> try positivity
  rw [← coe_coe_eq_ofReal]
  rw [hq₁] at wt_est_t
  exact wt_est_t

-- TODO: this may need to be generalized to the cases where the exponents equal ⊤
lemma weaktype_estimate_trunc_compl {C₀ : ℝ} {p p₀: ℝ} (hp₀ : 1 ≤ p₀) {q₀ : ℝ} (hq₀ : 1 ≤ q₀) (hp₀p : p₀ < p)
  {f : α → E₁} (hf : Memℒp f (ENNReal.ofReal p) μ)
    (h₀T : HasWeakType T (ENNReal.ofReal p₀) (ENNReal.ofReal q₀) μ ν C₀.toNNReal) {t : ℝ} (ht : t > 0) {a : ℝ} (ha : a > 0):
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν ≤ ENNReal.ofReal C₀ ^ q₀ *
        snorm (f - trunc f a) (ENNReal.ofReal p₀) μ ^ q₀ * (ENNReal.ofReal (t ^ (-q₀))) := by
  apply weaktype_estimate hq₀
  · apply trunc_compl_Lp_Lq_lower (p := (ENNReal.ofReal p))
    · refine ⟨?_, coe_lt_top⟩
      rw [← ENNReal.ofReal_one]
      apply ofReal_le_ofReal
      linarith
    · refine ⟨?_, ?_⟩
      · rw [← ENNReal.ofReal_one]
        apply ofReal_le_ofReal
        exact hp₀
      · refine (ofReal_lt_ofReal_iff ?_).mpr hp₀p
        linarith
    · exact hf
    · exact ha
  · exact h₀T
  · exact ht

lemma weaktype_estimate_trunc {C₁ : ℝ} {p p₁: ℝ} (hp : 1 ≤ p) {q₁ : ℝ} (hq₁ : 1 ≤ q₁) (hp₁p : p < p₁)
  {f : α → E₁} (hf : Memℒp f (ENNReal.ofReal p) μ)
    (h₁T : HasWeakType T (ENNReal.ofReal p₁) (ENNReal.ofReal q₁) μ ν C₁.toNNReal) {t : ℝ} (ht : t > 0) {a : ℝ} :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν ≤ ENNReal.ofReal C₁ ^ q₁ *
        snorm (trunc f a) (ENNReal.ofReal p₁) μ ^ q₁ * ENNReal.ofReal (t ^ (-q₁)) := by
  apply weaktype_estimate hq₁
  · apply trunc_Lp_MemLq_higher (p := (ENNReal.ofReal p))
    · rw [← ENNReal.ofReal_one]; exact ofReal_le_ofReal hp
    · refine (ofReal_lt_ofReal_iff ?hf.hq.h).mpr hp₁p
      linarith
    · exact hf
  · exact h₁T
  · exact ht

lemma _estimate_norm_rpow_range_operator {q : ℝ} {f : α → E₁} (hq : 1 ≤ q) (tc : ToneCouple) {A : ℝ} (hA : A > 0)
    (ht : Subadditive' T A) (hTf : AEMeasurable (T f) ν) :
  ∫⁻ x : α', ‖T f x‖₊ ^ q ∂ν ≤
  ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) +
  distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) := by
  rw [_rewrite_norm_func hq hA hTf]
  apply mul_le_mul'
  · exact le_refl _
  · apply setLIntegral_mono' measurableSet_Ioi
    intro s s_pos
    rw [← add_mul]
    apply mul_le_mul'
    · apply estimate_distribution_subadditive' s_pos (tc.ton s) hA ht
    · exact le_refl _

-- TODO : move this up front
-- local instance : Coe ℝ ℝ≥0∞ where
--   coe x := ENNReal.ofReal x

set_option maxHeartbeats 600000



-- local convenience function
lemma lintegral_rw_aux {g : ℝ → ℝ≥0∞} {f₁ f₂ : ℝ → ℝ≥0∞} {A : Set ℝ}
    (heq : f₁ =ᶠ[ae (volume.restrict A)] f₂) :
  (∫⁻ s in A, g s * f₁ s) =
  (∫⁻ s in A, g s * f₂ s) := by
  refine (lintegral_rw₂ ?_ ?_ HMul.hMul)
  · exact Filter.EventuallyEq.refl (ae (volume.restrict A)) g
  · exact heq

lemma power_aux {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ (p + q)) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal s ^ p * ENNReal.ofReal s ^ q ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  rw [ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs]
  rw [← ofReal_mul (by positivity)]
  rw [← Real.rpow_add hs]

lemma power_aux_2 {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal (s ^ (p + q))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p) * ENNReal.ofReal (s ^ q) ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  rw [← ofReal_mul (by positivity)]
  rw [← Real.rpow_add hs]

lemma ofReal_rpow_of_pos_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  exact ofReal_rpow_of_pos hs

#check ENNReal.rpow_mul

lemma ofReal_rpow_rpow_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro s (hs : s > 0)
  exact ofReal_rpow_of_pos hs
-- TODO: rename
lemma estimate_norm_rpow_range_operator {C₁ : ℝ} {p p₁: ℝ} (hp : 1 ≤ p) {q₁ : ℝ} (hq₁ : 1 ≤ q₁) (hp₁p : p < p₁) {q : ℝ} {C₀ : ℝ} {p₀: ℝ} (hp₀ : 1 ≤ p₀) {q₀ : ℝ} (hq₀ : 1 ≤ q₀) (hp₀p : p₀ < p) {f : α → E₁} (tc : ToneCouple)
    (hf : Memℒp f (ENNReal.ofReal p) μ)
    (hT₁ : HasWeakType T (ENNReal.ofReal p₁) (ENNReal.ofReal q₁) μ ν C₁.toNNReal) (hT₀ : HasWeakType T (ENNReal.ofReal p₀) (ENNReal.ofReal q₀) μ ν C₀.toNNReal):
    ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) +
    distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) ≤
    ENNReal.ofReal C₁ ^ q₁ * (∫⁻ s in Ioi (0 : ℝ),
        snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ ^ q₁ * ENNReal.ofReal (s ^ (q - q₁ - 1))) +
    ENNReal.ofReal C₀ ^ q₀ * ∫⁻ s in Ioi (0 : ℝ),
        snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ^ q₀ * ENNReal.ofReal (s ^ (q - q₀ - 1)) := by
  have : ∀ q' : ℝ, -q' + (q - 1) = q - q' - 1 := by intro q'; group
  rw [← this, ← this]
  -- TODO: is there a way to use lintegral_rw₂ conveniently?
  rw [lintegral_rw_aux power_aux_2, lintegral_rw_aux power_aux_2]
  rw [← lintegral_const_mul']; swap; exact coe_pow_ne_top' (hq₁)
  rw [← lintegral_const_mul']; swap; exact coe_pow_ne_top' (hq₀)
  simp_rw [← mul_assoc]
  rw [← lintegral_add_left']
  · apply setLIntegral_mono' measurableSet_Ioi
    intro s (s_pos : s > 0)
    gcongr
    · apply weaktype_estimate_trunc hp <;> try assumption
    · apply weaktype_estimate_trunc_compl <;> try assumption
      · exact tc.ran_ton s s_pos
  -- TODO: split off the measurability lemmas
  · apply AEMeasurable.mul
    · apply AEMeasurable.mul
      · apply AEMeasurable.const_mul
        · apply AEMeasurable.pow_const
          · change AEMeasurable ((fun t : ℝ ↦ snorm (trunc f t) (ENNReal.ofReal p₁) μ) ∘ (tc.ton)) (volume.restrict (Ioi 0))
            have tone := tc.ton_is_ton
            split_ifs at tone
            · apply aemeasurable_restrict_of_monotoneOn measurableSet_Ioi
              exact Monotone.comp_monotoneOn norm_trunc_mono (StrictMonoOn.monotoneOn tone)
            · apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
              exact Monotone.comp_antitoneOn norm_trunc_mono (StrictAntiOn.antitoneOn tone)
      · apply AEMeasurable.coe_nnreal_ennreal
        · apply AEMeasurable.real_toNNReal
          · apply AEMeasurable.pow_const
            apply aemeasurable_id'
    · apply AEMeasurable.coe_nnreal_ennreal
      · apply AEMeasurable.real_toNNReal
        · apply AEMeasurable.pow_const
          · apply aemeasurable_id'



#check distribution_trunc

-- lemma _estimate_norm_rpow_range_operator_trunc {C : ℝ} {p p' : ℝ≥0} (hp : 1 ≤ p) {q q' : ℝ≥0}
--   {f : α → E₁} (hf : Memℒp f p μ) (hq' : 1 ≤ q')  (hp'p : p < p') {a : ℝ}
--   (h₁T : HasWeakType T p' q' μ ν C.toNNReal) :
--   ∫⁻ s : ℝ in Ioi 0, distribution (T (trunc f a)) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q.toReal - 1)) ≤
--   ENNReal.ofReal C ^ q'.toReal * ∫⁻ s : ℝ in Ioi 0, snorm (trnc ⊤ f a) p' μ ^ q'.toReal * ENNReal.ofReal (s ^ (q.toReal - q'.toReal - 1)) := by
--   rw [← lintegral_const_mul']; swap; refine rpow_ne_top_of_nonneg (by positivity) coe_ne_top
--   apply setLIntegral_mono' measurableSet_Ioi
--   intro s (s_pos : s > 0)
--   rw [← mul_assoc]
--   refine le_trans (mul_le_mul_right' (weaktype_estimate_trunc hp hq' hp'p hf h₁T s_pos)
--         (ENNReal.ofReal (s ^ (q.toReal - 1)))) ?_
--   rw [ofReal_rpow_of_nonneg (x := s⁻¹), mul_assoc, ← ofReal_mul] <;> try positivity
--   unfold trnc; simp only [top_eq_true, ↓reduceIte]
--   gcongr
--   rw [Real.inv_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul, ← Real.rpow_add s_pos] <;> try positivity
--   apply le_of_eq; apply congr_arg; group

-- lemma _estimate_norm_rpow_range_operator_trunc_compl {C : ℝ} {p p' : ℝ≥0} (hp' : 1 ≤ p') {q q' : ℝ≥0}
--   {f : α → E₁} (hf : Memℒp f p μ) (hq' : 1 ≤ q') (hp'p : p' < p) {a : ℝ} (tc : ToneCouple) (h₁T : HasWeakType T p' q' μ ν C.toNNReal) :
--   ∫⁻ s : ℝ in Ioi 0, distribution (T (trnc ⊥ f a)) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q.toReal - 1)) ≤
--   ENNReal.ofReal C ^ q'.toReal * ∫⁻ s : ℝ in Ioi 0, snorm (trnc ⊥ f a) p' μ ^ q'.toReal * ENNReal.ofReal (s ^ (q.toReal - q'.toReal - 1)) := by
--   rw [← lintegral_const_mul']; swap; refine rpow_ne_top_of_nonneg (by positivity) coe_ne_top
--   apply setLIntegral_mono' measurableSet_Ioi
--   intro s (s_pos : s > 0)
--   rw [← mul_assoc]
--   refine le_trans (mul_le_mul_right' (weaktype_estimate_trunc_compl hp' hq' hp'p hf h₁T s_pos ha)
--         (ENNReal.ofReal (s ^ (q.toReal - 1)))) ?_
--   rw [ofReal_rpow_of_nonneg (x := s⁻¹), mul_assoc, ← ofReal_mul] <;> try positivity
--   unfold trnc; simp only [top_eq_true, ↓reduceIte]
--   gcongr
--   rw [Real.inv_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul, ← Real.rpow_add s_pos] <;> try positivity
--   apply le_of_eq; apply congr_arg; group

def res (j : Bool) (β : ℝ) : Set ℝ := if j then Ioo (0 : ℝ) β else Ioi β

lemma measurableSet_res {j : Bool} {β : ℝ} : MeasurableSet (res j β) := by
  unfold res
  split
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi

lemma res_subset_Ioi {j : Bool} {β : ℝ} (hβ : β > 0) : res j β ⊆ Ioi 0 := by
  unfold res
  split
  · exact Ioo_subset_Ioi_self
  · unfold Ioi
    simp
    intro s hs
    linarith

instance decidableMemRes {j : Bool} {β : ℝ} : Decidable (t ∈ res j β) := by
  exact Classical.propDecidable (t ∈ res j β)

def φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} (s t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
  distribution f (ENNReal.ofReal t) μ *
  if t ∈ res j (tc.ton s) then 1 else 0

lemma switch_arguments_φ' {j : Bool} {tc : ToneCouple} {s t : ℝ} (hs : s ∈ Ioi 0)
    (ht : t ∈ Ioi 0) :
    (if t ∈ res j (tc.ton s) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1 else
    @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0) =
    if s ∈ res (xor j tc.mon) (tc.inv t) then @OfNat.ofNat ℝ≥0∞ 1 One.toOfNat1 else
    @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 := by
  -- Written out because otherwise it got quite slow
  unfold res Ioo Ioi
  have h₀ := tc.inv_pf
  split at h₀ <;> rename_i mon
  · have h₀₁ := (h₀ s hs t ht).1
    have h₀₂ := (h₀ s hs t ht).2
    split <;> rename_i hj
    · rw [mon, hj]
      simp only [mem_setOf_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i hc1
      · split <;> rename_i hc2
        · exact Eq.refl (OfNat.ofNat 1)
        · exact False.elim (hc2 (h₀₂.mp hc1.2))
      · split <;> rename_i hc2
        · exact False.elim (hc1 (And.intro ht (h₀₂.mpr hc2)))
        · exact Eq.refl (OfNat.ofNat 0)
    · rw [mon, eq_false_of_ne_true hj]
      simp only [mem_setOf_eq, Bool.bne_true, Bool.not_false, ↓reduceIte]
      split <;> rename_i hc1
      · split <;> rename_i hc2
        · exact Eq.refl (OfNat.ofNat 1)
        · exact False.elim (hc2 (And.intro hs (h₀₁.mp hc1)))
      · split <;> rename_i hc2
        · exact False.elim (hc1 (h₀₁.mpr hc2.2))
        · exact Eq.refl (OfNat.ofNat 0)
  · have h₀₁ := (h₀ s hs t ht).1
    have h₀₂ := (h₀ s hs t ht).2
    split <;> rename_i hj
    · rw [eq_false_of_ne_true mon, hj]
      simp only [mem_setOf_eq, Bool.bne_false, ↓reduceIte]
      · split <;> rename_i hc1
        · split <;> rename_i hc2
          · exact Eq.refl (OfNat.ofNat 1)
          · exact False.elim (hc2 (And.intro hs (h₀₂.mp hc1.2)))
        · split <;> rename_i hc2
          · exact False.elim (hc1 (And.intro ht (h₀₂.mpr hc2.2)))
          · exact Eq.refl (OfNat.ofNat 0)
    · rw [eq_false_of_ne_true mon, eq_false_of_ne_true hj]
      simp only [mem_setOf_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      · split <;> rename_i hc1
        · split <;> rename_i hc2
          · exact Eq.refl (OfNat.ofNat 1)
          · exact False.elim (hc2 (h₀₁.mp hc1))
        · split <;> rename_i hc2
          · exact False.elim (hc1 (h₀₁.mpr hc2))
          · exact Eq.refl (OfNat.ofNat 0)

lemma switch_arguments_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} (s t : ℝ) (hs : s ∈ Ioi 0)
    (ht : t ∈ Ioi 0) :
    @φ _ _ _ μ _ f j p' q' q tc s t
    = ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
      distribution f (ENNReal.ofReal t) μ *
      if s ∈ res (xor j tc.mon) (tc.inv t) then 1 else 0
     := by
  unfold φ
  rw [switch_arguments_φ' hs ht]

-- TODO: generalize tc.inv?
lemma value_integral_φ' {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0):
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t),
    (ENNReal.ofReal s ^ ((q - q' - 1) * p' / q') * ENNReal.ofReal t ^ (p' - 1) *
        distribution f (ENNReal.ofReal t) μ) ^
      (q' / p')
    := by
  rw [lintegral_double_restrict_set (B := res (xor j tc.mon) (tc.inv t))]
  · rw [inter_eq_right.mpr (res_subset_Ioi (tc.ran_inv t ht))]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_res]
    intro s hs
    have h₁ : s ∈ Ioi 0 := res_subset_Ioi (tc.ran_inv t ht) hs
    rw [switch_arguments_φ _ _ h₁ ht]
    split
    · rw [mul_one]
    · contradiction
  · exact measurableSet_Ioi
  · exact measurableSet_res
  · filter_upwards
    intro s hs
    have h₁ : s ∈ Ioi 0 := by exact mem_of_mem_diff hs
    rw [switch_arguments_φ _ _ h₁ ht]
    split <;> rename_i hs1
    · exact False.elim (hs.2 hs1)
    . rw [mul_zero]
      rw [zero_rpow_of_pos]
      exact div_pos hq' hp'

lemma estimate_trunc_comp_integral (f : α → E₁) (hf : AEStronglyMeasurable f μ) (q p₀ q₀ : ℝ) {tc : ToneCouple} (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀)
    (β : ℝ) (hβ : β ≥ 0) :
    ∫⁻ (s : ℝ) in (Ioi 0),
    ENNReal.ofReal s ^ (q - q₀ - 1) * (snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ) ^ q₀ ≤
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₀) * (@φ _ _ _ μ _ f false p₀ q₀ q tc s t )) ^ (q₀ / p₀) := by
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  refine Preorder.le_trans ?_
      (ENNReal.ofReal s ^ (q - q₀ - 1) *
      ((∫⁻ (s : ℝ) in (res false (tc.ton s)),
        ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) * distribution f (ENNReal.ofReal s) μ) ^
      p₀⁻¹) ^ q₀) ?_ ?_ ?_
  · apply mul_le_mul_left'
    have hq₀ : q₀ ≥ 0 := by linarith
    have h₀ : snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ≤
        (∫⁻ s : ℝ in res false (tc.ton s), ENNReal.ofReal p₀ * ENNReal.ofReal s ^ (p₀ - 1) *
        distribution f (ENNReal.ofReal s) μ) ^ (p₀⁻¹) := by
      apply estimate_snorm_trunc_compl hp₀ hf
      sorry
    apply ENNReal.rpow_le_rpow
    · exact h₀
    · exact hq₀
  · have hq₀ : q₀ ≠ 0 := by linarith
    have hp₀inv : p₀⁻¹ ≠ 0 := by
      refine inv_ne_zero ?_
      linarith
    have hp₀ : (ENNReal.ofReal p₀).toReal = p₀ := by
      refine toReal_ofReal ?_
      linarith
    have h₁ : p₀⁻¹ * q₀ ≠ 0 := by sorry
    have h₂ : p₀⁻¹ * q₀ ≥ 0 := by sorry
    -- rw [hp₀]
    rw [← ENNReal.rpow_mul, div_eq_inv_mul]
    rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₀ - 1))]
    rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
    rw [← mul_rpow_of_nonneg (hz := h₂)]
    have h₃ : (ENNReal.ofReal s ^ (q - q₀ - q₀ / q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ≠ ⊤ := by sorry
    rw [← lintegral_const_mul' (hr := h₃)]
    refine ENNReal.rpow_le_rpow ?_ h₂
    unfold φ
    have h₃ : Ioi (0 : ℝ) ∩ res false (tc.ton s) = res false (tc.ton s) := by
      refine inter_eq_self_of_subset_right ?_
      refine res_subset_Ioi ?_
      sorry
    nth_rewrite 2 [lintegral_double_restrict_set (B := res false (tc.ton s)) _ measurableSet_res]
    · rw [h₃]
      apply setLIntegral_mono_ae' (measurableSet_Ioi)
      apply ae_of_all
      intro t ht; simp at ht
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₀)]
      split <;> rename_i t_res
      · rw [mul_one, ← mul_assoc]
        apply mul_le_mul_right'
        rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
        apply mul_le_mul_right'
        apply mul_le_mul_left'
        apply le_of_eq
        rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₀, ← mul_assoc]
        rfl
      · unfold res at t_res
        simp at t_res
        contrapose t_res; simp; exact ht
    · apply ae_of_all
      simp
      intro t ht ht2 ht3
      contrapose! ht3; exact ht2
    · exact measurableSet_Ioi

lemma estimate_trunc' (p₁ : ℝ) (A : ℝ):
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution (trunc f A) (ENNReal.ofReal t) μ =
          ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
          distribution f (ENNReal.ofReal ↑t) μ := by
  rw [lintegral_double_restrict_set (B := Ioo 0 A) _ measurableSet_Ioo]
  rw [inter_eq_self_of_subset_right Ioo_subset_Ioi_self]
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo]; intro t ht; rw [distribution_trunc]
    split <;> rename_i h₀
    · rfl
    · exact False.elim (h₀ ((ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht.1)).mpr ht.2))
  · apply ae_of_all; intro t ht; rw [distribution_trunc]
    split <;> rename_i ht2
    · exact False.elim (ht.2 ⟨ht.1, (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht.1)).mp ht2⟩)
    · rw [mul_zero]
  · exact measurableSet_Ioi

lemma estimate_trunc {p₁ : ℝ} (hp₁ : p₁ > 0) (A : ℝ) (hf : AEStronglyMeasurable f μ):
    snorm (trunc f A) (.ofReal p₁) μ =
    (∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal p₁ * ENNReal.ofReal t ^ (p₁ - 1) *
            distribution f (ENNReal.ofReal t) μ) ^ p₁⁻¹ := by
  rw [snorm_pow_eq_distribution', ← estimate_trunc', ← lintegral_const_mul']
  refine congrFun (congrArg ?_ ?_) ?_
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
  intro t ht
  rw [mul_comm _ (ENNReal.ofReal (t ^ (p₁ - 1))), ← mul_assoc]
  · congr; exact Eq.symm (ofReal_rpow_of_pos ht)
  · exact coe_ne_top
  · apply AEStronglyMeasurable.aemeasurable (aestronglyMeasurable_trunc hf)
  · exact hp₁

-- TODO: Combine this function with estimate_trunc_compl_integral'
-- TODO the assumption of AEStronglyMeasurable can probably be weakened to measurable
lemma eq_trunc_integral' (f : α → E₁) (hf : AEStronglyMeasurable f μ)
    (q p₁ q₁ : ℝ) (tc : ToneCouple) (hp₁ : p₁ > 0):
    ∫⁻ (s : ℝ) in Ioi 0,
    ENNReal.ofReal s ^ (q - q₁ - 1) *
    (snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ) ^ q₁ =
    ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁) * (@φ _ _ _ μ _ f true p₁ q₁ q tc s t )) ^ (q₁ / p₁)
    := by
  apply setLIntegral_congr_fun measurableSet_Ioi
  apply ae_of_all
  intro s hs
  rw [estimate_trunc hp₁ _ hf]
  have hq₀ : q₁ ≠ 0 := by sorry
  have hp₀inv : p₁⁻¹ ≠ 0 := by sorry
  have hp₀ : (ENNReal.ofReal p₁).toReal = p₁ := by
    refine toReal_ofReal sorry
  have h₁ : p₁⁻¹ * q₁ ≠ 0 := by sorry
  have h₂ : p₁⁻¹ * q₁ ≥ 0 := by sorry
  -- rw [hp₀]
  rw [← ENNReal.rpow_mul, div_eq_inv_mul]
  rw [← ENNReal.rpow_inv_rpow h₁ (ENNReal.ofReal s ^ (q - q₁ - 1))]
  rw [← (div_eq_one_iff_eq hq₀).mpr rfl]
  rw [← mul_rpow_of_nonneg (hz := h₂)]
  have h₃ : (ENNReal.ofReal s ^ (q - q₁ - q₁ / q₁)) ^ (p₁⁻¹ * q₁)⁻¹ ≠ ⊤ := by sorry
  rw [← lintegral_const_mul' (hr := h₃)]
  refine congrFun (congrArg HPow.hPow ?_) (p₁⁻¹ * q₁)
  unfold φ
  nth_rewrite 2 [lintegral_double_restrict_set (B := res true (tc.ton s)) _ measurableSet_res]
  · have h₃ : Ioi (0 : ℝ) ∩ (res true (tc.ton s)) = res true (tc.ton s) := by
      refine inter_eq_self_of_subset_right ?_
      refine res_subset_Ioi ?_
      sorry
    rw [h₃]
    apply setLIntegral_congr_fun (measurableSet_Ioo)
    apply ae_of_all
    intro t ht; simp at ht
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm _ (ENNReal.ofReal p₁)]
    split
    · rw [mul_one, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      rw [(div_eq_one_iff_eq hq₀).mpr rfl, ← mul_assoc]
      refine congrFun (congrArg ?_ ?_) ?_
      apply congrArg
      rw [← ENNReal.rpow_mul, @mul_inv, inv_inv p₁, ← mul_assoc]
      rfl
    · tauto
  · apply ae_of_all
    simp
    intro t ht1 ht2 ht3
    contradiction
  · exact measurableSet_Ioi

/-- Extract expressions for the lower Lebesgue integral of power functions -/

lemma lintegral_rpow_of_gt_abs {β γ : ℝ} (hβ : β > 0) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  have hγ2 : γ + 1 > 0 := by linarith
  rw [setLIntegral_congr Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le (le_of_lt hβ)]
    rw [integral_rpow]
    · rw [Real.zero_rpow (ne_of_gt hγ2), sub_zero]
      rw [abs_of_nonneg (le_of_lt hγ2)]
    · exact Or.inl hγ
  · apply (@intervalIntegral.intervalIntegrable_rpow' 0 β γ ?_).1
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt hs.1) γ

lemma lintegral_Ioi_rpow_of_lt_abs {β σ : ℝ} (hβ : β > 0) (hσ : σ < -1):
    ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / |σ + 1|) := by
  have hσ2 : σ + 1 < 0 := by linarith
  rw [abs_of_neg hσ2]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt hσ hβ]
    rw [div_neg, neg_div]
  · apply integrableOn_Ioi_rpow_of_lt hσ hβ
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun s hs ↦ Real.rpow_nonneg (le_of_lt (lt_trans hβ hs)) σ

-- TODO : check if the tc.inv parameter can be generalized
lemma lintegral_rpow_abs {j : Bool} {tc : ToneCouple} {γ : ℝ} {t : ℝ}
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) (ht : t > 0) :
  ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t), ENNReal.ofReal s ^ γ =
    ENNReal.ofReal ((tc.inv t) ^ (γ + 1) / |γ + 1|) := by
  rw [← lintegral_congr_ae (Filter.mp_mem (self_mem_ae_restrict measurableSet_res)
      (Filter.univ_mem'
      (fun s hs ↦ Eq.symm (ofReal_rpow_of_pos (res_subset_Ioi (tc.ran_inv t ht) hs)))))]
  unfold res
  split at hγ <;> rename_i xor_split
  · rw [xor_split]
    simp
    rw [lintegral_rpow_of_gt_abs (tc.ran_inv t ht) hγ]
  · rw [eq_false_of_ne_true xor_split]
    simp
    rw [lintegral_Ioi_rpow_of_lt_abs (tc.ran_inv t ht) hγ]

/-- Compute the integrals obtained after switching the arguments -/

lemma value_integral_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0)
    (hγ : if xor j tc.mon = true then q - q' - 1 > -1 else q - q' - 1 < -1):
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') =
    ENNReal.ofReal (tc.inv t ^ (q - q') / |q - q'|) * ENNReal.ofReal t ^ ((p' - 1) * (q' / p')) *
    distribution f (ENNReal.ofReal t) μ ^ (q' / p')
    --
    -- (ENNReal.ofReal s ^ (q - q' - 1))) * ENNReal.ofReal t ^ ((p' - 1) * (q' / p')) * (distribution f (ENNReal.ofReal t) μ) ^ (q' / p')
    := by
  have h₀ : q' / p' ≥ 0 := by sorry
  have h₁ : ((q - q' - 1) * p' / q') * (q' / p') = q - q' - 1 := by sorry
  rw [value_integral_φ' ht hq' hp']
  rw [funext fun f ↦ mul_rpow_of_nonneg _ _ h₀]
  rw [lintegral_mul_const _ (Measurable.pow_const (Measurable.mul_const
      (Measurable.pow_const measurable_ofReal _) _) _)]
  rw [funext fun f ↦ mul_rpow_of_nonneg _ _ h₀]
  rw [lintegral_mul_const _ (Measurable.pow_const (Measurable.pow_const measurable_ofReal _) _)]
  rw [← ENNReal.rpow_mul, ← funext fun _ ↦ ENNReal.rpow_mul _ _ _]
  rw [h₁]
  rw [lintegral_rpow_abs _ ht]
  · rw [sub_add_cancel]
  · exact hγ

lemma value_integral_φ'' {j : Bool} {p' q' q : ℝ} {spf : ScaledPowerFunction} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0)
    (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :
    ∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p') =
    ENNReal.ofReal (spf.d ^ (q - q')) * ENNReal.ofReal |q - q'|⁻¹ *
    ENNReal.ofReal t ^ ((p' - 1) * (q' / p') + spf.σ⁻¹ * (q - q')) *
    distribution f (ENNReal.ofReal t) μ ^ (q' / p') := by
  rewrite [value_integral_φ ht hq' hp' hγ]
  unfold ToneCouple.inv spf_to_tc
  simp only
  have h₀ : |q - q'|⁻¹   ≥ 0 := sorry
  have h₁ : (t ^ spf.σ⁻¹) ≥ 0 := sorry
  have h₂ : 0 ≤ spf.d ^ (q - q') := sorry
  rw [div_eq_mul_inv, ofReal_mul' h₀, Real.mul_rpow (le_of_lt spf.hd) h₁,
      ← Real.rpow_mul (le_of_lt ht), ofReal_mul h₂, ← mul_comm _ (ENNReal.ofReal _),
        mul_comm _ (ENNReal.ofReal t ^ ((p' - 1) * (q' / p'))), ← mul_assoc, ← mul_assoc,
        ← ofReal_rpow_of_pos, ← ENNReal.rpow_add, mul_assoc _ _ (ENNReal.ofReal |q - q'|⁻¹),
        mul_comm _ ((ENNReal.ofReal (spf.d ^ (q - q')) * ENNReal.ofReal |q - q'|⁻¹))]
  · sorry
  · exact coe_ne_top
  · exact ht

lemma value_integral_φ''' {j : Bool} {p' q' q : ℝ} {spf : ScaledPowerFunction} {t : ℝ}
    (ht : t > 0) (hq' : q' > 0) (hp' : p' > 0) (hp : p' + spf.σ⁻¹ * (q - q') * (p' / q') > 1)
    (hγ : if xor j ((spf_to_tc spf).mon) then q - q' - 1 > -1 else q - q' - 1 < -1) :
    ∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p')) ^ (p' / q') =
    ENNReal.ofReal (spf.d ^ (q - q')) ^ (p' / q') * ENNReal.ofReal |q - q'|⁻¹ ^ (p' / q') *
    ENNReal.ofReal (p' + spf.σ⁻¹ * (q - q') * (p' / q') )⁻¹ *
    snorm f (p' + spf.σ⁻¹ * (q - q') * (p' / q')).toNNReal μ ^
    (p' + spf.σ⁻¹ * (q - q') * (p' / q'))
    := by
  have hp2 : p' + spf.σ⁻¹ * (q - q') * (p' / q') > 0 := by linarith
  nth_rewrite 3 [← Real.coe_toNNReal (p' + spf.σ⁻¹ * (q - q') * (p' / q')) (le_of_lt hp2)]
  rw [snorm_pow_eq_distribution sorry]
  rw [Real.coe_toNNReal (p' + spf.σ⁻¹ * (q - q') * (p' / q')) (le_of_lt hp2)]
  have h₀ : p' - 1 + spf.σ⁻¹ * (q - q') * (p' / q') =
      p' + spf.σ⁻¹ * (q - q') * (p' / q') - 1 := by linarith
  rw [← h₀]
  rw [← lintegral_const_mul']
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    intro t ht
    rw [value_integral_φ'' ht hq' hp' hγ]
    have hpq : p'/q' ≥ 0 := sorry
    have hpq2 : q' / p' * (p' / q') = 1 := sorry
    rw [mul_rpow_of_nonneg _ _ hpq, mul_rpow_of_nonneg _ _ hpq,
        mul_rpow_of_nonneg _ _ hpq, ← ENNReal.rpow_mul, add_mul, ← ENNReal.rpow_mul,
        mul_assoc (p' - 1), hpq2, mul_one, ENNReal.rpow_one, mul_assoc]
    · sorry
  · sorry

--


-- TODO: fix the variables here?
def p_ (j : Bool) := match j with
  | ⊥ => p₀
  | ⊤ => p₁

def q_ (j : Bool) := match j with
  | ⊥ => q₀
  | ⊤ => q₁

#check spfI

lemma value_integral_summary {j : Bool} {spf : ScaledPowerFunction} {p₀ q₀ p₁ q₁ p q p' q' t : ℝ} (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (ht : t ∈ Ioo 0 1)
  (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
  (hspf : spf = spfI hp₀ hq₀ hp₁ hq₁ ht (ne_of_lt hp₀p₁) hq₀q₁ hp hq)
  (hp' : p' = match j with | ⊥ => p₀ | ⊤ => p₁)
  (hq' : q' = match j with | ⊥ => q₀ | ⊤ => if p₀ < p₁ then q₁ else q₀) :
  ∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q (spf_to_tc spf) s t ^ (q' / p')) ^ (p' / q') =
    ENNReal.ofReal (spf.d ^ (q - q')) ^ (p' / q') * ENNReal.ofReal |q - q'|⁻¹ ^ (p' / q') *
    ENNReal.ofReal (p' + spf.σ⁻¹ * (q - q') * (p' / q') )⁻¹ *
    snorm f (p' + spf.σ⁻¹ * (q - q') * (p' / q')).toNNReal μ ^
    (p' + spf.σ⁻¹ * (q - q') * (p' / q'))
    := by
  rcases j with bot | top
  · simp only at hp'; simp only at hq'; rw [hp', hq']
    apply value_integral_φ''' <;> try assumption
    · rw [hspf]
      · unfold spfI
        simp only
        rw [σ_equality_6] <;> try assumption
        · sorry
    · split_ifs with ch
      · have : spf.σ > 0 := sorry
        unfold xor ToneCouple.mon spf_to_tc at ch
        simp only [gt_iff_lt, this, ↓reduceIte, Bool.bne_true, Bool.not_false] at ch
        sorry
      · sorry
  · simp only at hp'; simp only at hq'; rw [hp', hq']
    apply value_integral_φ''' <;> try assumption
    · split_ifs with ch
      · have : spf.σ > 0 := sorry
        unfold xor ToneCouple.mon spf_to_tc at ch
        simp only [gt_iff_lt, this, ↓reduceIte, Bool.bne_true, Bool.not_false] at ch
        sorry
    · rw [hspf]
      · unfold spfI
        simp only
        sorry
    · sorry
#check PreservesAEStrongMeasurability
#check _estimate_norm_rpow_range_operator
-- TODO: can hq become hq > 0?
lemma combine_estimates {C₀ C₁ : ℝ} {p₀ q₀ p₁ q₁ p q t : ℝ} {A : ℝ} (hA : A > 0) {f : α → E₁} {tc : ToneCouple} (hp₀ : 1 ≤ p₀) (hq₀ : 1 ≤ q₀) (hp₁ : 1 ≤ p₁) (hq₁ : 1 ≤ q₁) (ht : t ∈ Ioo 0 1)
  (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹) (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹) (hf : Memℒp f (ENNReal.ofReal p) μ) (hT : Subadditive' T A)
  (h₁T : HasWeakType T (ENNReal.ofReal p₁) (ENNReal.ofReal q₁) μ ν C₁.toNNReal)
  (h₀T : HasWeakType T (ENNReal.ofReal p₀) (ENNReal.ofReal q₀) μ ν C₀.toNNReal)
  (h₂T : PreservesAEStrongMeasurability T (ENNReal.ofReal p) (ν := ν) (μ := μ)) :
    ∫⁻ x , ‖T f x‖₊ ^ q ∂ν ≤
    3 := calc
  ∫⁻ x , ‖T f x‖₊ ^ q ∂ν
    ≤ ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) +
  distribution (T (f - trunc f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1))  := by
    apply _estimate_norm_rpow_range_operator
    · sorry -- TODO: abstract
    · exact hA
    · exact hT
    · sorry
  _ ≤ ENNReal.ofReal ((2 * A)^q * q) *
      (ENNReal.ofReal C₁ ^ q₁ * (∫⁻ s in Ioi (0 : ℝ),
        snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ ^ q₁ * ENNReal.ofReal (s ^ (q - q₁ - 1))) +
    ENNReal.ofReal C₀ ^ q₀ * ∫⁻ s in Ioi (0 : ℝ),
        snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ^ q₀ * ENNReal.ofReal (s ^ (q - q₀ - 1))) := by
    gcongr
    have hp : 1 ≤ p := sorry
    apply estimate_norm_rpow_range_operator hp <;> try assumption
    · sorry
    · sorry
  _ = ENNReal.ofReal ((2 * A)^q * q) *
      (ENNReal.ofReal C₁ ^ q₁ * (∫⁻ s in Ioi (0 : ℝ),
       ENNReal.ofReal (s ^ (q - q₁ - 1)) * snorm (trunc f (tc.ton s)) (ENNReal.ofReal p₁) μ ^ q₁) +
      ENNReal.ofReal C₀ ^ q₀ * ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (q - q₀ - 1)) * snorm (f - trunc f (tc.ton s)) (ENNReal.ofReal p₀) μ ^ q₀ ) := by
      simp_rw [mul_comm]
  _ = _ * (_ * ∫⁻ s : ℝ in Ioi 0,
    ( ∫⁻ t : ℝ in Ioi 0, (ENNReal.ofReal p₁) * (@φ _ _ _ μ _ f true p₁ q₁ q tc s t )) ^ (q₁ / p₁)) + _ := by rw [eq_trunc_integral']
  _ ≤ _ := sorry


#exit






-- For Minkowski's inequality: first prove statement dual statement about the norm

/-- Minkowksi's inequality applied in this special case. -/

lemma minkowski_φ {j : Bool} {p' q' q : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in Ioi 0, ∫⁻ t : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t ^ (q' / p') ≤
    (∫⁻ t : ℝ in Ioi 0,
    (∫⁻ s : ℝ in Ioi 0, @φ _ _ _ μ _ f j p' q' q tc s t) ^ (p' / q') ) ^ (q' / p') := sorry

lemma rpow_add_of_pos (a : ℝ≥0∞) (c d : ℝ) (hc : c > 0) (hd : d > 0):
    a ^ (c + d) = a ^ c * a ^ d := by
  have hcd : c + d  > 0 := by linarith
  rcases (eq_or_ne a 0) with a_eq_zero | a_ne_zero
  · rw [a_eq_zero]
    rw [zero_rpow_of_pos hcd, zero_rpow_of_pos hc, zero_rpow_of_pos hd, mul_zero]
  · rcases (eq_or_ne a ⊤) with a_eq_top | a_ne_top
    · rw [a_eq_top]
      rw [top_rpow_of_pos hcd, top_rpow_of_pos hc, top_rpow_of_pos hd, top_mul_top]
    · rw [ENNReal.rpow_add c d a_ne_zero a_ne_top]

lemma exists_monotone_integrable {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∃ g : ℕ → α → ℝ≥0∞, Monotone g ∧ ∀ n : ℕ, ∫⁻ x, g n x ∂μ < ⊤ ∧
    ⨆ n : ℕ, g n = f := by
  sorry

lemma representationLp {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : Measurable f) {p q : ℝ} (hp : p > 1) (hq : q ≥ 1)
    (hpq : 1 / p + 1 / q = 1):
    ∫⁻ x : α, (f x) ^ p ∂μ =
    ⨆ g ∈ {g' : α → ℝ≥0∞ | ∫⁻ x : α, (g x) ^ q ∂μ ≤ 1},
    ∫⁻ x : α, (f x) * g x ∂μ := by
  let A := spanningSets μ
  have A_mon := monotone_spanningSets μ
  let g := fun n : ℕ ↦ (A n).indicator (fun x ↦ min (f x) n)
  have g_mon : Monotone g := by
    intro m n hmn x; unfold_let g; unfold indicator; simp only
    split <;> rename_i hx1
    · split <;> rename_i hx2
      · refine min_le_min_left (f x) (Nat.cast_le.mpr hmn)
      · exact (False.elim (hx2 (A_mon hmn hx1)))
    · exact zero_le _
  have f_mul : ∀ n : ℕ, (g n) ^ p ≤ f * (g n) ^ (p - 1) := by
    intro n x; unfold_let g; unfold indicator; simp; split <;> rename_i hx1
    · refine le_trans (b := (min (f x) ↑n) * min (f x) ↑n ^ (p - 1)) ?_ ?_
      · nth_rewrite 1 [← add_sub_cancel 1 p]
        rw [rpow_add_of_pos, ENNReal.rpow_one]; exact Real.zero_lt_one; linarith
      · exact mul_le_mul_right' (min_le_left (f x) ↑n) (min (f x) ↑n ^ (p - 1))
    · rw [zero_rpow_of_pos]; exact zero_le _; linarith
  have g_sup : ∀ x : α, ⨆ n : ℕ, g n x = f x := by
    intro x; refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?h₁ ?h₂
    · intro n; unfold_let g; unfold indicator; simp only
      split; exact min_le_left (f x) ↑n; exact zero_le (f x)
    · intro w hw
      rcases (exists_exists_eq_and.mp
          (Eq.mpr (id (congrArg (fun _a ↦ x ∈ _a) (MeasureTheory.iUnion_spanningSets μ))) True.intro)) with ⟨m, wm⟩
      rcases exists_nat_gt (w.toReal + (f x).toReal) with ⟨n, wn⟩
      use n + m
      unfold_let g; unfold indicator; simp only
      split <;> rename_i hx
      · rcases (eq_top_or_lt_top (f x)) with fx_eq_top | fx_lt_top
        · simp only [Nat.cast_add, lt_min_iff]; simp [fx_eq_top] at wn
          exact ⟨hw, lt_of_lt_of_le (b := (n : ℝ≥0∞))
              ((toNNReal_lt_toNNReal (LT.lt.ne_top hw) coe_ne_top).mp wn) le_self_add⟩
        · rw [min_eq_left]; exact hw
          rw [Nat.cast_add]
          refine le_trans (le_of_lt ?_) (le_self_add (a := (n : ℝ≥0∞)) (c := m))
          rw [← (ofReal_toReal_eq_iff.mpr (LT.lt.ne_top fx_lt_top))]
          exact (ofReal_lt_iff_lt_toReal toReal_nonneg coe_ne_top).mpr
              (lt_of_add_lt_of_nonneg_right wn (toReal_nonneg))
      · refine False.elim (hx (A_mon le_add_self wm))
  sorry

/-- Marcinkiewicz real interpolation theorem, for the case of equal domain: p₀ = p₁. -/
lemma exists_hasStrongType_real_interpolation' {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (hp₀₁ : p₀ = p₁) :
    ∃ C > 0, HasStrongType T p q μ ν C := by
  let Cfinal : ℝ≥0 := C₀
  exists Cfinal
  constructor
  · sorry
  · have p_eq_p₀ : p = p₀ := by sorry
    intros f f_mem
    rewrite [p_eq_p₀] at f_mem
    have h₀T_ap := (h₀T f f_mem).2
    rewrite [hp₀₁] at f_mem
    have h₁T_ap := (h₁T f f_mem).2
    constructor
    · exact (h₁T f f_mem).1
    · unfold wnorm at h₀T_ap
      split at h₀T_ap
      · have q_eq_top : q = ⊤ := sorry
        rewrite [← p_eq_p₀] at h₀T_ap
        unfold snorm
        split
        · apply zero_le
        · exact h₀T_ap
      · sorry

/-- Marcinkiewicz real interpolation theorem, for the case p₀ ≠ p₁ and all exponents
    are less than ∞.
    TODO: So far the assymption that p₀ ≠ p₁ is not added -/
lemma exists_hasStrongType_real_interpolation'' {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hq₀ : q₀ < ∞) (hq₁ : q₁ < ∞) :
    ∃ C > 0, HasStrongType T p q μ ν C := sorry

/-- Marcinkiewicz real interpolation theorem. -
-- feel free to assume that T also respect a.e.-equality if needed. -/
/- For the proof, see
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.4, theorem 6.28.
You want to use `trunc f A` when the book uses `h_A`.
Minkowski's inequality is `ENNReal.lintegral_Lp_add_le` -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hT : Sublinear T) (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) :
    ∃ C > 0, HasStrongType T p q μ ν C := by
  exists ?_
  constructor
  · sorry
  · unfold HasStrongType
    intros f fMem
    constructor
    · exact h₂T f fMem
    · let A := (3 : ℝ).toNNReal
      have h₀ : ∫⁻ x, ‖trunc f A x‖₊ ^ p.toReal ∂μ =
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
          distribution (trunc f A) (ENNReal.ofReal t) μ := by
        apply lintegral_norm_pow_eq_distribution
        sorry
      -- #check distribution_trunc
      -- have h₁ := distribution_trunc (f := f) (s := ENNReal.ofReal t) (t := A.toReal) (μ := μ)
      -- rewrite [h₁] at h₀
      -- have h₁ : ∫⁻ t in Ioo 0 A, ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ =
      --     ∫⁻ x : ℝ, (Ioo 0 A).indicator (fun t : ℝ ↦ ENNReal.ofReal (p.toReal * t ^ (p.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ) := by
      sorry
      -- have h₂ : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
      --     distribution (trunc f A) (ENNReal.ofReal t) μ =
      --     ∫⁻ (t : ℝ) in Ioo (0 : ℝ) A, ENNReal.ofReal (p₁.toReal * t ^ (p₁.toReal - 1)) *
      --     distribution f (ENNReal.ofReal ↑t) μ := by
      --   rewrite [← lintegral_indicator (hs := measurableSet_Ioi)]
      --   rewrite [← lintegral_indicator (hs := measurableSet_Ioo)]
      --   apply congr_arg
      --   ext t
      --   unfold indicator
      --   simp
      --   rewrite [distribution_trunc]
      --   simp
      --   split <;> rename_i h₃
      --   · split <;> rename_i h₄
      --     · split <;> rename_i h₅
      --       · rfl
      --       · simp at h₅
      --         have h₆ := h₅ h₃
      --         have _ : t < ↑A := by
      --           rewrite [← ofReal_coe_nnreal] at h₄
      --           refine (ofReal_lt_ofReal_iff_of_nonneg (le_of_lt h₃)).mp h₄
      --         linarith
      --     · split <;> rename_i h₅
      --       · have _ : A.toReal ≤ t := by
      --           simp at h₄
      --           rewrite [← ofReal_coe_nnreal] at h₄
      --           exact (ofReal_le_ofReal_iff (le_of_lt h₃)).mp h₄
      --         linarith
      --       · rfl
      --   · split <;> rename_i h₄
      --     · linarith
      --     · rfl
      -- unfold HasWeakType at h₀T
      -- unfold wnorm at h₀T
      -- unfold wnorm' at h₀T
      -- -- have h₃ : ∫⁻ x, ‖T f (x)‖₊ ^q.toReal ∂ν  =
      --     2^q.toReal * q * ∫⁻ s in Ioi (0 : ℝ),
      --     ENNReal.ofReal s^(q.toReal - 1) * distribution (T f) ((ENNReal.ofReal 2)*(ENNReal.ofReal s)) ν := by
      --   have one_le_q : (1 : ℝ) ≤ q.toReal := sorry
      --   rewrite [lintegral_norm_pow_eq_distribution one_le_q]
      --   · have two_gt_0 : (2 : ℝ) > 0 := by linarith
      --     nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := 2) two_gt_0]
      --     have h₄ : ENNReal.ofReal |2| ≠ ⊤ := coe_ne_top
      --     have h₅ : (2 ^ q.toReal) * q ≠ ⊤ := sorry
      --     rewrite [← lintegral_const_mul' (hr := h₄)]
      --     rewrite [← lintegral_const_mul' (hr := h₅)]
      --     apply set_lintegral_congr_fun (measurableSet_Ioi)
      --     apply ae_of_all
      --     simp
      --     intros t t_gt_0
      --     rw [ofReal_mul' (le_of_lt t_gt_0)]
      --     have h₈ : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
      --       exact ofReal_eq_ofNat.mpr rfl
      --     rw [h₈]
      --     rw [← mul_assoc]
      --     rw [← mul_assoc]
      --     -- TODO: rename!!!
      --     apply test_9
      --     sorry

/- State and prove Remark 1.2.7 -/

end MeasureTheory
