import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
import Carleson.ToMathlib.Analysis.MeanInequalitiesPow
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Carleson.ToMathlib.MeasureTheory.Function.SimpleFunc
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Carleson.ToMathlib.MeasureTheory.Integral.Misc

/-!
# Triangle inequality for `Lorentz`-seminorm

In this file we prove several versions of the triangle inequality for the `Lorentz` seminorm,
as well as simple corollaries.
-/

-- Upstreaming status: statements should be checked to closely match the corresponding statements
-- for `eLpNorm`; proofs might still need some cleanup

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {α ε : Type*} {m : MeasurableSpace α}
  [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {p q : ℝ≥0∞} {μ : Measure α} {f g : α → ε}

open ENNReal in
theorem eLorentzNorm_add_le'' :
    eLorentzNorm (f + g) p q μ ≤ 2 ^ p.toReal⁻¹ * LpAddConst q * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  unfold eLorentzNorm
  split_ifs with p_zero p_top q_zero q_top
  · simp
  · simp
  · unfold LpAddConst
    simp only [p_top, toReal_top, _root_.inv_zero, rpow_zero, q_top, Set.mem_Ioo, zero_lt_top,
      not_top_lt, and_false, ↓reduceIte, mul_one, one_mul]
    exact eLpNormEssSup_add_le
  · simp only [p_top, toReal_top, _root_.inv_zero, rpow_zero, one_mul]
    rw [← mul_add, ← mul_assoc, ENNReal.mul_top]
    · gcongr
      exact eLpNormEssSup_add_le
    unfold LpAddConst
    split_ifs <;> simp
  rw [eLorentzNorm'_eq p_zero p_top]
  calc _
    _ ≤ eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * (rearrangement f (t / 2) μ + rearrangement g (t / 2) μ))
          q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
      apply eLpNorm_mono_enorm
      intro t
      simp only [ENNReal.toReal_inv, enorm_eq_self]
      gcongr
      convert rearrangement_add_le
      simp
    _ ≤ LpAddConst q * (eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * rearrangement f (t / 2) μ) q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))
        + eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * rearrangement g (t / 2) μ) q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))) := by
      simp_rw [mul_add ( _ ^ _)]
      apply eLpNorm_add_le' (by fun_prop) (by fun_prop)
    _ = LpAddConst q * 2 ^ p.toReal⁻¹ * (eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * rearrangement f t μ) q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))
        + eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * rearrangement g t μ) q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))) := by
      rw [mul_assoc]
      congr
      rw [← eLpNorm_withDensity_scale_constant' (a := 2) (by fun_prop) (by norm_num)]
      nth_rw 2 [← eLpNorm_withDensity_scale_constant' (a := 2) (by fun_prop) (by norm_num)]
      simp only [coe_mul, coe_ofNat]
      conv in (2 * _) ^ p⁻¹.toReal => rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
      conv in (2 * _) ^ p⁻¹.toReal => rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
      have : ∀ {f : α → ε}, (fun (t : ℝ≥0) ↦ 2 ^ p⁻¹.toReal * t ^ p⁻¹.toReal * rearrangement f (2 * t / 2) μ)
          = (2 : ℝ≥0∞) ^ p⁻¹.toReal • fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f (2 * t / 2) μ := by
        intro f
        ext t
        simp only [toReal_inv, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this, this, eLpNorm_const_smul'' (by simp), eLpNorm_const_smul'' (by simp), ← mul_add]
      congr
      · simp
      all_goals
      · ext t
        congr
        rw [mul_div_assoc]
        apply ENNReal.mul_div_cancel
          <;> norm_num
    _ = 2 ^ p.toReal⁻¹ * LpAddConst q * (eLorentzNorm' f p q μ + eLorentzNorm' g p q μ) := by
      rw [mul_comm (LpAddConst q)]
      symm; congr <;>
      · exact eLorentzNorm'_eq p_zero p_top

/-- The function `k` in the proof of Theorem 6.7 in https://doi.org/10.1007/978-3-319-30034-4 -/
noncomputable def lorentz_helper (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0 → ℝ≥0∞ :=
  eLorentzNorm' f p q μ ^ (1 - q.toReal) •
    (fun (t : ℝ≥0) ↦ (t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) ^ (q.toReal - 1))

lemma eLpNorm_lorentz_helper (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  (one_le_q : 1 ≤ q) (q_ne_top : q ≠ ⊤)
  (hf : eLorentzNorm' f p q μ ≠ 0) (hf' : eLorentzNorm' f p q μ ≠ ⊤) :
    eLpNorm (lorentz_helper f p q μ) q.conjExponent = 1 := by
  have q_ne_zero : q ≠ 0 := by aesop
  have q'_ne_zero : q.conjExponent ≠ 0 := (ENNReal.HolderConjugate.conjExponent one_le_q).symm.ne_zero
  by_cases q_ne_one : q = 1
  · unfold lorentz_helper
    rw [q_ne_one]
    simp only [ENNReal.toReal_one, sub_self, ENNReal.rpow_zero, ENNReal.toReal_inv, inv_one,
      one_smul]
    convert eLpNorm_exponent_top
    · exact ENNReal.HolderConjugate.conjExponent_eq
    rw [eLpNormEssSup_const _ (NeZero.ne volume)]
    simp
  have q_sub_one : ¬q - 1 = 0 := by
    rw [tsub_eq_zero_iff_le]
    contrapose! q_ne_one
    exact le_antisymm q_ne_one one_le_q
  have q'_ne_top : q.conjExponent ≠ ⊤ := (ENNReal.HolderConjugate.conjExponent one_le_q).symm.ne_top_iff_ne_one.mpr q_ne_one
  unfold lorentz_helper
  rw [eLpNorm_const_smul''' (by fun_prop)]
  rw [eLorentzNorm'_eq' p_ne_zero p_ne_top, eLpNorm_eq_lintegral_rpow_enorm_toReal q_ne_zero q_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal q'_ne_zero q'_ne_top] at *
  simp only [ENNReal.toReal_inv, enorm_eq_self, one_div] at *
  rw [← ENNReal.rpow_mul]
  simp_rw [← ENNReal.rpow_mul]
  have : ((q.toReal - 1) * q.conjExponent.toReal) = q.toReal := by
    rw [ENNReal.conjExponent, ENNReal.toReal_add (by simp)
          (by simp only [ne_eq, ENNReal.inv_eq_top]; assumption),
        ENNReal.toReal_inv, ENNReal.toReal_sub_of_le one_le_q q_ne_top]
    simp only [ENNReal.toReal_one]
    rw [mul_add, mul_one, mul_inv_cancel₀, sub_add_cancel]
    contrapose! q_ne_one
    rw [sub_eq_zero] at q_ne_one
    rw [← ENNReal.ofReal_toReal q_ne_top, q_ne_one, ENNReal.ofReal_one]
  rw [this]
  rw [← ENNReal.rpow_add]
  · convert ENNReal.rpow_zero
    rw [ENNReal.conjExponent, ENNReal.toReal_add (by simp)
          (by simp only [ne_eq, ENNReal.inv_eq_top]; assumption),
        ENNReal.toReal_inv, ENNReal.toReal_sub_of_le one_le_q q_ne_top]
    simp only [ENNReal.toReal_one]
    grind
  · contrapose! hf
    rw [hf, ENNReal.zero_rpow_of_pos]
    exact inv_pos.mpr (ENNReal.toReal_pos q_ne_zero q_ne_top)
  · contrapose! hf'
    rw [hf', ENNReal.top_rpow_of_pos]
    exact inv_pos.mpr (ENNReal.toReal_pos q_ne_zero q_ne_top)


theorem antitone_rpow_inv_sub_inv (q_le_p : q ≤ p) (q_zero : q ≠ 0) :
    Antitone fun (x : ℝ≥0) ↦ (ENNReal.ofNNReal x) ^ (p.toReal⁻¹ - q.toReal⁻¹) := by
  have p_zero : p ≠ 0 := by
    aesop
  intro x y h
  simp only
  apply ENNReal.rpow_le_rpow_of_nonpos _ (by simpa)
  simp only [tsub_le_iff_right, zero_add]
  by_cases p_top : p = ⊤
  · rw [p_top]
    simp
  have q_top : q ≠ ⊤ := by
    aesop
  rw [inv_le_inv₀]
  · rwa [ENNReal.toReal_le_toReal q_top p_top]
  · exact ENNReal.toReal_pos p_zero p_top
  · exact ENNReal.toReal_pos q_zero q_top

lemma antitone_lorentz_helper (hq : 1 ≤ q) (q_le_p : q ≤ p) (p_top : p ≠ ⊤) :
    Antitone (lorentz_helper f p q μ) := by
  intro x y h
  unfold lorentz_helper
  simp only [ENNReal.toReal_inv, Pi.smul_apply, smul_eq_mul]
  gcongr 2
  · simp only [sub_nonneg]
    apply ENNReal.one_le_toReal hq (q_le_p.trans_lt p_top.lt_top)
  · gcongr 1
    · exact antitone_rpow_inv_sub_inv q_le_p (zero_lt_one.trans_le hq).ne' h
    · apply rearrangement_antitone' (by simpa)

@[measurability, fun_prop]
lemma lorentz_helper_measurable : Measurable (lorentz_helper f p q μ) := by
  unfold lorentz_helper
  fun_prop

lemma eLorentzNorm'_eq_lintegral_lorentz_helper_mul (p_ne_zero : p ≠ 0) (p_ne_top : p ≠ ⊤)
  (hq : 1 ≤ q) (q_ne_top : q ≠ ⊤) (f_ne_top : eLorentzNorm' f p q μ ≠ ⊤) :
    eLorentzNorm' f p q μ
      = eLpNorm (lorentz_helper f p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) 1 := by
  unfold lorentz_helper
  simp only [Algebra.smul_mul_assoc]
  rw [eLpNorm_const_smul''' (by fun_prop), Pi.mul_def]
  conv =>
    rhs
    congr
    rfl
    congr
    intro t
    rw [mul_comm]
    congr
    rw [← ENNReal.rpow_one (_ * rearrangement _ _ _)]
  conv =>
    rhs
    congr
    rfl
    congr
    intro t
    rw [← ENNReal.rpow_add_of_nonneg, add_sub_cancel]
    rfl
    exact zero_le_one
    tactic =>
      simp only [sub_nonneg]
      rw [← ENNReal.ofReal_le_iff_le_toReal q_ne_top]
      simpa
  conv =>
    rhs
    congr; rfl
    congr
    intro t
    congr
    rw [← enorm_eq_self (_ * _)]
  rw [eLpNorm_enorm_rpow _ (ENNReal.toReal_pos (by aesop) q_ne_top)]
  rw [one_mul, ENNReal.ofReal_toReal q_ne_top]
  rw [← eLorentzNorm'_eq' p_ne_zero p_ne_top, ← ENNReal.rpow_add_of_add_pos f_ne_top _ _ (by simp)]
  simp

open ENNReal in
theorem eLorentzNorm_add_le [ContinuousAdd ε] (one_le_q : 1 ≤ q) (q_le_p : q ≤ p)
     (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
      eLorentzNorm (f + g) p q μ ≤ eLorentzNorm f p q μ + eLorentzNorm g p q μ := by
  unfold eLorentzNorm
  split_ifs with p_zero p_top q_zero q_top
  · simp
  · simp
  · exact eLpNormEssSup_add_le
  · rw [← mul_add]
    gcongr
    exact eLpNormEssSup_add_le
  have q_top : q ≠ ⊤ := by aesop
  by_cases hfg : eLorentzNorm' (f + g) p q μ = 0
  · rw [hfg]
    simp
  by_cases hfg' : eLorentzNorm' (f + g) p q μ = ⊤
  · have := eLorentzNorm_add_le'' (p := p) (q := q) (f := f) (g := g) (μ := μ)
    rw [eLorentzNorm_eq_eLorentzNorm' p_zero p_top,
        eLorentzNorm_eq_eLorentzNorm' p_zero p_top,
        eLorentzNorm_eq_eLorentzNorm' p_zero p_top, hfg'] at this
    simp only [top_le_iff] at this
    rw [mul_eq_top] at this
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · rw [h]
      simp
    · contrapose! h
      apply mul_ne_top (by simp) (LpAddConst_lt_top _).ne
  rw [eLorentzNorm'_eq_lintegral_lorentz_helper_mul p_zero p_top one_le_q q_top hfg']
  calc _
    _ ≤ eLpNorm (lorentz_helper (f + g) p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * (rearrangement f t μ + rearrangement g t μ)) 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
      simp only [toReal_inv, Pi.mul_apply, enorm_eq_self]
      simp_rw [← mul_assoc]
      apply lintegral_antitone_mul_le (by fun_prop) (by fun_prop)
      · intro t
        apply (le_lintegral_add _ _).trans'
        have := lintegral_rearrangement_add_rearrangement_le_add_lintegral hf hg (t := t)
        rw [setLIntegral_ennreal_eq_setLintegral_of_nnreal measurableSet_Iio,
            setLIntegral_ennreal_eq_setLintegral_of_nnreal measurableSet_Iio,
            setLIntegral_ennreal_eq_setLintegral_of_nnreal measurableSet_Iio] at this
        convert this <;> aesop
      · apply Antitone.mul' (antitone_lorentz_helper one_le_q q_le_p p_top) (antitone_rpow_inv_sub_inv q_le_p (zero_lt_one.trans_le one_le_q).ne')
    _ ≤ eLpNorm (lorentz_helper (f + g) p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) 1
        + eLpNorm (lorentz_helper (f + g) p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement g t μ) 1 := by
      apply (eLpNorm_add_le (by fun_prop) (by fun_prop) le_rfl).trans'
      apply le_of_eq
      congr
      rw [← mul_add]
      congr with t
      simp
      ring
    _ ≤ eLpNorm (lorentz_helper (f + g) p q μ) q.conjExponent * eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) q
        + eLpNorm (lorentz_helper (f + g) p q μ) q.conjExponent * eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement g t μ) q := by
      gcongr <;>
      · apply eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm' (by fun_prop) (by fun_prop) (HolderConjugate.conjExponent one_le_q).symm
    _ = eLorentzNorm' f p q μ + eLorentzNorm' g p q μ := by
      rw [eLpNorm_lorentz_helper p_zero p_top one_le_q q_top hfg hfg', one_mul, one_mul,
        ← eLorentzNorm'_eq' p_zero p_top, ← eLorentzNorm'_eq' p_zero p_top]

/-- A constant for the inequality `‖f + g‖_{L^{p,q}} ≤ C * (‖f‖_{L^{p,q}} + ‖g‖_{L^{p,q}})`. It is equal to `1`
if `p = 0` or `1 ≤ r ≤ p` and `2^(1/p) * LpAddConst r` else. -/
noncomputable def LorentzAddConst (p r : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 ∨ r ∈ Set.Icc 1 p then 1 else 2 ^ p.toReal⁻¹ * LpAddConst r

theorem LorentzAddConst_of_one_le (hr : q ∈ Set.Icc 1 p) : LorentzAddConst p q = 1 := by
  rw [LorentzAddConst, if_pos]
  right
  assumption

theorem LorentzAddConst_zero : LorentzAddConst 0 q = 1 := by
  rw [LorentzAddConst, if_pos]
  left
  rfl

theorem LorentzAddConst_lt_top : LorentzAddConst p q < ∞ := by
  rw [LorentzAddConst]
  split_ifs
  · exact ENNReal.one_lt_top
  · apply ENNReal.mul_lt_top _ (LpAddConst_lt_top _)
    exact ENNReal.rpow_lt_top_of_nonneg (by simp) (by norm_num)

lemma eLorentzNorm_add_le' [ContinuousAdd ε] (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLorentzNorm (f + g) p q μ ≤ LorentzAddConst p q * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  unfold LorentzAddConst
  split_ifs with h
  · rcases h with p_zero | hr
    · simp [p_zero]
    rw [one_mul]
    exact eLorentzNorm_add_le hr.1 hr.2 hf hg
  · apply eLorentzNorm_add_le''

lemma eLorentzNorm_add_lt_top [ContinuousAdd ε] (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    eLorentzNorm (f + g) p q μ < ⊤ := by
  calc
    eLorentzNorm (f + g) p q μ ≤ LorentzAddConst p q * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) :=
      eLorentzNorm_add_le' hf.1 hg.1
    _ < ∞ := by
      apply ENNReal.mul_lt_top LorentzAddConst_lt_top
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

lemma MemLorentz.add [ContinuousAdd ε] (hf : MemLorentz f p q μ)
    (hg : MemLorentz g p q μ) : MemLorentz (f + g) p q μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, eLorentzNorm_add_lt_top hf hg⟩

--currently unused
open ENNReal in
theorem eLorentzNorm_add_le_of_disjoint_support (h : Disjoint f.support g.support)
  (hg : AEStronglyMeasurable g μ) :
    eLorentzNorm (f + g) p q μ
      ≤ (LpAddConst p) * (LpAddConst q) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  unfold eLorentzNorm
  have : eLpNormEssSup (f + g) μ ≤ LpAddConst p * LpAddConst q * (eLpNormEssSup f μ + eLpNormEssSup g μ) := by
    apply eLpNormEssSup_add_le.trans
    nth_rw 1 [← one_mul (_ + _)]
    gcongr
    rw [← one_mul 1]
    gcongr <;> exact one_le_LpAddConst
  split_ifs with p_zero p_top q_zero q_top
  · simp
  · simp
  · exact this
  · rw [← mul_add, ← mul_assoc, mul_comm _ ⊤, mul_assoc]
    gcongr
  · unfold eLorentzNorm'
    rw [← mul_add, ← mul_assoc, mul_comm (LpAddConst _ * _), mul_assoc]
    gcongr
    rw [mul_comm (LpAddConst _), mul_assoc, mul_add,
        ← eLpNorm_const_smul'' (LpAddConst_lt_top _).ne,
        ← eLpNorm_const_smul'' (LpAddConst_lt_top _).ne]
    apply (eLpNorm_add_le' (by fun_prop) (by fun_prop) _).trans'
    apply eLpNorm_mono_enorm
    intro t
    simp only [toReal_inv, enorm_eq_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_add, ← mul_add, ← mul_assoc, mul_comm (LpAddConst _), mul_assoc]
    gcongr
    apply (ENNReal.rpow_add_le_mul_rpow_add_rpow'' _ _ ).trans_eq'
    congr
    rw [distribution_add h hg]

end MeasureTheory
