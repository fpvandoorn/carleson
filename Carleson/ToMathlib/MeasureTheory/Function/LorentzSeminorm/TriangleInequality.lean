import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Defs


/-!
# Triangle inequality for `Lorentz`-seminorm

In this file we prove several versions of the triangle inequality for the `Lorentz` seminorm,
as well as simple corollaries.
-/

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {α ε : Type*} {m : MeasurableSpace α}
  [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {p q : ℝ≥0∞} {μ : Measure α} {f g : α → ε}


--TODO: move?
lemma eLpNorm_withDensity_scale_constant' {f : ℝ≥0 → ℝ≥0∞} (hf : AEStronglyMeasurable f) {p : ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0) :
  eLpNorm (fun t ↦ f (a * t)) p (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))
    = eLpNorm f p (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))  := by
  unfold eLpNorm
  split_ifs with p_zero p_top
  · rfl
  · --TODO: case p = ⊤
    sorry
  · symm
    rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
    rw [lintegral_withDensity_eq_lintegral_mul₀' (by measurability)
          (by apply aeMeasurable_withDensity_inv; apply AEMeasurable.pow_const; exact AEStronglyMeasurable.enorm hf),
        lintegral_withDensity_eq_lintegral_mul₀' (by measurability)
          (by apply aeMeasurable_withDensity_inv; apply AEMeasurable.pow_const; apply AEStronglyMeasurable.enorm; sorry)]
          --TODO: measurablility
    simp only [enorm_eq_self, Pi.mul_apply, one_div]
    rw [← lintegral_nnreal_scale_constant' h, ← lintegral_const_mul' _ _ (by simp)]
    have : ∀ {t : ℝ≥0}, (ENNReal.ofNNReal t)⁻¹ = a * (ENNReal.ofNNReal (a * t))⁻¹ := by
      intro t
      rw [ENNReal.coe_mul, ENNReal.mul_inv, ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
      · simpa
      · simp
      · right
        simp
      · left
        simp
    simp_rw [← mul_assoc, ← this]

open ENNReal in
theorem eLorentzNorm_add_le'' (hf : AEStronglyMeasurable f μ) :
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
      apply eLpNorm_add_le'
      · sorry --TODO: measurability
      · sorry --TODO: measurability
    _ = LpAddConst q * 2 ^ p.toReal⁻¹ * (eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * rearrangement f t μ) q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))
        + eLpNorm (fun (t : ℝ≥0) ↦ ↑t ^ p⁻¹.toReal * rearrangement g t μ) q (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))) := by
      rw [mul_assoc]
      congr
      rw [← eLpNorm_withDensity_scale_constant' (a := 2) sorry (by norm_num)] --TODO: measurability
      nth_rw 2 [← eLpNorm_withDensity_scale_constant' (a := 2) sorry (by norm_num)] --TODO: measurability
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

--TODO: move somewhere else, add the right measurability conditions on f and g
-- This is Theorem 4.19
theorem lintegral_antitone_mul_le {f g k : ℝ≥0 → ℝ≥0∞}
  (h : ∀ {t}, ∫⁻ s in Set.Iio t, f s ≤ ∫⁻ s in Set.Iio t, g s) (hk : Antitone k) :
    ∫⁻ s, k s * f s ≤ ∫⁻ s, k s * g s := by
  sorry --use: Lebesgue induction

noncomputable def lorentz_helper (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0 → ℝ≥0∞ :=
  eLorentzNorm' f p q μ ^ (1 - q.toReal) •
    (fun (t : ℝ≥0) ↦ (t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) ^ (q.toReal - 1))

--TODO: probably need some assumption on f
lemma eLpNorm_lorentz_helper :
    eLpNorm (lorentz_helper f p q μ) q.conjExponent = 1 := by
  sorry

theorem antitone_rpow_inv_sub_inv (q_le_p : q ≤ p) (p_zero : ¬p = 0) (p_top : ¬p = ⊤) :
    Antitone fun (x : ℝ≥0) ↦ (ENNReal.ofNNReal x) ^ (p.toReal⁻¹ - q.toReal⁻¹) := sorry

lemma antitone_lorentz_helper :
    Antitone (lorentz_helper f p q μ) := by
  sorry

--TODO: probably need some assumptions on f, p, r
lemma eLorentzNorm'_eq_lintegral_lorentz_helper_mul :
    eLorentzNorm' f p q μ
      = eLpNorm (lorentz_helper f p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) 1 := by
  --use : eLorentzNorm'_eq'
  sorry

open ENNReal in
theorem eLorentzNorm_add_le (one_le_q : 1 ≤ q) (q_le_p : q ≤ p)
    [NoAtoms μ] (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
      eLorentzNorm (f + g) p q μ ≤ eLorentzNorm f p q μ + eLorentzNorm g p q μ := by
  unfold eLorentzNorm
  split_ifs with p_zero p_top q_zero q_top
  · simp
  · simp
  · exact eLpNormEssSup_add_le
  · rw [← mul_add]
    gcongr
    exact eLpNormEssSup_add_le
  --rw [eLorentzNorm'_eq p_zero p_top, eLorentzNorm'_eq p_zero p_top, eLorentzNorm'_eq p_zero p_top]
  rw [eLorentzNorm'_eq_lintegral_lorentz_helper_mul]
  calc _
    _ ≤ eLpNorm (lorentz_helper (f + g) p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * (rearrangement f t μ + rearrangement g t μ)) 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
      simp only [toReal_inv, Pi.mul_apply, enorm_eq_self]
      simp_rw [← mul_assoc]
      apply lintegral_antitone_mul_le
      · intro t
        apply (le_lintegral_add _ _).trans'
        exact lintegral_rearrangement_add_rearrangement_le_add_lintegral hf hg
      · apply Antitone.mul' antitone_lorentz_helper (antitone_rpow_inv_sub_inv q_le_p p_zero p_top)
    _ ≤ eLpNorm (lorentz_helper (f + g) p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) 1
        + eLpNorm (lorentz_helper (f + g) p q μ * fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement g t μ) 1 := by
      apply (eLpNorm_add_le sorry sorry le_rfl).trans' --TODO: measurability
      apply le_of_eq
      congr
      rw [← mul_add]
      congr with t
      simp
      ring
    _ ≤ eLpNorm (lorentz_helper (f + g) p q μ) q.conjExponent * eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) q
        + eLpNorm (lorentz_helper (f + g) p q μ) q.conjExponent * eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement g t μ) q := by
      gcongr <;>
      · sorry
        --apply eLpNorm_le_eLpNorm_mul_eLpNorm
        --TODO: apply Hölder's inequality which does not seem to exist for enorm.
    _ = eLorentzNorm' f p q μ + eLorentzNorm' g p q μ := by
      rw [eLpNorm_lorentz_helper, one_mul, one_mul,
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

lemma eLorentzNorm_add_le' [NoAtoms μ] (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLorentzNorm (f + g) p q μ ≤ LorentzAddConst p q * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  unfold LorentzAddConst
  split_ifs with h
  · rcases h with p_zero | hr
    · simp [p_zero]
    rw [one_mul]
    exact eLorentzNorm_add_le hr.1 hr.2 hf hg
  · apply eLorentzNorm_add_le'' hf

lemma eLorentzNorm_add_lt_top [NoAtoms μ] (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    eLorentzNorm (f + g) p q μ < ⊤ := by
  calc
    eLorentzNorm (f + g) p q μ ≤ LorentzAddConst p q * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) :=
      eLorentzNorm_add_le' hf.1 hg.1
    _ < ∞ := by
      apply ENNReal.mul_lt_top LorentzAddConst_lt_top
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

lemma MemLorentz.add [NoAtoms μ] [ContinuousAdd ε] (hf : MemLorentz f p q μ)
    (hg : MemLorentz g p q μ) : MemLorentz (f + g) p q μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, eLorentzNorm_add_lt_top hf hg⟩

end MeasureTheory
