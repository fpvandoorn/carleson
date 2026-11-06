module

public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
public import Carleson.ToMathlib.RealInterpolation.Misc

/-!
# Monotonicity of the Lorentz seminorm in the second exponent

For `0 < r₁ ≤ r₂`, the Lorentz space `L^{p,r₁}` is contained in `L^{p,r₂}`.
In particular, `L^{p,q} ⊆ L^p` for `q ≤ p`.
-/

-- Upstreaming status: the current qualitative proof relies on `memLp_of_memLp_le_of_memLp_ge`
-- from `RealInterpolation.Misc`; it should be replaced by the quantitative inequality
-- `‖f‖_{p,r₂} ≤ C ‖f‖_{p,r₁}` (Grafakos, Prop. 1.4.10) before upstreaming.

public section

noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology

variable {α ε : Type*} {m0 : MeasurableSpace α} {p q : ℝ≥0∞} {μ : Measure α} [ENorm ε]

namespace MeasureTheory

-- TODO: could maybe be strengthened to ↔
lemma MemLorentz_of_MemLorentz_ge [TopologicalSpace ε]
    {r₁ r₂ : ℝ≥0∞} (r₁_pos : 0 < r₁) (r₁_le_r₂ : r₁ ≤ r₂) {f : α → ε} (hf : MemLorentz f p r₁ μ) :
    MemLorentz f p r₂ μ := by
  have meas_f := hf.aestronglyMeasurable
  rw [memLorentz_iff, eLorentzNorm, ite_eq_left meas_f] at hf ⊢
  split_ifs at * with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.zero_lt_top
  · exfalso
    exact r₁_pos.ne h₆.symm
  · exact hf
  · rw [ENNReal.top_mul'] at hf
    split_ifs at hf with h
    · rwa [h]
    · exfalso
      exact (lt_self_iff_false ⊤).mp hf
  · exfalso
    exact r₁_pos.ne h₈.symm
  · exfalso
    rw [h₉, top_le_iff] at r₁_le_r₂
    exact h₅ r₁_le_r₂
  · exact hf
  · by_cases r₁_top : r₁ = ∞
    · convert hf
      rw [r₁_top, top_le_iff] at r₁_le_r₂
      rw [r₁_top, r₁_le_r₂]
    --Now the only interesting case
    have measurable_mul_distribution_rpow : Measurable fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal := by measurability
    unfold eLorentzNorm' at hf
    rw [ENNReal.mul_lt_top_iff] at hf
    rcases hf with ⟨_, norm_lt_top⟩ | p_zero | norm_zero
    · wlog r₂_top : r₂ = ⊤ generalizing r₂
      · have memLp_top : MemLp (fun (t : ℝ≥0) ↦ ↑t * distribution f (↑t) μ ^ p⁻¹.toReal) ⊤
                          (volume.withDensity fun t ↦ (↑t)⁻¹) := by
          rw [memLp_iff]
          have := this le_top rfl
          unfold eLorentzNorm' at this
          rw [ENNReal.mul_lt_top_iff] at this
          rcases this with ⟨_, norm_lt_top⟩ | p_zero | norm_zero
          · exact norm_lt_top
          · --TODO: duplicate from below
            exfalso
            rw [ENNReal.rpow_eq_zero_iff] at p_zero
            rcases p_zero with ⟨p_zero, _⟩ | ⟨p_top, _⟩
            · exact h₀ p_zero
            · exact h₁ p_top
          · rw [norm_zero]
            exact ENNReal.zero_lt_top
        unfold eLorentzNorm'
        rw [ENNReal.mul_lt_top_iff]
        left
        use ENNReal.rpow_lt_top_of_nonneg (by simp) h₁
        exact memLp_of_memLp_le_of_memLp_ge r₁_pos ⟨r₁_le_r₂, le_top⟩ norm_lt_top memLp_top
      /- Hardest part -/
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal r₁_pos.ne' r₁_top (by fun_prop),
          lintegral_withDensity_eq_lintegral_mul₀ (by measurability) (by fun_prop),
          lintegral_nnreal_eq_lintegral_toNNReal_Ioi] at norm_lt_top
      simp only [ENNReal.toReal_inv, enorm_eq_self, Pi.mul_apply, one_div] at norm_lt_top
      rw [r₂_top, eLorentzNorm'_exponent_top]
      rw [iSup_lt_iff]
      have toReal_r₁_pos := ENNReal.toReal_pos r₁_pos.ne' r₁_top
      have : r₁ ^ r₁.toReal⁻¹ < ∞ := ENNReal.rpow_lt_top_of_nonneg (by simp) r₁_top
      have norm_lt_top' := ENNReal.mul_lt_top norm_lt_top this
      exists _, norm_lt_top'
      intro s
      rw [← ENNReal.div_le_iff_le_mul (by left; positivity) (by left; exact this.ne)] --TODO: improve this
      calc _
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (↑s / r₁ ^ r₁.toReal⁻¹) := by
          rw [mul_comm, mul_div_assoc]
        _ = distribution f (↑s) μ ^ p.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          rw [ENNReal.div_rpow_of_nonneg,
              ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne', r₁_top⟩)]
          simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ * (s ^ r₁.toReal / r₁) ^ r₁.toReal⁻¹ := by
          congr 1
          · rw [ENNReal.rpow_mul, ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨r₁_pos.ne', r₁_top⟩)]
        _ = (distribution f (↑s) μ ^ (p.toReal⁻¹ * r₁.toReal)) ^ r₁.toReal⁻¹ *
              (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, ENNReal.ofReal (x ^ (r₁.toReal - 1))) ^ r₁.toReal⁻¹:= by
          congr
          rw [lintegral_rpow_of_gt NNReal.zero_le_coe (by linarith), ENNReal.ofReal_div_of_pos (by simpa),
              ← ENNReal.ofReal_rpow_of_nonneg NNReal.zero_le_coe (by linarith)]
          ring_nf
          rw [ENNReal.ofReal_toReal r₁_top, ENNReal.ofReal, Real.toNNReal_coe]
        _ = (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal ^ r₁.toReal * distribution f s μ ^ (p.toReal⁻¹ * r₁.toReal))) ^ r₁.toReal⁻¹ := by
          rw [← ENNReal.mul_rpow_of_nonneg, ← lintegral_const_mul]
          · congr 1
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro x hx
            simp only
            rw [mul_comm, ← mul_assoc]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_pos hx.1, ← ENNReal.rpow_neg_one,
              ← ENNReal.rpow_add _ _ (by simp [hx.1]) (by simp), neg_add_eq_sub]
            congr
          · measurability
          · simp only [inv_nonneg, ENNReal.toReal_nonneg]
        _ = (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal * distribution f s μ ^ p.toReal⁻¹) ^ r₁.toReal) ^ r₁.toReal⁻¹ := by
          congr with x
          rw [ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul]
          exact ENNReal.toReal_nonneg
        _ ≤ (∫⁻ (x : ℝ) in Set.Ioo 0 s.toReal, (↑x.toNNReal)⁻¹ *
              (↑x.toNNReal * distribution f (↑x.toNNReal) μ ^ p.toReal⁻¹) ^ r₁.toReal) ^ r₁.toReal⁻¹ := by
          apply ENNReal.rpow_le_rpow _ (by simp only [inv_nonneg, ENNReal.toReal_nonneg])
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ht
          gcongr
          exact Real.toNNReal_le_iff_le_coe.mpr ht.2.le
        _ ≤ (∫⁻ (x : ℝ) in Set.Ioi 0, (↑x.toNNReal)⁻¹ * (↑x.toNNReal * distribution f (↑x.toNNReal) μ ^ p.toReal⁻¹) ^ r₁.toReal) ^
            r₁.toReal⁻¹ := by
          gcongr
          exact Set.Ioo_subset_Ioi_self
    · exfalso
      rw [ENNReal.rpow_eq_zero_iff] at p_zero
      rcases p_zero with ⟨p_zero, _⟩ | ⟨p_top, _⟩
      · exact h₀ p_zero
      · exact h₁ p_top
    · unfold eLorentzNorm'
      rw [ENNReal.mul_lt_top_iff]
      right; right
      rw [eLpNorm_eq_zero_iff r₁_pos.ne'] at norm_zero
      rwa [eLpNorm_eq_zero_iff (r₁_pos.trans_le r₁_le_r₂).ne']


section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

lemma MemLorentz.memLp {f : α → ε} (hf : MemLorentz f p q μ) (h : q ∈ Set.Ioc 0 p) :
    MemLp f p μ := by
  rw [← MemLorentz_iff_MemLp]
  apply MemLorentz_of_MemLorentz_ge h.1 h.2 hf


end ESeminormedAddMonoid

end MeasureTheory
