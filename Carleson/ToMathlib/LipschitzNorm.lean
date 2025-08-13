import Mathlib.Analysis.RCLike.Basic

open Metric Function ENNReal
open scoped NNReal

/-!
# Inhomogeneous Lipschitz norm

This file defines the Lipschitz norm, which probably in some form should end up in Mathlib.
Lemmas about this norm that are proven in Carleson are collected here.

-/

noncomputable section

section Def

variable {𝕜 X : Type*} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖ϕ x - ϕ y‖ₑ / edist x y

/-- The `NNReal` version of the inhomogeneous Lipschitz norm on a ball, `iLipENorm`. -/
def iLipNNNorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0 :=
  (iLipENorm ϕ x₀ R).toNNReal

end Def

section iLipENorm

variable {𝕜 X : Type*} {x z : X} {R : ℝ} {C C' : ℝ≥0} {ϕ : X → 𝕜}
variable [MetricSpace X] [NormedField 𝕜]

lemma iLipENorm_le_add (h : ∀ x ∈ ball z R, ‖ϕ x‖ ≤ C)
    (h' : ∀ x ∈ ball z R, ∀ x' ∈ ball z R, x ≠ x' → ‖ϕ x - ϕ x'‖ ≤ C' * dist x x' / R) :
    iLipENorm ϕ z R ≤ C + C' := by
  apply add_le_add
  · simp only [iSup_le_iff, enorm_le_coe]
    exact h
  · apply ENNReal.mul_le_of_le_div'
    simp only [ne_eq, iSup_le_iff]
    intro x hx x' hx' hne
    have hR : 0 < R := pos_of_mem_ball hx
    have W := h' x hx x' hx' hne
    rw [ENNReal.div_le_iff (by simpa only [ne_eq, edist_eq_zero] using hne) (edist_ne_top x x')]
    convert ENNReal.ofReal_le_ofReal W
    · exact (ofReal_norm_eq_enorm (ϕ x - ϕ x')).symm
    · rw [ENNReal.ofReal_div_of_pos hR, ENNReal.ofReal_mul NNReal.zero_le_coe, edist_dist,
        ENNReal.mul_div_right_comm, ENNReal.ofReal_coe_nnreal]

lemma iLipENorm_le (h : ∀ x ∈ ball z R, ‖ϕ x‖ ≤ 2⁻¹ * C)
    (h' : ∀ x ∈ ball z R, ∀ x' ∈ ball z R, x ≠ x' → ‖ϕ x - ϕ x'‖ ≤ 2⁻¹ * C * dist x x' / R) :
    iLipENorm ϕ z R ≤ C := by
  apply (iLipENorm_le_add (C := 2⁻¹ * C) (C' := 2⁻¹ * C) h h').trans_eq
  simp [← add_mul, ENNReal.inv_two_add_inv_two]

lemma enorm_le_iLipENorm_of_mem (hx : x ∈ ball z R) :
    ‖ϕ x‖ₑ ≤ iLipENorm ϕ z R := by
  apply le_trans _ le_self_add
  simp only [le_iSup_iff, iSup_le_iff]
  tauto

lemma LipschitzOnWith.of_iLipENorm_ne_top (hϕ : iLipENorm ϕ z R ≠ ⊤) :
    LipschitzOnWith (iLipNNNorm ϕ z R / R.toNNReal) ϕ (ball z R) := by
  intro x hx y hy
  have hR : 0 < R := by
    simp only [mem_ball] at hx
    apply dist_nonneg.trans_lt hx
  rcases eq_or_ne x y with rfl | hne
  · simp
  have : (ENNReal.ofReal R) * (‖ϕ x - ϕ y‖ₑ / edist x y) ≤ iLipENorm ϕ z R := calc
      (ENNReal.ofReal R) * (‖ϕ x - ϕ y‖ₑ / (edist x y))
    _ ≤ (ENNReal.ofReal R) *
        ⨆ (x ∈ ball z R) (y ∈ ball z R) (_ : x ≠ y), (‖ϕ x - ϕ y‖ₑ / edist x y) := by
      gcongr
      simp only [ne_eq, le_iSup_iff, iSup_le_iff]
      tauto
    _ ≤ _ := le_add_self
  rw [edist_eq_enorm_sub, ENNReal.coe_div (by simp [hR]), iLipNNNorm, coe_toNNReal hϕ]
  rw [← ENNReal.div_le_iff_le_mul]; rotate_left
  · have : edist x y ≠ 0 := by simp [hne]
    simp [this]
  · simp [edist_ne_top]
  rw [ENNReal.le_div_iff_mul_le]; rotate_left
  · simp [hR]
  · simp
  convert this using 1
  simp only [ENNReal.ofReal, mul_comm]

lemma continuous_of_iLipENorm_ne_top {z : X} {R : ℝ}
    {ϕ : X → 𝕜} (hϕ : tsupport ϕ ⊆ ball z R) (h'ϕ : iLipENorm ϕ z R ≠ ⊤) :
    Continuous ϕ :=
  (LipschitzOnWith.of_iLipENorm_ne_top h'ϕ).continuousOn.continuous_of_tsupport_subset
    isOpen_ball hϕ

section iLipNNNorm

lemma norm_le_iLipNNNorm_of_mem (hϕ : iLipENorm ϕ z R ≠ ⊤) (hx : x ∈ ball z R) :
    ‖ϕ x‖ ≤ iLipNNNorm ϕ z R :=
  (ENNReal.toReal_le_toReal (by simp) hϕ).2 (enorm_le_iLipENorm_of_mem hx)

lemma norm_le_iLipNNNorm_of_subset (hϕ : iLipENorm ϕ z R ≠ ⊤) (h : support ϕ ⊆ ball z R) :
    ‖ϕ x‖ ≤ iLipNNNorm ϕ z R := by
  by_cases hx : x ∈ ball z R
  · apply norm_le_iLipNNNorm_of_mem hϕ hx
  · have : x ∉ support ϕ := fun a ↦ hx (h a)
    simp [notMem_support.mp this]

end iLipNNNorm

end iLipENorm
