module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Carleson.Defs

@[expose] public section

open Metric Function ENNReal
open scoped NNReal

/-!
# Inhomogeneous Lipschitz norm

This file defines the Lipschitz norm, which probably in some form should end up in Mathlib.
Lemmas about this norm that are proven in Carleson are collected here.

TODO: Assess Mathlib-readiness, complete basic results, optimize imports.
-/

noncomputable section

section Def

variable {𝕜 X : Type*} [NormedField 𝕜] [PseudoMetricSpace X]

/-!
TODO The iLipENorm should be properly generalized to Mathlib standards.
Until then, it is defined in `Defs.lean` instead. See PR #493.

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm (φ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖φ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖φ x - φ y‖ₑ / edist x y
-/

/-- The `NNReal` version of the inhomogeneous Lipschitz norm on a ball, `iLipENorm`. -/
def iLipNNNorm (φ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0 :=
  (iLipENorm φ x₀ R).toNNReal

end Def

section iLipENorm

variable {𝕜 X : Type*} {x z : X} {R : ℝ} {C C' : ℝ≥0} {φ : X → 𝕜}
variable [MetricSpace X] [NormedField 𝕜]

lemma iLipENorm_le_add (h : ∀ x ∈ ball z R, ‖φ x‖ ≤ C)
    (h' : ∀ x ∈ ball z R, ∀ x' ∈ ball z R, x ≠ x' → ‖φ x - φ x'‖ ≤ C' * dist x x' / R) :
    iLipENorm φ z R ≤ C + C' := by
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
    · exact (ofReal_norm_eq_enorm (φ x - φ x')).symm
    · rw [ENNReal.ofReal_div_of_pos hR, ENNReal.ofReal_mul NNReal.zero_le_coe, edist_dist,
        ENNReal.mul_div_right_comm, ENNReal.ofReal_coe_nnreal]

lemma iLipENorm_le (h : ∀ x ∈ ball z R, ‖φ x‖ ≤ 2⁻¹ * C)
    (h' : ∀ x ∈ ball z R, ∀ x' ∈ ball z R, x ≠ x' → ‖φ x - φ x'‖ ≤ 2⁻¹ * C * dist x x' / R) :
    iLipENorm φ z R ≤ C := by
  apply (iLipENorm_le_add (C := 2⁻¹ * C) (C' := 2⁻¹ * C) h h').trans_eq
  simp [← add_mul, ENNReal.inv_two_add_inv_two]

lemma enorm_le_iLipENorm_of_mem (hx : x ∈ ball z R) :
    ‖φ x‖ₑ ≤ iLipENorm φ z R := by
  apply le_trans _ le_self_add
  simp only [le_iSup_iff, iSup_le_iff]
  tauto

lemma LipschitzOnWith.of_iLipENorm_ne_top (hφ : iLipENorm φ z R ≠ ⊤) :
    LipschitzOnWith (iLipNNNorm φ z R / R.toNNReal) φ (ball z R) := by
  intro x hx y hy
  have hR : 0 < R := by
    simp only [mem_ball] at hx
    apply dist_nonneg.trans_lt hx
  rcases eq_or_ne x y with rfl | hne
  · simp
  have : (ENNReal.ofReal R) * (‖φ x - φ y‖ₑ / edist x y) ≤ iLipENorm φ z R := calc
      (ENNReal.ofReal R) * (‖φ x - φ y‖ₑ / (edist x y))
    _ ≤ (ENNReal.ofReal R) *
        ⨆ (x ∈ ball z R) (y ∈ ball z R) (_ : x ≠ y), (‖φ x - φ y‖ₑ / edist x y) := by
      gcongr
      simp only [ne_eq, le_iSup_iff, iSup_le_iff]
      tauto
    _ ≤ _ := le_add_self
  rw [edist_eq_enorm_sub, ENNReal.coe_div (by simp [hR]), iLipNNNorm, coe_toNNReal hφ]
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
    {φ : X → 𝕜} (hφ : tsupport φ ⊆ ball z R) (h'φ : iLipENorm φ z R ≠ ⊤) :
    Continuous φ :=
  (LipschitzOnWith.of_iLipENorm_ne_top h'φ).continuousOn.continuous_of_tsupport_subset
    isOpen_ball hφ

section iLipNNNorm

lemma norm_le_iLipNNNorm_of_mem (hφ : iLipENorm φ z R ≠ ⊤) (hx : x ∈ ball z R) :
    ‖φ x‖ ≤ iLipNNNorm φ z R :=
  (ENNReal.toReal_le_toReal (by simp) hφ).2 (enorm_le_iLipENorm_of_mem hx)

lemma norm_le_iLipNNNorm_of_subset (hφ : iLipENorm φ z R ≠ ⊤) (h : support φ ⊆ ball z R) :
    ‖φ x‖ ≤ iLipNNNorm φ z R := by
  by_cases hx : x ∈ ball z R
  · apply norm_le_iLipNNNorm_of_mem hφ hx
  · have : x ∉ support φ := fun a ↦ hx (h a)
    simp [notMem_support.mp this]

end iLipNNNorm

end iLipENorm
