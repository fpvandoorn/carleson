import Carleson.Defs
import Mathlib.Tactic.Rify

open ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma calculation_1 (s : ℤ) : 4 * (D : ℝ) ^ (-2 : ℝ) * ↑D ^ (s + 3) = 4 * ↑D ^ (s + 1) := by
  have D_pos : (0 : ℝ) < D := defaultD_pos a
  calc 4 * (D : ℝ) ^ (-2 : ℝ) * ↑D ^ (s + 3)
  _ = 4 * (↑D ^ (-2 : ℝ) * ↑D ^ (s + 3)) := by
    ring
  _ = 4 * ↑D ^ (-2 + (s + 3)) := by
    congr
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-2)) (z := (s + 3)) D_pos
    rw_mod_cast [pow_th]
  _ = 4 * ↑D ^ (s + 1) := by
    ring_nf

lemma calculation_2 (s : ℤ) : ((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s + 3) = 8⁻¹ * ↑D ^ s := by
  have D_pos : (0 : ℝ) < D := defaultD_pos a
  calc (8 : ℝ)⁻¹ * (D : ℝ) ^ (-3 : ℝ) * ↑D ^ (s + 3)
  _ = (8 : ℝ)⁻¹ * (↑D ^ (-3 : ℝ) * ↑D ^ (s + 3)) := by
    ring
  _ = (8 : ℝ)⁻¹ * ↑D ^ (-3 + (s + 3)) := by
    congr
    have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-3)) (z := (s + 3)) D_pos
    rw_mod_cast [pow_th]
  _ = (8 : ℝ)⁻¹* ↑D ^ (s) := by
    norm_num
