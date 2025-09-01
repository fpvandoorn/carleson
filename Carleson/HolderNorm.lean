import Mathlib.Topology.MetricSpace.Holder

open Set Metric Function ENNReal
open scoped NNReal

/-!
# L^∞-normalized t-Hölder norm

This file defines the L^∞-normalized t-Hölder norm, which probably in some form should end up in Mathlib.
Lemmas about this norm that are proven in Carleson are collected here.

TODO: Assess Mathlib-readiness, complete basic results, optimize imports.
-/

noncomputable section

section Def

variable {𝕜 X : Type*} [PseudoMetricSpace X] [NormedField 𝕜]

/-- the L^∞-normalized t-Hölder norm. Defined in ℝ≥0∞ to avoid sup-related issues. -/
def iHolENorm (φ : X → 𝕜) (x₀ : X) (R : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (⨆ (x ∈ ball x₀ R), ‖φ x‖ₑ) + (ENNReal.ofReal R) ^ t *
    ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), (‖φ x - φ y‖ₑ / (edist x y) ^ t)

/-- The `NNReal` version of the L^∞-normalized t-Hölder norm, `iHolENorm`. -/
def iHolNNNorm (φ : X → 𝕜) (x₀ : X) (R : ℝ) (t : ℝ) : ℝ≥0 :=
  (iHolENorm φ x₀ R t).toNNReal

end Def

section iHolENorm

variable {X 𝕜 : Type*} {x z : X} {R t : ℝ} {φ : X → 𝕜}
variable [MetricSpace X] [NormedField 𝕜]

lemma enorm_le_iHolENorm_of_mem (hx : x ∈ ball z R) : ‖φ x‖ₑ ≤ iHolENorm φ z R t := by
  apply le_trans _ le_self_add
  simp only [le_iSup_iff, iSup_le_iff]
  tauto

lemma HolderOnWith.of_iHolENorm_ne_top (ht : 0 ≤ t) (hφ : iHolENorm φ z R t ≠ ⊤) :
    HolderOnWith (iHolNNNorm φ z R t / R.toNNReal ^ t) t.toNNReal φ (ball z R) := by
  intro x hx y hy
  have hR : 0 < R := by
    simp only [mem_ball] at hx
    apply dist_nonneg.trans_lt hx
  rcases eq_or_ne x y with rfl | hne
  · simp
  have : (ENNReal.ofReal R) ^ t * (‖φ x - φ y‖ₑ / (edist x y) ^ t) ≤ iHolENorm φ z R t := calc
    _ ≤ (ENNReal.ofReal R) ^ t *
        ⨆ (x ∈ ball z R) (y ∈ ball z R) (_ : x ≠ y), (‖φ x - φ y‖ₑ / (edist x y) ^ t) := by
      gcongr
      simp only [ne_eq, le_iSup_iff, iSup_le_iff]
      tauto
    _ ≤ _ := le_add_self
  rw [edist_eq_enorm_sub, ENNReal.coe_div (by simp [hR]), iHolNNNorm, coe_toNNReal hφ,
    ← ENNReal.div_le_iff_le_mul (by simp [hne]) (by simp [edist_ne_top]),
    ENNReal.le_div_iff_mul_le (by simp [hR]) (by simp)]
  apply this.trans_eq'
  rw [ENNReal.coe_rpow_of_ne_zero (by simp [hR]), Real.coe_toNNReal t ht, ENNReal.ofReal, mul_comm]

lemma continuous_of_iHolENorm_ne_top (ht : 0 < t) (hφ : tsupport φ ⊆ ball z R)
    (h'φ : iHolENorm φ z R t ≠ ∞) :
    Continuous φ :=
  HolderOnWith.of_iHolENorm_ne_top ht.le h'φ |>.continuousOn (by simp [ht])
    |>.continuous_of_tsupport_subset isOpen_ball hφ

lemma continuous_of_iHolENorm_ne_top' (ht : 0 < t) (hφ : support φ ⊆ ball z R)
    (h'φ : iHolENorm φ z (2 * R) t ≠ ∞) :
    Continuous φ := by
  rcases le_or_gt R 0 with hR | hR
  · have : support φ ⊆ ∅ := by rwa [ball_eq_empty.2 hR] at hφ
    simp only [subset_empty_iff, support_eq_empty_iff] at this
    simp only [this]
    exact continuous_const
  apply HolderOnWith.of_iHolENorm_ne_top ht.le h'φ |>.continuousOn (by simp [ht])
    |>.continuous_of_tsupport_subset isOpen_ball
  apply (closure_mono hφ).trans (closure_ball_subset_closedBall.trans ?_)
  exact closedBall_subset_ball (by linarith)

section iHolNNNorm

lemma norm_le_iHolNNNorm_of_mem (hφ : iHolENorm φ z R t ≠ ⊤) (hx : x ∈ ball z R) :
    ‖φ x‖ ≤ iHolNNNorm φ z R t :=
  (ENNReal.toReal_le_toReal (by simp) hφ).2 (enorm_le_iHolENorm_of_mem hx)

lemma norm_le_iHolNNNorm_of_subset (hφ : iHolENorm φ z R t ≠ ⊤) (h : support φ ⊆ ball z R) :
    ‖φ x‖ ≤ iHolNNNorm φ z R t := by
  by_cases hx : x ∈ ball z R
  · apply norm_le_iHolNNNorm_of_mem hφ hx
  · have : x ∉ support φ := fun a ↦ hx (h a)
    simp [notMem_support.mp this]

end iHolNNNorm

end iHolENorm
