import Carleson.DiscreteCarleson
import Carleson.TileExistence

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

theorem integrable_tile_sum_operator
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) {x : X} {s : ℤ} :
    Integrable fun y ↦ Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  simp_rw [mul_assoc, mul_comm (Ks s x _)]
  refine integrable_Ks_x (one_lt_D (X := X)) |>.bdd_mul ?_ ⟨1, fun y ↦ ?_⟩
  · exact hf.mul ((measurable_ofReal.comp (map_continuous (Q x)).measurable |>.sub
      measurable_const).const_mul I).cexp |>.aestronglyMeasurable
  · rw [norm_mul, ← one_mul 1]
    gcongr
    · exact le_trans (h2f y) (F.indicator_le_self' (by simp) y)
    · rw_mod_cast [mul_comm, norm_eq_abs, abs_exp_ofReal_mul_I]

/-- Lemma 4.0.3 -/
theorem tile_sum_operator [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
    {G' : Set X} (hG' : MeasurableSet G') (h2G' : 2 * volume G' ≤ volume G)
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hfg' : ∫⁻ x in G \ G', ‖∑' p, T p f x‖₊ ≤
      C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹) {x : X}
    (hx : x ∈ G \ G') :
    ∑ p : 𝔓 X, T p f x =
    ∑ s in Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  sorry

/- The constant used in Proposition 2.0.1 -/
def C2_0_1 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := C2_0_2 a q

lemma C2_0_1_pos : C2_0_1 a nnq > 0 := C2_0_2_pos

variable (X) in
theorem finitary_carleson : ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖∑ s in Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖₊ ≤
    C2_0_1 a nnq * (volume G) ^ (1 - q⁻¹) * (volume F) ^ q⁻¹ := by
  rcases discrete_carleson X with ⟨G', hG', h2G', hfG'⟩
  refine ⟨G', hG', h2G', fun f meas_f h2f ↦ le_of_eq_of_le ?_ (hfG' f meas_f h2f)⟩
  refine setLIntegral_congr_fun (measurableSet_G.diff hG') (ae_of_all volume fun x hx ↦ ?_)
  have : ∫⁻ (x : X) in G \ G', ‖∑' p : 𝔓 X, T p f x‖₊ ≤
      (C2_0_2 a nnq) * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
    convert (hfG' f meas_f h2f) using 5
    apply tsum_eq_sum
    simp_rw [Finset.mem_univ, not_true_eq_false, false_implies, implies_true]
  simp_rw [tile_sum_operator hG' h2G' meas_f h2f this hx, mul_sub, exp_sub, mul_div, div_eq_mul_inv,
    ← smul_eq_mul (a' := _⁻¹), integral_smul_const, ← Finset.sum_smul, nnnorm_smul]
  suffices ‖(cexp (I * ((Q x) x : ℂ)))⁻¹‖₊ = 1 by rw [this, mul_one]
  simp [← coe_eq_one, mul_comm I]
