import Carleson.Discrete.MainTheorem
import Carleson.TileExistence

open MeasureTheory Measure NNReal Metric Complex Set Classical
open scoped ENNReal
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

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

section

variable [TileStructure Q D κ S o]

@[reducible] -- Used to simplify notation in the proof of `tile_sum_operator`
private def 𝔓X_s (s : ℤ) := (@Finset.univ (𝔓 X) _).filter (fun p ↦ 𝔰 p = s)

private lemma 𝔰_eq {s : ℤ} {p : 𝔓 X} (hp : p ∈ 𝔓X_s s) : 𝔰 p = s := by simpa using hp

private lemma 𝔓_biUnion : @Finset.univ (𝔓 X) _ = (Icc (-S : ℤ) S).toFinset.biUnion 𝔓X_s := by
  ext p
  refine ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ p⟩
  rw [Finset.mem_biUnion]
  refine ⟨𝔰 p, ?_, by simp⟩
  rw [toFinset_Icc, Finset.mem_Icc]
  exact range_s_subset ⟨𝓘 p, rfl⟩

private lemma sum_eq_zero_of_nmem_Icc {f : X → ℂ} {x : X} (s : ℤ)
    (hs : s ∈ (Icc (-S : ℤ) S).toFinset.filter (fun t ↦ t ∉ Icc (σ₁ x) (σ₂ x))) :
    ∑ i ∈ Finset.univ.filter (fun p ↦ 𝔰 p = s), carlesonOn i f x = 0 := by
  refine Finset.sum_eq_zero (fun p hp ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [mem_Icc, not_and, not_le, toFinset_Icc, Finset.mem_filter, Finset.mem_Icc] at hs
  rw [carlesonOn, Set.indicator_of_not_mem]
  simp only [E, Grid.mem_def, mem_Icc, sep_and, mem_inter_iff, mem_setOf_eq, not_and, not_le]
  exact fun _ ⟨_, h⟩ _ ↦ hp ▸ hs.2 (hp ▸ h)

lemma exists_Grid {x : X} (hx : x ∈ G) {s : ℤ} (hs : s ∈ (Icc (σ₁ x) (σ₂ x)).toFinset) :
    ∃ I : GridStructure.Grid X (defaultA a), GridStructure.s I = s ∧ x ∈ I := by
  have DS : (D : ℝ) ^ S = (D : ℝ) ^ (S : ℤ) := rfl
  have : x ∈ ball o (D ^ S / 4) := ProofData.G_subset hx
  sorry /- TODO(bump-4.13): fix proof, was
  rw [← c_topCube (X := X), DS, ← s_topCube (X := X)] at this
  have x_mem_topCube := ball_subset_Grid this
  by_cases hS : s = S -- Handle separately b/c `Grid_subset_biUnion`, as stated, doesn't cover `s=S`
  · exact ⟨topCube, by rw [s_topCube, hS], x_mem_topCube⟩
  have s_mem : s ∈ Ico (-S : ℤ) (GridStructure.s (X := X) topCube) :=
    have : s ∈ Icc (-S : ℤ) S := Icc_σ_subset_Icc_S (mem_toFinset.1 hs)
    ⟨this.1, s_topCube (X := X) ▸ lt_of_le_of_ne this.2 hS⟩
  simpa only [mem_iUnion, exists_prop] using Grid_subset_biUnion s s_mem x_mem_topCube -/

/-- Lemma 4.0.3 -/
theorem tile_sum_operator {G' : Set X} {f : X → ℂ}
    {x : X} (hx : x ∈ G \ G') : ∑ (p : 𝔓 X), carlesonOn p f x =
    ∑ s in Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  rw [𝔓_biUnion, Finset.sum_biUnion]; swap
  · exact fun s _ s' _ hss' A hAs hAs' p pA ↦ False.elim <| hss' (𝔰_eq (hAs pA) ▸ 𝔰_eq (hAs' pA))
  rw [← (Icc (-S : ℤ) S).toFinset.sum_filter_add_sum_filter_not (fun s ↦ s ∈ Icc (σ₁ x) (σ₂ x))]
  rw [Finset.sum_eq_zero sum_eq_zero_of_nmem_Icc, add_zero]
  refine Finset.sum_congr (Finset.ext fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩) (fun s hs ↦ ?_)
  · rw [Finset.mem_filter, ← mem_toFinset] at hs
    exact hs.2
  · rw [mem_toFinset] at hs
    rw [toFinset_Icc, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.2 (Icc_σ_subset_Icc_S hs), hs⟩
  · rcases exists_Grid hx.1 hs with ⟨I, Is, xI⟩
    obtain ⟨p, 𝓘pI, Qp⟩ : ∃ (p : 𝔓 X), 𝓘 p = I ∧ Q x ∈ Ω p := by simpa using biUnion_Ω ⟨x, rfl⟩
    have p𝔓Xs : p ∈ 𝔓X_s s := by simpa [𝔰, 𝓘pI]
    have : ∀ p' ∈ 𝔓X_s s, p' ≠ p → carlesonOn p' f x = 0 := by
      intro p' p'𝔓Xs p'p
      apply indicator_of_not_mem
      simp only [E, mem_setOf_eq, not_and]
      refine fun x_in_𝓘p' Qp' ↦ False.elim ?_
      have s_eq := 𝔰_eq p𝔓Xs ▸ 𝔰_eq p'𝔓Xs
      have : ¬ Disjoint (𝓘 p' : Set X) (𝓘 p : Set X) := not_disjoint_iff.2 ⟨x, x_in_𝓘p', 𝓘pI ▸ xI⟩
      exact disjoint_left.1 (disjoint_Ω p'p <| Or.resolve_right (eq_or_disjoint s_eq) this) Qp' Qp
    rw [Finset.sum_eq_single_of_mem p p𝔓Xs this]
    have xEp : x ∈ E p :=
      ⟨𝓘pI ▸ xI, Qp, by simpa only [toFinset_Icc, Finset.mem_Icc, 𝔰_eq p𝔓Xs] using hs⟩
    simp_rw [carlesonOn_def', indicator_of_mem xEp, 𝔰_eq p𝔓Xs]

end

/- The constant used in Proposition 2.0.1 -/
def C2_0_1 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := C2_0_2 a q

lemma C2_0_1_pos [TileStructure Q D κ S o] : C2_0_1 a nnq > 0 := C2_0_2_pos

variable (X) in
theorem finitary_carleson : ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖∑ s in Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖₊ ≤
    C2_0_1 a nnq * (volume G) ^ (1 - q⁻¹) * (volume F) ^ q⁻¹ := by
  have g : GridStructure X D κ S o := grid_existence X
  have t : TileStructure Q D κ S o := tile_existence X
  clear g
  rcases discrete_carleson X with ⟨G', hG', h2G', hfG'⟩
  refine ⟨G', hG', h2G', fun f meas_f h2f ↦ le_of_eq_of_le ?_ (hfG' f meas_f h2f)⟩
  refine setLIntegral_congr_fun (measurableSet_G.diff hG') (ae_of_all volume fun x hx ↦ ?_)
  simp_rw [carlesonSum, mem_univ, Finset.filter_True, tile_sum_operator hx, mul_sub, exp_sub,
    mul_div, div_eq_mul_inv,
    ← smul_eq_mul (a' := _⁻¹), integral_smul_const, ← Finset.sum_smul, nnnorm_smul]
  suffices ‖(cexp (I * ((Q x) x : ℂ)))⁻¹‖₊ = 1 by rw [this, mul_one]
  simp [← coe_eq_one, mul_comm I]
