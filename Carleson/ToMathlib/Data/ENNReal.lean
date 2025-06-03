import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.CompletePartialOrder

/-! ## `ENNReal` manipulation lemmas -/

open Function Set Bornology
open scoped NNReal

variable {α ι : Type*} {s : Set ι} {t : Finset α}

namespace ENNReal

attribute [simp] ofReal_of_nonpos
-- protect ENNReal.mul_le_mul_left

theorem ofReal_inv_le {x : ℝ} : ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
  obtain hx|hx := lt_or_le 0 x <;> simp [ofReal_inv_of_pos, hx]

theorem ofReal_div_le {x y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (x / y) ≤ ENNReal.ofReal x / ENNReal.ofReal y := by
  simp_rw [div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy)]
  gcongr
  exact ofReal_inv_le

lemma coe_biSup {f : ι → ℝ≥0} (hf : BddAbove (range f)) :
    ⨆ x ∈ s, f x = ⨆ x ∈ s, (f x : ℝ≥0∞) := by
  simp_rw [bddAbove_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hf
  rw [ENNReal.coe_iSup]
  · congr with x
    rw [ENNReal.coe_iSup]
    apply IsBounded.bddAbove
    simp only [Metric.isBounded_iff, mem_range, exists_prop, and_imp, forall_apply_eq_imp_iff,
      dist_self, forall_self_imp]
    aesop
  · simp_rw [bddAbove_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    obtain ⟨K, hK⟩ := hf
    exact ⟨K, fun c ↦ ciSup_le' fun _ ↦ hK c⟩

-- unused
lemma biSup_add_biSup {f g : ι → ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, f i + g j ≤ f k + g k) :
    (⨆ i ∈ s, f i) + ⨆ i ∈ s, g i = ⨆ i ∈ s, f i + g i := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  · refine le_antisymm ?_ (iSup₂_le fun a ma => add_le_add (le_biSup _ ma) (le_biSup _ ma))
    refine biSup_add_biSup_le hs hs fun i hi j hj => ?_
    obtain ⟨k, mk, hk⟩ := h i hi j hj
    exact hk.trans <| le_iSup₂_of_le k mk fun a za ↦ ⟨a, za, le_rfl⟩

-- unused
lemma finsetSum_biSup {f : α → ι → ℝ≥0∞}
    (hf : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ t, ⨆ i ∈ s, f a i = ⨆ i ∈ s, ∑ a ∈ t, f a i := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    exact biSup_add_biSup fun i hi j hj ↦ (hf i hi j hj).imp fun k hk ↦
      ⟨hk.1, add_le_add (hk.2 a).1 (Finset.sum_le_sum fun i a ↦ (hk.2 _).2)⟩

lemma biSup_add_le_add_biSup {f g : ι → ℝ≥0∞} :
    ⨆ i ∈ s, f i + g i ≤ (⨆ i ∈ s, f i) + ⨆ i ∈ s, g i :=
  iSup₂_le fun _ ma => add_le_add (le_biSup _ ma) (le_biSup _ ma)

lemma biSup_finsetSum_le_finsetSum_biSup {f : α → ι → ℝ≥0∞} :
    ⨆ i ∈ s, ∑ a ∈ t, f a i ≤ ∑ a ∈ t, ⨆ i ∈ s, f a i := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp only [Finset.sum_cons]
    exact biSup_add_le_add_biSup.trans (add_le_add_left ihs _)

variable {E : Type*} [SeminormedAddCommGroup E]

lemma edist_sum_le_sum_edist {f g : α → E} : edist (∑ i ∈ t, f i) (∑ i ∈ t, g i) ≤
    ∑ i ∈ t, edist (f i) (g i) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp only [Finset.sum_cons]
    exact (edist_add_add_le _ _ _ _).trans (add_le_add_left ihs _)

lemma enorm_sum_eq_sum_enorm {f : α → ℝ} (hf : ∀ i ∈ t, 0 ≤ f i) :
    ‖∑ i ∈ t, f i‖ₑ = ∑ i ∈ t, ‖f i‖ₑ := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ihs =>
    simp only [Finset.sum_cons]
    simp only [Finset.mem_cons, forall_eq_or_imp] at hf
    have n₁ := hf.1
    have n₂ := Finset.sum_nonneg hf.2
    rw [Real.enorm_of_nonneg (add_nonneg n₁ n₂), ENNReal.ofReal_add n₁ n₂,
      ← Real.enorm_of_nonneg n₁, ← Real.enorm_of_nonneg n₂, ihs hf.2]

/-- The reverse triangle inequality for `enorm`. -/
-- TODO: does a seminormed abelian additive group also have an ENormedAddMonoid structure?
lemma enorm_enorm_sub_enorm_le {E} [NormedAddCommGroup E] {x y : E} : ‖‖x‖ₑ - ‖y‖ₑ‖ₑ ≤ ‖x - y‖ₑ := by
  rw [enorm_eq_self, tsub_le_iff_right]
  nth_rw 1 [← sub_add_cancel x y]
  exact enorm_add_le (x - y) y

lemma exists_biSup_le_enorm_add_eps
    {f : ι → E} {ε : ℝ≥0} (εpos : 0 < ε) (hs : s.Nonempty) (hf : IsBounded (f '' s)) :
    ∃ x ∈ s, ⨆ z ∈ s, ‖f z‖ₑ ≤ ‖f x‖ₑ + ε := by
  by_contra! H
  have M : ⨆ z ∈ s, ‖f z‖ₑ + ε ≤ ⨆ z ∈ s, ‖f z‖ₑ := by
    simpa only [iSup_le_iff] using fun i hi ↦ (H i hi).le
  have nt : ⨆ z ∈ s, ‖f z‖ₑ ≠ ⊤ := by -- boundedness of `f` used here
    rw [ne_eq, iSup₂_eq_top]; push_neg
    obtain ⟨C, pC, hC⟩ := hf.exists_pos_norm_le; lift C to ℝ≥0 using pC.le
    simp_rw [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hC
    exact ⟨C, coe_lt_top, mod_cast hC⟩
  obtain ⟨B, eB⟩ : ∃ B : ℝ≥0, ⨆ z ∈ s, ‖f z‖ₑ = B := Option.ne_none_iff_exists'.mp nt
  rw [← biSup_add hs, eB] at M
  norm_cast at M
  exact lt_irrefl _ (M.trans_lt (lt_add_of_pos_right B εpos))

lemma exists_enorm_sub_eps_le_biInf
    {f : ι → E} {ε : ℝ≥0} (εpos : 0 < ε) (hs : s.Nonempty) :
    ∃ x ∈ s, ‖f x‖ₑ - ε ≤ ⨅ z ∈ s, ‖f z‖ₑ := by
  obtain ⟨i₀, mi₀⟩ := hs; set A := ⨅ z ∈ s, ‖f z‖ₑ
  have glb : IsGLB ((‖f ·‖ₑ) '' s) A := isGLB_biInf
  rw [isGLB_iff_le_iff] at glb
  by_contra! h
  specialize glb (A + ε)
  have key : A + ε ∈ lowerBounds ((‖f ·‖ₑ) '' s) := fun i mi ↦ by
    rw [mem_image] at mi; obtain ⟨x, mx, hx⟩ := mi
    specialize h x mx; rw [hx] at h; exact (lt_tsub_iff_right.mp h).le
  rw [← glb] at key
  obtain ⟨B, eB⟩ : ∃ B : ℝ≥0, A = B := Option.ne_none_iff_exists'.mp (h i₀ mi₀).ne_top
  rw [eB, ← ENNReal.coe_add, coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add,
    add_le_iff_nonpos_right] at key
  rw [← NNReal.coe_pos] at εpos; linarith only [εpos, key]

lemma biInf_enorm_sub_le {f g : ι → E} :
    ⨅ x ∈ s, ‖f x - g x‖ₑ ≤ (⨅ x ∈ s, ‖f x‖ₑ) + (⨆ x ∈ s, ‖g x‖ₑ) := by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  refine ENNReal.le_of_forall_pos_le_add fun ε εpos _ ↦ ?_
  obtain ⟨x, mx, hx⟩ := exists_enorm_sub_eps_le_biInf (f := f) εpos hs
  calc
    _ ≤ ‖f x - g x‖ₑ := biInf_le (fun i ↦ ‖f i - g i‖ₑ) mx
    _ ≤ ‖f x‖ₑ + ‖g x‖ₑ := enorm_sub_le
    _ ≤ ε + (⨅ x ∈ s, ‖f x‖ₑ) + ⨆ x ∈ s, ‖g x‖ₑ :=
      add_le_add (by rwa [← tsub_le_iff_left]) (le_biSup (‖g ·‖ₑ) mx)
    _ = _ := by rw [add_rotate]

end ENNReal

/-- Transfer an inequality over `ℝ` to one of `ENorm`s over `ℝ≥0∞`. -/
lemma Real.enorm_le_enorm {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) : ‖x‖ₑ ≤ ‖y‖ₑ := by
  rw [Real.enorm_of_nonneg hx, Real.enorm_of_nonneg (hx.trans hy)]
  exact ENNReal.ofReal_le_ofReal hy
