import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.WeakType
import Carleson.ToMathlib.RealInterpolation.Misc

/-!
# Minkowski's integral inequality

In this file, we prove Minkowski's integral inequality and apply it to truncations.
We use this to deduce weak type estimates for truncations.

-/

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents
    ComputationsChoiceExponent

variable {α α' ε E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {ε ε₁ ε₂ : Type*} [TopologicalSpace ε] [TopologicalSpace ε₁] [TopologicalSpace ε₂]
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}
  {f : α → E₁} {t : ℝ≥0∞}

/-! ## Minkowski's integral inequality -/
namespace MeasureTheory

lemma rpow_add_of_pos (a : ℝ≥0∞) (c d : ℝ) (hc : 0 < c) (hd : 0 < d):
    a ^ (c + d) = a ^ c * a ^ d := by
  have hcd : 0 < c + d := by linarith
  rcases (eq_or_ne a 0) with a_eq_zero | a_ne_zero
  · rw [a_eq_zero, zero_rpow_of_pos hcd, zero_rpow_of_pos hc, zero_rpow_of_pos hd, mul_zero]
  · rcases (eq_or_ne a ⊤) with a_eq_top | a_ne_top
    · rw [a_eq_top, top_rpow_of_pos hcd, top_rpow_of_pos hc, top_rpow_of_pos hd, top_mul_top]
    · rw [ENNReal.rpow_add c d a_ne_zero a_ne_top]

lemma eq_of_le_of_le (a b : ℝ≥0∞) (hab : a ≤ b) (hab': b ≤ a) : a = b := by
  rcases (eq_or_ne a b) with a_eq_b | a_ne_b
  · exact a_eq_b
  · rcases lt_or_gt_of_ne a_ne_b with a_lt_b | b_lt_a
    · contrapose! a_lt_b; exact hab'
    · contrapose! b_lt_a; exact hab

def trunc_cut (f : α → ℝ≥0∞) (μ : Measure α) [SigmaFinite μ] :=
  fun n : ℕ ↦ indicator (spanningSets μ n) (fun x ↦ min (f x) n)

lemma trunc_cut_mono {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∀ x : α, Monotone (fun n ↦ trunc_cut f μ n x) := by
  intro x m n hmn; simp only [trunc_cut, indicator]
  split_ifs with is_fx_le_m is_fx_le_n
  · exact min_le_min_left (f x) (Nat.cast_le.mpr hmn)
  · contrapose! is_fx_le_n
    exact monotone_spanningSets _ hmn is_fx_le_m
  · exact zero_le _
  · exact zero_le _

lemma trunc_cut_mono₀ {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    Monotone (trunc_cut f μ) := by
  intro m n hmn x; apply trunc_cut_mono
  exact hmn

lemma trunc_cut_sup {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∀ x : α, ⨆ n : ℕ, trunc_cut f μ n x = f x := by
  intro x; refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?h₁ ?h₂
  · intro n; unfold trunc_cut indicator
    split_ifs
    · exact min_le_left (f x) ↑n
    · exact zero_le _
  · intro w hw
    unfold trunc_cut
    have : ∃ m : ℕ, x ∈ spanningSets μ m := by
      have obs := iUnion_spanningSets μ
      refine mem_iUnion.mp ?_
      rw [obs]
      exact trivial
    rcases this with ⟨m, wm⟩
    rcases ENNReal.exists_nat_gt hw.ne_top with ⟨n, wn⟩
    use (m + n)
    simp only [indicator]
    split_ifs with is_x_in_Ampn
    · refine lt_min hw ?_
      calc
      w < n := wn
      _ ≤ m + n := le_add_self
      _ = _ := (Nat.cast_add m n).symm
    · contrapose! is_x_in_Ampn
      exact monotone_spanningSets _ (Nat.le_add_right m n) wm

set_option linter.flexible false in
/-- Characterization of `∫⁻ x : α, f x ^ p ∂μ` by a duality argument. -/
lemma representationLp {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {p q : ℝ} (hp : p > 1) (hq : q ≥ 1)
    (hpq : p⁻¹ + q⁻¹ = 1) :
    (∫⁻ x : α, (f x) ^ p ∂μ) ^ (1 / p) =
    ⨆ g ∈ {g' : α → ℝ≥0∞ | AEMeasurable g' μ ∧ ∫⁻ x : α, (g' x) ^ q ∂μ ≤ 1},
    ∫⁻ x : α, (f x) * g x ∂μ := by
  let A := spanningSets μ
  let g := trunc_cut f μ
  have hpq' : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, hpq⟩
  have f_mul : ∀ n : ℕ, (g n) ^ p ≤ f * (g n) ^ (p - 1) := by
    intro n x
    simp only [g, Pi.pow_apply, Pi.mul_apply, trunc_cut, indicator]
    split_ifs
    · refine le_trans (b := (min (f x) ↑n) * min (f x) ↑n ^ (p - 1)) ?_ ?_
      · nth_rewrite 1 [← add_sub_cancel 1 p]
        rw [rpow_add_of_pos, ENNReal.rpow_one] <;> try linarith
      · exact mul_le_mul_right' (min_le_left (f x) ↑n) (min (f x) ↑n ^ (p - 1))
    · rw [ENNReal.zero_rpow_of_pos] <;> positivity
  have g_lim : ∀ x : α, Filter.Tendsto (fun n ↦ g n x) Filter.atTop (nhds (f x)) := by
    intro x
    apply tendsto_atTop_isLUB (trunc_cut_mono _)
    exact isLUB_iff_sSup_eq.mpr (trunc_cut_sup _)
  have g_sup' : (fun x ↦ ⨆ n : ℕ, (g n x) ^ p) = fun x ↦ (f x) ^ p := by
    ext x
    apply iSup_eq_of_tendsto
    · intro m n hmn
      dsimp only
      gcongr
      exact trunc_cut_mono _ hmn
    · exact (g_lim x).ennrpow_const p
  have g_meas (n : ℕ): AEMeasurable (g n) μ := by
    exact AEMeasurable.indicator (by fun_prop) (measurableSet_spanningSets μ n)
  have g_fin (n : ℕ): ∫⁻ (z : α), g n z ^ p ∂μ < ⊤ := by
    calc
    _ = ∫⁻ (z : α) in A n, g n z ^ p ∂μ := by
      unfold g trunc_cut
      rw [← lintegral_indicator]; swap; exact measurableSet_spanningSets μ n
      congr 1
      ext x
      dsimp only [indicator]
      split_ifs
      · rfl
      · simp only [ENNReal.rpow_eq_zero_iff, true_and, zero_ne_top, false_and, or_false]; positivity
    _ ≤ ∫⁻ (_x : α) in A n, n ^ p ∂μ := by
      apply setLIntegral_mono measurable_const
      · intro x hx
        gcongr
        unfold g trunc_cut indicator
        split_ifs
        · exact min_le_right (f x) ↑n
        · contradiction
    _ = n ^ p * μ (A n) := setLIntegral_const (A n) (↑n ^ p)
    _ < ⊤ := mul_lt_top (rpow_lt_top_of_nonneg (by linarith) coe_ne_top)
              (measure_spanningSets_lt_top μ n)
  have obs : ∀ n : ℕ, ∫⁻ x : α, (f x) * ((g n x) ^ (p - 1) /
      (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹) ∂μ ≥
      (∫⁻ x : α, (g n x) ^ p ∂μ) ^ p⁻¹ := by
    intro n
    rcases eq_or_ne (∫⁻ x : α, (g n x) ^ p ∂μ) 0  with int_eq_zero | int_ne_zero
    · rw [int_eq_zero, ENNReal.zero_rpow_of_pos]
      · exact zero_le _
      · refine inv_pos_of_pos (by positivity)
    · calc
      _ = (∫⁻ x : α, (f x) * (g n x) ^ (p - 1) ∂μ) * (
          (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ := by
        simp_rw [div_eq_mul_inv, ← mul_assoc]
        rw [lintegral_mul_const'' _ (by fun_prop)]
      _ ≥ (∫⁻ x : α, (g n x) ^ (p) ∂μ) * ((∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ := by
        gcongr
        apply f_mul
      _ = (∫⁻ x : α, (g n x) ^ (p) ∂μ) * ((∫⁻ y : α, (g n y) ^ p ∂μ) ^ q⁻¹)⁻¹ := by
        congr
        ext x
        rw [← ENNReal.rpow_mul]
        congr
        refine Real.HolderConjugate.sub_one_mul_conj hpq'
      _ = (∫⁻ x : α, (g n x) ^ p ∂μ) ^ p⁻¹ := by
        rw [← ENNReal.rpow_neg]
        nth_rw 1 [← ENNReal.rpow_one (x := (∫⁻ x : α, (g n x) ^ (p) ∂μ))]
        rw [← ENNReal.rpow_add _ _ int_ne_zero (g_fin n).ne]
        congr
        exact add_neg_eq_of_eq_add hpq.symm
  have int_fg : ∫⁻ (x : α), f x ^ p ∂μ = ⨆ n : ℕ, ∫⁻ x : α, g n x ^ p ∂μ := by
    rw [← g_sup']
    apply lintegral_iSup' (fun n ↦ by fun_prop) (ae_of_all _ fun x m n hmn ↦ ?_)
    dsimp only
    gcongr
    exact trunc_cut_mono _ hmn
  have sup_rpow : (⨆ n : ℕ, ∫⁻ x : α, g n x ^ p ∂μ) ^ (1 / p) =
      ⨆ n : ℕ, (∫⁻ x : α, g n x ^ p ∂μ) ^ (1 / p) := by
    apply Monotone.map_iSup_of_continuousAt (f := fun (x : ℝ≥0∞) ↦ x ^ (1 / p))
    · fun_prop
    · apply ENNReal.monotone_rpow_of_nonneg (by positivity)
    · simp; positivity
  let h := fun n : ℕ ↦ (fun x ↦ g n x ^ (p - 1) / (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)
  have comp_sup : (⨆ n : ℕ, ∫⁻ (x : α), f x * h n x ∂μ) ≤
      ⨆ g ∈ {g' : α → ℝ≥0∞ | AEMeasurable g' μ ∧ ∫⁻ (z : α), (g' z) ^ q ∂μ ≤ 1},
      ∫⁻ (x : α), f x * g x ∂μ := by
    nth_rw 1 [← iSup_range (f := fun n : ℕ ↦ h n) (g := fun r ↦ ∫⁻ x : α, f x * r x ∂μ)]
    apply iSup_le_iSup_of_subset fun r exists_n ↦ ?_
    rcases exists_n with ⟨n, wn⟩
    simp_rw [← wn]
    unfold h
    refine ⟨by fun_prop, ?_⟩
    simp_rw [div_eq_mul_inv]
    calc
    _ = ∫⁻ (z : α), ((g n z ^ (p - 1)) ^ q) *
        ((∫⁻ (y : α), (g n y ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ ^ q ∂μ := by
      congr 1
      ext z
      rw [ENNReal.mul_rpow_of_nonneg]
      linarith
    _ = (∫⁻ (z : α), ((g n z ^ (p - 1)) ^ q) ∂μ) *
        ((∫⁻ (y : α), (g n y ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ ^ q := by
      rw [lintegral_mul_const'' _ (by fun_prop)]
    _ ≤ _ := by
      rcases eq_or_ne (∫⁻ x : α, ((g n x) ^ (p - 1)) ^ q ∂μ) 0 with int_eq_zero | int_ne_zero
      · rw [int_eq_zero]
        simp
      · rw [ENNReal.inv_rpow, ENNReal.rpow_inv_rpow]
        apply le_of_eq
        refine ENNReal.mul_inv_cancel int_ne_zero ?inr.a.ht
        · apply ne_of_lt
          calc
          _ = ∫⁻ (z : α), g n z ^ p ∂μ := by
            congr 1
            ext z
            rw [← ENNReal.rpow_mul]
            congr
            exact Real.HolderConjugate.sub_one_mul_conj hpq'
          _ < ⊤ := g_fin n
        · linarith
  apply eq_of_le_of_le
  · rw [int_fg, sup_rpow]
    calc
    _ ≤ ⨆ n : ℕ, ∫⁻ x : α, (f x) * ((g n x) ^ (p - 1) /
        (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹) ∂μ := by
      gcongr
      rw [one_div]
      apply obs
    _ ≤ _ := comp_sup
  · refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
    calc
    _ ≤ (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) * (∫⁻ x : α, r x ^ q ∂μ) ^ (1 / q) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq' hf hr.1
    _ ≤ (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) * (1) ^ (1 / q) := by
      gcongr
      exact hr.2
    _ = _ := by simp

lemma aemeasurability_prod₁ {α : Type u_1} {β : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    ⦃f : α × β → ENNReal⦄
    (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x : α ∂μ, AEMeasurable (f ∘ (Prod.mk x)) ν := by
  rcases hf with ⟨g, hg⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hg.2] with x h
  exact ⟨g ∘ Prod.mk x, hg.1.comp (measurable_prodMk_left), h⟩

lemma aemeasurability_prod₂ {α : Type u_1} {β : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SFinite μ] ⦃f : α × β → ENNReal⦄
    (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y : β ∂ν, AEMeasurable (f ∘ (fun x ↦ Prod.mk x y)) μ := by
  have : AEMeasurable (f ∘ Prod.swap) (ν.prod μ) := by
    refine AEMeasurable.comp_measurable ?_ measurable_swap
    rw [Measure.prod_swap]
    assumption
  convert aemeasurability_prod₁ this -- perf: convert is faster than exact

lemma aemeasurability_integral_component {α : Type u_1} {β : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    ⦃f : α × β → ENNReal⦄
    (hf : AEMeasurable f (μ.prod ν)) :
    AEMeasurable (fun x ↦ ∫⁻ (y : β), f (x, y) ∂ν) μ := by
  rcases hf with ⟨g, hg⟩
  refine ⟨fun x ↦ ∫⁻ y : β, g (x, y) ∂ν, Measurable.lintegral_prod_right hg.1, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hg.2] with x h using lintegral_congr_ae h

/-- Minkowsi's integral inequality -/
-- TODO: the condition on `μ` can probably be weakened to `SFinite μ`, by using a limit
-- argument
lemma lintegral_lintegral_pow_swap {α : Type u_1} {β : Type u_3} {p : ℝ} (hp : 1 ≤ p)
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SigmaFinite μ] ⦃f : α → β → ENNReal⦄
    (hf : AEMeasurable (Function.uncurry f) (μ.prod ν)) :
    (∫⁻ (x : α), (∫⁻ (y : β), f x y ∂ν) ^ p ∂μ) ^ p⁻¹ ≤
    ∫⁻ (y : β), (∫⁻ (x : α), (f x y) ^ p ∂μ) ^ p⁻¹ ∂ν := by
  rcases Decidable.lt_or_eq_of_le hp with one_lt_p | one_eq_p
  · let q := Real.conjExponent p
    have hpq' : p.HolderConjugate q := Real.HolderConjugate.conjExponent one_lt_p
    have one_lt_q : 1 < q := (Real.HolderConjugate.symm hpq').lt
    have ineq : ∀ g ∈ {g' : α → ℝ≥0∞ | AEMeasurable g' μ ∧ ∫⁻ (z : α), (g' z) ^ q ∂μ ≤ 1},
        ∫⁻ x : α, (∫⁻ y : β, f x y ∂ν) * g x ∂μ ≤
        ∫⁻ (y : β), (∫⁻ (x : α), f x y ^ p ∂μ) ^ p⁻¹ ∂ν := by
      intro g ⟨hg1, hg2⟩
      have ae_meas₁ : ∀ᵐ x : α ∂μ, AEMeasurable (f x) ν :=
        aemeasurability_prod₁ (f := Function.uncurry f) hf
      calc
      _ = ∫⁻ x : α, (∫⁻ y : β, f x y * g x ∂ν) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_meas₁] with a ha using (lintegral_mul_const'' _ ha).symm
      _ = ∫⁻ y : β, (∫⁻ x : α, f x y * g x ∂μ) ∂ν := lintegral_lintegral_swap (hf.mul hg1.fst)
      _ ≤ ∫⁻ (y : β), (∫⁻ (x : α), f x y ^ p ∂μ) ^ p⁻¹ ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [aemeasurability_prod₂ hf] with y hy
        calc
        _ ≤ (∫⁻ (x : α), f x y ^ p ∂μ) ^ (1 / p) * (∫⁻ (x : α), g x ^ q ∂μ) ^ (1 / q) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq' hy hg1
        _ ≤ (∫⁻ (x : α), f x y ^ p ∂μ) ^ (1 / p) * 1 ^ (1 / q) := by
          gcongr
        _ = (∫⁻ (x : α), f x y ^ p ∂μ) ^ p⁻¹ := by
          simp [one_div]
    nth_rw 1 [← one_div]
    rw [representationLp (hp := one_lt_p) (hq := one_lt_q.le) (hpq := hpq'.inv_add_inv_eq_one)]
    · exact (iSup_le fun g ↦ iSup_le fun hg ↦ ineq g hg)
    · exact (aemeasurability_integral_component hf)
  · rw [← one_eq_p]
    simp only [ENNReal.rpow_one, inv_one]
    exact (lintegral_lintegral_swap hf).le

lemma lintegral_lintegral_pow_swap_rpow {α : Type u_1} {β : Type u_3} {p : ℝ} (hp : p ≥ 1)
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SigmaFinite μ] ⦃f : α → β → ENNReal⦄
    (hf : AEMeasurable (Function.uncurry f) (μ.prod ν)) :
    (∫⁻ (x : α), (∫⁻ (y : β), f x y ∂ν) ^ p ∂μ) ≤
    (∫⁻ (y : β), (∫⁻ (x : α), (f x y) ^ p ∂μ) ^ p⁻¹ ∂ν) ^ p := by
  have p_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  refine le_of_rpow_le2 (inv_pos_of_pos p_pos) ?_
  rw [ENNReal.rpow_rpow_inv p_pos.ne']
  exact lintegral_lintegral_pow_swap hp hf

/-! ## Apply Minkowski's integral inequality to truncations
-/

@[measurability, fun_prop]
theorem ton_aeMeasurable (tc : ToneCouple) : AEMeasurable tc.ton (volume.restrict (Ioi 0)) := by
  -- ton is either increasing or decreasing
  have mono_or_anti := tc.ton_is_ton
  split_ifs at mono_or_anti
  · exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioi mono_or_anti.monotoneOn
  · exact aemeasurable_restrict_of_antitoneOn measurableSet_Ioi mono_or_anti.antitoneOn

@[measurability]
lemma indicator_ton_measurable {g : α → E₁} [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [BorelSpace E₁] [SigmaFinite μ] (hg : AEMeasurable g μ) (tc : ToneCouple) :
    NullMeasurableSet {(s, x) : ℝ × α | ‖g x‖ₑ ≤ tc.ton (ENNReal.ofReal s) }
        ((volume.restrict (Ioi 0)).prod μ) := by
  apply nullMeasurableSet_le
  · sorry
  have : AEMeasurable ENNReal.ofReal := by fun_prop
  sorry -- proof was: nullMeasurableSet_le hg.snd.norm (ton_aeMeasurable tc).fst

@[measurability]
lemma indicator_ton_measurable_lt {g : α → E₁} [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [BorelSpace E₁] [SigmaFinite μ] (hg : AEMeasurable g μ) (tc : ToneCouple) :
    NullMeasurableSet {(s, x) : ℝ × α | tc.ton (ENNReal.ofReal s) < ‖g x‖ₑ }
        ((volume.restrict (Ioi 0)).prod μ) :=
  nullMeasurableSet_lt sorry /- was: (ton_aeMeasurable tc).fst -/ sorry -- was: hg.snd.norm

@[measurability]
lemma AEMeasurable.trunc_ton {f : α → E₁}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [SigmaFinite (μ.restrict (Function.support f))] -- TODO: TypeClass or implicit variable?
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a : ℝ × α ↦ (trunc f (tc.ton (ENNReal.ofReal a.1))) a.2)
    ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f) )) := by
  let A := {(s, x) : ℝ × α | ‖f x‖ₑ ≤ tc.ton (ENNReal.ofReal s)}
  have : (fun z : ℝ × α ↦ (trunc f (tc.ton (ENNReal.ofReal z.1))) z.2) =
      Set.indicator A (fun z : ℝ × α ↦ f z.2) := by
    ext z; simp [trunc, indicator, A]
  rw [this]
  exact (aemeasurable_indicator_iff₀ (indicator_ton_measurable hf.restrict _)).mpr
    hf.restrict.snd.restrict

@[measurability]
lemma AEMeasurable.truncCompl_ton {f : α → E₁}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [SigmaFinite (μ.restrict (Function.support f))] -- TODO: TypeClass or implicit variable?
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a : ℝ × α ↦ ((truncCompl f (tc.ton (ENNReal.ofReal a.1)))) a.2)
    ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f) )) := by
  let A := {(s, x) : ℝ × α | tc.ton (ENNReal.ofReal s) < ‖f x‖ₑ}
  have : (fun z : ℝ × α ↦ (truncCompl f (tc.ton (ENNReal.ofReal z.1))) z.2) = Set.indicator A (fun z : ℝ × α ↦ f z.2) := by
    ext z; rw [truncCompl_eq]; simp [A, indicator]
  rw [this]
  refine (aemeasurable_indicator_iff₀ (indicator_ton_measurable_lt hf.restrict _)).mpr
    hf.restrict.snd.restrict

lemma restrict_to_support {p : ℝ} (hp : 0 < p) [NormedAddCommGroup E₁] (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖trunc f t x‖ₑ ^ p ∂ μ = ∫⁻ x : α, ‖trunc f t x‖ₑ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support trunc
  rw [setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  simp_rw [f_zero]; simp [hp]

lemma restrict_to_support_truncCompl {p : ℝ} [NormedAddCommGroup E₁] (hp : 0 < p) (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖(truncCompl f t) x‖ₑ ^ p ∂μ =
    ∫⁻ x : α, ‖(truncCompl f t) x‖ₑ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support
  rw [truncCompl_eq, setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  simp [hp, f_zero]

lemma restrict_to_support_trnc {p : ℝ} {j : Bool} [NormedAddCommGroup E₁] (hp : 0 < p) (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖trnc j f t x‖ₑ ^ p ∂μ =
    ∫⁻ x : α, ‖trnc j f t x‖ₑ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support trnc trunc
  rw [setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  rcases j
  · dsimp only [Pi.sub_apply]; simp_rw [f_zero]; simp [hp]
  · simp_rw [f_zero]; simp [hp]

@[fun_prop]
theorem AEMeasurable.trunc_restrict
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁] {j : Bool}
    {hμ : SigmaFinite (μ.restrict (Function.support f))} (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a ↦ trnc j f (tc.ton a.1) a.2)
      ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f))) :=
  sorry -- was: j.rec (hf.truncCompl_ton _) (hf.trunc_ton _)

lemma lintegral_lintegral_pow_swap_truncCompl {q q₀ p₀ : ℝ} [MeasurableSpace E₁]
    [NormedAddCommGroup E₁]
    [BorelSpace E₁] {j : Bool} {hμ : SigmaFinite (μ.restrict (Function.support f))}
    (hp₀ : 0 < p₀) (hp₀q₀ : p₀ ≤ q₀)
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    ∫⁻ (s : ℝ) in Ioi 0,
        (∫⁻ (a : α) in Function.support f, ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton (ENNReal.ofReal s)) a‖ₑ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) ≤
    (∫⁻ a : α in Function.support f,
      (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton (ENNReal.ofReal s)) a‖ₑ ^ p₀) ^ (p₀⁻¹ * q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
  apply lintegral_lintegral_pow_swap_rpow
  · apply le_of_mul_le_mul_left _ hp₀
    field_simp [hp₀q₀]
  · unfold Function.uncurry
    simp only [Pi.sub_apply]
    sorry -- TODO: was fun_prop

lemma lintegral_congr_support {f : α → E₁} {g h: α → ENNReal}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hf : AEMeasurable f μ) (hgh : ∀ x ∈ Function.support f, g x = h x) :
    ∫⁻ x : α in Function.support f, g x ∂μ = ∫⁻ x : α in Function.support f, h x ∂μ := by
  refine lintegral_congr_ae (ae_iff.mpr ?_)
  rw [Measure.restrict_apply₀']
  · refine measure_mono_null (fun x h₀ ↦ ?_) measure_empty
    have : g x = h x := hgh _ (mem_of_mem_inter_right h₀)
    have : x ∈ {a | ¬g a = h a} := mem_of_mem_diff h₀
    change ¬ (g x = h x) at this
    contradiction
  · have : (Function.support f) = (Function.support (fun x ↦ ‖f x‖)) := by
      unfold Function.support
      ext x
      simp only [ne_eq, mem_setOf_eq, norm_eq_zero]
    rw [this]
    exact (aestronglyMeasurable_iff_aemeasurable.mpr hf.norm).nullMeasurableSet_support

/-- One of the key estimates for the real interpolation theorem, not yet using
    the particular choice of exponent and scale in the `ScaledPowerFunction`. -/
lemma estimate_trnc {p₀ q₀ q : ℝ} {spf : ScaledPowerFunction} {j : Bool}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₀q₀ : p₀ ≤ q₀)
    (hf : AEMeasurable f μ) (hf₂ : SigmaFinite (μ.restrict (Function.support f)))
    (hpowers : if xor j (spf_to_tc spf).mon = true then q₀ < q else q < q₀) :
    ∫⁻ s : ℝ in Ioi 0,
    eLpNorm (trnc j f ((spf_to_tc spf).ton (ENNReal.ofReal s))) (ENNReal.ofReal p₀) μ ^ q₀ *
    ENNReal.ofReal (s ^ (q - q₀ - 1)) ≤
    (spf.d ^ (q - q₀)) * ENNReal.ofReal |q - q₀|⁻¹ *
    (∫⁻ (a : α) in Function.support f,
    ‖f a‖ₑ ^ (p₀ + spf.σ⁻¹ * (q - q₀) * (p₀ / q₀)) ∂μ) ^ (p₀⁻¹ * q₀) := by
  have := spf.hd
  unfold eLpNorm eLpNorm'
  set tc := spf_to_tc spf
  split_ifs with is_p₀pos is_p₀top
  · have : p₀ ≤ 0 := ofReal_eq_zero.mp is_p₀pos
    contrapose! this; exact hp₀
  · contrapose! is_p₀top; exact coe_ne_top
  · rw [toReal_ofReal hp₀.le]
    calc
    _ = ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (s ^ (q - q₀ - 1)) *
    ((∫⁻ (a : α), ↑‖trnc j f ((spf_to_tc spf).ton (ENNReal.ofReal s)) a‖ₑ ^ p₀ ∂μ) ^ (1 / p₀)) ^ q₀ := by
      simp only [enorm_eq_nnnorm]
      congr 1
      ext x
      rw [mul_comm]
    _ = ∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹) ^ (p₀⁻¹ * q₀) *
        (∫⁻ (a : α) in Function.support f, ↑‖trnc j f (tc.ton (ENNReal.ofReal s)) a‖ₑ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [ENNReal.rpow_inv_rpow]
      · rw [one_div, ← ENNReal.rpow_mul, restrict_to_support_trnc hp₀]
      · positivity
    _ = ∫⁻ (s : ℝ) in Ioi 0,
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton (ENNReal.ofReal s)) a‖ₑ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [lintegral_const_mul', ENNReal.mul_rpow_of_nonneg]
      · positivity
      · exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) coe_ne_top).ne
    _ ≤ (∫⁻ a : α in Function.support f,
        (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton (ENNReal.ofReal s)) a‖ₑ ^ p₀) ^ (p₀⁻¹ * q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      -- This is a consequence of Minkowski's integral inequality
      apply lintegral_lintegral_pow_swap_truncCompl hp₀ hp₀q₀ hf tc; assumption
    _ = (∫⁻ a : α in Function.support f,
        (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) *
        ↑‖trnc j f (tc.ton (ENNReal.ofReal s)) a‖ₑ ^ q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x _
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_inv_rpow, ← ENNReal.rpow_mul] <;> try positivity
      congr
      field_simp
    _ = (∫⁻ a : α in Function.support f,
        ((∫⁻ (s : ℝ) in res (xor j tc.mon) (tc.inv ‖f a‖ₑ),
        (ENNReal.ofReal (s ^ (q - q₀ - 1)))) * ‖f a‖ₑ ^ q₀) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 1
      exact lintegral_trunc_mul hq₀ (enorm_pos.mpr hfx)
    _ = (∫⁻ a : α in Function.support f,
        (((tc.inv ‖f a‖ₑ ^ (q - q₀ - 1 + 1) / ENNReal.ofReal |q - q₀ - 1 + 1|)) *
        ‖f a‖ₑ ^ q₀) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 2
      · apply value_lintegral_res₀
        · sorry -- proof was: apply tc.ran_inv
          -- exact norm_pos_iff.mpr hfx
        · split_ifs with h
          · simp only [h, ↓reduceIte] at hpowers; linarith
          · simp only [h, Bool.false_eq_true, ↓reduceIte] at hpowers; linarith
    _ = (∫⁻ a : α in Function.support f,
        ((
        (spf.d ^ (q - q₀ - 1 + 1) * ‖f a‖ₑ ^ (spf.σ⁻¹ * (q - q₀ - 1 + 1) + q₀) /
        ENNReal.ofReal |q - q₀ - 1 + 1|))) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 1
      exact value_lintegral_res₁ (enorm_pos.mpr hfx)
    _ = (∫⁻ a : α in Function.support f,
        (((spf.d ^ (q - q₀)) ^ (p₀⁻¹ * q₀)⁻¹ *
        (‖f a‖ₑ ^ ((spf.σ⁻¹ * (q - q₀) + q₀) * (p₀⁻¹ * q₀)⁻¹)) *
    ENNReal.ofReal |q - q₀|⁻¹ ^ (p₀⁻¹ * q₀)⁻¹))  ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x _
      rw [div_eq_mul_inv, sub_add_cancel, ENNReal.mul_rpow_of_nonneg,
        ENNReal.mul_rpow_of_nonneg] <;> try positivity
      rw [ENNReal.rpow_mul, ofReal_inv_of_pos]
      have : q ≠ q₀ := by split_ifs at hpowers <;> order
      exact abs_sub_pos.mpr this
    _ = (spf.d ^ (q - q₀)) *
        (∫⁻ (a : α) in Function.support f,
        ‖f a‖ₑ ^ ((spf.σ⁻¹ * (q - q₀) + q₀) * (p₀⁻¹ * q₀)⁻¹) ∂μ) ^ (p₀⁻¹ * q₀) *
        ENNReal.ofReal |q - q₀|⁻¹ := by
      rw [lintegral_mul_const', lintegral_const_mul', ENNReal.mul_rpow_of_nonneg,
          ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_inv_rpow, ENNReal.rpow_inv_rpow] <;>
          try positivity
      · apply rpow_ne_top_of_nonneg (by positivity)
        -- TODO: can finiteness prove this?
        by_contra h
        simp only [rpow_eq_top_iff, sub_neg, spf.hd', sub_pos, false_and, or_false] at h
        exact this.ne h.1.symm
      · exact rpow_ne_top_of_nonneg (by positivity) coe_ne_top
    _ = (spf.d ^ (q - q₀)) *
        (∫⁻ (a : α) in Function.support f,
        ‖f a‖ₑ ^ (p₀ + spf.σ⁻¹ * (q - q₀) * (p₀ / q₀)) ∂μ) ^ (p₀⁻¹ * q₀) *
        ENNReal.ofReal |q - q₀|⁻¹ := by
      congr
      ext x
      congr
      ring_nf
      rw [inv_inv]
      field_simp
    _ = _ := by ring

def sel (j : Bool) (p₀ p₁ : ℝ≥0∞) := match j with | true => p₁ | false => p₀

/-- One of the key estimates for the real interpolation theorem, now using
    the particular choice of exponent, but not yet using the
    particular choice of scale in the `ScaledPowerFunction`. -/
lemma estimate_trnc₁ {spf : ScaledPowerFunction} {j : Bool}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁] (ht : t ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hpq : sel j p₀ p₁ ≤ sel j q₀ q₁)
    (hp' : sel j p₀ p₁ ≠ ⊤) (hq' : sel j q₀ q₁ ≠ ⊤)  (hp₀p₁ : p₀ < p₁)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - t) * p₀⁻¹ + t * p₁⁻¹)
    (hq : q⁻¹ = (1 - t) * q₀⁻¹ + t * q₁⁻¹)
    (hf : AEMeasurable f μ) (hf₂ : SigmaFinite (μ.restrict (Function.support f)))
    (hspf : spf.σ = ζ p₀ q₀ p₁ q₁ t.toReal) :
    ∫⁻ s : ℝ in Ioi 0,
    eLpNorm (trnc j f ((spf_to_tc spf).ton (ENNReal.ofReal s))) (sel j p₀ p₁) μ ^ (sel j q₀ q₁).toReal *
    ENNReal.ofReal (s ^ (q.toReal - (sel j q₀ q₁).toReal - 1)) ≤
    (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
    ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
    ((eLpNorm f p μ) ^ p.toReal) ^ ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
  have p_toReal_pos : 0 < p.toReal :=
    interp_exp_toReal_pos'2 ht hp₀ hp₁ hp (Or.inl hp₀p₁.ne_top)
  calc
  _ ≤ (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (∫⁻ (a : α) in Function.support f,
      ‖f a‖ₑ ^ ((sel j p₀ p₁).toReal + spf.σ⁻¹ * (q.toReal - (sel j q₀ q₁).toReal) *
      ((sel j p₀ p₁).toReal / (sel j q₀ q₁).toReal)) ∂μ) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    have coe_p' : ENNReal.ofReal (sel j p₀ p₁).toReal = (sel j p₀ p₁) := ofReal_toReal_eq_iff.mpr hp'
    nth_rw 1 [← coe_p']
    apply estimate_trnc
    · apply toReal_pos
      · cases j
        · exact hp₀.ne'
        · exact hp₁.ne'
      · exact hp'
    · apply toReal_pos
      · cases j
        · exact hq₀.ne'
        · exact hq₁.ne'
      · exact hq'
    · exact toReal_mono hq' hpq
    · exact hf
    · exact hf₂
    · unfold spf_to_tc
      cases j
      · unfold sel
        dsimp only
        rw [hspf]
        simp only [Bool.if_false_right, Bool.and_true, Bool.false_bne, decide_eq_true_eq]
        split_ifs with is_ζ_pos
        · apply toReal_strict_mono
          · exact interp_exp_ne_top2 hq₀q₁ ht hq
          · exact (ζ_pos_iff_of_lt₀2 ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp is_ζ_pos
        · apply toReal_strict_mono hq'
          exact (ζ_le_zero_iff_of_lt₀2 ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp
            (le_of_not_lt is_ζ_pos)
      · unfold sel
        dsimp only
        rw [hspf]
        simp only [Bool.if_false_right, Bool.and_true, Bool.true_bne, Bool.not_eq_true',
            decide_eq_false_iff_not]
        split_ifs with is_ζ_pos
        · apply toReal_strict_mono hq'
          exact (ζ_pos_iff_of_lt₁2 ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp is_ζ_pos
        · apply toReal_strict_mono
          · exact interp_exp_ne_top2 hq₀q₁ ht hq
          · exact (ζ_le_zero_iff_of_lt₁2 ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp
                (le_of_not_lt is_ζ_pos)
  _ = (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
        ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
        (∫⁻ (a : α) in Function.support f,
        (‖f a‖ₑ ^ p.toReal) ∂μ) ^ ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    ext x
    congr
    rcases j
    · dsimp only [sel]
      rw [hspf]
      apply ζ_equality₅2 (hp₀p₁ := hp₀p₁.ne) <;> assumption
    · dsimp only [sel]
      rw [hspf]
      apply ζ_equality₆2 (hp₀p₁ := hp₀p₁.ne) <;> assumption
  _ ≤ (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (∫⁻ (a : α), ‖f a‖ₑ ^ p.toReal ∂μ) ^ ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    gcongr
    exact setLIntegral_le_lintegral _ _
  _ = (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (((∫⁻ (a : α), ‖f a‖ₑ ^ p.toReal ∂μ) ^ p.toReal⁻¹ ) ^ p.toReal) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    rw [ENNReal.rpow_inv_rpow]
    positivity
  _ = (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      ((eLpNorm f p μ) ^ p.toReal) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    rw [← one_div]
    refine (eLpNorm_eq_lintegral_rpow_enorm (ε := E₁) ?_ ?_).symm
    · exact (interpolated_pos'2 hp₀ hp₁ hp).ne'
    · exact interp_exp_ne_top2 hp₀p₁.ne ht hp

-- TODO: move this to WeakType.lean?
lemma wnorm_eq_zero_iff [ENormedAddMonoid ε] {f : α → ε} {p : ℝ≥0∞} (hp : p ≠ 0) :
    wnorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  unfold wnorm
  split_ifs with h₀
  · exact eLpNormEssSup_eq_zero_iff
  · refine Iff.trans ⟨?_, ?_⟩ eLpNormEssSup_eq_zero_iff <;> intro h
    · have iSup_wnorm := iSup_eq_zero.mp h
      by_contra h₁
      have : 0 < eLpNormEssSup f μ := pos_iff_ne_zero.mpr h₁
      unfold eLpNormEssSup at this
      rw [essSup_eq_sInf] at this
      let b := (min (sInf {a : ℝ≥0∞ | μ {x | a < ‖f x‖ₑ} = 0}) 1) / 2
      have b_lt_inf : b < min (sInf {a : ℝ≥0∞ | μ {x | a < ‖f x‖ₑ} = 0}) 1 :=
        ENNReal.half_lt_self (lt_min this zero_lt_one).ne'
          (lt_of_le_of_lt (min_le_right _ 1) one_lt_top).ne
      have meas_ne_zero : μ {x | b < ‖f x‖ₑ} ≠ 0 := by
        intro h
        have obs : sInf {a | μ {x | a < ‖f x‖ₑ} = 0} ≤ b := csInf_le' h
        contrapose! obs
        calc
        _ < _ := b_lt_inf
        _ ≤ _ := min_le_left ..
      have b_ne_0 : b ≠ 0 := (ENNReal.half_pos (lt_min this zero_lt_one).ne').ne'
      have p_toReal_inv_pos : 0 < p.toReal⁻¹ := inv_pos_of_pos (toReal_pos hp h₀)
      have coe_b : ENNReal.ofNNReal b.toNNReal = b := coe_toNNReal b_lt_inf.ne_top
      have : distribution f b μ = 0 := by
        refine (rpow_eq_zero_iff_of_pos p_toReal_inv_pos).mp ?_
        refine eq_zero_of_ne_zero_of_mul_left_eq_zero b_ne_0 ?_
        rw [← coe_b]
        exact iSup_wnorm b.toNNReal
      exact meas_ne_zero this
    · refine iSup_eq_zero.mpr fun t ↦ mul_eq_zero.mpr
        (Or.inr ((rpow_eq_zero_iff_of_pos (inv_pos_of_pos (toReal_pos hp h₀))).mpr (nonpos_iff_eq_zero.mp ?_)))
      calc
        _ ≤ distribution f 0 μ := by gcongr; exact zero_le _
        _ = distribution f (eLpNormEssSup f μ) μ := by congr; exact h.symm
        _ = 0 := distribution_snormEssSup


/-! ## Weaktype estimates applied to truncations -/

variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]

lemma eLpNorm_trnc_est {f : α → E₁} {j : Bool} :
    eLpNorm (trnc j f t) p μ ≤ eLpNorm f p μ := eLpNorm_mono_enorm fun _x ↦ trnc_le_func

variable [ContinuousENorm ε₁] [ContinuousENorm ε₂] {T : (α → ε₁) → (α' → ε₂)} in
lemma weaktype_estimate {C₀ : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞} {f : α → ε₁}
      (hq : 0 < q) (hq' : q < ⊤) (hf : MemLp f p μ)
    (h₀T : HasWeakType T p q μ ν C₀) (ht : 0 < t) :
    distribution (T f) t ν ≤ C₀ ^ q.toReal *
        eLpNorm f p μ ^ q.toReal * (t ^ (-q.toReal)) := by
  by_cases ht' : t = ⊤
  · simp [ht']
  have wt_est := (h₀T f hf).2 -- the weaktype estimate
  have q_pos : 0 < q.toReal := toReal_pos hq.ne' hq'.ne_top
  have tq_pos : 0 < t ^ q.toReal := ENNReal.rpow_pos_of_nonneg ht q_pos.le
  have tq_ne_top : t ^ q.toReal ≠ ⊤ := rpow_ne_top_of_nonneg q_pos.le ht'
  -- have hq₁ : q.toReal = q := by exact toReal_ofReal q_nonneg
  simp only [wnorm, wnorm', hq'.ne_top, ↓reduceIte, iSup_le_iff] at wt_est
  have wt_est_t := wt_est t.toNNReal -- this is the weaktype estimate applied to t
  sorry /- rw [← ENNReal.mul_le_mul_right (c := t ^ q.toReal) _ tq_ne_top,
      mul_assoc _ _ (t ^ q.toReal), ← ofReal_mul',
      ← Real.rpow_add, neg_add_cancel, Real.rpow_zero, ofReal_one, mul_one, mul_comm,
      ← ENNReal.mul_rpow_of_nonneg] <;> try positivity
  refine (ENNReal.rpow_inv_le_iff q_pos).mp ?_
  rw [ENNReal.mul_rpow_of_nonneg, ENNReal.ofReal_rpow_of_pos,
      Real.rpow_rpow_inv] <;> try positivity
  rwa [← coe_coe_eq_ofReal] -/

variable [ContinuousENorm ε₁] [ContinuousENorm ε₂] {T : (α → ε₁) → (α' → ε₂)} in
lemma weaktype_estimate_top {C : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞}
    (hq' : q = ⊤) {f : α → ε₁} (hf : MemLp f p μ)
    (hT : HasWeakType T p q μ ν C) {t : ℝ} (ht : C * eLpNorm f p μ ≤ ENNReal.ofReal t) :
    distribution (T f) (ENNReal.ofReal t) ν = 0 := by
  have wt_est := (hT f hf).2
  unfold wnorm at wt_est
  split_ifs at wt_est
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T f) (eLpNormEssSup (T f) ν) ν := distribution_mono_right (le_trans wt_est ht)
  _ = _ := meas_essSup_lt

-- TODO: generalise this lemma in Mathlib/.../LpSeminorm/Basic.lean
theorem eLpNorm_eq_zero_iff_enorm {p : ℝ≥0∞} {μ : Measure α} [ENormedAddMonoid ε] {f : α → ε}
    (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

variable [ENormedAddMonoid ε₁] [ENormedAddMonoid ε₂] in
/-- If `T` has weaktype `p₀`-`p₁`, `f` is `AEStronglyMeasurable` and the `p`-norm of `f`
    vanishes, then the `q`-norm of `T f` vanishes. -/
lemma weaktype_aux₀ {f : α → ε₁} {T : (α → ε₁) → (α' → ε₂)}
    {p₀ q₀ p q : ℝ≥0∞} (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp : 0 < p) (hq : 0 < q)
    {C₀ : ℝ≥0} (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (hf : AEStronglyMeasurable f μ) (hF : eLpNorm f p μ = 0) : eLpNorm (T f) q ν = 0 := by
  have f_ae_0 : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff_enorm hf hp.ne').mp hF
  have hf₂ : eLpNorm f p₀ μ = 0 := (eLpNorm_eq_zero_iff_enorm hf hp₀.ne').mpr f_ae_0
  have hf₁ : MemLp f p₀ μ := ⟨hf, by rw [hf₂]; exact zero_lt_top⟩
  have := (h₀T f hf₁).2
  rw [hf₂, mul_zero] at this
  have wnorm_0 : wnorm (T f) q₀ ν = 0 := nonpos_iff_eq_zero.mp this
  have : (T f) =ᵐ[ν] 0 := (wnorm_eq_zero_iff hq₀.ne').mp wnorm_0
  exact (eLpNorm_eq_zero_iff_enorm (h₀T _ hf₁).1 hq.ne').mpr this

variable [MeasurableSpace E₁] [BorelSpace E₁]

-- for the remaining lemmas we use too much measure theory that is just for normed spaces
-- try to generalize to ENorm-classes after Mathlib refactor
variable {T : (α → E₁) → (α' → E₂)}

lemma weaktype_estimate_truncCompl {C₀ : ℝ≥0} {p p₀: ℝ≥0∞} {f : α → E₁}
    (hp₀ : 0 < p₀) {q₀ : ℝ≥0∞} (hp : p ≠ ⊤) (hq₀ : 0 < q₀) (hq₀' : q₀ < ⊤)
    (hp₀p : p₀ < p) (hf : MemLp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (ht : 0 < t) {a : ℝ≥0∞} (ha : 0 < a) :
    distribution (T (truncCompl f a)) t ν ≤ C₀ ^ q₀.toReal *
        eLpNorm (truncCompl f a) p₀ μ ^ q₀.toReal * (t ^ (-q₀.toReal)) := by
  apply weaktype_estimate hq₀ hq₀' ?_ h₀T ht
  exact truncCompl_Lp_Lq_lower hp ⟨hp₀, hp₀p⟩ ha hf

-- TODO: can we remove the hypothesis on a?
lemma weaktype_estimate_trunc {C₁ : ℝ≥0} {p p₁ q₁: ℝ≥0∞} {f : α → E₁}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₁' : q₁ < ⊤) (hp₁p : p < p₁) (hf : MemLp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) (ht : 0 < t) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    distribution (T (trunc f a)) t ν ≤ C₁ ^ q₁.toReal *
      eLpNorm (trunc f a) p₁ μ ^ q₁.toReal * (t ^ (-q₁.toReal)) :=
  weaktype_estimate hq₁ hq₁' (trunc_Lp_Lq_higher (p := p) ⟨hp, hp₁p⟩ hf ha) h₁T ht

lemma weaktype_estimate_trunc_top_top {a : ℝ≥0∞} {C₁ : ℝ≥0}
    (hC₁ : 0 < C₁) {p p₁ q₁ : ℝ≥0∞} (hp : 0 < p)
    (hp₁ : p₁ = ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : MemLp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ≥0∞} (ht : 0 < t) (ha : a = t / C₁) :
    distribution (T (trunc f a)) t ν = 0 := by
  by_cases ht : t = ⊤
  · simp [ht]
  rw [ha]
  have obs : MemLp (trunc f (t / C₁)) p₁ μ := trunc_Lp_Lq_higher ⟨hp, hp₁p⟩ hf (by finiteness)
  have wt_est := (h₁T (trunc f (t / C₁)) obs).2
  simp only [wnorm, eLpNorm, hq₁, ↓reduceIte, hp₁, top_ne_zero] at wt_est
  apply nonpos_iff_eq_zero.mp
  have ineq : eLpNormEssSup (T (trunc f (t / C₁))) ν ≤ t := calc
    _ ≤ C₁ * eLpNormEssSup (trunc f (t / C₁)) μ := wt_est
    _ ≤ C₁ * (max 0 (t / C₁)) := by
      gcongr
      exact trunc_eLpNormEssSup_le
    _ ≤ _ := by
      sorry /- TODO: this should have a much simpler proof now! let C := C₁.toReal
      have coe_C : C.toNNReal = C₁ := Real.toNNReal_coe
      rw [← coe_C, coe_coe_eq_ofReal, max_eq_right, --congrArg toReal coe_C,
        mul_div_cancel₀]
      · exact Ne.symm (ne_of_lt hC₁)
      · positivity
      · positivity -/
  calc
  _ ≤ distribution (T (trunc f (t / C₁))) (eLpNormEssSup (T (trunc f (t / C₁))) ν) ν :=
      distribution_mono_right ineq
  _ = 0 := distribution_snormEssSup

lemma weaktype_estimate_truncCompl_top {C₀ : ℝ≥0} (hC₀ : 0 < C₀) {p p₀ q₀ : ℝ≥0∞}
    (hp₀ : 0 < p₀) (hq₀ : q₀ = ⊤) (hp₀p : p₀ < p) (hp : p ≠ ⊤) {f : α → E₁} (hf : MemLp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (ht : 0 < t) {a : ℝ≥0∞} {d : ℝ≥0∞} -- (hd : 0 < d)
    (ha : a = (t / d) ^ (p₀.toReal / (p₀.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal) ^ p₀.toReal⁻¹) :
    distribution (T (truncCompl f a)) t ν = 0 := by
  by_cases ht' : t = ∞
  · simp [ht']
  rcases (eq_zero_or_pos (eLpNormEssSup f μ)) with snorm_zero | snorm_pos
  · have : eLpNorm (trnc ⊥ f a) ⊤ μ = 0 := by
      apply nonpos_iff_eq_zero.mp
      rw [← snorm_zero]
      exact eLpNorm_trnc_est (p := ⊤)
    have obs : eLpNorm (T (trnc ⊥ f a)) ⊤ ν = 0 :=
      weaktype_aux₀ hp₀ (hq₀ ▸ zero_lt_top) zero_lt_top zero_lt_top h₀T hf.1.truncCompl this
    exact nonpos_iff_eq_zero.mp (Trans.trans (distribution_mono_right (Trans.trans obs
      (zero_le t))) meas_eLpNormEssSup_lt)
  · have p_pos : 0 < p := lt_trans hp₀ hp₀p
    have snorm_p_pos : eLpNorm f p μ ≠ 0 := fun snorm_0 ↦ snorm_pos.ne' <|
      eLpNormEssSup_eq_zero_iff.mpr <| (eLpNorm_eq_zero_iff hf.1 p_pos.ne').mp snorm_0
    have term_pos : (ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal > 0 := by
      apply ENNReal.mul_pos <;> exact (rpow_pos_of_nonneg (by positivity) (by positivity)).ne'
    have term_ne_top : (ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal ≠ ⊤ :=
        mul_ne_top (rpow_ne_top'2 (ENNReal.coe_ne_zero.mpr hC₀.ne') coe_ne_top)
          (rpow_ne_top'2 snorm_p_pos (MemLp.eLpNorm_ne_top hf))
    have d_pos : 0 < d := hdeq ▸ ENNReal.rpow_pos term_pos term_ne_top
    have d_ne_top  : d ≠ ⊤ := hdeq ▸ ENNReal.rpow_ne_top_of_pos term_pos.ne' term_ne_top
    have a_pos : 0 < a := ha ▸ ENNReal.rpow_pos (ENNReal.div_pos ht.ne' d_ne_top) (by finiteness)
    have obs : MemLp (truncCompl f a) p₀ μ := truncCompl_Lp_Lq_lower hp ⟨hp₀, hp₀p⟩ a_pos hf
    have wt_est := (h₀T (truncCompl f a) obs).2
    unfold wnorm at wt_est
    split_ifs at wt_est
    have snorm_est : eLpNormEssSup (T (truncCompl f a)) ν ≤ t := by
      apply le_of_rpow_le2 (exp_toReal_pos2 hp₀ hp₀p.ne_top)
      calc
      _ ≤ (↑C₀ * eLpNorm (truncCompl f a) p₀ μ) ^ p₀.toReal := by gcongr
      _ ≤ (↑C₀) ^ p₀.toReal * ((a ^ (p₀.toReal - p.toReal)) *
          eLpNorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ toReal_nonneg]
        gcongr
        exact estimate_eLpNorm_truncCompl hp ⟨hp₀, hp₀p⟩ hf.1.aemeasurable a_pos
      _ = (↑C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal * (d ^ p₀.toReal)⁻¹ * (t ^ p₀.toReal) := by
        rw [ha, ← ENNReal.rpow_mul, div_mul_cancel₀]
        · sorry /- was: rw [ENNReal.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          rw [div_eq_mul_inv]
          ring -/
        · exact (sub_neg.mpr (toReal_strict_mono hp hp₀p)).ne
      _ = _ := by
        sorry /- TODO! was rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top, ENNReal.mul_inv_cancel (by positivity) term_ne_top]
        exact toReal_ne_zero.mpr ⟨hp₀.ne', hp₀p.ne_top⟩ -/
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ distribution (T (truncCompl f a)) (eLpNormEssSup (T (truncCompl f a)) ν) ν :=
      distribution_mono_right snorm_est
    _ = _ := meas_eLpNormEssSup_lt

lemma weaktype_estimate_trunc_top {C₁ : ℝ≥0} (hC₁ : 0 < C₁) {p p₁ q₁ : ℝ≥0∞}
    (hp : 0 < p)
    (hp₁ : p₁ < ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : MemLp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) (ht : 0 < t) {a : ℝ≥0∞} {d : ℝ≥0∞} -- (hd : 0 < d)
    (ha : a = (t / d) ^ (p₁.toReal / (p₁.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal) ^ p₁.toReal⁻¹) :
    distribution (T (trunc f a)) t ν = 0 := by
  have obs : MemLp (trunc f a) p₁ μ := trunc_Lp_Lq_higher ⟨hp, hp₁p⟩ hf sorry -- TODO: prove!
  have wt_est := (h₁T (trunc f a) obs).2
  unfold wnorm at wt_est
  split_ifs at wt_est
  have : p₁.toReal ≠ 0 := exp_toReal_ne_zero'2 (lt_trans hp hp₁p) hp₁.ne_top
  have : eLpNormEssSup (T (trunc f a)) ν ^ p₁.toReal ≤
      (C₁ * eLpNorm (trunc f a) p₁ μ) ^ p₁.toReal := by gcongr
  have snorm_est : eLpNormEssSup (T (trunc f a)) ν ≤ t := by
    apply le_of_rpow_le2 (exp_toReal_pos2 (lt_trans hp hp₁p) hp₁.ne_top)
    refine le_trans this ?_
    rcases (eq_zero_or_pos (eLpNormEssSup f μ)) with snorm_zero | snorm_pos
    · gcongr
      calc
      _ ≤ (ENNReal.ofNNReal C₁) * eLpNorm f p₁ μ := by
        gcongr
        apply eLpNorm_mono (fun x ↦ trunc_le_func)
      _ ≤ _ := by
        have : eLpNorm f p₁ μ = 0 := Trans.trans (eLpNorm_congr_ae
            (eLpNormEssSup_eq_zero_iff.mp snorm_zero)) eLpNorm_zero
        simp only [this, mul_zero, zero_le]
    · have snorm_p_pos : eLpNorm f p μ ≠ 0 := by
        intro snorm_0
        apply Ne.symm (ne_of_lt snorm_pos)
        apply eLpNormEssSup_eq_zero_iff.mpr
        exact (eLpNorm_eq_zero_iff hf.1 hp.ne').mp snorm_0
      -- XXX: these lines are the same as above
      have term_pos : (ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal > 0 := by
        apply ENNReal.mul_pos <;> exact (rpow_pos_of_nonneg (by positivity) (by positivity)).ne'
      have term_ne_top : (ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal ≠ ⊤ :=
        mul_ne_top (rpow_ne_top'2 (ENNReal.coe_ne_zero.mpr hC₁.ne') coe_ne_top)
          (rpow_ne_top'2 snorm_p_pos (MemLp.eLpNorm_ne_top hf))
      have d_pos : 0 < d := hdeq ▸ ENNReal.rpow_pos term_pos term_ne_top
      calc
      _ ≤ ↑C₁ ^ p₁.toReal * (((a ^ (p₁.toReal - p.toReal))) * eLpNorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        gcongr
        · exact estimate_eLpNorm_trunc hp₁.ne_top ⟨hp, hp₁p⟩ hf.1
        · exact toReal_nonneg
      _ = ↑C₁ ^ p₁.toReal * eLpNorm f p μ ^ p.toReal * (d ^ p₁.toReal)⁻¹ * (t ^ p₁.toReal) := by
        rw [ha, ← ENNReal.rpow_mul, div_mul_cancel₀]
        · sorry /- proof was: rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          rw [div_eq_mul_inv]
          ring -/
          -- MR: can this be shared with the lemma above?
        · exact (sub_pos.mpr (toReal_strict_mono hp₁.ne_top hp₁p)).ne'
      _ = _ := by
        --rw [ofReal_rpow_of_pos ht]
        nth_rw 2 [← one_mul (t ^ p₁.toReal)]
        congr
        sorry /- proof was; also need hdeq
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top, ENNReal.mul_inv_cancel (by positivity) term_ne_top] -/
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T (trunc f a)) (eLpNormEssSup (T (trunc f a)) ν) ν := by gcongr
  _ = _ := meas_eLpNormEssSup_lt

end MeasureTheory

end
