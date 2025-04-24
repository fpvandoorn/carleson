import Carleson.ToMathlib.WeakType
import Carleson.ToMathlib.RealInterpolation.Basic

/-!
# Minkowski's integral inequality

In this file, we prove Minkowski's integral inequality and apply it to truncations.
We use this to deduce weak type estimates for truncations.

-/

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents
    ComputationsChoiceExponent

variable {α α' ε E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}
  {f : α → E₁} {t : ℝ}

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
  refine le_of_rpow_le (inv_pos_of_pos p_pos) ?_
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
    NullMeasurableSet {(s, x) : ℝ × α | ‖g x‖₊ ≤ tc.ton s }
        ((volume.restrict (Ioi 0)).prod μ) :=
  nullMeasurableSet_le hg.snd.norm (ton_aeMeasurable tc).fst

@[measurability]
lemma indicator_ton_measurable_lt {g : α → E₁} [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [BorelSpace E₁] [SigmaFinite μ] (hg : AEMeasurable g μ) (tc : ToneCouple) :
    NullMeasurableSet {(s, x) : ℝ × α | tc.ton s < ‖g x‖₊ }
        ((volume.restrict (Ioi 0)).prod μ) :=
  nullMeasurableSet_lt (ton_aeMeasurable tc).fst hg.snd.norm

@[measurability]
lemma AEMeasurable.trunc_ton {f : α → E₁}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [SigmaFinite (μ.restrict (Function.support f))] -- TODO: TypeClass or implicit variable?
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a : ℝ × α ↦ (trunc f (tc.ton a.1)) a.2)
    ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f) )) := by
  let A := {(s, x) : ℝ × α | ‖f x‖₊ ≤ tc.ton s}
  have : (fun z : ℝ × α ↦ (trunc f (tc.ton z.1)) z.2) =
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
    AEMeasurable (fun a : ℝ × α ↦ ((truncCompl f (tc.ton a.1))) a.2)
    ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f) )) := by
  let A := {(s, x) : ℝ × α | tc.ton s < ‖f x‖₊}
  have : (fun z : ℝ × α ↦ (truncCompl f (tc.ton z.1)) z.2) = Set.indicator A (fun z : ℝ × α ↦ f z.2) := by
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

lemma restrict_to_support_truncCompl {p : ℝ} [NormedAddCommGroup E₁] (hp : 0 < p)
    (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖(truncCompl f t) x‖ₑ ^ p ∂μ =
    ∫⁻ x : α, ‖(truncCompl f t) x‖ₑ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support
  rw [truncCompl_eq, setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  simp [hp, f_zero]

lemma restrict_to_support_trnc {p : ℝ} {j : Bool} [NormedAddCommGroup E₁] (hp : 0 < p)
    (f : α → E₁) :
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
  j.rec (hf.truncCompl_ton _) (hf.trunc_ton _)

lemma lintegral_lintegral_pow_swap_truncCompl {q q₀ p₀ : ℝ} [MeasurableSpace E₁]
    [NormedAddCommGroup E₁]
    [BorelSpace E₁] {j : Bool} {hμ : SigmaFinite (μ.restrict (Function.support f))}
    (hp₀ : 0 < p₀) (hp₀q₀ : p₀ ≤ q₀)
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    ∫⁻ (s : ℝ) in Ioi 0,
        (∫⁻ (a : α) in Function.support f, ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton s) a‖ₑ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) ≤
    (∫⁻ a : α in Function.support f,
      (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton s) a‖ₑ ^ p₀) ^ (p₀⁻¹ * q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
  apply lintegral_lintegral_pow_swap_rpow
  · apply le_of_mul_le_mul_left _ hp₀
    field_simp [hp₀q₀]
  · unfold Function.uncurry
    simp only [Pi.sub_apply]
    fun_prop

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
    eLpNorm (trnc j f ((spf_to_tc spf).ton s)) (ENNReal.ofReal p₀) μ ^ q₀ *
    ENNReal.ofReal (s ^ (q - q₀ - 1)) ≤
    ENNReal.ofReal (spf.d ^ (q - q₀)) * ENNReal.ofReal |q - q₀|⁻¹ *
    (∫⁻ (a : α) in Function.support f,
    ENNReal.ofReal (‖f a‖ ^ (p₀ + spf.σ⁻¹ * (q - q₀) * (p₀ / q₀))) ∂μ) ^
    (p₀⁻¹ * q₀) := by
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
    ((∫⁻ (a : α), ↑‖trnc j f ((spf_to_tc spf).ton s) a‖ₑ ^ p₀ ∂μ) ^ (1 / p₀)) ^ q₀ := by
      simp only [enorm_eq_nnnorm]
      congr 1
      ext x
      rw [mul_comm]
    _ = ∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹) ^ (p₀⁻¹ * q₀) *
        (∫⁻ (a : α) in Function.support f, ↑‖trnc j f (tc.ton s) a‖ₑ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [ENNReal.rpow_inv_rpow]
      · rw [one_div, ← ENNReal.rpow_mul, restrict_to_support_trnc hp₀]
      · positivity
    _ = ∫⁻ (s : ℝ) in Ioi 0,
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton s) a‖ₑ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [lintegral_const_mul', ENNReal.mul_rpow_of_nonneg]
      · positivity
      · exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) coe_ne_top).ne
    _ ≤ (∫⁻ a : α in Function.support f,
        (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ‖trnc j f (tc.ton s) a‖ₑ ^ p₀) ^ (p₀⁻¹ * q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      -- This is a consequence of Minkowski's integral inequality
      apply lintegral_lintegral_pow_swap_truncCompl hp₀ hp₀q₀ hf tc; assumption
    _ = (∫⁻ a : α in Function.support f,
        (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) *
        ↑‖trnc j f (tc.ton s) a‖ₑ ^ q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
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
        ((∫⁻ (s : ℝ) in res (xor j tc.mon) (tc.inv ‖f a‖),
        (ENNReal.ofReal (s ^ (q - q₀ - 1))))*
        ‖f a‖ₑ ^ q₀) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 1
      apply lintegral_trunc_mul hq₀ (nnnorm_pos.mpr hfx)
    _ = (∫⁻ a : α in Function.support f,
        ((ENNReal.ofReal (tc.inv ‖f a‖ ^ (q - q₀ - 1 + 1) / |q - q₀ - 1 + 1|)) *
        ENNReal.ofReal (‖f a‖ ^ q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 2
      · apply value_lintegral_res₀
        · apply tc.ran_inv
          exact norm_pos_iff.mpr hfx
        · split_ifs with h
          · simp only [h, ↓reduceIte] at hpowers; linarith
          · simp only [h, Bool.false_eq_true, ↓reduceIte] at hpowers; linarith
      · rw [← ofReal_rpow_of_nonneg, ofReal_norm_eq_enorm] <;> positivity
    _ = (∫⁻ a : α in Function.support f,
        ((ENNReal.ofReal
        (spf.d ^ (q - q₀ - 1 + 1) * ‖f a‖ ^ (spf.σ⁻¹ * (q - q₀ - 1 + 1) + q₀) /
      |q - q₀ - 1 + 1|))) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 1
      apply value_lintegral_res₁
      exact norm_pos_iff.mpr hfx
    _ = (∫⁻ a : α in Function.support f,
        ((ENNReal.ofReal (spf.d ^ (q - q₀)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ENNReal.ofReal (‖f a‖ ^ ((spf.σ⁻¹ * (q - q₀) + q₀) * (p₀⁻¹ * q₀)⁻¹)) *
    ENNReal.ofReal |q - q₀|⁻¹ ^ (p₀⁻¹ * q₀)⁻¹))  ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x _
      rw [div_eq_mul_inv, ENNReal.ofReal_mul, sub_add_cancel, ENNReal.ofReal_mul,
          ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg] <;> try positivity
      nth_rw 2 [ENNReal.ofReal_rpow_of_nonneg] <;> try positivity
      rw [← Real.rpow_mul] ; try positivity
    _ = ENNReal.ofReal (spf.d ^ (q - q₀)) *
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (‖f a‖ ^ ((spf.σ⁻¹ * (q - q₀) + q₀) * (p₀⁻¹ * q₀)⁻¹)) ∂μ) ^
        (p₀⁻¹ * q₀) *
        ENNReal.ofReal |q - q₀|⁻¹ := by
      rw [lintegral_mul_const', lintegral_const_mul', ENNReal.mul_rpow_of_nonneg,
          ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_inv_rpow, ENNReal.rpow_inv_rpow] <;>
          try positivity
      · exact rpow_ne_top_of_nonneg (by positivity) coe_ne_top
      · exact rpow_ne_top_of_nonneg (by positivity) coe_ne_top
    _ = ENNReal.ofReal (spf.d ^ (q - q₀)) *
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (‖f a‖ ^ (p₀ + spf.σ⁻¹ * (q - q₀) * (p₀ / q₀))) ∂μ) ^
        (p₀⁻¹ * q₀) *
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
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hf : AEMeasurable f μ) (hf₂ : SigmaFinite (μ.restrict (Function.support f)))
    (hspf : spf.σ = ζ p₀ q₀ p₁ q₁ t) :
    ∫⁻ s : ℝ in Ioi 0,
    eLpNorm (trnc j f ((spf_to_tc spf).ton s)) (sel j p₀ p₁) μ ^ (sel j q₀ q₁).toReal *
    ENNReal.ofReal (s ^ (q.toReal - (sel j q₀ q₁).toReal - 1)) ≤
    ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
    ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
    ((eLpNorm f p μ) ^ p.toReal) ^ ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
  have p_toReal_pos : 0 < p.toReal :=
    interp_exp_toReal_pos' ht hp₀ hp₁ hp (Or.inl hp₀p₁.ne_top)
  calc
  _ ≤ ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (∫⁻ (a : α) in Function.support f,
      ENNReal.ofReal (‖f a‖ ^ ((sel j p₀ p₁).toReal + spf.σ⁻¹ * (q.toReal - (sel j q₀ q₁).toReal) *
      ((sel j p₀ p₁).toReal / (sel j q₀ q₁).toReal))) ∂μ) ^
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
          · exact interp_exp_ne_top hq₀q₁ ht hq
          · exact (ζ_pos_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp is_ζ_pos
        · apply toReal_strict_mono hq'
          exact (ζ_le_zero_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp
            (le_of_not_lt is_ζ_pos)
      · unfold sel
        dsimp only
        rw [hspf]
        simp only [Bool.if_false_right, Bool.and_true, Bool.true_bne, Bool.not_eq_true',
            decide_eq_false_iff_not]
        split_ifs with is_ζ_pos
        · apply toReal_strict_mono hq'
          exact (ζ_pos_iff_of_lt₁ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp is_ζ_pos
        · apply toReal_strict_mono
          · exact interp_exp_ne_top hq₀q₁ ht hq
          · exact (ζ_le_zero_iff_of_lt₁ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp
                (le_of_not_lt is_ζ_pos)
  _ = ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
        ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ) ^
        ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    ext x
    congr
    rcases j
    · dsimp only [sel]
      rw [hspf]
      apply ζ_equality₅ (hp₀p₁ := hp₀p₁.ne) <;> assumption
    · dsimp only [sel]
      rw [hspf]
      apply ζ_equality₆ (hp₀p₁ := hp₀p₁.ne) <;> assumption
  _ ≤ ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (∫⁻ (a : α),
      ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    gcongr
    exact setLIntegral_le_lintegral _ _
  _ = ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (((∫⁻ (a : α), ‖f a‖ₑ ^ p.toReal ∂μ) ^ p.toReal⁻¹ ) ^ p.toReal) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    rw [ENNReal.rpow_inv_rpow] <;> try positivity
    congr
    ext x
    rw [← ofReal_rpow_of_nonneg] <;> try positivity
    congr
    exact ofReal_norm_eq_enorm (f x)
  _ = ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      ((eLpNorm f p μ) ^ p.toReal) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    rw [← one_div]
    refine (eLpNorm_eq_lintegral_rpow_enorm (ε := E₁) ?_ ?_).symm
    · exact (interpolated_pos' hp₀ hp₁ hp).ne'
    · exact interp_exp_ne_top hp₀p₁.ne ht hp

-- TODO: move this to WeakType.lean?
lemma wnorm_eq_zero_iff {f : α → E₁} {p : ℝ≥0∞} [NormedAddCommGroup E₁] (hp : p ≠ 0) :
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
    eLpNorm (trnc j f t) p μ ≤ eLpNorm f p μ := eLpNorm_mono fun _x ↦ trnc_le_func

variable [TopologicalSpace ε] [ContinuousENorm ε] {T : (α → E₁) → (α' → ε)} in
-- TODO: remove the subindex 0 here
lemma weaktype_estimate {C₀ : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞} {f : α → E₁}
      (hq : 0 < q) (hq' : q < ⊤) (hf : MemLp f p μ)
    (h₀T : HasWeakType T p q μ ν C₀) (ht : 0 < t) :
    distribution (T f) (ENNReal.ofReal t) ν ≤ C₀ ^ q.toReal *
        eLpNorm f p μ ^ q.toReal * ENNReal.ofReal (t ^ (-q.toReal)) := by
  have wt_est := (h₀T f hf).2 -- the weaktype estimate
  have q_pos : 0 < q.toReal := toReal_pos hq.ne' hq'.ne_top
  have tq_pos : 0 < ENNReal.ofReal t ^ q.toReal := coe_pow_pos ht
  have tq_ne_top : (ENNReal.ofReal t) ^ q.toReal ≠ ⊤ := coe_rpow_ne_top' q_pos
  -- have hq₁ : q.toReal = q := by exact toReal_ofReal q_nonneg
  simp only [wnorm, wnorm', hq'.ne_top, ↓reduceIte, iSup_le_iff] at wt_est
  have wt_est_t := wt_est t.toNNReal -- this is the weaktype estimate applied to t
  rw [← ENNReal.mul_le_mul_right (c := (ENNReal.ofReal t) ^ q.toReal) _ tq_ne_top,
      ofReal_rpow_of_pos, mul_assoc _ _ (ENNReal.ofReal (t ^ q.toReal)), ← ofReal_mul',
      ← Real.rpow_add, neg_add_cancel, Real.rpow_zero, ofReal_one, mul_one, mul_comm,
      ← ENNReal.mul_rpow_of_nonneg] <;> try positivity
  refine (ENNReal.rpow_inv_le_iff q_pos).mp ?_
  rw [ENNReal.mul_rpow_of_nonneg, ENNReal.ofReal_rpow_of_pos,
      Real.rpow_rpow_inv] <;> try positivity
  rwa [← coe_coe_eq_ofReal]

variable [TopologicalSpace ε] [ContinuousENorm ε] {T : (α → E₁) → (α' → ε)} in
lemma weaktype_estimate_top {C : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞}
    (hq' : q = ⊤) {f : α → E₁} (hf : MemLp f p μ)
    (hT : HasWeakType T p q μ ν C) {t : ℝ} (ht : C * eLpNorm f p μ ≤ ENNReal.ofReal t) :
    distribution (T f) (ENNReal.ofReal t) ν = 0 := by
  have wt_est := (hT f hf).2
  unfold wnorm at wt_est
  split_ifs at wt_est
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T f) (eLpNormEssSup (T f) ν) ν := distribution_mono_right (le_trans wt_est ht)
  _ = _ := meas_essSup_lt -- meas_eLpNormEssSup_lt

-- for the remaining lemmas we use too much measure theory that is just for normed spaces
-- try to generalize to ENorm-classes after Mathlib refactor
variable {T : (α → E₁) → (α' → E₂)}

/-- If `T` has weaktype `p₀`-`p₁`, `f` is `AEStronglyMeasurable` and the `p`-norm of `f`
    vanishes, then the `q`-norm of `T f` vanishes. -/
lemma weaktype_aux₀ {p₀ q₀ p q : ℝ≥0∞} (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hp : 0 < p) (hq : 0 < q)
    {C₀ : ℝ≥0} (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (hf : AEStronglyMeasurable f μ) (hF : eLpNorm f p μ = 0) : eLpNorm (T f) q ν = 0 := by
  have f_ae_0 : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hf hp.ne').mp hF
  have hf₂ : eLpNorm f p₀ μ = 0 := (eLpNorm_eq_zero_iff hf hp₀.ne').mpr f_ae_0
  have hf₁ : MemLp f p₀ μ := ⟨hf, by rw [hf₂]; exact zero_lt_top⟩
  have := (h₀T f hf₁).2
  rw [hf₂, mul_zero] at this
  have wnorm_0 : wnorm (T f) q₀ ν = 0 := nonpos_iff_eq_zero.mp this
  have : (T f) =ᵐ[ν] 0 := (wnorm_eq_zero_iff hq₀.ne').mp wnorm_0
  exact (eLpNorm_eq_zero_iff (h₀T _ hf₁).1 hq.ne').mpr this

variable [MeasurableSpace E₁] [BorelSpace E₁]

lemma weaktype_estimate_truncCompl {C₀ : ℝ≥0} {p p₀: ℝ≥0∞} {f : α → E₁}
    (hp₀ : 0 < p₀) {q₀ : ℝ≥0∞} (hp : p ≠ ⊤) (hq₀ : 0 < q₀) (hq₀' : q₀ < ⊤)
    (hp₀p : p₀ < p) (hf : MemLp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 < a) :
    distribution (T (truncCompl f a)) (ENNReal.ofReal t) ν ≤ C₀ ^ q₀.toReal *
        eLpNorm (truncCompl f a) p₀ μ ^ q₀.toReal * (ENNReal.ofReal (t ^ (-q₀.toReal))) := by
  apply weaktype_estimate hq₀ hq₀' ?_ h₀T ht
  exact truncCompl_Lp_Lq_lower hp ⟨hp₀, hp₀p⟩ ha hf

lemma weaktype_estimate_trunc {C₁ : ℝ≥0} {p p₁ q₁: ℝ≥0∞} {f : α → E₁}
    (hp : 0 < p)
    (hq₁ : 0 < q₁) (hq₁' : q₁ < ⊤) (hp₁p : p < p₁)
    (hf : MemLp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : 0 < t) {a : ℝ} :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν ≤ C₁ ^ q₁.toReal *
      eLpNorm (trunc f a) p₁ μ ^ q₁.toReal * ENNReal.ofReal (t ^ (-q₁.toReal)) :=
  weaktype_estimate hq₁ hq₁' (trunc_Lp_Lq_higher (p := p) ⟨hp, hp₁p⟩ hf) h₁T ht

lemma weaktype_estimate_trunc_top_top {a : ℝ} {C₁ : ℝ≥0}
    (hC₁ : 0 < C₁) {p p₁ q₁ : ℝ≥0∞} (hp : 0 < p)
    (hp₁ : p₁ = ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : MemLp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : 0 < t) (ha : a = t / C₁) :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  rw [ha]
  have obs : MemLp (trunc f (t / C₁)) p₁ μ := trunc_Lp_Lq_higher ⟨hp, hp₁p⟩ hf
  have wt_est := (h₁T (trunc f (t / C₁)) obs).2
  simp only [wnorm, eLpNorm, hq₁, ↓reduceIte, hp₁, top_ne_zero] at wt_est
  apply nonpos_iff_eq_zero.mp
  have ineq : eLpNormEssSup (T (trunc f (t / C₁))) ν ≤ ENNReal.ofReal t := calc
    _ ≤ C₁ * eLpNormEssSup (trunc f (t / C₁)) μ := wt_est
    _ ≤ C₁ * ENNReal.ofReal (max 0 (t / C₁)) := by
      gcongr
      exact trunc_eLpNormEssSup_le
    _ ≤ _ := by
      let C := C₁.toReal
      have coe_C : C.toNNReal = C₁ := Real.toNNReal_coe
      rw [← coe_C, coe_coe_eq_ofReal, ← ENNReal.ofReal_mul, max_eq_right, congrArg toReal coe_C,
        mul_div_cancel₀]
      · exact Ne.symm (ne_of_lt hC₁)
      · positivity
      · positivity
  calc
  _ ≤ distribution (T (trunc f (t / C₁))) (eLpNormEssSup (T (trunc f (t / C₁))) ν) ν :=
      distribution_mono_right ineq
  _ = 0 := distribution_snormEssSup

lemma weaktype_estimate_truncCompl_top {C₀ : ℝ≥0} (hC₀ : 0 < C₀) {p p₀ q₀ : ℝ≥0∞}
    (hp₀ : 0 < p₀) (hq₀ : q₀ = ⊤) (hp₀p : p₀ < p) (hp : p ≠ ⊤) {f : α → E₁} (hf : MemLp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) {t : ℝ} (ht : 0 < t) {a : ℝ} {d : ℝ} -- (hd : 0 < d)
    (ha : a = (t / d) ^ (p₀.toReal / (p₀.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₀) ^ p₀.toReal *
        eLpNorm f p μ ^ p.toReal).toReal ^ p₀.toReal⁻¹) :
    distribution (T (truncCompl f a)) (ENNReal.ofReal t) ν = 0 := by
  rcases (eq_zero_or_pos (eLpNormEssSup f μ)) with snorm_zero | snorm_pos
  · have : eLpNorm (trnc ⊥ f a) ⊤ μ = 0 := by
      apply nonpos_iff_eq_zero.mp
      rw [← snorm_zero]
      exact eLpNorm_trnc_est (p := ⊤)
    have obs : eLpNorm (T (trnc ⊥ f a)) ⊤ ν = 0 :=
      weaktype_aux₀ hp₀ (hq₀ ▸ zero_lt_top) zero_lt_top zero_lt_top h₀T hf.1.truncCompl this
    exact nonpos_iff_eq_zero.mp (Trans.trans (distribution_mono_right (Trans.trans obs
      (zero_le (ENNReal.ofReal t)))) meas_eLpNormEssSup_lt)
  · have p_pos : 0 < p := lt_trans hp₀ hp₀p
    have snorm_p_pos : eLpNorm f p μ ≠ 0 := fun snorm_0 ↦ snorm_pos.ne' <|
      eLpNormEssSup_eq_zero_iff.mpr <| (eLpNorm_eq_zero_iff hf.1 p_pos.ne').mp snorm_0
    have term_pos : (ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal > 0 := by
      apply ENNReal.mul_pos <;> exact (rpow_pos_of_nonneg (by positivity) (by positivity)).ne'
    have term_ne_top : (ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal ≠ ⊤ :=
        mul_ne_top (rpow_ne_top' (ENNReal.coe_ne_zero.mpr hC₀.ne') coe_ne_top)
          (rpow_ne_top' snorm_p_pos (MemLp.eLpNorm_ne_top hf))
    have d_pos : 0 < d := hdeq ▸ Real.rpow_pos_of_pos (toReal_zero ▸
      toReal_strict_mono term_ne_top term_pos) _
    have a_pos : 0 < a := by rw [ha]; positivity
    have obs : MemLp (truncCompl f a) p₀ μ := truncCompl_Lp_Lq_lower hp ⟨hp₀, hp₀p⟩ a_pos hf
    have wt_est := (h₀T (truncCompl f a) obs).2
    unfold wnorm at wt_est
    split_ifs at wt_est
    have snorm_est : eLpNormEssSup (T (truncCompl f a)) ν ≤ ENNReal.ofReal t := by
      apply le_of_rpow_le (exp_toReal_pos hp₀ hp₀p.ne_top)
      calc
      _ ≤ (↑C₀ * eLpNorm (truncCompl f a) p₀ μ) ^ p₀.toReal := by gcongr
      _ ≤ (↑C₀) ^ p₀.toReal * (ENNReal.ofReal (a ^ (p₀.toReal - p.toReal)) *
          eLpNorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ toReal_nonneg]
        gcongr
        exact estimate_eLpNorm_truncCompl hp ⟨hp₀, hp₀p⟩ hf.1.aemeasurable a_pos
      _ = (↑C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal *
          (ENNReal.ofReal (d ^ p₀.toReal))⁻¹ * ENNReal.ofReal (t ^ p₀.toReal) := by
        rw [ha, ← Real.rpow_mul, div_mul_cancel₀]
        · rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          rw [div_eq_mul_inv]
          ring
        · exact (sub_neg.mpr (toReal_strict_mono hp hp₀p)).ne
        · positivity
      _ = _ := by
        rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top, ENNReal.mul_inv_cancel (by positivity) term_ne_top]
        exact toReal_ne_zero.mpr ⟨hp₀.ne', hp₀p.ne_top⟩
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ distribution (T (truncCompl f a)) (eLpNormEssSup (T (truncCompl f a)) ν) ν :=
      distribution_mono_right snorm_est
    _ = _ := meas_eLpNormEssSup_lt

lemma weaktype_estimate_trunc_top {C₁ : ℝ≥0} (hC₁ : 0 < C₁) {p p₁ q₁ : ℝ≥0∞}
    (hp : 0 < p)
    (hp₁ : p₁ < ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : MemLp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : 0 < t) {a : ℝ} {d : ℝ} -- (hd : 0 < d)
    (ha : a = (t / d) ^ (p₁.toReal / (p₁.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₁) ^ p₁.toReal *
        eLpNorm f p μ ^ p.toReal).toReal ^ p₁.toReal⁻¹) :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  have obs : MemLp (trunc f a) p₁ μ := trunc_Lp_Lq_higher ⟨hp, hp₁p⟩ hf
  have wt_est := (h₁T (trunc f a) obs).2
  unfold wnorm at wt_est
  split_ifs at wt_est
  have : p₁.toReal ≠ 0 := exp_toReal_ne_zero' (lt_trans hp hp₁p) hp₁.ne_top
  have : eLpNormEssSup (T (trunc f a)) ν ^ p₁.toReal ≤
      (C₁ * eLpNorm (trunc f a) p₁ μ) ^ p₁.toReal := by gcongr
  have snorm_est : eLpNormEssSup (T (trunc f a)) ν ≤ ENNReal.ofReal t := by
    apply le_of_rpow_le (exp_toReal_pos (lt_trans hp hp₁p) hp₁.ne_top)
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
      have term_pos : (ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal > 0 := by
        apply ENNReal.mul_pos <;> exact (rpow_pos_of_nonneg (by positivity) (by positivity)).ne'
      have term_ne_top : (ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal ≠ ⊤ :=
        mul_ne_top (rpow_ne_top' (ENNReal.coe_ne_zero.mpr hC₁.ne') coe_ne_top)
          (rpow_ne_top' snorm_p_pos (MemLp.eLpNorm_ne_top hf))
      have d_pos : 0 < d  := hdeq ▸ Real.rpow_pos_of_pos (toReal_zero ▸
        toReal_strict_mono term_ne_top term_pos) _
      calc
      _ ≤ ↑C₁ ^ p₁.toReal * ((ENNReal.ofReal (a ^ (p₁.toReal - p.toReal))) * eLpNorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        gcongr
        · exact estimate_eLpNorm_trunc hp₁.ne_top ⟨hp, hp₁p⟩ hf.1.aemeasurable
        · exact toReal_nonneg
      _ = ↑C₁ ^ p₁.toReal * eLpNorm f p μ ^ p.toReal * (ENNReal.ofReal (d ^ p₁.toReal))⁻¹ *
          ENNReal.ofReal (t ^ p₁.toReal) := by
        rw [ha, ← Real.rpow_mul, div_mul_cancel₀]
        · rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          rw [div_eq_mul_inv]
          ring
        · exact (sub_pos.mpr (toReal_strict_mono hp₁.ne_top hp₁p)).ne'
        · positivity
      _ = _ := by
        rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top, ENNReal.mul_inv_cancel (by positivity) term_ne_top]
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T (trunc f a)) (eLpNormEssSup (T (trunc f a)) ν) ν := by gcongr
  _ = _ := meas_eLpNormEssSup_lt

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set Pointwise

variable {α α' ε E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ} -- truncation parameter
  [NormedAddCommGroup E] [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₃] [BorelSpace E₃]
  {f : α → E₁} {t : ℝ}
  {T : (α → E₁) → (α' → E₂)}
namespace MeasureTheory

-- /-- # The real interpolation theorem

-- ## Definitions-/

def Subadditive [ENorm ε] (T : (α → E₁) → α' → ε) : Prop :=
  ∃ A ≠ ⊤, ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

def Subadditive_trunc [ENorm ε] (T : (α → E₁) → α' → ε) (A : ℝ≥0∞) (f : α → E₁) (ν : Measure α') :
    Prop :=
  ∀ a : ℝ, 0 < a → ∀ᵐ y ∂ν,
  ‖T (trunc f a + truncCompl f a) y‖ₑ ≤ A * (‖T (trunc f a) y‖ₑ + ‖T (truncCompl f a) y‖ₑ)

/-- The operator is subadditive on functions satisfying `P` with constant `A`
(this is almost vacuous if `A = ⊤`). -/
def AESubadditiveOn [ENorm ε] (T : (α → E₁) → α' → ε) (P : (α → E₁) → Prop) (A : ℝ≥0∞)
    (ν : Measure α') : Prop :=
  ∀ (f g : α → E₁), P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

namespace AESubadditiveOn

variable [TopologicalSpace ε] [ENormedAddMonoid ε] {ν : Measure α'}

lemma antitone {T : (α → E₁) → α' → ε} {P P' : (α → E₁) → Prop}
    (h : ∀ {u : α → E₁}, P u → P' u) {A : ℝ≥0∞} (sa : AESubadditiveOn T P' A ν) :
    AESubadditiveOn T P A ν :=
  fun f g hf hg ↦ sa f g (h hf) (h hg)

lemma zero {P : (α → E₁) → Prop} (hP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (A : ℝ≥0∞) (h : ∀ u, P u → T u =ᵐ[ν] 0) : AESubadditiveOn T P A ν := by
  intro f g hf hg
  filter_upwards [h f hf, h g hg, h (f + g) (hP hf hg)] with x hx1 hx2 hx3
  simp [hx1, hx2, hx3]

lemma forall_le {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → E₁) → α' → ε}
    {P : (α → E₁) → Prop} {A : ℝ≥0∞}
    (h : ∀ i ∈ 𝓑, AESubadditiveOn (T i) P A ν)
    {f g : α → E₁} (hf : P f) (hg : P g) :
    ∀ᵐ x ∂ν, ∀ i ∈ 𝓑, ‖T i (f + g) x‖ₑ ≤ A * (‖T i f x‖ₑ + ‖T i g x‖ₑ) :=
  eventually_countable_ball h𝓑 |>.mpr fun i hi ↦ h i hi f g hf hg

lemma biSup {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → E₁) → α' → ℝ≥0∞}
    {P : (α → E₁) → Prop} (hT : ∀ (u : α → E₁), P u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (hP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    {A : ℝ≥0∞} (h : ∀ i ∈ 𝓑, AESubadditiveOn (T i) P A ν) :
    AESubadditiveOn (fun u x ↦ ⨆ i ∈ 𝓑, T i u x) P A ν := by
  have hT' : ∀ i ∈ 𝓑, ∀ (u : α → E₁), P u → ∀ᵐ x ∂ν, T i u x ≠ ∞ := by
    intro i hi f hf
    filter_upwards [hT f hf] with x hx
    rw [ne_eq, eq_top_iff] at hx ⊢
    exact fun h ↦ hx <| h.trans (le_biSup (fun i ↦ T i f x) hi)
  -- rcases lt_or_le A 0 with A0 | A0
  -- · refine AESubadditiveOn.zero hP A (fun f hf ↦ ?_)
  --   have h (i : ι) (hi : i ∈ 𝓑) := (h i hi).neg _ A0
  --   simp_rw [Set.forall_in_swap, imp.swap, ← imp_forall_iff] at h hT'
  --   filter_upwards [(ae_ball_iff h𝓑).mpr (h f hf), (ae_ball_iff h𝓑).mpr (hT' f hf)] with x hx hx'
  --   simp only [Pi.zero_apply, toReal_eq_zero_iff, ENNReal.iSup_eq_zero]
  --   refine Or.inl fun i hi ↦ ?_
  --   have := (ENNReal.toReal_eq_zero_iff _).mp (hx i hi)
  --   tauto
  intro f g hf hg
  simp_rw [AESubadditiveOn, Set.forall_in_swap, imp.swap, ← imp_forall_iff] at h hT'
  specialize h f hf g hg
  simp_rw [enorm_eq_self] at h ⊢
  filter_upwards [hT f hf, hT g hg, (ae_ball_iff h𝓑).mpr h, (ae_ball_iff h𝓑).mpr (hT' f hf),
    (ae_ball_iff h𝓑).mpr (hT' g hg), (ae_ball_iff h𝓑).mpr (hT' (f + g) (hP hf hg))] with x hTfx hTgx hx hT'fx hT'gx hT'fgx
  simp_rw [iSup_le_iff]
  intro i hi
  specialize hx i hi
  apply hx.trans
  gcongr <;> apply le_biSup _ hi

lemma indicator {T : (α → E₁) → α' → ε} {P : (α → E₁) → Prop} {A : ℝ≥0∞}
    (sa : AESubadditiveOn T P A ν) (S : Set α') :
    AESubadditiveOn (fun u x ↦ (S.indicator (fun y ↦ T u y) x)) P A ν := by
  intro f g hf hg
  filter_upwards [sa f g hf hg] with x hx
  by_cases h : x ∈ S <;> simp [hx, h]

-- If `T` is constant in the second argument (but not necessarily the first) and satisfies
-- a subadditivity criterion, then `AESubadditiveOn T P 1`
lemma const (T : (α → E₁) → ε) (P : (α → E₁) → Prop)
    (h_add : ∀ {f g}, P f → P g → ‖T (f + g)‖ₑ ≤ ‖T f‖ₑ + ‖T g‖ₑ) :
    AESubadditiveOn (fun u (_ : α') ↦ T u) P 1 ν :=
  fun f g hf hg ↦ ae_of_all _ fun _ ↦ (by simpa using h_add hf hg)

end AESubadditiveOn

variable [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] [TopologicalSpace ε] [ENormedSpace ε]

/-- The operator is sublinear on functions satisfying `P` with constant `A`. -/
def AESublinearOn (T : (α → E₁) → α' → ε) (P : (α → E₁) → Prop) (A : ℝ≥0∞) (ν : Measure α') :
    Prop :=
  AESubadditiveOn T P A ν ∧ ∀ (f : α → E₁) (c : ℝ≥0), P f → T (c • f) =ᵐ[ν] c • T f

namespace AESublinearOn

variable {ν : Measure α'}

lemma antitone {T : (α → E₁) → α' → ε} {P P' : (α → E₁) → Prop}
    (h : ∀ {u : α → E₁}, P u → P' u) {A : ℝ≥0∞} (sl : AESublinearOn T P' A ν) :
    AESublinearOn T P A ν :=
  ⟨sl.1.antitone (fun hu ↦ h hu), fun u c hu ↦ sl.2 u c (h hu)⟩

lemma biSup {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → E₁) → α' → ℝ≥0∞}
    {P : (α → E₁) → Prop} (hT : ∀ (u : α → E₁), P u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (h_add : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (h_smul : ∀ {f : α → E₁} {c : ℝ≥0}, P f → P (c • f))
    {A : ℝ≥0∞} (h : ∀ i ∈ 𝓑, AESublinearOn (T i) P A ν) :
    AESublinearOn (fun u x ↦ ⨆ i ∈ 𝓑, T i u x) P A ν := by
  have hT' : ∀ i ∈ 𝓑, ∀ (u : α → E₁), P u → ∀ᵐ x ∂ν, T i u x ≠ ∞ := by
    intro i hi f hf
    filter_upwards [hT f hf] with x hx
    rw [ne_eq, eq_top_iff] at hx ⊢
    exact fun h ↦ hx <| h.trans (le_biSup (fun i ↦ T i f x) hi)
  refine ⟨AESubadditiveOn.biSup h𝓑 hT h_add (fun i hi ↦ (h i hi).1), fun f c hf ↦ ?_⟩
  simp_rw [Set.forall_in_swap, imp.swap, ← imp_forall_iff] at hT'
  filter_upwards [(ae_ball_iff h𝓑).mpr (fun i hi ↦ (h i hi).2 f c hf),
    (ae_ball_iff h𝓑).mpr (hT' f hf), (ae_ball_iff h𝓑).mpr (hT' (c • f) (h_smul hf))] with x hx hT'fx hT'cfx
  simp_rw [Pi.smul_apply, ENNReal.smul_iSup]
  refine biSup_congr (fun i hi ↦ ?_)
  specialize hx i hi
  simpa only [Pi.smul_apply, smul_eq_mul] using hx

lemma biSup2 {ι : Type*} {𝓑 : Set ι} (h𝓑 : 𝓑.Countable) {T : ι → (α → E₁) → α' → ℝ≥0∞}
    {P : (α → E₁) → Prop} {Q : (α → E₁) → Prop}
    (hPT : ∀ (u : α → E₁), P u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (hQT : ∀ (u : α → E₁), Q u → ∀ᵐ x ∂ν, ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (P0 : P 0)
    (Q0 : Q 0)
    (haP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (haQ : ∀ {f g : α → E₁}, Q f → Q g → Q (f + g))
    (hsP : ∀ {f : α → E₁} {c : ℝ≥0}, P f → P (c • f))
    (hsQ : ∀ {f : α → E₁} {c : ℝ≥0}, Q f → Q (c • f))
    {A : ℝ≥0} -- todo, here and elsewhere: probably better to have {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hAP : ∀ i ∈ 𝓑,
      AESublinearOn (T i) (fun g ↦ g ∈ {f | P f} + {f | Q f}) A ν) :
    AESublinearOn (fun u x ↦ ⨆ i ∈ 𝓑, T i u x) (fun f ↦ P f ∨ Q f) A ν := by
  set R := fun g ↦ g ∈ {f | P f} + {f | Q f}
  have hPR : ∀ {f}, P f → R f := fun hu ↦ ⟨_, hu, 0, Q0, by simp⟩
  have hQR : ∀ {f}, Q f → R f := fun hu ↦ ⟨0, P0, _, hu, by simp⟩
  apply AESublinearOn.antitone (P' := R) (fun hu ↦ hu.elim hPR hQR)
  refine AESublinearOn.biSup (P := R) h𝓑 ?_ ?_ ?_ hAP
  · rintro _ ⟨f, hf, g, hg, rfl⟩
    filter_upwards [hPT f hf, hQT g hg,
      AESubadditiveOn.forall_le h𝓑 (fun i hi ↦ hAP i hi |>.1) (hPR hf) (hQR hg)] with x hfx hgx hTx
    simp_rw [← lt_top_iff_ne_top] at hfx hgx ⊢
    simp_rw [enorm_eq_self] at hTx
    calc
      _ ≤ ⨆ i ∈ 𝓑, A * (T i f x + T i g x) := by gcongr; exact hTx _ ‹_›
      _ ≤ A * ((⨆ i ∈ 𝓑, T i f x) + (⨆ i ∈ 𝓑, T i g x)) := by
          simp_rw [← ENNReal.mul_iSup]
          gcongr
          -- todo: make lemma
          simp_rw [iSup_le_iff]
          intro i hi
          gcongr <;> apply le_biSup _ hi
      _ < ⊤ := mul_lt_top coe_lt_top <| add_lt_top.mpr ⟨hfx, hgx⟩
  · rintro _ _ ⟨f₁, hf₁, g₁, hg₁, rfl⟩ ⟨f₂, hf₂, g₂, hg₂, rfl⟩
    exact ⟨f₁ + f₂, haP hf₁ hf₂, g₁ + g₂, haQ hg₁ hg₂, by dsimp only; abel_nf⟩
  · rintro _ c ⟨f, hf, g, hg, rfl⟩
    exact ⟨c • f, hsP hf, c • g, hsQ hg, by module⟩

lemma indicator {T : (α → E₁) → α' → ε} {P : (α → E₁) → Prop} {A : ℝ≥0∞} (S : Set α')
    (sl : AESublinearOn T P A ν) :
    AESublinearOn (fun u x ↦ (S.indicator (fun y ↦ T u y) x)) P A ν := by
  refine ⟨AESubadditiveOn.indicator sl.1 S, fun f c hf ↦ ?_⟩
  filter_upwards [sl.2 f c hf] with x hx
  by_cases h : x ∈ S <;> simp [h, hx]

-- If `T` is constant in the second argument (but not necessarily the first) and satisfies
-- certain requirements, then `AESublinearOn T P 1`
lemma const (T : (α → E₁) → ε) (P : (α → E₁) → Prop)
    (h_add : ∀ {f g}, P f → P g → ‖T (f + g)‖ₑ ≤ ‖T f‖ₑ + ‖T g‖ₑ)
    (h_smul : ∀ f {c : ℝ≥0}, P f → T (c • f) = c • T f) :
    AESublinearOn (fun u (_ : α') ↦ T u) P 1 ν := by
  refine ⟨AESubadditiveOn.const T P h_add, fun f c hf ↦ ae_of_all _ fun _ ↦ ?_⟩
  simpa using h_smul f hf

lemma toReal {T : (α → E₁) → α' → ℝ≥0∞}
    {P : (α → E₁) → Prop}
    {A : ℝ≥0∞} (h : AESublinearOn T P A ν)
    (hP : ∀ (u : α → E₁), P u → ∀ᵐ x ∂ν, T u x ≠ ∞) :
    AESublinearOn (T · · |>.toReal) P A ν := by
  refine ⟨fun f g hf hg ↦ ?_, fun f c hf ↦ ?_⟩
  · filter_upwards [h.1 f g hf hg, hP f hf, hP g hg] with x hx hfx hgx
    simp only [enorm_eq_self, ne_eq, hfx, not_false_eq_true, enorm_toReal, hgx] at hx ⊢
    exact enorm_toReal_le.trans hx
  · filter_upwards [h.2 f c hf, hP f hf] with x hx hfx
    simp_rw [hx, Pi.smul_apply, toReal_smul]

end AESublinearOn

end MeasureTheory

end


noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsChoiceExponent
    ComputationsInterpolatedExponents ChoiceScale

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  {f : α → E₁} {t : ℝ}
  {T : (α → E₁) → (α' → E₂)}

/-! ## Proof of the real interpolation theorem

    In this section the estimates are combined to finally give a proof of the
    real interpolation theorem.
-/
namespace MeasureTheory

/-- Proposition that expresses that the map `T` map between function spaces preserves
    AE strong measurability on L^p. -/
def PreservesAEStrongMeasurability
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    (T : (α → E₁) → α' → E₂) (p : ℝ≥0∞) : Prop :=
    ∀ ⦃f : α → E₁⦄, MemLp f p μ → AEStronglyMeasurable (T f) ν

lemma estimate_distribution_Subadditive_trunc {f : α → E₁} {t : ℝ≥0}
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    {a : ℝ} (ha : 0 < a) {A : ℝ≥0∞} (h : Subadditive_trunc T A f ν) :
    distribution (T f) (2 * A * t) ν ≤
    distribution (T (trunc f a)) t ν +
    distribution (T (truncCompl f a)) t ν := by
  nth_rw 2 [mul_comm]
  rw [mul_assoc, two_mul]
  apply distribution_add_le'
  nth_rw 1 [trunc_buildup (f := f) (t := a)]
  exact h a ha

lemma rewrite_norm_func {q : ℝ} {g : α' → E}
    [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E] (hq : 0 < q) {A : ℝ≥0} (hA : 0 < A)
    (hg : AEMeasurable g ν) :
    ∫⁻ x, ‖g x‖ₑ ^ q ∂ν =
    ENNReal.ofReal ((2 * A) ^ q * q) * ∫⁻ s in Ioi (0 : ℝ),
    distribution g ((ENNReal.ofReal (2 * A * s)))  ν * (ENNReal.ofReal (s^(q - 1))) := by
  have : 0 < (A : ℝ) := hA
  rw [lintegral_norm_pow_eq_distribution hg (by linarith)]
  nth_rewrite 1 [← lintegral_scale_constant_halfspace' (a := (2*A)) (by linarith)]
  rw [← lintegral_const_mul']; swap; · exact coe_ne_top
  rw [← lintegral_const_mul']; swap; · exact coe_ne_top
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (zero_lt_t : 0 < t)
  nth_rw 12 [mul_comm]
  rw [Real.mul_rpow, ← mul_assoc, ← ofReal_mul', ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← ofReal_mul']
      <;> try positivity
  congr 3
  rw [mul_assoc, mul_comm q, ← mul_assoc]
  congr 1
  rw [abs_of_nonneg] <;> try positivity
  nth_rw 1 [← Real.rpow_one (2 * A), ← Real.rpow_add (by linarith), add_sub_cancel]

lemma estimate_norm_rpow_range_operator {q : ℝ} {f : α → E₁}
    [NormedAddCommGroup E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂]
    (hq : 0 < q) (tc : ToneCouple) {A : ℝ≥0} (hA : 0 < A)
    (ht : Subadditive_trunc T A f ν) (hTf : AEMeasurable (T f) ν) :
  ∫⁻ x : α', ‖T f x‖ₑ ^ q ∂ν ≤
  ENNReal.ofReal ((2 * A)^q * q) * ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s)))
      (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) +
  distribution (T (truncCompl f (tc.ton s))) (ENNReal.ofReal s) ν * ENNReal.ofReal (s^(q - 1)) := by
  rw [rewrite_norm_func hq hA hTf]
  apply mul_le_mul' (le_refl _)
  apply setLIntegral_mono' measurableSet_Ioi
  intro s s_pos
  rw [← add_mul]
  apply mul_le_mul' ?_ (le_refl _)
  convert estimate_distribution_Subadditive_trunc (tc.ran_ton s s_pos) ht
  simp [ofReal_mul, ENNReal.ofNNReal_toNNReal]

-- XXX: can this be golfed or unified with `ton_aeMeasurable`?
@[measurability, fun_prop]
theorem ton_aeMeasurable_eLpNorm_trunc [NormedAddCommGroup E₁] (tc : ToneCouple) :
    AEMeasurable (fun x ↦ eLpNorm (trunc f (tc.ton x)) p₁ μ) (volume.restrict (Ioi 0)) := by
  change AEMeasurable ((fun t : ℝ ↦ eLpNorm (trunc f t) p₁ μ) ∘ (tc.ton)) (volume.restrict (Ioi 0))
  have tone := tc.ton_is_ton
  split_ifs at tone
  · apply aemeasurable_restrict_of_monotoneOn measurableSet_Ioi
    exact eLpNorm_trunc_mono.comp_monotoneOn tone.monotoneOn
  · apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
    exact eLpNorm_trunc_mono.comp_antitoneOn tone.antitoneOn

lemma estimate_norm_rpow_range_operator'
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [NormedAddCommGroup E₂]
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hp₁p : p < p₁) (hp₀p : p₀ < p)
    (tc : ToneCouple)
    (hq₀' : q₀ = ⊤ → ∀ s ∈ Ioi (0 : ℝ), distribution (T (truncCompl f (tc.ton s)))
        (ENNReal.ofReal s) ν = 0)
    (hq₁' : q₁ = ⊤ → ∀ s ∈ Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s)))
        (ENNReal.ofReal s) ν = 0)
    (hf : MemLp f p μ) (hT₁ : HasWeakType T p₁ q₁ μ ν C₁) (hT₀ : HasWeakType T p₀ q₀ μ ν C₀) :
    ∫⁻ s in Ioi (0 : ℝ), distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν *
    ENNReal.ofReal (s^(q.toReal - 1)) +
    distribution (T (truncCompl f (tc.ton s))) (ENNReal.ofReal s) ν *
    ENNReal.ofReal (s^(q.toReal - 1)) ≤
    (if q₁ < ⊤ then 1 else 0) * (C₁ ^ q₁.toReal * (∫⁻ s in Ioi (0 : ℝ),
        eLpNorm (trunc f (tc.ton s)) p₁ μ ^ q₁.toReal *
        ENNReal.ofReal (s ^ (q.toReal - q₁.toReal - 1)))) +
    (if q₀ < ⊤ then 1 else 0) * (C₀ ^ q₀.toReal * ∫⁻ s in Ioi (0 : ℝ),
        eLpNorm (truncCompl f (tc.ton s)) (p₀) μ ^ q₀.toReal *
        ENNReal.ofReal (s ^ (q.toReal - q₀.toReal - 1))) := by
  have : ∀ q' q : ℝ, -q' + (q - 1) = q - q' - 1 := by intro q' q; group
  repeat rw [← this]
  have p_pos : 0 < p := lt_trans hp₀ hp₀p
  -- TODO: is there a way to use lintegral_rw₂ conveniently?
  rw [lintegral_rw_aux power_aux_2, lintegral_rw_aux power_aux_2]
  nth_rw 2 [← lintegral_const_mul']; swap; · exact rpow_ne_top_of_nonneg toReal_nonneg coe_ne_top
  nth_rw 1 [← lintegral_const_mul']; swap; · exact rpow_ne_top_of_nonneg toReal_nonneg coe_ne_top
  simp_rw [← mul_assoc]
  split_ifs with is_q₁top is_q₀top
  · rw [one_mul, one_mul, ← lintegral_add_left']
    · apply setLIntegral_mono' measurableSet_Ioi
      intro s (s_pos : 0 < s)
      gcongr
      · apply weaktype_estimate_trunc p_pos hq₁ <;> assumption
      · apply weaktype_estimate_truncCompl (p₀ := p₀) hp₀ <;> try assumption
        · exact hp₁p.ne_top
        · exact tc.ran_ton s s_pos
    exact ((((ton_aeMeasurable_eLpNorm_trunc tc).pow_const _).const_mul _).mul
      (by fun_prop)).mul (by fun_prop)
  · rw [one_mul, zero_mul, add_zero]
    apply setLIntegral_mono' measurableSet_Ioi
    intro s (s_pos : 0 < s)
    simp only [is_q₀top, mem_Ioi, false_or] at hq₀'
    have : q₀ = ⊤ := not_lt_top.mp is_q₀top
    rw [hq₀' this s s_pos, zero_mul, add_zero]
    gcongr
    apply weaktype_estimate_trunc p_pos <;> try assumption
  · rw [one_mul, zero_mul, zero_add]
    apply setLIntegral_mono' measurableSet_Ioi
    intro s (s_pos : 0 < s)
    simp only [is_q₁top, mem_Ioi, false_or] at hq₁'
    have : q₁ = ⊤ := not_lt_top.mp is_q₁top
    rw [hq₁' this s s_pos, zero_mul, zero_add]
    gcongr
    apply weaktype_estimate_truncCompl (p₀ := p₀) <;> try assumption
    · exact hp₁p.ne_top
    · exact tc.ran_ton s s_pos
  · simp only [zero_mul, add_zero, nonpos_iff_eq_zero]
    have : ∫⁻ (_ : ℝ) in Ioi 0, 0 = 0 := lintegral_zero
    rw [← this]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (s_pos)
    have is_q₀top : ¬ q₀ < ⊤ := by assumption
    simp only [is_q₀top, mem_Ioi, false_or] at hq₀'
    simp only [is_q₁top, mem_Ioi, false_or] at hq₁'
    rw [hq₀' (not_lt_top.mp is_q₀top) s s_pos, hq₁' (not_lt_top.mp is_q₁top) s s_pos, zero_mul, add_zero]

lemma simplify_factor_rw_aux₀ (a b c d e f : ℝ≥0∞) :
    a * b * c * d * e * f = a * c * e * (b * d * f) := by ring
lemma simplify_factor_rw_aux₁ (a b c d e f : ℝ≥0∞) :
    a * b * c * d * e * f = c * (a * e) * (b * f * d) := by ring_nf

lemma simplify_factor₀ {D : ℝ}
    [NormedAddCommGroup E₁] (hq₀' : q₀ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    (ht : t ∈ Ioo 0 1)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    C₀ ^ q₀.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
    ENNReal.ofReal (D ^ (q.toReal - q₀.toReal)) =
    C₀ ^ ((1 - t) * q.toReal) * C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₀pos : 0 < p₀ := hp₀.1
  have q₀pos : 0 < q₀ := lt_of_lt_of_le hp₀.1 hp₀.2
  have p₁pos : 0 < p₁ := hp₁.1
  have q₁pos : 0 < q₁ := lt_of_lt_of_le hp₁.1 hp₁.2
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀' hp₀.2
  have hp' : p ∈ Ioo 0 ⊤ := interp_exp_in_Ioo_zero_top ht p₀pos p₁pos (by left; exact p₀ne_top) hp
  have p_toReal_pos : 0 < p.toReal := toReal_pos_of_Ioo hp'
  rw [hD]
  unfold d
  rw [← ofReal_rpow_of_pos]
  · rw [ofReal_toReal]
    · nth_rw 2 [div_eq_mul_inv]
      rw [ENNReal.mul_inv]
      · repeat rw [ENNReal.mul_rpow_of_ne_zero _ _ (q.toReal - q₀.toReal)]
        · rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
          repeat rw [← ENNReal.rpow_mul]
          repeat rw [← mul_assoc]
          rw [simplify_factor_rw_aux₀ (a := C₀ ^ q₀.toReal)]
          repeat rw [← ENNReal.rpow_add] <;> try positivity
          · congr 1
            · congr 1
              · rw [eq_exponents₀] <;> try assumption
              · rw [neg_mul, eq_exponents₁ (t := t)] <;> try assumption
                ring_nf
            · congr 1
              rw [mul_assoc, ← mul_add, eq_exponents₂ (t := t)] <;> try assumption
              rw [mul_assoc, mul_assoc, ← mul_add, neg_mul, eq_exponents₃ (t := t)] <;> try assumption
              simp only [neg_mul, neg_neg]
              rw [← mul_assoc, ← add_mul, ← preservation_interpolation ht hp₀.1 hp₁.1 hp, toReal_inv]
              field_simp
          · exact ne_zero_of_Ioo hF
          · exact ne_top_of_Ioo hF
          · exact ne_zero_of_Ioo hF
          · exact ne_top_of_Ioo hF
          · exact coe_ne_top
        · exact ENNReal.inv_ne_zero.mpr (d_ne_top_aux₁ hC₁)
        · exact ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF)
        · exact d_ne_zero_aux₁ hC₀
        · exact d_ne_zero_aux₀ hF
        · exact d_ne_zero_aux₂ hC₀ hF
        · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₁ hC₁))
            (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF))
      · exact Or.inr (d_ne_top_aux₂ hF)
      · exact Or.inr (d_ne_zero_aux₀ hF)
    · exact d_ne_top_aux₄ hC₀ hC₁ hF
  · apply d_pos <;> try assumption

lemma simplify_factor₁ {D : ℝ}
    [NormedAddCommGroup E₁] (hq₁' : q₁ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    (ht : t ∈ Ioo 0 1)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    C₁ ^ q₁.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
    ENNReal.ofReal (D ^ (q.toReal - q₁.toReal)) =
    C₀ ^ ((1 - t) * q.toReal) * C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₀pos : 0 < p₀ := hp₀.1
  have q₀pos : 0 < q₀ := lt_of_lt_of_le hp₀.1 hp₀.2
  have p₁pos : 0 < p₁ := hp₁.1
  have q₁pos : 0 < q₁ := lt_of_lt_of_le hp₁.1 hp₁.2
  have p₁ne_top : p₁ ≠ ⊤ := ne_top_of_le_ne_top hq₁' hp₁.2
  have hp' : p ∈ Ioo 0 ⊤ := interp_exp_in_Ioo_zero_top ht p₀pos p₁pos
    (Decidable.not_or_of_imp fun _ ↦ p₁ne_top) hp
  have p_toReal_pos : 0 < p.toReal := toReal_pos_of_Ioo hp'
  rw [hD]
  unfold d
  rw [← ofReal_rpow_of_pos]
  · rw [ofReal_toReal]
    · nth_rw 2 [div_eq_mul_inv]
      rw [ENNReal.mul_inv]
      · repeat rw [ENNReal.mul_rpow_of_ne_zero _ _ (q.toReal - q₁.toReal)]
        · rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
          repeat rw [← ENNReal.rpow_mul]
          repeat rw [← mul_assoc]
          rw [simplify_factor_rw_aux₁ (a := C₁ ^ q₁.toReal)]
          repeat rw [← ENNReal.rpow_add]
          · rw [neg_mul]
            congr 3
            · rw [eq_exponents₆] <;> try assumption
            · rw [eq_exponents₅] <;> try assumption
            · rw [mul_assoc, mul_assoc, ← mul_add, eq_exponents₈, neg_mul,
                eq_exponents₇ (ht := ht)] <;> try assumption
              rw [← mul_add, ← add_mul, add_comm, ← preservation_interpolation ht hp₀.1 hp₁.1 hp,
                toReal_inv]
              field_simp
          · exact ne_zero_of_Ioo hF
          · exact ne_top_of_Ioo hF
          · exact ne_zero_of_Ioo hF
          · exact ne_top_of_Ioo hF
          · exact (ENNReal.coe_pos.mpr hC₁).ne'
          · exact coe_ne_top
        · exact ENNReal.inv_ne_zero.mpr (rpow_ne_top' ((ENNReal.coe_pos.mpr hC₁).ne') coe_ne_top)
        · exact ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF)
        · exact d_ne_zero_aux₁ hC₀
        · exact d_ne_zero_aux₀ hF
        · exact d_ne_zero_aux₂ hC₀ hF
        · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₁ hC₁))
            (ENNReal.inv_ne_zero.mpr (d_ne_top_aux₂ hF))
      · exact Or.inr (d_ne_top_aux₂ hF)
      · exact Or.inr (d_ne_zero_aux₀ hF)
    · exact d_ne_top_aux₄ hC₀ hC₁ hF
  · exact d_pos hC₀ hC₁ hF

def finite_spanning_sets_from_lintegrable {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hg_int : ∫⁻ x, g x ∂μ < ⊤) : Measure.FiniteSpanningSetsIn
      (μ.restrict (Function.support g)) (Set.univ) where
  set := fun n ↦ if n = 0 then {x | g x = 0} else { x | 1 / (n + 1) ≤ g x }
  set_mem := fun _ ↦ trivial
  finite := by
    intro n
    split_ifs
    · rw [Measure.restrict_apply₀']
      · rw [measure_mono_null _ measure_empty]
        · exact zero_lt_top
        · intro x; simp
      · exact (aestronglyMeasurable_iff_aemeasurable.mpr hg).nullMeasurableSet_support
    · have one_div_ne_zero : (1 : ℝ≥0∞) / (n + 1) ≠ 0 := by
        apply ne_of_gt
        rw [one_div]
        exact ENNReal.inv_pos.mpr (add_ne_top.mpr ⟨coe_ne_top, one_ne_top⟩)
      calc
      _ ≤ (∫⁻ x : α in (Function.support g), g x ∂μ) / (1 / (n + 1)) := by
        apply meas_ge_le_lintegral_div hg.restrict one_div_ne_zero
        · rw [one_div]
          apply inv_ne_top.mpr
          simp
      _ ≤ (∫⁻ x : α, g x ∂μ) / (1 / (n + 1)) := by
        gcongr
        exact setLIntegral_le_lintegral _ _
      _ < ⊤ := div_lt_top hg_int.ne one_div_ne_zero
  spanning := by
    ext x
    constructor
    · simp
    · intro _
      rcases (eq_zero_or_pos (g x)) with gx_zero | gx_pos
      · simp only [mem_iUnion]; use 0; simpa
      · simp only [mem_iUnion]
        have : ∃ n : ℕ, (g x)⁻¹ < n := ENNReal.exists_nat_gt (inv_lt_top.mpr gx_pos).ne
        obtain ⟨n, wn⟩ := ENNReal.exists_nat_gt (inv_lt_top.mpr gx_pos).ne
        use n
        simp only [one_div]
        split_ifs with is_n_zero
        · simp [is_n_zero] at wn
        · simp only [mem_setOf_eq]
          refine inv_le_iff_inv_le.mpr ?_
          apply le_of_lt
          refine lt_trans wn ?_
          nth_rw 1 [← add_zero (n : ℝ≥0∞)]
          exact (ENNReal.add_lt_add_iff_left coe_ne_top).mpr zero_lt_one

lemma support_sigma_finite_of_lintegrable {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hg_int : ∫⁻ x, g x ∂μ < ⊤) :
    SigmaFinite (μ.restrict (Function.support g)) where
  out' := by
    apply nonempty_of_exists
    use (finite_spanning_sets_from_lintegrable hg hg_int)

lemma support_sigma_finite_from_MemLp
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hf : MemLp f p μ) (hp : p ≠ ⊤) (hp' : p ≠ 0) :
    SigmaFinite (μ.restrict (Function.support f)) := by
  let g : α → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ p.toReal
  have : Function.support g = Function.support f := by
    unfold Function.support g
    ext x
    simp only [ne_eq, ENNReal.rpow_eq_zero_iff, ENNReal.coe_eq_zero, enorm_eq_zero, coe_ne_top,
      false_and, or_false, not_and, not_lt, mem_setOf_eq]
    constructor
    · contrapose
      simp [not_not, Classical.not_imp, not_le, toReal_pos hp' hp]
    · tauto
  rw [← this]
  apply support_sigma_finite_of_lintegrable
  · exact (hf.1.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const _
  · unfold g
    have obs := hf.2
    unfold eLpNorm eLpNorm' at obs
    split_ifs at obs
    · contradiction
    · exact lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top (toReal_pos hp' hp) obs

-- lemma support_sfinite_from_MemLp
--     [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁] (hf : MemLp f p μ)
--     (hp : p ≠ ⊤) (hp' : p ≠ 0) :
--     SFinite (μ.restrict (Function.support f)) := by
--   have : SigmaFinite (μ.restrict (Function.support f)) := support_sigma_finite_from_MemLp hf hp hp'
--   exact instSFiniteOfSigmaFinite

lemma combine_estimates₀ {A : ℝ≥0} (hA : 0 < A)
  [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂]
  {spf : ScaledPowerFunction}
  (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
  (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁)
  (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
  (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
  (hf : MemLp f p μ) (hT : Subadditive_trunc T A f ν)
  (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
  (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
  (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 (lt_of_lt_of_le hp₀.1 hp₀.2) hp₁.1
      (lt_of_lt_of_le hp₁.1 hp₁.2) hp₀p₁.ne hC₀ hC₁ hF)
  (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
  (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
  (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ)) :
    ∫⁻ x , ‖T f x‖ₑ ^ q.toReal ∂ν ≤
    ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
    ((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) *
    C₀ ^ ((1 - t) * q.toReal) * C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have one_le_p₀ := hp₀.1
  have one_le_p1 := hp₁.1
  have p₀pos : 0 < p₀ := hp₀.1
  have q₀pos : 0 < q₀ := lt_of_lt_of_le hp₀.1 hp₀.2
  have p₁pos : 0 < p₁ := hp₁.1
  have q₁pos : 0 < q₁ := lt_of_lt_of_le hp₁.1 hp₁.2
  have p_pos : 0 < p := interpolated_pos' one_le_p₀ one_le_p1 hp
  have : SigmaFinite (μ.restrict (Function.support f)) :=
    support_sigma_finite_from_MemLp hf (interp_exp_ne_top hp₀p₁.ne ht hp) p_pos.ne'
  let tc := spf_to_tc spf
  calc
  ∫⁻ x , ‖T f x‖ₑ ^ q.toReal ∂ν
    ≤ ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) * ∫⁻ s in Ioi (0 : ℝ),
      distribution (T (trunc f (tc.ton s))) (ENNReal.ofReal s) ν *
      ENNReal.ofReal (s^(q.toReal - 1)) +
      distribution (T (truncCompl f (tc.ton s))) (ENNReal.ofReal s) ν *
      ENNReal.ofReal (s^(q.toReal - 1)) :=
    estimate_norm_rpow_range_operator
      (interp_exp_toReal_pos ht q₀pos q₁pos hq₀q₁ hq) _ hA hT (h₂T hf).aemeasurable
  _ ≤ ENNReal.ofReal ((2 * A)^q.toReal * q.toReal) *
      ((if q₁ < ⊤ then 1 else 0) * (C₁ ^ q₁.toReal * (∫⁻ s in Ioi (0 : ℝ),
        eLpNorm (trunc f (tc.ton s)) p₁ μ ^ q₁.toReal *
        ENNReal.ofReal (s ^ (q.toReal - q₁.toReal - 1)))) +
      (if q₀ < ⊤ then 1 else 0) * (C₀ ^ q₀.toReal * ∫⁻ s in Ioi (0 : ℝ),
        eLpNorm (truncCompl f (tc.ton s)) p₀ μ ^ q₀.toReal *
        ENNReal.ofReal (s ^ (q.toReal - q₀.toReal - 1)))) := by
    gcongr
    apply estimate_norm_rpow_range_operator' (p := p) p₀pos q₀pos q₁pos <;> try assumption
    · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).2
    · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).1
    · intro q₀top s (hs : 0 < s)
      apply weaktype_estimate_truncCompl_top (d := spf.d) hC₀ hp₀.1 q₀top _ _ hf h₀T hs _
      · rw [hspf]
        exact d_eq_top₀ one_le_p₀ q₁pos hp₀p₁.ne_top q₀top hq₀q₁
      · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).1
      · exact interp_exp_ne_top hp₀p₁.ne ht hp
      · dsimp only [tc, spf_to_tc]
        congr
        rw [hspf]
        dsimp only [spf_ch]
        exact ζ_equality₇ ht one_le_p₀ q₀pos one_le_p1 q₁pos hp₀p₁.ne hq₀q₁ hp hq hp₀p₁.ne_top q₀top

    · intro q₁top s (hs : 0 < s)
      rcases (eq_or_ne p₁ ⊤) with p₁eq_top | p₁ne_top
      · apply weaktype_estimate_trunc_top_top hC₁ _ p₁eq_top q₁top _ hf h₁T hs
        · dsimp only [tc, spf_to_tc]
          rw [hspf]
          dsimp only [spf_ch]
          rw [d_eq_top_top] <;> try assumption
          rw [ζ_eq_top_top, Real.rpow_one] <;> try assumption
          exact hp₀p₁.ne
        · exact p_pos
        · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).2
      · apply weaktype_estimate_trunc_top (p₁ := p₁) (p := p) (d := spf.d) hC₁ <;> try assumption
        · unfold tc
          rw [hspf]
          dsimp only [spf_to_tc, spf_ch]
          congr
          apply ζ_equality₈ ht (hp₀p₁ := hp₀p₁.ne) <;> assumption
        · rw [hspf]
          dsimp only [spf_ch]
          apply d_eq_top₁ <;> assumption
        · exact p₁ne_top.lt_top
        · exact (interp_exp_between p₀pos p₁pos hp₀p₁ ht hp).2
  _ ≤ ENNReal.ofReal ((2 * A)^q.toReal * q.toReal) *
      ((if q₁ < ⊤ then 1 else 0) * (C₁ ^ q₁.toReal *
      (ENNReal.ofReal (spf.d ^ (q.toReal - q₁.toReal)) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ *
        ((eLpNorm f p μ) ^ p.toReal) ^ ((sel ⊤ p₀ p₁).toReal ⁻¹ * (sel ⊤ q₀ q₁).toReal)))
        +
      (if q₀ < ⊤ then 1 else 0) * (C₀ ^ q₀.toReal *
      (ENNReal.ofReal (spf.d ^ (q.toReal - q₀.toReal)) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ *
        (((eLpNorm f p μ) ^ p.toReal) ^ ((sel ⊥ p₀ p₁).toReal ⁻¹ * (sel ⊥ q₀ q₁).toReal))))) := by
      apply mul_le_mul_left'
      apply add_le_add
      · split_ifs with is_q₁top
        · gcongr
          apply estimate_trnc₁ (j := ⊤) ht <;> try assumption
          · exact hp₁.2
          · exact ne_top_of_Ioc hp₁ is_q₁top
          · exact is_q₁top.ne_top
          · exact hf.1.aemeasurable
          · rw [hspf]; rfl
        · simp
      · split_ifs with is_q₀top
        · gcongr
          apply estimate_trnc₁ (j := ⊥) ht <;> try assumption
          · exact hp₀.2
          · exact ne_top_of_Ioc hp₀ is_q₀top
          · exact is_q₀top.ne_top
          · exact hf.1.aemeasurable
          · rw [hspf]; rfl
        · simp
  _ = (if q₁ < ⊤ then 1 else 0) *
      (↑C₁ ^ q₁.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₁.toReal / p₁.toReal) *
            ENNReal.ofReal (spf.d ^ (q.toReal - q₁.toReal)) *
          ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹) +
      (if q₀ < ⊤ then 1 else 0) *
      (↑C₀ ^ q₀.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) *
            ENNReal.ofReal (spf.d ^ (q.toReal - q₀.toReal)) *
          ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
    dsimp only [sel]
    ring_nf
  _ = (if q₁ < ⊤ then 1 else 0) *
      (↑C₀ ^ ((1 - t) * q.toReal) * ↑C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal *
          ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹) +
    (if q₀ < ⊤ then 1 else 0) *
      (↑C₀ ^ ((1 - t) * q.toReal) * ↑C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal *
          ENNReal.ofReal ((2 * A) ^ q.toReal * q.toReal) *
        ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹) := by
    congr 1
    · split_ifs with is_q₁top
      · congr 3
        apply simplify_factor₁ _ hp₀ <;> try assumption
        · rw [hspf]; rfl
        · exact is_q₁top.ne_top
      · simp
    · split_ifs with is_q₀top
      · congr 3
        apply simplify_factor₀ _ hp₀ hp₁ <;> try assumption
        · rw [hspf]; rfl
        · exact is_q₀top.ne_top
      · simp
  _ = _ := by ring

lemma combine_estimates₁ {A : ℝ≥0} [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂] (hA : 0 < A)
    {spf : ScaledPowerFunction}
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hf : MemLp f p μ) (hT : Subadditive_trunc T A f ν)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability T p (ν := ν) (μ := μ))
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hspf : spf = spf_ch ht hq₀q₁ hp₀.1 (lt_of_lt_of_le hp₀.1 hp₀.2) hp₁.1
        (lt_of_lt_of_le hp₁.1 hp₁.2) hp₀p₁.ne hC₀ hC₁ hF) :
    eLpNorm (T f) q ν ≤
    ENNReal.ofReal (2 * A) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t) * C₁ ^ t * eLpNorm f p μ := by
  have q_ne_zero : q ≠ 0 := (interpolated_pos' (lt_of_lt_of_le hp₀.1 hp₀.2) (lt_of_lt_of_le hp₁.1 hp₁.2) hq).ne'
  have q_ne_top : q ≠ ⊤ := interp_exp_ne_top hq₀q₁ ht hq
  have q'pos : 0 < q.toReal := toReal_pos q_ne_zero q_ne_top
  refine le_of_rpow_le q'pos ?_
  calc
  _ = ∫⁻ x , ‖T f x‖ₑ ^ q.toReal ∂ν := by
    unfold eLpNorm eLpNorm'
    split_ifs <;> [contradiction; rw [one_div, ENNReal.rpow_inv_rpow q'pos.ne']]
  _ ≤ _ := by
    apply combine_estimates₀ (hT := hT) (p := p) <;> try assumption
  _ = _ := by
    repeat rw [ENNReal.mul_rpow_of_nonneg _ _ q'pos.le]
    rw [ENNReal.ofReal_mul' q'pos.le]
    repeat rw [ENNReal.rpow_mul]
    congr
    · rw [ofReal_rpow_of_nonneg] <;> positivity
    · rw [toReal_inv, ENNReal.rpow_inv_rpow q'pos.ne']
      exact ofReal_toReal_eq_iff.mpr q_ne_top
    · rw [toReal_inv, ENNReal.rpow_inv_rpow q'pos.ne']

lemma simplify_factor₃ [NormedAddCommGroup E₁] (hp₀ : 0 < p₀) (hp₀' : p₀ ≠ ⊤) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) (hp₀p₁ : p₀ = p₁) :
    C₀ ^ q₀.toReal * (eLpNorm f p μ ^ p.toReal) ^ (q₀.toReal / p₀.toReal) =
    (↑C₀ * eLpNorm f p μ) ^ q₀.toReal := by
  rw [← interp_exp_eq hp₀p₁ ht hp, ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul, ← mul_div_assoc,
    mul_div_cancel_left₀]
  · exact (toReal_pos hp₀.ne' hp₀').ne'
  positivity

lemma simplify_factor_aux₄ [NormedAddCommGroup E₁] (hq₀' : q₀ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ = p₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    ↑C₀ ^ ((1 - t) * q.toReal) * (eLpNorm f p μ ^ p.toReal) ^ ((1 - t) * p₀⁻¹.toReal * q.toReal) *
      ↑C₁ ^ (t * q.toReal) *
    (eLpNorm f p μ ^ p.toReal) ^ (t * p₁⁻¹.toReal * q.toReal) = C₀ ^ ((1 - t) * q.toReal) *
    C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have hp' : p₀ = p := (interp_exp_eq hp₀p₁ ht hp)
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀' hp₀.2
  have p₀toReal_pos : 0 < p₀.toReal := toReal_pos hp₀.1.ne' p₀ne_top
  rw [← hp', ← hp₀p₁]
  have (a b c d : ℝ≥0∞): a * b * c * d = a * c * (b * d) := by ring
  rw [this, ← ENNReal.rpow_add]
  · rw [← ENNReal.rpow_mul]
    congr
    rw [toReal_inv]
    ring_nf
    field_simp
  · rw [hp']
    exact d_pos_aux₀ hF |>.ne'
  · rw [hp']
    exact d_ne_top_aux₀ hF

lemma simplify_factor₄ {D : ℝ} [NormedAddCommGroup E₁] (hq₀' : q₀ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ = p₁)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    (↑C₀ * eLpNorm f p μ) ^ q₀.toReal * ENNReal.ofReal (D ^ (q.toReal - q₀.toReal)) =
    C₀ ^ ((1 - t) * q.toReal) * C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₀pos : 0 < p₀ := hp₀.1
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀' hp₀.2
  rw [← simplify_factor₃] <;> try assumption
  rw [simplify_factor₀ (ht := ht) (hD := hD)] <;> assumption


lemma simplify_factor₅ {D : ℝ} [NormedAddCommGroup E₁] (hq₁' : q₁ ≠ ⊤)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    (ht : t ∈ Ioo 0 1)
    (hp₀p₁ : p₀ = p₁)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤)
    (hD : D = @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f) :
    (↑C₁ * eLpNorm f p μ) ^ q₁.toReal * ENNReal.ofReal (D ^ (q.toReal - q₁.toReal)) =
    C₀ ^ ((1 - t) * q.toReal) * C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal := by
  have p₁pos : 0 < p₁ := hp₁.1
  have p₁ne_top : p₁ ≠ ⊤ := ne_top_of_le_ne_top hq₁' hp₁.2
  have := switch_exponents ht hp
  rw [← simplify_factor₃ (ht := Ioo.one_sub_mem ht), simplify_factor₁ (ht := ht) (hD := hD)]
      <;> try assumption
  rw [hp₀p₁]

/-- The trivial case for the estimate in the real interpolation theorem
    when the function `Lp` norm of `f` vanishes. -/
lemma exists_hasStrongType_real_interpolation_aux₀ {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁)
    {C₀ : ℝ≥0}
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + (ENNReal.ofReal t) / p₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) (hf : MemLp f p μ)
    (hF : eLpNorm f p μ = 0) :
    eLpNorm (T f) q ν = 0 := by
  unfold HasWeakType at h₀T
  have p_pos : 0 < p := interpolated_pos' hp₀.1 hp₁.1 hp
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  have q_pos : 0 < q := interpolated_pos' q₀pos q₁pos hq
  have f_ae_0 : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hf.1 p_pos.ne').mp hF
  have hf₂ : eLpNorm f p₀ μ = 0 := (eLpNorm_eq_zero_iff hf.1 hp₀.1.ne').mpr f_ae_0
  have hf₁ : MemLp f p₀ μ := ⟨hf.1, by rw [hf₂]; exact zero_lt_top⟩
  have := (h₀T f hf₁).2
  rw [hf₂, mul_zero] at this
  have wnorm_0 : wnorm (T f) q₀ ν = 0 := nonpos_iff_eq_zero.mp this
  have : (T f) =ᵐ[ν] 0 := (wnorm_eq_zero_iff q₀pos.ne').mp wnorm_0
  exact (eLpNorm_eq_zero_iff (h₂T hf) q_pos.ne').mpr this

/-- The estimate for the real interpolation theorem in case `p₀ < p₁`. -/
lemma exists_hasStrongType_real_interpolation_aux {p₀ p₁ q₀ q₁ p q : ℝ≥0∞} {A : ℝ≥0}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂] (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ < p₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + (ENNReal.ofReal t) / p₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁)
    (hT : Subadditive_trunc T A f ν) (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    ENNReal.ofReal (2 * A) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t) * C₁ ^ t * eLpNorm f p μ := by
  have hq₀ : 0 < q₀ := pos_of_rb_Ioc hp₀
  have hq₁ : 0 < q₁ := pos_of_rb_Ioc hp₁
  rcases (eq_zero_or_pos (eLpNorm f p μ)) with hF | hF
  · refine le_of_eq_of_le ?_ (zero_le _)
    apply exists_hasStrongType_real_interpolation_aux₀ (hp := hp) (hq := hq) <;> try assumption
  · let spf := spf_ch ht hq₀q₁ hp₀.1 hq₀ hp₁.1 hq₁ hp₀p₁.ne hC₀ hC₁ ⟨hF, hf.2⟩
    apply combine_estimates₁ <;> try assumption
    on_goal 1 => unfold spf
    rfl

-- TODO: the below lemmas were split because otherwise the lean server would crash
-- (seems to be related to the linter?) (after the merge)
lemma exists_hasStrongType_real_interpolation_aux₁ {f : α → E₁} [NormedAddCommGroup E₁]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ = p₁) (hq₀q₁ : q₀ < q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + (ENNReal.ofReal t) / p₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁)
    (hF : eLpNorm f p μ ∈  Ioo 0 ⊤) :
    (ENNReal.ofReal q.toReal *
        ((C₀ * eLpNorm f p μ )^ q₀.toReal *
        (∫⁻ (t : ℝ) in Ioo 0 (@d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f),
        ENNReal.ofReal (t ^ (q.toReal - q₀.toReal - 1))) * (if q₀ = ⊤ then 0 else 1) +
        ((C₁ * eLpNorm f p μ) ^ q₁.toReal *
        ∫⁻ (t : ℝ) in Ici (@d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f),
        ENNReal.ofReal (t ^ (q.toReal - q₁.toReal - 1))) * if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ =
    q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
    ↑C₀ ^ ((1 - t)) * ↑C₁ ^ t * eLpNorm f p μ := by
    let M := @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f
    have hq₀q₁' : q₀ ≠ q₁ := hq₀q₁.ne
    have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
    have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
    have q₀lt_q_toReal : q₀.toReal < q.toReal :=
      preservation_inequality_of_lt₀ ht q₀pos q₁pos hq hq₀q₁
    have q_toReal_ne_zero : q.toReal ≠ 0 :=
      (interp_exp_toReal_pos' ht q₀pos q₁pos hq (Or.inl hq₀q₁.ne_top)).ne'
    have M_pos : 0 < M := by
      apply d_pos <;> try assumption
    have coe_q : ENNReal.ofReal q.toReal = q :=
    ofReal_toReal_eq_iff.mpr (interp_exp_ne_top hq₀q₁.ne ht hq)
    have eq :
        (ENNReal.ofReal q.toReal *
        ((((↑C₀ * eLpNorm f p μ) ^ q₀.toReal * ∫⁻ (t : ℝ) in Ioo 0 M,
            ENNReal.ofReal (t ^ (q.toReal - q₀.toReal - 1))) *
            if q₀ = ⊤ then 0 else 1) +
          ((↑C₁ * eLpNorm f p μ) ^ q₁.toReal * ∫⁻ (t : ℝ) in Ici M,
            ENNReal.ofReal (t ^ (q.toReal - q₁.toReal - 1))) *
            if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ = (ENNReal.ofReal q.toReal *
            (↑C₀ ^ ((1 - t) * q.toReal) * ↑C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal *
              ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
            ↑C₀ ^ ((1 - t) * q.toReal) * ↑C₁ ^ (t * q.toReal) * eLpNorm f p μ ^ q.toReal *
                ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * if q₁ = ⊤ then 0 else 1)) ^
            q.toReal⁻¹ := by
      congr 3
      · rw [lintegral_rpow_of_gt_abs, sub_add_cancel, ENNReal.ofReal_div_of_pos,
            div_eq_mul_inv, ← ofReal_inv_of_pos] <;> try positivity
        rw [← mul_assoc, simplify_factor₄ (ht := ht) (hC₁ := hC₁) (hD := rfl) (hq₀' := hq₀q₁.ne_top)]
            <;> try assumption
        · rw [abs_of_pos] <;> linarith
        · rw [abs_of_pos] <;> linarith
        · linarith
      · split_ifs with is_q₁top
        · rw [mul_zero, mul_zero]
        · have q_lt_q₁toReal : q.toReal < q₁.toReal :=
            preservation_inequality_of_lt₁ ht q₀pos q₁pos hq hq₀q₁ is_q₁top
          rw [mul_one, mul_one, setLIntegral_congr (Filter.EventuallyEq.symm Ioi_ae_eq_Ici),
          lintegral_Ioi_rpow_of_lt_abs, sub_add_cancel, ENNReal.ofReal_div_of_pos,
            div_eq_mul_inv, ← ofReal_inv_of_pos] <;> try positivity
          rw [← mul_assoc, simplify_factor₅ (hC₀ := hC₀) (ht := ht) (q₀ := q₀) (q₁ := q₁) (p₀ := p₀)
              (p₁ := p₁) (hD := rfl)] <;> try assumption
          · rw [abs_of_neg] <;> linarith
          · rw [abs_of_neg] <;> linarith
          · linarith
    rw [eq, coe_q]
    nth_rw 1 [mul_assoc]
    nth_rw 3 [mul_assoc]
    rw [← mul_add]
    have obs : q.toReal⁻¹ ≥ 0 := by positivity
    repeat rw [ENNReal.mul_rpow_of_nonneg _ _ obs]
    rw [ENNReal.rpow_rpow_inv, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_assoc (1 - t),
        mul_inv_cancel₀, mul_assoc t, mul_inv_cancel₀, mul_one, mul_one] <;> try positivity
    ring

/-- The main estimate in the real interpolation theorem for `p₀ = p₁`, before taking roots,
    for the case `q₀ < q₁`. -/
lemma exists_hasStrongType_real_interpolation_aux₂ {f : α → E₁}
    [NormedAddCommGroup E₁] [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ = p₁) (hq₀q₁ : q₀ < q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + (ENNReal.ofReal t) / p₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
    ↑C₀ ^ ((1 - t)) * ↑C₁ ^ t * eLpNorm f p μ := by
  let M := @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ _ f
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  have p₀ne_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top hq₀q₁.ne_top hp₀.2
  have q_toReal_ne_zero : q.toReal ≠ 0 :=
    (interp_exp_toReal_pos' ht q₀pos q₁pos hq (Or.inl hq₀q₁.ne_top)).ne'
  have p_eq_p₀ : p = p₀ := (interp_exp_eq hp₀p₁ ht hp).symm
  rcases (eq_zero_or_pos (eLpNorm f p μ)) with hF | snorm_pos
  · refine le_of_eq_of_le ?_ (zero_le _)
    apply exists_hasStrongType_real_interpolation_aux₀ (hp := hp) (hq := hq) <;> try assumption
  · have hF : eLpNorm f p μ ∈ Ioo 0 ⊤ := ⟨snorm_pos, hf.2⟩
    have M_pos : 0 < M := by
      apply d_pos <;> assumption
    have coe_q : ENNReal.ofReal q.toReal = q :=
    ofReal_toReal_eq_iff.mpr (interp_exp_ne_top hq₀q₁.ne ht hq)
    nth_rw 1 [← coe_q]
    rw [eLpNorm_eq_distribution (h₂T hf).aemeasurable
        (interp_exp_toReal_pos ht q₀pos q₁pos hq₀q₁.ne hq)]
    calc
    (ENNReal.ofReal q.toReal *
    ∫⁻ (t : ℝ) in Ioi 0, distribution (T f) (ENNReal.ofReal t) ν *
    ENNReal.ofReal (t ^ (q.toReal - 1))) ^
    q.toReal⁻¹
      ≤ (ENNReal.ofReal q.toReal * (
        (∫⁻ (t : ℝ) in Ioo 0 M, distribution (T f) (ENNReal.ofReal t) ν *
        ENNReal.ofReal (t ^ (q.toReal - 1))) +
        (∫⁻ (t : ℝ) in Ici M, distribution (T f) (ENNReal.ofReal t) ν *
        ENNReal.ofReal (t ^ (q.toReal - 1))))) ^
        q.toReal⁻¹ := by
      gcongr
      rw [← Ioo_union_Ici_eq_Ioi (M_pos)]
      apply lintegral_union_le _ (Ioo (0 : ℝ) (M : ℝ)) (Ici (M : ℝ))
    _ ≤ (ENNReal.ofReal q.toReal *
        ((∫⁻ (t : ℝ) in Ioo 0 M, C₀ ^ q₀.toReal *
        eLpNorm f p μ ^ q₀.toReal * ENNReal.ofReal (t ^ (-q₀.toReal)) *
        ENNReal.ofReal (t ^ (q.toReal - 1))) * (if q₀ = ⊤ then 0 else 1)+
        (∫⁻ (t : ℝ) in Ici M, C₁ ^ q₁.toReal *
        eLpNorm f p μ ^ q₁.toReal * ENNReal.ofReal (t ^ (-q₁.toReal)) *
        ENNReal.ofReal (t ^ (q.toReal - 1))) * if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ := by
      apply ENNReal.rpow_le_rpow <;> try positivity
      apply mul_le_mul_left'
      apply add_le_add
      · split_ifs with is_q₀top
        · contrapose! is_q₀top; exact hq₀q₁.ne_top
        · rw [mul_one]
          apply setLIntegral_mono' measurableSet_Ioo
          intro t ⟨(ht₁ : 0 < t), _⟩
          gcongr
          apply weaktype_estimate <;> try assumption
          · exact (hq₀q₁.ne_top).lt_top
          · rw [p_eq_p₀]; exact h₀T
      · split_ifs with is_q₁_top
        · simp only [mul_zero, nonpos_iff_eq_zero]
          have hf_0 : ∀ᵐ t : ℝ, t ∈ Ici M → distribution (T f) (ENNReal.ofReal t) ν *
          ENNReal.ofReal (t ^ (q.toReal - 1)) = 0 := by
            apply ae_of_all
            intro t (ht : M ≤ t)
            rw [weaktype_estimate_top] <;> try assumption
            · simp
            · rw [p_eq_p₀, hp₀p₁]; exact h₁T
            · have p₀pos : 0 < p₀ := hp₀.1
              have p₁pos : 0 < p₁ := hp₁.1
              have q₀ne_top : q₀ ≠ ⊤ := hq₀q₁.ne_top
              unfold M at ht
              rw [d_eq_top_of_eq] at ht <;> try assumption
              have : ENNReal.ofReal (C₁ * eLpNorm f p μ).toReal = C₁ * eLpNorm f p μ := by
                refine ofReal_toReal_eq_iff.mpr ?_
                exact mul_ne_top coe_ne_top hF.2.ne
              rw [← this]
              exact ofReal_le_ofReal ht
          rw [setLIntegral_congr_fun measurableSet_Ici hf_0, lintegral_zero]
        · rw [mul_one]
          apply setLIntegral_mono' measurableSet_Ici
          intro t (ht : t ≥ M)
          gcongr
          apply weaktype_estimate <;> try assumption
          · exact Ne.lt_top is_q₁_top
          · rw [p_eq_p₀, hp₀p₁]; exact h₁T
          · exact lt_of_lt_of_le M_pos ht
    _ = (ENNReal.ofReal q.toReal *
        ((C₀ * eLpNorm f p μ )^ q₀.toReal *
        (∫⁻ (t : ℝ) in Ioo 0 M, ENNReal.ofReal (t ^ (q.toReal - q₀.toReal - 1))) *
        (if q₀ = ⊤ then 0 else 1) +
        ((C₁ * eLpNorm f p μ) ^ q₁.toReal *
        ∫⁻ (t : ℝ) in Ici M,  ENNReal.ofReal (t ^ (q.toReal - q₁.toReal - 1))) *
        if q₁ = ⊤ then 0 else 1)) ^
        q.toReal⁻¹ := by
      congr
      · rw [← lintegral_const_mul]
        · apply setLIntegral_congr_fun measurableSet_Ioo
          apply ae_of_all
          intro t ⟨(ht₁ : 0 < t), _⟩
          rw [ENNReal.mul_rpow_of_nonneg] <;> try positivity
          rw [mul_assoc, ← ofReal_mul] <;> try positivity
          congr
          rw [← Real.rpow_add ht₁]
          congr 1; linarith
        · refine Measurable.ennreal_ofReal ?_
          exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) (q.toReal - q₀.toReal - 1)
      · rw [← lintegral_const_mul]
        · apply setLIntegral_congr_fun measurableSet_Ici
          apply ae_of_all
          intro t (ht : M ≤ t)
          have t_pos : 0 < t := lt_of_lt_of_le M_pos ht
          rw [ENNReal.mul_rpow_of_nonneg] <;> try positivity
          rw [mul_assoc, ← ofReal_mul] <;> try positivity
          congr
          rw [← Real.rpow_add] <;> try positivity
          congr 1; linarith
        · refine Measurable.ennreal_ofReal ?_
          exact Measurable.pow_const (fun ⦃t⦄ a ↦ a) (q.toReal - q₁.toReal - 1)
    _ = _ := by
      apply exists_hasStrongType_real_interpolation_aux₁ <;> assumption

/-- The main estimate for the real interpolation theorem for `p₀ = p₁`, requiring
    `q₀ ≠ q₁`, before taking roots. -/
lemma exists_hasStrongType_real_interpolation_aux₃  {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    [NormedAddCommGroup E₁] [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hp₀p₁ : p₀ = p₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + (ENNReal.ofReal t) / p₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p)
    (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
      ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
    ↑C₀ ^ ((1 - t)) * ↑C₁ ^ t * eLpNorm f p μ := by
  rcases lt_or_gt_of_ne hq₀q₁ with q₀lt_q₁ | q₁lt_q₀
  · apply exists_hasStrongType_real_interpolation_aux₂ <;> assumption
  · have (a b c d : ℝ≥0∞) : a * b * c * d = a * c * b * d := by ring
    rw [this, add_comm]
    have hp' := switch_exponents ht hp
    have hq' := switch_exponents ht hq
    nth_rw 1 [← sub_sub_self 1 t]
    apply exists_hasStrongType_real_interpolation_aux₂
      (ht := Ioo.one_sub_mem ht) (hp₀p₁ := hp₀p₁.symm) (hq₀q₁ := q₁lt_q₀) <;> try assumption

/-- The main estimate for the real interpolation theorem, before taking roots, combining
    the cases `p₀ ≠ p₁` and `p₀ = p₁`. -/
lemma exists_hasStrongType_real_interpolation_aux₄ {p₀ p₁ q₀ q₁ p q : ℝ≥0∞} {A : ℝ≥0}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂] (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + (ENNReal.ofReal t) / p₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁)
    (hT : Subadditive_trunc T A f ν) (h₀T : HasWeakType T p₀ q₀ μ ν C₀)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁)
    (h₂T : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T p) (hf : MemLp f p μ) :
    eLpNorm (T f) q ν ≤
    (if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A)) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t) * C₁ ^ t * eLpNorm f p μ := by
  let M := if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A)
  have hM : M = if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A) := rfl
  rw [← hM]
  split_ifs at hM with are_ps_eq
  · rw [hM, one_mul]
    have p_eq_p₀ : p = p₀ := (interp_exp_eq are_ps_eq ht hp).symm
    calc
    _ ≤ q ^ q.toReal⁻¹ * (ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ * (if q₀ = ⊤ then 0 else 1) +
        ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ * (if q₁ = ⊤ then 0 else 1)) ^ q.toReal⁻¹ *
        ↑C₀ ^ ((1 - t)) * ↑C₁ ^ t * eLpNorm f p μ := by
      apply exists_hasStrongType_real_interpolation_aux₃ <;> try assumption
    _ = _ := by
      rw [p_eq_p₀]
      congr 4
      · rw [toReal_inv]
      · rw [add_comm]
        congr 2
        · rw [mul_comm]
          have : (q₁ < ⊤) ↔ (q₁ ≠ ⊤):= lt_top_iff_ne_top
          split_ifs <;> tauto
        · rw [mul_comm]
          have : (q₀ < ⊤) ↔ (q₀ ≠ ⊤):= lt_top_iff_ne_top
          split_ifs <;> tauto
        · rw [toReal_inv]
  · rcases (lt_or_gt_of_ne are_ps_eq) with p₀lt_p₁ | p₁lt_p₀
    · rw [hM]
      apply exists_hasStrongType_real_interpolation_aux <;> try assumption
    · have (a b c d e f : ℝ≥0∞) : a * b * c * d * e * f = a * b * c * e * d * f := by ring
      rw [hM, this, add_comm]
      have hp' := switch_exponents ht hp
      have hq' := switch_exponents ht hq
      nth_rw 1 [← sub_sub_self 1 t]
      apply exists_hasStrongType_real_interpolation_aux
        (ht := Ioo.one_sub_mem ht) (hq₀q₁ := hq₀q₁.symm) <;> assumption

/-- The definition of the constant in the real interpolation theorem, when viewed as
    an element of `ℝ≥0∞`. -/
def C_realInterpolation_ENNReal (p₀ p₁ q₀ q₁ q : ℝ≥0∞) (C₀ C₁: ℝ≥0) (A : ℝ≥0) (t : ℝ) :=
    (if p₀ = p₁ then 1 else ENNReal.ofReal (2 * A)) * q ^ q⁻¹.toReal *
    (((if q₁ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ +
    (if q₀ < ⊤ then 1 else 0) * ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹)) ^ q⁻¹.toReal *
    C₀ ^ (1 - t) * C₁ ^ t

lemma C_realInterpolation_ENNReal_ne_top {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0}
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁) :
    C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t ≠ ⊤ := by
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  unfold C_realInterpolation_ENNReal
  apply mul_ne_top
  · apply mul_ne_top
    · apply mul_ne_top
      · apply mul_ne_top
        · split_ifs
          · exact top_ne_one.symm
          · exact coe_ne_top
        · apply rpow_ne_top'
          · exact interpolated_pos' q₀pos q₁pos hq |>.ne'
          · exact interp_exp_ne_top hq₀q₁ ht hq
      · apply rpow_ne_top'
        · split_ifs
          · rw [one_mul, one_mul]
            apply ne_of_gt
            apply add_pos'
            · exact ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq
            · exact ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq
          · rw [one_mul, zero_mul, add_zero]
            exact ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq |>.ne'
          · rw [zero_mul, one_mul, zero_add]
            exact ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq |>.ne'
          · have q₀top : q₀ = ⊤ := not_lt_top.mp (by assumption)
            have q₁top : q₁ = ⊤ := not_lt_top.mp (by assumption)
            rw [q₀top, q₁top] at hq₀q₁
            simp only [ne_eq, not_true_eq_false] at hq₀q₁
        · split_ifs <;> exact (ne_of_beq_false rfl).symm
    · exact rpow_ne_top' (ENNReal.coe_pos.mpr hC₀).ne' coe_ne_top
  · exact rpow_ne_top' (ENNReal.coe_pos.mpr hC₁).ne' coe_ne_top

lemma C_realInterpolation_ENNReal_pos {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0} (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁) :
    0 < C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t := by
  have q₀pos : 0 < q₀ := pos_of_rb_Ioc hp₀
  have q₁pos : 0 < q₁ := pos_of_rb_Ioc hp₁
  unfold C_realInterpolation_ENNReal
  apply ENNReal.mul_pos
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · split_ifs
          · exact one_ne_zero
          · rw [← ofReal_zero]
            exact ((ofReal_lt_ofReal_iff_of_nonneg le_rfl).mpr (_root_.mul_pos zero_lt_two hA)).ne'
        · apply ne_of_gt
          apply ENNReal.rpow_pos
          · exact interpolated_pos' q₀pos q₁pos hq
          · exact interp_exp_ne_top hq₀q₁ ht hq
      · apply ne_of_gt
        apply ENNReal.rpow_pos
        · split_ifs
          · rw [one_mul, one_mul]
            apply add_pos'
            · exact ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq
            · exact ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq
          · rw [one_mul, zero_mul, add_zero]
            exact ofReal_inv_interp_sub_exp_pos₁ ht q₀pos q₁pos hq₀q₁ hq
          · rw [zero_mul, one_mul, zero_add]
            exact ofReal_inv_interp_sub_exp_pos₀ ht q₀pos q₁pos hq₀q₁ hq
          · have q₀top : q₀ = ⊤ := not_lt_top.mp (by assumption)
            have q₁top : q₁ = ⊤ := not_lt_top.mp (by assumption)
            rw [q₀top, q₁top] at hq₀q₁
            simp only [ne_eq, not_true_eq_false] at hq₀q₁
        · refine add_ne_top.mpr ⟨?_, ?_⟩
          · apply mul_ne_top ?_ coe_ne_top
            split_ifs
            · exact top_ne_one.symm
            · exact top_ne_zero.symm
          · apply mul_ne_top ?_ coe_ne_top
            split_ifs
            · exact top_ne_one.symm
            · exact top_ne_zero.symm
    · exact (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hC₀) coe_ne_top).ne'
  · exact (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hC₁) coe_ne_top).ne'

/-- The constant occurring in the real interpolation theorem. -/
-- todo: check order of arguments
def C_realInterpolation (p₀ p₁ q₀ q₁ q : ℝ≥0∞) (C₀ C₁ A : ℝ≥0) (t : ℝ) : ℝ≥0 :=
    C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t |>.toNNReal

lemma C_realInterpolation_pos {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0} (hA : 0 < A)
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁) :
    0 < C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t := by
  unfold C_realInterpolation
  refine toNNReal_pos ?_ ?_
  · apply ne_of_gt
    apply C_realInterpolation_ENNReal_pos <;> assumption
  · apply C_realInterpolation_ENNReal_ne_top (A := A) <;> assumption

lemma coe_C_realInterpolation {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {A : ℝ≥0}
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) / q₀ + (ENNReal.ofReal t) / q₁) :
  ENNReal.ofNNReal (C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t) =
     C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q C₀ C₁ A t := by
  refine coe_toNNReal ?_
  apply C_realInterpolation_ENNReal_ne_top (A := A) <;> assumption

lemma Subadditive_trunc_from_SubadditiveOn_Lp₀p₁ {p₀ p₁ p : ℝ≥0∞}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [NormedAddCommGroup E₂]
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    {A : ℝ≥0} (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) / p₀ + ENNReal.ofReal t / p₁)
    (hT : AESubadditiveOn T (fun f ↦ MemLp f p₀ μ ∨ MemLp f p₁ μ) A ν)
    (hf : MemLp f p μ) :
    Subadditive_trunc T A f ν := by
  refine fun a a_pos ↦ ?_
  apply hT
  · rcases lt_trichotomy p₀ p₁ with p₀lt_p₁ | (p₀eq_p₁ | p₁lt_p₀)
    · refine Or.inr (trunc_Lp_Lq_higher (p := p) ?_ hf)
      exact ⟨interpolated_pos' hp₀ hp₁ hp, (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).2⟩
    · exact Or.inl <| interp_exp_eq p₀eq_p₁ ht hp ▸ trunc_preserves_Lp hf
    · refine Or.inl (trunc_Lp_Lq_higher (p := p) ?_ hf)
      exact ⟨interpolated_pos' hp₀ hp₁ hp,
        (interp_exp_between hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)).2⟩
  · rcases lt_trichotomy p₀ p₁ with p₀lt_p₁ | (p₀eq_p₁ | p₁lt_p₀)
    · refine Or.inl (truncCompl_Lp_Lq_lower (p := p) (interp_exp_ne_top p₀lt_p₁.ne ht hp)
        ⟨hp₀, (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1⟩ a_pos hf)
    · exact Or.inl <| interp_exp_eq p₀eq_p₁ ht hp ▸ truncCompl_preserves_Lp hf
    · refine Or.inr <| truncCompl_Lp_Lq_lower (p := p) ?_ ?_ a_pos hf
      · exact interp_exp_ne_top p₁lt_p₀.ne (Ioo.one_sub_mem ht) (switch_exponents ht hp)
      · exact ⟨hp₁,
          (interp_exp_between hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)).1⟩

/-- Marcinkiewicz real interpolation theorem. -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂] [BorelSpace E₂]
    (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    {C₀ C₁ t A : ℝ≥0} (hA : 0 < A) (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hmT : ∀ f, MemLp f p μ → AEStronglyMeasurable (T f) ν)
    (hT : AESubadditiveOn T (fun f ↦ MemLp f p₀ μ ∨ MemLp f p₁ μ) A ν)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁) :
    HasStrongType T p q μ ν (C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t) := by
  intro f hf
  refine ⟨hmT f hf, ?_⟩
  have hp' : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹ := by
    rw [hp]; congr <;> exact Real.toNNReal_coe.symm
  have hq' : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹ := by
    rw [hq]; congr <;> exact Real.toNNReal_coe.symm
  have obs : Subadditive_trunc T A f ν :=
    Subadditive_trunc_from_SubadditiveOn_Lp₀p₁ hp₀.1 hp₁.1 ht hp' hT hf
  rw [coe_C_realInterpolation hp₀ hp₁ hq₀q₁] <;> try assumption
  apply exists_hasStrongType_real_interpolation_aux₄ <;> assumption

/- State and prove Remark 1.2.7 -/

end MeasureTheory

end
