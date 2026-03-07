module

public import Carleson.Psi
public import Carleson.TileStructure
public import Carleson.ToMathlib.BoundedCompactSupport

@[expose] public section

open Set MeasureTheory Metric Function Complex Bornology
open scoped ComplexConjugate
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

/-! ## Carleson operators -/

section Carleson

variable [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma bcs_of_measurable_of_le_indicator_f {f : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) : BoundedCompactSupport f := by
  have : BoundedCompactSupport (F.indicator 1 : X → ℝ) :=
    BoundedCompactSupport.indicator_of_isCompact_closure (memLp_top_const _)
      isBounded_F.isCompact_closure measurableSet_F
  exact this.mono_norm hf.aestronglyMeasurable h2f

lemma bcs_of_measurable_of_le_indicator_g {g : X → ℂ}
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) : BoundedCompactSupport g := by
  have : BoundedCompactSupport (G.indicator 1 : X → ℝ) :=
    BoundedCompactSupport.indicator_of_isCompact_closure (memLp_top_const _)
      isBounded_G.isCompact_closure measurableSet_G
  exact this.mono_norm hg.aestronglyMeasurable h2g

variable [TileStructure Q D κ S o] {p p' : 𝔓 X}

/-- The operator `T_𝔭` defined in Proposition 2.0.2. -/
def carlesonOn (p : 𝔓 X) (f : X → ℂ) : X → ℂ :=
  indicator (E p)
    fun x ↦ ∫ y, exp (I * (Q x y - Q x x)) * Ks (𝔰 p) x y * f y

/- Deprecated for `AEStronglyMeasurable.carlesonOn`
Used through `measurable_carlesonSum` in `Antichain.AntichainOperator` and `ForestOperator.Forests`
with nontrivial rework in order to move from `Measurable` to `AEStronglyMeasurable`. -/
lemma measurable_carlesonOn {p : 𝔓 X} {f : X → ℂ} (measf : Measurable f) :
    Measurable (carlesonOn p f) := by
  refine (StronglyMeasurable.integral_prod_right ?_).measurable.indicator measurableSet_E
  exact (show Measurable _ by fun_prop).stronglyMeasurable

open Classical in
/-- The operator `T_ℭ f` defined at the bottom of Section 7.4.
We will use this in other places of the formalization as well. -/
def carlesonSum (ℭ : Set (𝔓 X)) (f : X → ℂ) (x : X) : ℂ :=
  ∑ p with p ∈ ℭ, carlesonOn p f x

@[fun_prop]
lemma measurable_carlesonSum {ℭ : Set (𝔓 X)} {f : X → ℂ} (measf : Measurable f) :
    Measurable (carlesonSum ℭ f) :=
  Finset.measurable_sum _ fun _ _ ↦ measurable_carlesonOn measf

lemma _root_.MeasureTheory.AEStronglyMeasurable.carlesonOn {p : 𝔓 X} {f : X → ℂ}
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (carlesonOn p f) := by
  refine .indicator ?_ measurableSet_E
  refine .integral_prod_right'
    (f := fun z ↦ exp (Complex.I * (Q z.1 z.2 - Q z.1 z.1)) * Ks (𝔰 p) z.1 z.2 * f z.2) ?_
  refine (AEStronglyMeasurable.mul (by fun_prop) aestronglyMeasurable_Ks).mul ?_
  exact hf.comp_snd

lemma _root_.MeasureTheory.AEStronglyMeasurable.carlesonSum {ℭ : Set (𝔓 X)}
    {f : X → ℂ} (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (carlesonSum ℭ f) :=
  Finset.aestronglyMeasurable_fun_sum _ fun _ _ ↦ hf.carlesonOn

lemma carlesonOn_def' (p : 𝔓 X) (f : X → ℂ) : carlesonOn p f =
    indicator (E p) fun x ↦ ∫ y, Ks (𝔰 p) x y * f y * exp (I * (Q x y - Q x x)) :=
  congr_arg _ (funext fun x ↦ (congr_arg _ (funext fun y ↦ by ring)))

lemma support_carlesonOn_subset_E {f : X → ℂ} : support (carlesonOn p f) ⊆ E p :=
  fun _ hx ↦ mem_of_indicator_ne_zero hx

lemma support_carlesonSum_subset {ℭ : Set (𝔓 X)} {f : X → ℂ} :
    support (carlesonSum ℭ f) ⊆ (⋃ p ∈ ℭ, 𝓘 p) := by
  intro x hx
  rw [mem_support] at hx
  contrapose! hx
  refine Finset.sum_eq_zero <| fun p hp ↦ notMem_support.mp (fun hxp ↦ hx ?_)
  simp only [Finset.mem_filter] at hp
  exact Set.mem_biUnion hp.2 <| E_subset_𝓘 <| support_carlesonOn_subset_E hxp

namespace MeasureTheory

variable (p) in
theorem BoundedCompactSupport.bddAbove_norm_carlesonOn
    {f : X → ℂ} (hf : BoundedCompactSupport f) : BddAbove (range (‖carlesonOn p f ·‖)) := by
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨r₀, hr₀, hfr₀⟩ := hf.hasCompactSupport.isBounded.subset_closedBall_lt 0 x₀
  let r₁ := (↑D ^ 𝔰 p / 2) + r₀
  have hcf : support (_root_.carlesonOn p f) ⊆ closedBall x₀ r₁ := by
    simp_rw [carlesonOn_def']
    intro x hx
    simp only [mem_support] at hx
    apply indicator_apply_ne_zero.mp at hx
    replace hx := hx.2
    simp only [mem_support] at hx
    have : ∃ y, Ks (𝔰 p) x y * f y * cexp (I * (Q x y - Q x x)) ≠ 0 := by
      by_contra! hc
      apply hx
      simp [hc]
    obtain ⟨y, hy⟩ := this
    simp only [ne_eq, mul_eq_zero, exp_ne_zero, or_false, not_or] at hy
    apply le_trans <| dist_triangle _ y _
    unfold r₁
    gcongr
    exacts [(dist_mem_Icc_of_Ks_ne_zero hy.1).2, hfr₀ (subset_tsupport _ hy.2)]
  obtain ⟨CK, nnCK, hCK⟩ :=
    Metric.isBounded_closedBall (x := x₀) (r := r₁) |>.exists_bound_of_norm_Ks (𝔰 p)
  let C := volume.real (closedBall x₀ r₀) * (CK * (eLpNorm f ⊤).toReal)
  rw [bddAbove_def]
  use C; simp_rw [mem_range, forall_exists_index, forall_apply_eq_imp_iff]; intro x
  by_cases hx : x ∈ support (_root_.carlesonOn p f); swap
  · simp only [mem_support, ne_eq, not_not] at hx
    rw [hx, norm_zero]
    positivity
  · simp_rw [carlesonOn_def']
    apply le_trans <| norm_indicator_le_norm_self ..
    let g := (closedBall x₀ r₀).indicator (fun _ ↦ CK * (eLpNorm f ⊤).toReal)
    have hK : ∀ᵐ y, ‖Ks (𝔰 p) x y * f y * cexp (I * (Q x y - Q x x))‖ ≤ g y := by
      filter_upwards [hf.memLp_top.ae_norm_le] with y hy
      by_cases hy' : y ∈ support f
      · simp_rw [norm_mul, ← ofReal_sub, norm_exp_I_mul_ofReal, mul_one, g,
          indicator_of_mem (hfr₀ <|subset_tsupport _ hy' ) _]
        gcongr
        exact hCK x y (hcf hx)
      · simp_rw [notMem_support.mp hy', mul_zero, zero_mul, norm_zero, g]
        unfold indicator
        split_ifs <;> positivity
    calc
      _ ≤ ∫ y, g y := by
        refine norm_integral_le_of_norm_le ?_ hK
        exact Integrable.indicator_const measurableSet_closedBall measure_closedBall_lt_top
      _ = volume.real (closedBall x₀ r₀) * (CK * (eLpNorm f ⊤ volume).toReal) :=
        integral_indicator_const _ measurableSet_closedBall

@[fun_prop]
theorem BoundedCompactSupport.carlesonOn {f : X → ℂ}
    (hf : BoundedCompactSupport f) : BoundedCompactSupport (carlesonOn p f) where
  memLp_top := by
    obtain ⟨C, hC⟩ := bddAbove_def.mp <| hf.bddAbove_norm_carlesonOn p
    simp_rw [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
    exact memLp_top_of_bound hf.aestronglyMeasurable.carlesonOn C (.of_forall hC)
  hasCompactSupport := by
    suffices support (_root_.carlesonOn p f) ⊆ 𝓘 p by
      refine HasCompactSupport.of_support_subset_isBounded ?_ this
      exact Metric.isBounded_ball.subset Grid_subset_ball
    exact support_carlesonOn_subset_E.trans E_subset_𝓘

theorem BoundedCompactSupport.bddAbove_norm_carlesonSum
    {ℭ : Set (𝔓 X)} {f : X → ℂ} (hf : BoundedCompactSupport f) :
    BddAbove (range (‖carlesonSum ℭ f ·‖)) := by
  apply BddAbove.range_mono _ fun _ ↦ norm_sum_le ..
  exact .range_finsetSum fun _ _ ↦ hf.bddAbove_norm_carlesonOn _

@[fun_prop]
theorem BoundedCompactSupport.carlesonSum {ℭ : Set (𝔓 X)} {f : X → ℂ}
    (hf : BoundedCompactSupport f) : BoundedCompactSupport (carlesonSum ℭ f) :=
  .finset_sum (fun _ _ ↦ hf.carlesonOn)

end MeasureTheory

lemma carlesonSum_inter_add_inter_compl {f : X → ℂ} {x : X} (A B : Set (𝔓 X)) :
    carlesonSum (A ∩ B) f x + carlesonSum (A ∩ Bᶜ) f x = carlesonSum A f x := by
  classical
  simp only [carlesonSum]
  conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not _ (fun p ↦ p ∈ B)]
  congr 2
  · ext; simp
  · ext; simp

lemma sum_carlesonSum_of_pairwiseDisjoint {ι : Type*} {f : X → ℂ} {x : X} {A : ι → Set (𝔓 X)}
    {s : Finset ι} (hs : (s : Set ι).PairwiseDisjoint A) :
    ∑ i ∈ s, carlesonSum (A i) f x = carlesonSum (⋃ i ∈ s, A i) f x := by
  classical
  simp only [carlesonSum]
  rw [← Finset.sum_biUnion]
  · congr with p
    simp
  · convert hs
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · intro i hi j hj hij
      convert Finset.disjoint_coe.2 (h hi hj hij)
      · ext; simp
      · ext; simp
    · intro i hi j hj hij
      apply Finset.disjoint_coe.1
      convert h hi hj hij
      · ext; simp
      · ext; simp

end Carleson

/-! ## Adjoint operators -/

section Adjoint

variable [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o] {p p' : 𝔓 X}

/-- The definition of `Tₚ*g(x)`, defined above Lemma 7.4.1 -/
def adjointCarleson (p : 𝔓 X) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in E p, conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y

open scoped Classical in
/-- The definition of `T_ℭ*g(x)`, defined at the bottom of Section 7.4 -/
def adjointCarlesonSum (ℭ : Set (𝔓 X)) (f : X → ℂ) (x : X) : ℂ :=
  ∑ p with p ∈ ℭ, adjointCarleson p f x

/-- A helper lemma used in Lemma 7.5.10. -/
lemma adjointCarlesonSum_inter {A B : Set (𝔓 X)} {f : X → ℂ} {x : X} :
    adjointCarlesonSum (A ∩ B) f x = adjointCarlesonSum A f x - adjointCarlesonSum (A \ B) f x := by
  unfold adjointCarlesonSum; symm
  classical rw [sub_eq_iff_eq_add, ← Finset.sum_union]; swap
  · simp only [Finset.disjoint_filter, mem_diff, not_and, not_not]
    exact fun x _ ⟨xA, xB⟩ _ ↦ xB
  congr; ext x
  simp_rw [Finset.mem_union, Finset.mem_filter_univ, mem_inter_iff, mem_diff]
  tauto

variable {f g : X → ℂ}

lemma adjoint_eq_adjoint_indicator (h : E p ⊆ 𝓘 p') :
    adjointCarleson p f = adjointCarleson p ((𝓘 p' : Set X).indicator f) := by
  ext x; refine setIntegral_congr_fun measurableSet_E (fun y my ↦ ?_); congr
  exact (indicator_of_mem (h my) f).symm

namespace MeasureTheory

attribute [fun_prop] continuous_exp -- not needed here, but clearly missing in mathlib

@[fun_prop]
lemma StronglyMeasurable.adjointCarleson (hf : StronglyMeasurable f) :
    StronglyMeasurable (adjointCarleson p f) := by
  refine .integral_prod_right'
    (f := fun z ↦ conj (Ks (𝔰 p) z.2 z.1) * exp (Complex.I * (Q z.2 z.2 - Q z.2 z.1)) * f z.2) ?_
  refine .mul (.mul ?_ ?_) (by fun_prop)
  · exact Complex.continuous_conj.comp_stronglyMeasurable (stronglyMeasurable_Ks.prod_swap)
  · refine Complex.continuous_exp.comp_stronglyMeasurable (.const_mul (.sub ?_ ?_) _)
    · exact Measurable.stronglyMeasurable (by fun_prop)
    · exact continuous_ofReal.comp_stronglyMeasurable stronglyMeasurable_Q₂.prod_swap

@[fun_prop]
lemma AEStronglyMeasurable.adjointCarleson (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (adjointCarleson p f) := by
  refine .integral_prod_right'
    (f := fun z ↦ conj (Ks (𝔰 p) z.2 z.1) * exp (Complex.I * (Q z.2 z.2 - Q z.2 z.1)) * f z.2) ?_
  refine .mono_ac (.prod .rfl restrict_absolutelyContinuous) ?_
  refine .mul (.mul ?_ ?_) hf.comp_snd
  · exact Complex.continuous_conj.comp_aestronglyMeasurable aestronglyMeasurable_Ks.prod_swap
  · refine Complex.continuous_exp.comp_aestronglyMeasurable (.const_mul (.sub ?_ ?_) _)
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · exact continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_Q₂.prod_swap

lemma StronglyMeasurable.adjointCarlesonSum {ℭ : Set (𝔓 X)} (hf : StronglyMeasurable f) :
    StronglyMeasurable (adjointCarlesonSum ℭ f) := by
  unfold _root_.adjointCarlesonSum; fun_prop

lemma AEStronglyMeasurable.adjointCarlesonSum {ℭ : Set (𝔓 X)} (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (adjointCarlesonSum ℭ f) := by
  unfold _root_.adjointCarlesonSum; fun_prop

variable (p) in
theorem BoundedCompactSupport.bddAbove_norm_adjointCarleson (hf : BoundedCompactSupport f) :
    BddAbove (range (‖adjointCarleson p f ·‖)) := by
  obtain ⟨CKf, hCKf, hCKf⟩ := hf.hasCompactSupport.isBounded.exists_bound_of_norm_Ks (𝔰 p)
  let C : ℝ := CKf * (eLpNorm f ⊤).toReal * volume.real (E p)
  use C
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  intro x
  apply norm_setIntegral_le_of_norm_le_const_ae volume_E_lt_top <| ae_restrict_of_ae _
  filter_upwards [hf.memLp_top.ae_norm_le] with y hy
  suffices ‖Ks (𝔰 p) y x‖ * ‖f y‖ ≤ ?C by
    simp_rw [norm_mul, ← ofReal_sub, norm_exp_I_mul_ofReal, mul_one, RCLike.norm_conj]
    exact this
  by_cases hy : y ∈ tsupport f
  · specialize hCKf y x hy; gcongr
  · simp_rw [image_eq_zero_of_notMem_tsupport hy, norm_zero, mul_zero]
    positivity

@[fun_prop]
theorem BoundedCompactSupport.adjointCarleson (hf : BoundedCompactSupport f) :
    BoundedCompactSupport (adjointCarleson p f) where
  memLp_top := by
    obtain ⟨C, hC⟩ := hf.bddAbove_norm_adjointCarleson p
    simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
    apply MeasureTheory.memLp_top_of_bound (by fun_prop) C (.of_forall hC)
  hasCompactSupport := by
    obtain x₀ : X := Classical.choice (by infer_instance)
    obtain ⟨r₀, h⟩ := hf.isBoundedSupport.subset_ball x₀
    let C : ℝ := (D ^ 𝔰 p / 2) + r₀
    apply HasCompactSupport.of_support_subset_closedBall (x := x₀) (r := C)
    intro x hx
    apply mem_support.mp at hx
    have : ∃ y, conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y ≠ 0 := by
      by_contra! hc
      exact hx <| setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ hc x
    simp only [ne_eq, mul_eq_zero, map_eq_zero, exp_ne_zero, or_false, not_or] at this
    obtain ⟨y, hKy, hfy⟩ := this
    rw [mem_closedBall]
    apply le_trans <| dist_triangle _ y _
    unfold C
    gcongr
    · rw [dist_comm]; exact dist_mem_Icc_of_Ks_ne_zero hKy |>.2
    · exact le_of_lt <| h hfy

variable (p) in
theorem BoundedCompactSupport.bddAbove_norm_adjointCarlesonSum
    {ℭ : Set (𝔓 X)} (hf : BoundedCompactSupport f) :
    BddAbove (range (‖adjointCarlesonSum ℭ f ·‖)) := by
  apply BddAbove.range_mono _ fun _ ↦ norm_sum_le ..
  exact .range_finsetSum fun _ _ ↦ hf.bddAbove_norm_adjointCarleson _

@[fun_prop]
theorem BoundedCompactSupport.adjointCarlesonSum {ℭ : Set (𝔓 X)}
    (hf : BoundedCompactSupport f) : BoundedCompactSupport (adjointCarlesonSum ℭ f) := by
  unfold _root_.adjointCarlesonSum; fun_prop

end MeasureTheory

/-- `MKD` is short for "modulated kernel times dilated bump". -/
private abbrev MKD (s : ℤ) x y := exp (I * (Q x y - Q x x)) * Ks s x y (K := K)

omit [TileStructure Q D κ S o] in
private lemma norm_MKD_le_norm_Ks {s : ℤ} {x y : X} : ‖MKD s x y‖ ≤ ‖Ks s x y‖ := by
  rw [norm_mul, ← ofReal_sub, norm_exp_I_mul_ofReal, one_mul]

/-- `adjointCarleson` is the adjoint of `carlesonOn`. -/
lemma adjointCarleson_adjoint
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (p : 𝔓 X) :
    ∫ x, conj (g x) * carlesonOn p f x = ∫ y, conj (adjointCarleson p g y) * f y := by
  let H := fun x ↦ fun y ↦ conj (g x) * (E p).indicator 1 x * MKD (𝔰 p) x y * f y
  have hH : Integrable (uncurry H) := by
    let H₀ := fun x y ↦ ‖g x‖ * ‖f y‖
    obtain ⟨M₀, hM₀nn, hM₀⟩ := hg.hasCompactSupport.isBounded.exists_bound_of_norm_Ks (𝔰 p)
    have hHleH₀ x y : ‖H x y‖ ≤ M₀ * ‖g x‖ * ‖f y‖ := by
      by_cases h : x ∈ tsupport g
      · unfold H
        rw [norm_mul, norm_mul, norm_mul, norm_conj]
        nth_rw 2 [mul_assoc, mul_comm]
        gcongr
        apply mul_le_mul (norm_indicator_one_le ..) norm_MKD_le_norm_Ks (by simp) (by simp) |>.trans
        simp [hM₀ x y h]
      · suffices hz : H x y = 0 by rw [hz]; simp only [norm_zero, ge_iff_le]; positivity
        unfold H; simp [image_eq_zero_of_notMem_tsupport h]
    have : Integrable (fun z : X × X ↦ M₀ * ‖g z.1‖ * ‖f z.2‖) :=
      (hg.norm.const_mul _).integrable.mul_prod hf.norm.integrable
    apply this.mono
    · refine .mul ?_ hf.aestronglyMeasurable.comp_snd
      refine .mul ?_ ?_
      · refine .mul ?_ ?_
        · exact RCLike.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable.comp_fst
        · exact aestronglyMeasurable_const.indicator measurableSet_E |>.comp_fst
      · unfold MKD
        fun_prop
    · apply ae_of_all
      exact fun z ↦ (hHleH₀ z.1 z.2).trans <| Real.le_norm_self _
  calc
    _ = ∫ x, conj (g x) * ∫ y, (E p).indicator 1 x * MKD (𝔰 p) x y * f y := by
      conv =>
        enter [1, 2, x, 2]; unfold carlesonOn
        rw [indicator_eq_indicator_one_mul, ← integral_const_mul]
        enter [2, y]; rw [← mul_assoc]
    _ = ∫ x, ∫ y, H x y := by unfold H; simp_rw [← integral_const_mul, mul_assoc]
    _ = ∫ y, ∫ x, H x y := integral_integral_swap hH
    _ = ∫ y, (∫ x, conj (g x) * (E p).indicator 1 x * MKD (𝔰 p) x y) * f y := by
      simp_rw [H, integral_mul_const]
    _ = ∫ y, conj (∫ x, g x * (E p).indicator 1 x * conj (MKD (𝔰 p) x y)) * f y := by
      simp_rw [← integral_conj]; congrm (∫ _, (∫ _, ?_) * (f _))
      rw [map_mul, conj_conj, map_mul, conj_indicator, map_one]
    _ = _ := by
      congr! with y
      simp_rw [mul_comm (g _) _]
      calc
        _ = ∫ x, (E p).indicator (fun x ↦ g x * conj (MKD (𝔰 p) x y)) x := by
          congr with x; simp only [indicator]; split_ifs <;> simp
        _ = ∫ x in E p, g x * conj (MKD (𝔰 p) x y) := integral_indicator measurableSet_E
        _ = ∫ x in E p, conj (MKD (𝔰 p) x y) * g x := by congr; funext; rw [mul_comm]
        _ = _ := by
          unfold adjointCarleson MKD
          congr; funext; rw [map_mul, ← exp_conj, mul_comm (cexp _)]
          congr; simp; ring

-- Bug: why is `integrable_fun_mul` needed, despite `integrable_mul` existing?
-- the fun_prop documentation implies it's superfluous. TODO ask on zulip!

/-- `adjointCarlesonSum` is the adjoint of `carlesonSum`. -/
lemma adjointCarlesonSum_adjoint
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (ℭ : Set (𝔓 X)) :
    ∫ x, conj (g x) * carlesonSum ℭ f x = ∫ x, conj (adjointCarlesonSum ℭ g x) * f x := by
  unfold carlesonSum
  simp_rw [Finset.mul_sum]
  classical calc
    _ = ∑ p with p ∈ ℭ, ∫ x, conj (g x) * carlesonOn p f x :=
      integral_finset_sum _ fun p _ ↦ by fun_prop
    _ = ∑ p with p ∈ ℭ, ∫ y, conj (adjointCarleson p g y) * f y := by
      simp_rw [adjointCarleson_adjoint hf hg]
    _ = ∫ y, ∑ p with p ∈ ℭ, conj (adjointCarleson p g y) * f y :=
      (integral_finset_sum _ fun p _ ↦ by fun_prop).symm
    _ = _ := by congr!; rw [← Finset.sum_mul, ← map_sum]; rfl

lemma integrable_adjointCarlesonSum (s : Set (𝔓 X)) {f : X → ℂ} (hf : BoundedCompactSupport f) :
    Integrable (adjointCarlesonSum s f ·) := by fun_prop

end Adjoint
