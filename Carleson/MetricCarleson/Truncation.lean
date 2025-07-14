import Carleson.FinitaryCarleson

open scoped NNReal
open MeasureTheory Set ENNReal Filter Topology ShortVariables Bornology Metric Complex

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
variable [KernelProofData a K] {Q : SimpleFunc X (Θ X)} {f : X → ℂ} {σ₁ σ₂ : X → ℤ}

/-- The operator T_{s₁, s₂} introduced in Lemma 3.0.3. -/
def T_S (Q : SimpleFunc X (Θ X)) (s₁ s₂ : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ s ∈ Finset.Icc s₁ s₂, ∫ y, Ks s x y * f y * exp (I * Q x y)

lemma measurable_T_inner_integral {s : ℤ} (mf : Measurable f) :
    Measurable fun x ↦ ∫ y, Ks s x y * f y * exp (I * Q x y) := by
  rw [← stronglyMeasurable_iff_measurable]
  apply StronglyMeasurable.integral_prod_right
  rw [stronglyMeasurable_iff_measurable]
  apply (measurable_Ks.mul (mf.comp measurable_snd)).mul
  refine ((Complex.measurable_ofReal.comp measurable_Q₂).const_mul I).cexp

lemma measurable_T_S {s₁ s₂} (mf : Measurable f) : Measurable (T_S Q s₁ s₂ f ·) :=
  Finset.measurable_sum _ fun _ _ ↦ measurable_T_inner_integral mf

/-- The operator T_{2, σ₁, σ₂} introduced in Lemma 3.0.4. -/
def T_lin (Q : SimpleFunc X (Θ X)) (σ₁ σ₂ : X → ℤ) (f : X → ℂ) (x : X) : ℂ :=
  T_S Q (σ₁ x) (σ₂ x) f x

lemma measurable_T_lin (mf : Measurable f) (mσ₁ : Measurable σ₁) (mσ₂ : Measurable σ₂)
    (rσ₁ : (range σ₁).Finite) (rσ₂ : (range σ₂).Finite) : Measurable (T_lin Q σ₁ σ₂ f ·) := by
  obtain ⟨lb, hlb⟩ := bddBelow_def.mp rσ₁.bddBelow
  obtain ⟨ub, hub⟩ := bddAbove_def.mp rσ₂.bddAbove
  simp_rw [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hlb hub
  have rearr : T_lin Q σ₁ σ₂ f = fun x ↦ ∑ s ∈ Finset.Icc lb ub,
      {x' | s ∈ Icc (σ₁ x') (σ₂ x')}.indicator
        (fun z ↦ ∫ y, Ks s z y * f y * exp (I * Q z y)) x := by
    ext x; unfold T_lin T_S
    calc
      _ = ∑ s ∈ Finset.Icc (σ₁ x) (σ₂ x), {x' | s ∈ Icc (σ₁ x') (σ₂ x')}.indicator
          (fun z ↦ ∫ y, Ks s z y * f y * exp (I * Q z y)) x := by
        congr! with s ms; rw [indicator_of_mem (by simpa using ms)]
      _ = _ := by
        refine Finset.sum_subset (Finset.Icc_subset_Icc (hlb x) (hub x)) fun s ms ns ↦ ?_
        apply indicator_of_notMem; rwa [mem_setOf_eq, mem_Icc, ← Finset.mem_Icc]
  rw [rearr]
  refine Finset.measurable_sum _ fun _ _ ↦ (measurable_T_inner_integral mf).indicator ?_
  rw [measurableSet_setOf]; apply (measurable_set_mem _).comp
  apply Measurable.comp (f := fun x ↦ (σ₁ x, σ₂ x)) (g := fun p ↦ Icc p.1 p.2)
  · exact measurable_from_prod_countable fun _ _ _ ↦ trivial
  · exact mσ₁.prodMk mσ₂

section Linearised

variable [IsCancellative X (defaultτ a)]

variable (q q' F f σ₁ σ₂) in
/-- Convenience structure for the parameters that stay constant throughout the recursive calls to
finitary Carleson in the proof of Lemma 3.0.4. -/
structure CP304 where
  /-- `Q` is the only non-`Prop` field of `CP304`. -/
  Q : SimpleFunc X (Θ X)
  BST_T_Q (θ : Θ X) : HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
    2 2 volume volume (C_Ts a)
  hq : q ∈ Ioc 1 2
  hqq' : q.HolderConjugate q'
  bF : IsBounded F
  mF : MeasurableSet F
  mf : Measurable f
  nf : (‖f ·‖) ≤ F.indicator 1
  mσ₁ : Measurable σ₁
  mσ₂ : Measurable σ₂
  rσ₁ : (range σ₁).Finite
  rσ₂ : (range σ₂).Finite
  lσ : σ₁ ≤ σ₂

theorem finitary_carleson_step
    (CP : CP304 q q' F f σ₁ σ₂) (bG : IsBounded G) (mG : MeasurableSet G) :
    ∃ G' ⊆ G, IsBounded G' ∧ MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∫⁻ x in G \ G', ‖T_lin CP.Q σ₁ σ₂ f x‖ₑ ≤
    C2_0_1 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  obtain ⟨Q, BST_T_Q, hq, hqq', bF, mF, mf, nf, mσ₁, mσ₂, rσ₁, rσ₂, lσ⟩ := CP
  rcases eq_zero_or_pos (volume G) with vG | vG
  · use ∅, empty_subset _, isBounded_empty, MeasurableSet.empty
    simp only [measure_empty, mul_zero, zero_le, diff_empty, true_and]
    rw [setLIntegral_measure_zero _ _ vG]; exact zero_le _
  rcases eq_zero_or_pos (volume F) with vF | vF
  · use ∅, empty_subset _, isBounded_empty, MeasurableSet.empty
    simp only [measure_empty, mul_zero, zero_le, diff_empty, true_and]
    suffices ∀ x, ‖T_lin Q σ₁ σ₂ f x‖ₑ = 0 by
      rw [lintegral_congr this, lintegral_zero]; exact zero_le _
    intro x; rw [enorm_eq_zero, T_lin]
    refine Finset.sum_eq_zero fun s ms ↦ integral_eq_zero_of_ae ?_
    classical
    convert ite_ae_eq_of_measure_zero (fun y ↦ Ks s x y * f y * exp (I * Q x y)) 0 F vF using 1
    ext y; symm; rw [ite_eq_left_iff]; intro ny
    specialize nf y; simp_rw [indicator_of_notMem ny, norm_le_zero_iff] at nf; simp [nf]
  let PD : ProofData a q K σ₁ σ₂ F G :=
    ⟨‹_›, hq, bF, bG, mF, mG, vF, vG, mσ₁, mσ₂, rσ₁, rσ₂, lσ, Q, BST_T_Q⟩
  obtain ⟨G₁, mG₁, vG₁, hG₁⟩ := finitary_carleson X
  refine ⟨G ∩ G₁, inter_subset_left, bG.subset inter_subset_left, mG.inter mG₁, ?_, ?_⟩
  · refine le_trans ?_ vG₁; gcongr; exact inter_subset_right
  · simp_rw [diff_self_inter]; simp_rw [toFinset_Icc, show nnq = q by rfl] at hG₁
    convert hG₁ f mf nf using 4; rw [eq_sub_iff_add_eq]; norm_cast
    exact hqq'.symm.inv_add_inv_eq_one

variable (q q' F f σ₁ σ₂) in
/-- All the parameters needed to apply the recursion of Lemma 3.0.4. -/
structure P304 where
  /-- `CP` holds all constant parameters. -/
  CP : CP304 q q' F f σ₁ σ₂
  /-- `G` is the set being recursed on. -/
  G : Set X
  bG : IsBounded G
  mG : MeasurableSet G

/-- Construct `G_{n+1}` given `G_n`. -/
def P304.succ (P : P304 q q' F f σ₁ σ₂) : P304 q q' F f σ₁ σ₂ where
  CP := P.CP
  G := (finitary_carleson_step P.CP P.bG P.mG).choose
  bG := (finitary_carleson_step P.CP P.bG P.mG).choose_spec.2.1
  mG := (finitary_carleson_step P.CP P.bG P.mG).choose_spec.2.2.1

variable (CP : CP304 q q' F f σ₁ σ₂) (bG : IsBounded G) (mG : MeasurableSet G)

/-- `slice CP bG mG n` contains `G_n` and its associated data. -/
def slice (n : ℕ) : P304 q q' F f σ₁ σ₂ := P304.succ^[n] ⟨CP, G, bG, mG⟩

variable {CP bG mG n}

@[simp]
lemma slice_CP : (slice CP bG mG n).CP = CP := by
  induction n with
  | zero => simp [slice]
  | succ n ih => rw [slice] at ih ⊢; rwa [Function.iterate_succ_apply']

lemma slice_G_subset : (slice CP bG mG (n + 1)).G ⊆ (slice CP bG mG n).G := by
  rw [slice, Function.iterate_succ_apply']
  set P := slice CP bG mG n
  exact (finitary_carleson_step P.CP P.bG P.mG).choose_spec.1

lemma antitone_slice_G : Antitone fun n ↦ (slice CP bG mG n).G :=
  antitone_nat_of_succ_le fun _ ↦ slice_G_subset

lemma volume_slice : 2 * volume (slice CP bG mG (n + 1)).G ≤ volume (slice CP bG mG n).G := by
  rw [slice, Function.iterate_succ_apply']
  set P := slice CP bG mG n
  exact (finitary_carleson_step P.CP P.bG P.mG).choose_spec.2.2.2.1

lemma volume_slice_le_inv_two_pow_mul : volume (slice CP bG mG n).G ≤ 2⁻¹ ^ n * volume G := by
  induction n with
  | zero => simp [slice]
  | succ n ih =>
    replace ih := volume_slice.trans ih
    rwa [mul_le_iff_le_inv two_ne_zero ofNat_ne_top, ← mul_assoc, ← pow_succ'] at ih

/-- The sets `G_n` become arbitrarily small. -/
lemma exists_volume_slice_lt_eps {ε : ℝ≥0∞} (εpos : 0 < ε) :
    ∃ n, volume (slice CP bG mG (n + 1)).G < ε := by
  suffices ∃ n, 2⁻¹ ^ (n + 1) * volume G < ε by
    obtain ⟨n, hn⟩ := this
    exact ⟨n, volume_slice_le_inv_two_pow_mul.trans_lt hn⟩
  rcases eq_zero_or_pos (volume G) with vG | vG; · simpa [vG]
  have vGnt : volume G ≠ ⊤ := bG.measure_lt_top.ne
  conv =>
    enter [1, n]
    rw [← ENNReal.lt_div_iff_mul_lt (.inl vG.ne') (.inl vGnt), pow_succ', ← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (.inl two_ne_zero) (.inl ofNat_ne_top)]
  have εdvn0 : ε / volume G * 2 ≠ 0 :=
    mul_ne_zero (ENNReal.div_ne_zero.mpr ⟨εpos.ne', vGnt⟩) two_ne_zero
  exact exists_inv_two_pow_lt εdvn0

lemma slice_integral_bound :
    ∫⁻ x in (slice CP bG mG n).G \ (slice CP bG mG (n + 1)).G, ‖T_lin CP.Q σ₁ σ₂ f x‖ₑ ≤
    C2_0_1 a q * volume (slice CP bG mG n).G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  set P := slice CP bG mG n
  convert (finitary_carleson_step P.CP P.bG P.mG).choose_spec.2.2.2.2
  · rw [slice, Function.iterate_succ_apply']; rfl
  · simp [P]

/-- The slightly unusual way of writing the integrand is to facilitate applying the
monotone convergence theorem. -/
lemma slice_integral_bound_sum :
    ∫⁻ x, (G \ (slice CP bG mG (n + 1)).G).indicator (‖T_lin CP.Q σ₁ σ₂ f ·‖ₑ) x ≤
    C2_0_1 a q * (∑ i ∈ Finset.range (n + 1), (2⁻¹ ^ i) ^ (q' : ℝ)⁻¹) *
    volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  rw [lintegral_indicator (mG.diff (slice CP bG mG _).mG)]
  induction n with
  | zero =>
    rw [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_rpow, mul_one]
    convert slice_integral_bound; simp [slice]
  | succ n ih =>
    rw [← diff_union_diff_cancel _ slice_G_subset]; swap
    · exact antitone_slice_G (zero_le _)
    rw [lintegral_union ((slice CP bG mG _).mG.diff (slice CP bG mG _).mG)]; swap
    · exact disjoint_of_subset_right diff_subset disjoint_sdiff_left
    rw [Finset.sum_range_succ, mul_add, add_mul, add_mul]; gcongr
    rw [mul_assoc _ _ (volume G ^ _), ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    apply slice_integral_bound.trans; gcongr; exact volume_slice_le_inv_two_pow_mul

end Linearised

lemma sum_le_four_div_q_sub_one (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') {n : ℕ} :
    ∑ i ∈ Finset.range n, ((2 : ℝ≥0∞)⁻¹ ^ i) ^ (q' : ℝ)⁻¹ ≤ (2 ^ 2 / (q - 1) : ℝ≥0) := by
  have ltq' : 1 < q' := (NNReal.holderConjugate_iff.mp hqq'.symm).1
  calc
    _ = ∑ i ∈ Finset.range n, ((2 : ℝ≥0∞) ^ (-(q' : ℝ)⁻¹)) ^ i := by
      congr! with i mi
      simp_rw [← ENNReal.rpow_natCast, ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_mul]
      rw [mul_comm]
    _ ≤ _ := ENNReal.sum_le_tsum _
    _ = (1 - 2 ^ (-(q' : ℝ)⁻¹))⁻¹ := ENNReal.tsum_geometric _
    _ ≤ 2 * (ENNReal.ofReal (q' : ℝ)⁻¹)⁻¹ := by
      refine near_1_geometric_bound ⟨by positivity, ?_⟩
      norm_cast; rw [inv_le_one_iff₀]; exact .inr ltq'.le
    _ = ENNReal.ofNNReal (2 * q / (q - 1)) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), inv_inv, ofReal_coe_nnreal,
        show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, ← ENNReal.coe_mul]
      rw [NNReal.holderConjugate_iff_eq_conjExponent hq.1] at hqq'
      rw [hqq', mul_div_assoc]
    _ ≤ _ := by rw [sq]; gcongr; exact hq.2

/-- The constant used in `linearized_truncation` and `S_truncation`. -/
def C3_0_4 (a : ℕ) (q : ℝ≥0) : ℝ≥0 :=
  2 ^ ((3 * CDN + 19 + 5 * (CDN / 4)) * a ^ 3 + 2) / (q - 1) ^ 6

lemma eq_C3_0_4 : C2_0_1 a q * (2 ^ 2 / (q - 1)) = C3_0_4 a q := by
  rw [C2_0_1, C2_0_2]
  simp only [C3_0_4, div_mul_div_comm, ← pow_add]
  congr

/-- Lemma 3.0.4. -/
lemma linearized_truncation
    [IsCancellative X (defaultτ a)] (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (bG : IsBounded G) (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1) (mσ₁ : Measurable σ₁) (mσ₂ : Measurable σ₂)
    (rσ₁ : (range σ₁).Finite) (rσ₂ : (range σ₂).Finite) (lσ : σ₁ ≤ σ₂)
    (BST_T_Q : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, ‖T_lin Q σ₁ σ₂ f x‖ₑ ≤
    C3_0_4 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  let CP : CP304 q q' F f σ₁ σ₂ := ⟨Q, BST_T_Q, hq, hqq', bF, mF, mf, nf, mσ₁, mσ₂, rσ₁, rσ₂, lσ⟩
  calc
    _ = ∫⁻ x in ⋃ n, G \ (slice CP bG mG (n + 1)).G, ‖T_lin CP.Q σ₁ σ₂ f x‖ₑ := by
      apply setLIntegral_congr; rw [← diff_iInter]; refine (diff_null_ae_eq_self ?_).symm
      rw [Antitone.measure_iInter]; rotate_left
      · exact fun _ _ _ ↦ antitone_slice_G (by omega)
      · exact fun n ↦ (slice CP bG mG (n + 1)).mG.nullMeasurableSet
      · use 0; rw [← lt_top_iff_ne_top]
        exact (measure_mono slice_G_subset).trans_lt bG.measure_lt_top
      rw [show (0 : ℝ≥0∞) = ⊥ by rfl, iInf_eq_bot]
      exact fun _ ↦ exists_volume_slice_lt_eps
    _ = ∫⁻ x, ⨆ n, (G \ (slice CP bG mG (n + 1)).G).indicator (‖T_lin CP.Q σ₁ σ₂ f ·‖ₑ) x := by
      rw [← lintegral_indicator (MeasurableSet.iUnion fun n ↦ mG.diff (slice CP bG mG (n + 1)).mG)]
      congr! with x
      rw [← iSup_apply, iSup_indicator rfl monotone_const]; swap
      · exact fun _ _ _ ↦ sdiff_le_sdiff_left (antitone_slice_G (by omega))
      rw [iSup_const]
    _ = ⨆ n, ∫⁻ x, (G \ (slice CP bG mG (n + 1)).G).indicator (‖T_lin CP.Q σ₁ σ₂ f ·‖ₑ) x := by
      refine lintegral_iSup (fun n ↦ ?_) (fun i j hl ↦ ?_)
      · exact (measurable_T_lin mf mσ₁ mσ₂ rσ₁ rσ₂).enorm.indicator
          (mG.diff (slice CP bG mG (n + 1)).mG)
      · exact indicator_le_indicator_of_subset (sdiff_le_sdiff_left (antitone_slice_G (by omega)))
          (zero_le _)
    _ ≤ C2_0_1 a q * (2 ^ 2 / (q - 1) : ℝ≥0) * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
      refine iSup_le fun n ↦ slice_integral_bound_sum.trans ?_
      gcongr; exact sum_le_four_div_q_sub_one hq hqq'
    _ = _ := by rw [← ENNReal.coe_mul, eq_C3_0_4]

/-- Lemma 3.0.3. `B` is the blueprint's `S`. -/
lemma S_truncation
    [IsCancellative X (defaultτ a)] {B : ℕ} (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (bG : IsBounded G) (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (BST_T_Q : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, ⨆ s₁ ∈ Finset.Icc (-B : ℤ) B, ⨆ s₂ ∈ Finset.Icc s₁ B, ‖T_S Q s₁ s₂ f x‖ₑ ≤
    C3_0_4 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  -- Define `T1'` and `T1` and prove their measurability
  let T1' (x : X) (s' : ℤ) := ⨆ s₂ ∈ Finset.Icc s' B, ‖T_S Q s' s₂ f x‖ₑ
  have mT1' {n : ℤ} : Measurable (T1' · n) :=
    Measurable.iSup fun _ ↦ Measurable.iSup fun _ ↦ (measurable_T_S mf).enorm
  let T1 (x : X) := ⨆ s₁ ∈ Finset.Icc (-B : ℤ) B, T1' x s₁
  have mT1 : Measurable T1 := Measurable.iSup fun _ ↦ Measurable.iSup fun _ ↦ mT1'
  -- For each `x` define a candidate set of values for `σ₁ x`;
  -- the final value is the minimum in this set. Also prove measurability of membership
  let candσ₁ (x : X) := (Finset.Icc (-B : ℤ) B).filter (T1 x = T1' x ·)
  have necσ₁ (x : X) : (candσ₁ x).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    obtain ⟨s', ms', hs'⟩ := (Finset.Icc (-B : ℤ) B).exists_max_image (T1' x) ⟨0, by simp⟩
    use s', ms'; apply le_antisymm
    · exact iSup₂_le hs'
    · apply le_biSup _ ms'
  have scσ₁ (x : X) : candσ₁ x ⊆ Finset.Icc (-B) B := by simp [candσ₁]
  have mcσ₁ {n : ℤ} : Measurable (n ∈ candσ₁ ·) := by
    simp_rw [candσ₁, Finset.mem_filter, Finset.mem_Icc]
    apply measurable_const.and; rw [← measurableSet_setOf]; exact measurableSet_eq_fun' mT1 mT1'
  -- Define `σ₁` and prove its measurability and finite range
  let σ₁ (x : X) := (candσ₁ x).min' (necσ₁ x)
  have eσ₁ (x : X) : σ₁ x ∈ candσ₁ x := (candσ₁ x).min'_mem (necσ₁ x)
  have minσ₁ (x : X) {n : ℤ} (hn : n ∈ candσ₁ x) : σ₁ x ≤ n := (candσ₁ x).min'_le _ hn
  have mσ₁ : Measurable σ₁ := by
    classical
    refine measurable_to_countable' fun n ↦ ?_
    have eqv : σ₁ ⁻¹' {n} =
        candσ₁ ⁻¹' ((Finset.Icc (-B : ℤ) B).powerset.filter fun c ↦ n ∈ c ∧ ∀ m ∈ c, n ≤ m) := by
      ext x
      simp_rw [mem_preimage, mem_singleton_iff, Finset.coe_filter, Finset.mem_powerset,
        mem_setOf_eq, scσ₁, true_and]
      constructor <;> intro h
      · rw [← h]; exact ⟨eσ₁ x, fun m ↦ minσ₁ x⟩
      · rw [← (candσ₁ x).le_min'_iff (necσ₁ x)] at h; obtain ⟨h₁, h₂ : n ≤ σ₁ x⟩ := h
        exact le_antisymm ((candσ₁ x).min'_le _ h₁) h₂
    simp_rw [eqv, Finset.coe_filter, Finset.mem_powerset, preimage_setOf_eq, measurableSet_setOf]
    refine Measurable.and ?_ (mcσ₁.and (Measurable.forall fun m ↦ mcσ₁.imp measurable_const))
    simp [scσ₁]
  have rσ₁ : (range σ₁).Finite := by
    suffices range σ₁ ⊆ Set.Icc (-B) B by exact (finite_Icc (-B : ℤ) B).subset this
    simp_rw [range_subset_iff, mem_Icc, ← Finset.mem_Icc]; exact fun x ↦ scσ₁ x (eσ₁ x)
  -- Incorporate `σ₁` into the main integral
  simp_rw [candσ₁, Finset.mem_filter, Finset.mem_Icc] at eσ₁
  change ∫⁻ x in G, T1 x ≤ _
  conv_lhs => enter [2, x]; rw [(eσ₁ x).2]
  -- Work analogously to define `σ₂`
  let candσ₂ (x : X) :=
    (Finset.Icc (σ₁ x) B).filter (fun s'' : ℤ ↦ T1' x (σ₁ x) = ‖T_S Q (σ₁ x) s'' f x‖ₑ)
  have necσ₂ (x : X) : (candσ₂ x).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    obtain ⟨s', ms', hs'⟩ := (Finset.Icc (σ₁ x) B).exists_max_image
      (‖T_S Q (σ₁ x) · f x‖ₑ) ⟨σ₁ x, by simpa using (eσ₁ x).1.2⟩
    use s', ms'; apply le_antisymm
    · exact iSup₂_le hs'
    · apply le_biSup _ ms'
  have scσ₂ (x : X) : candσ₂ x ⊆ Finset.Icc (-B : ℤ) B :=
    subset_trans (by simp [candσ₂]) (Finset.Icc_subset_Icc_left (eσ₁ x).1.1)
  have mcσ₂ {n : ℤ} : Measurable (n ∈ candσ₂ ·) := by
    simp_rw [candσ₂, Finset.mem_filter, Finset.mem_Icc]
    apply Measurable.and
    · apply Measurable.and ?_ measurable_const
      rw [← measurableSet_setOf]; exact measurableSet_le mσ₁ measurable_const
    · rw [← measurableSet_setOf]; apply measurableSet_eq_fun'
      · apply Measurable.comp (f := fun x ↦ (x, σ₁ x)) (g := fun p ↦ T1' p.1 p.2)
        · exact measurable_from_prod_countable fun _ ↦ mT1'
        · exact measurable_id.prodMk mσ₁
      · apply Measurable.enorm
        apply (Measurable.comp (f := fun x ↦ (x, σ₁ x)) (g := fun p ↦ T_S Q p.2 n f p.1))
        · exact measurable_from_prod_countable fun _ ↦ measurable_T_S mf
        · exact measurable_id.prodMk mσ₁
  -- Work analogously to prove `σ₂`'s properties
  let σ₂ (x : X) := (candσ₂ x).min' (necσ₂ x)
  have eσ₂ (x : X) : σ₂ x ∈ candσ₂ x := (candσ₂ x).min'_mem (necσ₂ x)
  have minσ₂ (x : X) {n : ℤ} (hn : n ∈ candσ₂ x) : σ₂ x ≤ n := (candσ₂ x).min'_le _ hn
  have mσ₂ : Measurable σ₂ := by
    classical
    refine measurable_to_countable' fun n ↦ ?_
    have eqv : σ₂ ⁻¹' {n} =
        candσ₂ ⁻¹' ((Finset.Icc (-B : ℤ) B).powerset.filter fun c ↦ n ∈ c ∧ ∀ m ∈ c, n ≤ m) := by
      ext x
      simp_rw [mem_preimage, mem_singleton_iff, Finset.coe_filter, Finset.mem_powerset,
        mem_setOf_eq, scσ₂, true_and]
      constructor <;> intro h
      · rw [← h]; exact ⟨eσ₂ x, fun m ↦ minσ₂ x⟩
      · rw [← (candσ₂ x).le_min'_iff (necσ₂ x)] at h; obtain ⟨h₁, h₂ : n ≤ σ₂ x⟩ := h
        exact le_antisymm ((candσ₂ x).min'_le _ h₁) h₂
    simp_rw [eqv, Finset.coe_filter, Finset.mem_powerset, preimage_setOf_eq, measurableSet_setOf]
    refine Measurable.and ?_ (mcσ₂.and (Measurable.forall fun m ↦ mcσ₂.imp measurable_const))
    simp [scσ₂]
  have rσ₂ : (range σ₂).Finite := by
    suffices range σ₂ ⊆ Set.Icc (-B) B by exact (finite_Icc (-B : ℤ) B).subset this
    simp_rw [range_subset_iff, mem_Icc, ← Finset.mem_Icc]; exact fun x ↦ scσ₂ x (eσ₂ x)
  simp_rw [candσ₂, Finset.mem_filter, Finset.mem_Icc] at eσ₂
  have lσ : σ₁ ≤ σ₂ := by intro x; exact (eσ₂ x).1.1
  -- Complete the reduction
  conv_lhs => enter [2, x]; rw [(eσ₂ x).2]
  exact linearized_truncation hq hqq' bF bG mF mG mf nf mσ₁ mσ₂ rσ₁ rσ₂ lσ BST_T_Q

section RTruncation

/-- The largest integer `s₁` satisfying `D ^ (-(s₁ - 2)) * R₁ > 1 / 2`. -/
def L302 (a : ℕ) (R₁ : ℝ) : ℤ := ⌊Real.logb D (2 * R₁)⌋ + 3

/-- The smallest integer `s₂` satisfying `D ^ (-(s₂ + 2)) * R₂ < 1 / (4 * D)`. -/
def U302 (a : ℕ) (R₂ : ℝ) : ℤ := ⌈Real.logb D (4 * R₂)⌉ - 2

include K in
lemma R₁_le_D_zpow_div_four {R₁ : ℝ} : R₁ ≤ D ^ (L302 a R₁ - 1) / 4 := by
  rcases le_or_gt R₁ 0 with hR₁ | hR₁; · exact hR₁.trans (by positivity)
  rw [le_div_iff₀' zero_lt_four, L302, add_sub_assoc, show (3 - 1 : ℤ) = 2 by norm_num]
  have Dg1 := one_lt_realD X
  calc
    _ = (2 : ℝ) * D ^ Real.logb D (2 * R₁) := by
      rw [Real.rpow_logb (defaultD_pos a) Dg1.ne' (by linarith only [hR₁])]; ring
    _ ≤ D * D ^ (⌊Real.logb D (2 * R₁)⌋ + 1) := by
      rw [← Real.rpow_intCast]; gcongr
      · linarith only [four_le_realD X]
      · exact Dg1.le
      · push_cast; exact (Int.lt_floor_add_one _).le
    _ = _ := by rw [← zpow_one_add₀ (defaultD_pos a).ne']; congr 1; omega

include K in
lemma D_zpow_div_two_le_R₂ {R₂ : ℝ} (hR₂ : 0 < R₂) : D ^ (U302 a R₂) / 2 ≤ R₂ := by
  rw [div_le_iff₀' zero_lt_two, U302]
  have Dg1 := one_lt_realD X
  calc
    _ = (D : ℝ)⁻¹ * D ^ (⌈Real.logb D (4 * R₂)⌉ - 1) := by
      conv_rhs => rw [mul_comm, ← zpow_sub_one₀ (defaultD_pos a).ne']
      congr 1; omega
    _ ≤ 2⁻¹ * (4 * R₂) := by
      gcongr; · linarith only [four_le_realD X]
      have : 0 < 4 * R₂ := by positivity
      nth_rw 2 [← Real.rpow_logb (defaultD_pos a) Dg1.ne' this]
      rw [← Real.rpow_intCast]; gcongr
      · exact Dg1.le
      · push_cast; rw [sub_le_iff_le_add]; exact (Int.ceil_lt_add_one _).le
    _ = _ := by ring

include K in
lemma monotoneOn_L302 : MonotoneOn (L302 a) {r | 0 < r} := fun r₁ pr₁ r₂ pr₂ hle ↦ by
  unfold L302; gcongr
  · exact one_lt_realD X
  · rw [mem_setOf_eq] at pr₁; positivity

include K in
lemma monotoneOn_U302 : MonotoneOn (U302 a) {r | 0 < r} := fun r₁ pr₁ r₂ pr₂ hle ↦ by
  unfold U302; gcongr
  · exact one_lt_realD X
  · rw [mem_setOf_eq] at pr₁; positivity

include K in
/-- There exists a uniform bound for all possible values of `L302` and `U302` over the annulus in
`R_truncation`. -/
lemma exists_uniform_annulus_bound {R : ℝ} (hR : 0 < R) :
    ∃ B : ℕ, ∀ R₁ ∈ Ioo R⁻¹ R, ∀ R₂ ∈ Ioo R₁ R,
      L302 a R₁ ∈ Finset.Icc (-B : ℤ) B ∧ U302 a R₂ ∈ Finset.Icc (-B : ℤ) B := by
  have iRpos : 0 < R⁻¹ := by positivity
  let B₁ := (L302 a R⁻¹).natAbs
  let B₂ := (L302 a R).natAbs
  let B₃ := (U302 a R⁻¹).natAbs
  let B₄ := (U302 a R).natAbs
  use max (max B₁ B₂) (max B₃ B₄); intro R₁ mR₁ R₂ mR₂
  have R₁pos : 0 < R₁ := iRpos.trans mR₁.1
  have R₂pos : 0 < R₂ := R₁pos.trans mR₂.1
  constructor
  · suffices L302 a R₁ ∈ Finset.Icc (-B₁ : ℤ) B₂ by rw [Finset.mem_Icc] at this ⊢; omega
    simp_rw [Finset.mem_Icc, B₁, B₂]
    have h₁ : L302 a R⁻¹ ≤ L302 a R₁ := monotoneOn_L302 (X := X) iRpos R₁pos mR₁.1.le
    have h₂ : L302 a R₁ ≤ L302 a R := monotoneOn_L302 (X := X) R₁pos hR mR₁.2.le
    omega
  · suffices U302 a R₂ ∈ Finset.Icc (-B₃ : ℤ) B₄ by rw [Finset.mem_Icc] at this ⊢; omega
    simp_rw [Finset.mem_Icc, B₃, B₄]
    have h₃ : U302 a R⁻¹ ≤ U302 a R₂ := monotoneOn_U302 (X := X) iRpos R₂pos (mR₁.1.trans mR₂.1).le
    have h₄ : U302 a R₂ ≤ U302 a R := monotoneOn_U302 (X := X) R₂pos hR mR₂.2.le
    omega

lemma enorm_setIntegral_annulus_le {x : X} {R₁ R₂ : ℝ} {s : ℤ} (nf : (‖f ·‖) ≤ F.indicator 1) :
    ‖∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ ≤
    C2_1_3 a * globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
  calc
    _ ≤ ∫⁻ y in Annulus.oo x R₁ R₂, ‖Ks s x y‖ₑ * ‖f y‖ₑ * ‖exp (I * Q x y)‖ₑ := by
      simp_rw [← enorm_mul]; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in Annulus.oo x R₁ R₂ ∩ ball x (D ^ s), ‖Ks s x y‖ₑ * ‖f y‖ₑ := by
      simp_rw [enorm_exp_I_mul_ofReal, mul_one]
      rw [← lintegral_inter_add_diff (B := ball x (D ^ s)) _
        (Annulus.oo x R₁ R₂) measurableSet_ball]
      conv_rhs => rw [← add_zero (lintegral ..)]
      congr 1
      refine setLIntegral_eq_zero (Annulus.measurableSet_oo.diff measurableSet_ball) fun y my ↦ ?_
      suffices Ks s x y = 0 by rw [this, enorm_zero, zero_mul, Pi.zero_apply]
      contrapose! my; replace my := dist_mem_Ioo_of_Ks_ne_zero my
      rw [mem_diff, not_and_or, not_not]; right
      rw [mem_Ioo, ← mem_ball'] at my; exact (ball_subset_ball (half_le_self (by positivity))) my.2
    _ ≤ ∫⁻ y in ball x (D ^ s), ‖Ks s x y‖ₑ * ‖f y‖ₑ := lintegral_mono_set inter_subset_right
    _ ≤ ∫⁻ y in ball x (D ^ s),
        C2_1_3 a / volume (ball x (D ^ s)) * ‖F.indicator (1 : X → ℝ) y‖ₑ := by
      gcongr with y
      · exact enorm_Ks_le
      · simp_rw [enorm_le_iff_norm_le, norm_indicator_eq_indicator_norm, Pi.one_apply, norm_one]
        exact nf y
    _ = C2_1_3 a * ⨍⁻ y in ball x (D ^ s), ‖F.indicator (1 : X → ℝ) y‖ₑ ∂volume := by
      rw [lintegral_const_mul']; swap
      · exact div_ne_top coe_ne_top (measure_ball_pos _ x (defaultD_pow_pos a _)).ne'
      rw [setLAverage_eq, div_eq_mul_inv, ENNReal.div_eq_inv_mul, mul_assoc]
    _ ≤ _ := by
      gcongr; exact laverage_le_globalMaximalFunction (by rw [dist_self, defaultD]; positivity)

/-- The fringes of the scale interval in Lemma 3.0.2's proof that require separate handling. -/
def edgeScales (a : ℕ) (R₁ R₂ : ℝ) : Finset ℤ :=
  {L302 a R₁ - 1, L302 a R₁ - 2, U302 a R₂ + 1, U302 a R₂ + 2}

lemma diff_subset_edgeScales {a : ℕ} {R₁ R₂ : ℝ} :
    Finset.Icc (L302 a R₁ - 2) (U302 a R₂ + 2) \ Finset.Icc (L302 a R₁) (U302 a R₂) ⊆
    edgeScales a R₁ R₂ := fun s ms ↦ by
  simp_rw [Finset.mem_sdiff, Finset.mem_Icc, not_and_or, not_le] at ms
  simp only [edgeScales, Finset.mem_insert, Finset.mem_singleton]
  omega

lemma enorm_carlesonOperatorIntegrand_le_T_S {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1) {x : X} :
    ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ₑ ≤
    ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ +
    4 * C2_1_3 a * globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
  have Dg1 := one_lt_realD X
  let BR := Finset.Icc (L302 a R₁ - 2) (U302 a R₂ + 2) -- big range
  let SR := Finset.Icc (L302 a R₁) (U302 a R₂) -- small range
  calc
    _ = ‖∫ y in Annulus.oo x R₁ R₂, ∑ s ∈ BR, Ks s x y * f y * exp (I * Q x y)‖ₑ := by
      unfold carlesonOperatorIntegrand; congr 1
      refine setIntegral_congr_fun Annulus.measurableSet_oo fun y my ↦ ?_
      have dpos : 0 < dist x y := by rw [Annulus.oo, mem_setOf_eq] at my; exact hR₁.trans my.1
      simp_rw [← Finset.sum_mul]; congr
      refine (sum_Ks (Finset.Icc_subset_Icc ?_ ?_) Dg1 dpos).symm
      · rw [L302, add_sub_assoc, show (3 : ℤ) - 2 = 1 by norm_num, add_comm 1, Int.floor_add_one]
        gcongr; exact my.1.le
      · rw [U302, sub_add_cancel]; gcongr; exact my.2.le
    _ = ‖∑ s ∈ BR, ∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ := by
      congr 1; refine integral_finset_sum _ fun s ms ↦ ?_
      simp_rw [mul_rotate _ (f _)]; refine ((integrable_Ks_x Dg1).bdd_mul ?_ ?_).restrict
      · rw [aestronglyMeasurable_iff_aemeasurable]
        exact (mf.mul ((Complex.measurable_ofReal.comp (measurable_Q₁ _))
          |>.const_mul I).cexp).aemeasurable
      · simp_rw [norm_mul, norm_exp_I_mul_ofReal, mul_one]
        use 1; exact fun y ↦ (nf y).trans (indicator_one_le_one y)
    _ ≤ ‖∑ s ∈ SR, ∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ +
        ‖∑ s ∈ BR \ SR, ∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ := by
      have : SR ⊆ BR := Finset.Icc_subset_Icc (by omega) (by omega)
      rw [← Finset.inter_eq_right] at this
      rw [← Finset.sum_inter_add_sum_diff BR SR, this]
      exact enorm_add_le _ _
    _ = ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ +
        ‖∑ s ∈ BR \ SR, ∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ := by
      unfold SR T_S; congr! 3 with s ms; rw [Finset.mem_Icc] at ms
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y ny ↦ ?_
      suffices Ks s x y = 0 by simp_rw [this, zero_mul]
      contrapose! ny; replace ny := dist_mem_Ioo_of_Ks_ne_zero ny
      rw [Annulus.oo, mem_setOf_eq]; refine mem_of_mem_of_subset ny (Ioo_subset_Ioo ?_ ?_)
      · apply R₁_le_D_zpow_div_four (X := X).trans; gcongr; exacts [Dg1.le, ms.1]
      · refine le_trans ?_ (D_zpow_div_two_le_R₂ (X := X) (hR₁.trans hR₂))
        gcongr; exacts [Dg1.le, ms.2]
    _ ≤ ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ +
        ∑ s ∈ BR \ SR, ‖∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ := by
      gcongr; exact enorm_sum_le _ _
    _ ≤ ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ + ∑ s ∈ edgeScales a R₁ R₂,
        ‖∫ y in Annulus.oo x R₁ R₂, Ks s x y * f y * exp (I * Q x y)‖ₑ := by
      gcongr; exact diff_subset_edgeScales
    _ ≤ ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ + ∑ s ∈ edgeScales a R₁ R₂,
        C2_1_3 a * globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      gcongr with s ms; rw [← Finset.mem_coe] at ms; exact enorm_setIntegral_annulus_le nf
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]; gcongr; exact_mod_cast Finset.card_le_four

lemma lintegral_globalMaximalFunction_le (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (mF : MeasurableSet F) (mG : MeasurableSet G) :
    ∫⁻ x in G, globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x ≤
    C2_0_6' (defaultA a) 1 q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  calc
    _ = ∫⁻ x, G.indicator 1 x * globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      simp_rw [← indicator_eq_indicator_one_mul]; rw [lintegral_indicator mG]
    _ ≤ eLpNorm (G.indicator (1 : X → ℝ≥0∞)) q' *
        eLpNorm (globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ))) q := by
      apply lintegral_mul_le_eLpNorm_mul_eLqNorm
      · rw [holderConjugate_coe_iff]; exact hqq'.symm
      · exact aemeasurable_const.indicator mG
      · exact AEStronglyMeasurable.globalMaximalFunction.aemeasurable
    _ ≤ volume G ^ (q' : ℝ)⁻¹ *
        (C2_0_6' (defaultA a) 1 q * eLpNorm (F.indicator (1 : X → ℝ)) q) := by
      gcongr
      · rw [Pi.one_def]; convert eLpNorm_indicator_const_le (1 : ℝ≥0∞) q'
        rw [enorm_eq_self, coe_toReal, one_div, one_mul]
      · refine (hasStrongType_globalMaximalFunction zero_lt_one hq.1 _ ?_).2
        rw [Pi.one_def]; exact memLp_indicator_const _ mF _ (.inr bF.measure_lt_top.ne)
    _ ≤ _ := by
      rw [← mul_assoc, mul_comm (_ ^ _)]; gcongr
      rw [Pi.one_def]; convert eLpNorm_indicator_const_le (1 : ℝ) q
      rw [enorm_one, coe_toReal, one_div, one_mul]

/-- The operator T_{R₁, R₂, R} introduced in Lemma 3.0.2. -/
def T_R (K : X → X → ℂ) (Q : SimpleFunc X (Θ X)) (R₁ R₂ R : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  (ball o R).indicator (fun x ↦ carlesonOperatorIntegrand K (Q x) R₁ R₂ f x) x

/-- The constant used from `R_truncation` to `metric_carleson`. -/
def C1_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ ((3 * CDN + 20 + 5 * (CDN / 4)) * a ^ 3) / (q - 1) ^ 6

lemma C1_0_2_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C1_0_2 a q := by
  rw [C1_0_2]
  apply div_pos
  · positivity
  · exact pow_pos (tsub_pos_of_lt hq) _

lemma le_C1_0_2 (a4 : 4 ≤ a) (hq : q ∈ Ioc 1 2) :
    C3_0_4 a q + 4 * C2_1_3 a * C2_0_6' (defaultA a) 1 q ≤ C1_0_2 a q := by
  have : (1 : ℝ≥0) ≤ 2 := by norm_num
  grw [C2_0_6'_defaultA_one_le hq.1 (a := a)]
  have : q / (q - 1) ≤ 2 / (q - 1) ^ 6 := by
    gcongr
    · have : 0 < q - 1 := tsub_pos_iff_lt.2 hq.1
      positivity
    · exact hq.2
    · have : q - 1 = (q - 1) ^ 1 := by simp
      conv_rhs => rw [this]
      apply pow_le_pow_of_le_one (by simp) ?_ (by norm_num)
      rw [tsub_le_iff_left]
      exact hq.2.trans_eq (by norm_num)
  grw [this]
  simp only [C3_0_4, C2_1_3, C1_0_2, div_eq_mul_inv, ← mul_assoc, ← add_mul]
  gcongr
  rw [show (4 : ℝ≥0) = 2 ^ 2 by norm_num]
  simp only [← pow_add, ← pow_succ]
  have : 2 + (CDN + 2) * a ^ 3 + (4 * a + 1) + 1 ≤ (3 * CDN + 19 + 5 * (CDN / 4)) * a ^ 3 + 2 := by
    ring_nf
    suffices 2 + 4 * a ≤ a ^ 3 by omega
    calc
    _ = 2 * 1 * 1 + 2 * 2 * a := by ring
    _ ≤ 2 * a * a + 2 * a * a := by gcongr <;> linarith
    _ = 4 * a ^ 2 := by ring
    _ ≤ a * a ^ 2 := by gcongr
    _ = a ^ 3 := by ring
  grw [this]
  rw [← mul_two, ← pow_succ]
  gcongr 2 ^ ?_
  suffices 3 ≤ a ^ 3 by linarith
  apply le_trans (by norm_num) (le_trans a4 ?_)
  apply le_self_pow (by linarith) (by norm_num)

variable [IsCancellative X (defaultτ a)]

lemma R_truncation' (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (mF : MeasurableSet F) (mG : MeasurableSet G) (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    {n : ℕ} {R : ℝ} (hR : R = 2 ^ n) (sF : F ⊆ ball o (2 * R)) (sG : G ⊆ ball o R)
    (BST_T_Q : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, ⨆ R₁ ∈ Ioo R⁻¹ R, ⨆ R₂ ∈ Ioo R₁ R, ‖T_R K Q R₁ R₂ R f x‖ₑ ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  have Rpos : 0 < R := by rw [hR]; positivity
  have iRpos : 0 < R⁻¹ := by rw [hR]; positivity
  obtain ⟨B, hB⟩ := exists_uniform_annulus_bound (X := X) Rpos
  calc
    _ = ∫⁻ x in G, ⨆ R₁ ∈ Ioo R⁻¹ R, ⨆ R₂ ∈ Ioo R₁ R,
        ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ₑ := by
      refine setLIntegral_congr_fun mG fun x mx ↦ ?_
      unfold T_R; congr! 7 with R₁ mR₁ R₂ mR₂; rw [indicator_of_mem (sG mx)]
    _ ≤ ∫⁻ x in G, ⨆ R₁ ∈ Ioo R⁻¹ R, ⨆ R₂ ∈ Ioo R₁ R,
        ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ +
        4 * C2_1_3 a * globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      gcongr with x R₁ mR₁ R₂ mR₂
      exact enorm_carlesonOperatorIntegrand_le_T_S (iRpos.trans mR₁.1) mR₂.1 mf nf
    _ ≤ ∫⁻ x in G, ⨆ R₁ ∈ Ioo R⁻¹ R, (⨆ R₂ ∈ Ioo R₁ R, ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ) +
        ⨆ R₂ ∈ Ioo R₁ R, 4 * C2_1_3 a *
          globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      gcongr with x R₁ mR₁; exact biSup_add_le_add_biSup
    _ ≤ ∫⁻ x in G, (⨆ R₁ ∈ Ioo R⁻¹ R, ⨆ R₂ ∈ Ioo R₁ R, ‖T_S Q (L302 a R₁) (U302 a R₂) f x‖ₑ) +
        ⨆ R₁ ∈ Ioo R⁻¹ R, ⨆ R₂ ∈ Ioo R₁ R, 4 * C2_1_3 a *
          globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      gcongr with x; exact biSup_add_le_add_biSup
    _ ≤ ∫⁻ x in G, (⨆ s₁ ∈ Finset.Icc (-B : ℤ) B, ⨆ s₂ ∈ Finset.Icc s₁ B, ‖T_S Q s₁ s₂ f x‖ₑ) +
        4 * C2_1_3 a * globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      gcongr with x
      all_goals refine iSup₂_le fun R₁ mR₁ ↦ iSup₂_le fun R₂ mR₂ ↦ ?_
      · specialize hB R₁ mR₁ R₂ mR₂
        rcases lt_or_ge (U302 a R₂) (L302 a R₁) with hul | hul
        · rw [T_S, Finset.Icc_eq_empty (not_le.mpr hul), Finset.sum_empty, enorm_zero]
          exact zero_le _
        · trans ⨆ s₂ ∈ Finset.Icc (L302 a R₁) B, ‖T_S Q (L302 a R₁) s₂ f x‖ₑ
          · have : U302 a R₂ ∈ Finset.Icc (L302 a R₁) B :=
              Finset.mem_Icc.mpr ⟨hul, (Finset.mem_Icc.mp hB.2).2⟩
            exact le_biSup (α := ℝ≥0∞) _ this
          · exact le_biSup (α := ℝ≥0∞) _ hB.1
      · rfl
    _ = (∫⁻ x in G, ⨆ s₁ ∈ Finset.Icc (-B : ℤ) B, ⨆ s₂ ∈ Finset.Icc s₁ B, ‖T_S Q s₁ s₂ f x‖ₑ) +
        4 * C2_1_3 a * ∫⁻ x in G, globalMaximalFunction volume 1 (F.indicator (1 : X → ℝ)) x := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]; apply lintegral_add_left
      simp_rw [← Finset.mem_coe]
      refine Measurable.biSup _ (Finset.countable_toSet _) fun s₁ ms₁ ↦ ?_
      exact Measurable.biSup _ (Finset.countable_toSet _) fun s₂ ms₂ ↦ (measurable_T_S mf).enorm
    _ ≤ C3_0_4 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ + 4 * C2_1_3 a *
        (C2_0_6' (defaultA a) 1 q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹) := by
      have bF := isBounded_ball.subset sF
      have bG := isBounded_ball.subset sG
      gcongr
      · exact S_truncation hq hqq' bF bG mF mG mf nf BST_T_Q
      · exact lintegral_globalMaximalFunction_le hq hqq' bF mF mG
    _ ≤ _ := by
      simp_rw [← mul_assoc, ← add_mul]; gcongr; norm_cast; exact le_C1_0_2 (four_le_a X) hq

/-- Lemma 3.0.2. -/
lemma R_truncation (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (mF : MeasurableSet F) (mG : MeasurableSet G) (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    {n : ℕ} {R : ℝ} (hR : R = 2 ^ n)
    (BST_T_Q : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, ⨆ R₁ ∈ Ioo R⁻¹ R, ⨆ R₂ ∈ Ioo R₁ R, ‖T_R K Q R₁ R₂ R f x‖ₑ ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  wlog sG : G ⊆ ball o R generalizing G
  · calc
      _ = _ := by
        rw [← inter_comm, ← setLIntegral_indicator measurableSet_ball]
        refine lintegral_congr fun x ↦ ?_
        symm; rw [indicator_apply_eq_self]; intro nx
        simp_rw [T_R, indicator_of_notMem nx, enorm_zero, iSup_zero]
      _ ≤ _ := @this (G ∩ ball o R) (mG.inter measurableSet_ball) inter_subset_right
      _ ≤ _ := by gcongr; exact inter_subset_left
  wlog sF : F ⊆ ball o (2 * R) generalizing F f
  · have nf' : (‖(ball o (2 * R)).indicator f ·‖) ≤ (F ∩ ball o (2 * R)).indicator 1 := fun x ↦ by
      rw [inter_comm, ← indicator_indicator]
      by_cases hx : x ∈ ball o (2 * R)
      · simp_rw [indicator_of_mem hx]; exact nf x
      · simp_rw [indicator_of_notMem hx]; simp
    calc
      _ = _ := by
        refine setLIntegral_congr_fun mG fun x mx ↦ ?_
        unfold T_R carlesonOperatorIntegrand; congr! 7 with R₁ mR₁ R₂ mR₂ x'
        simp_rw [indicator_of_mem (sG mx)]
        refine setIntegral_congr_fun Annulus.measurableSet_oo fun y my ↦ ?_
        congr 2; symm; rw [indicator_apply_eq_self]; apply absurd
        specialize sG mx; rw [Annulus.oo, mem_setOf_eq] at my; rw [mem_ball] at sG ⊢
        calc
          _ ≤ dist x y + dist x o := dist_triangle_left ..
          _ < R₂ + R := add_lt_add my.2 sG
          _ < _ := by rw [two_mul]; exact add_lt_add_right mR₂.2 _
      _ ≤ _ :=
        this (mF.inter measurableSet_ball) (mf.indicator measurableSet_ball) nf' inter_subset_right
      _ ≤ _ := by gcongr; exact inter_subset_left
  exact R_truncation' hq hqq' mF mG mf nf hR sF sG BST_T_Q

end RTruncation
