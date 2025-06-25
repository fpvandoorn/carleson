import Carleson.FinitaryCarleson
-- import Carleson.MetricCarleson.Basic

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

variable [IsCancellative X (defaultτ a)]

section Recursion

variable (q q' F f σ₁ σ₂) in
/-- Convenience structure for the parameters that stay constant throughout the recursive calls to
finitary Carleson in the proof of Lemma 3.0.4. -/
structure CP304 where
  /-- `Q` is the only non-`Prop` field of `CP304`. -/
  Q : SimpleFunc X (Θ X)
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
  obtain ⟨Q, hq, hqq', bF, mF, mf, nf, mσ₁, mσ₂, rσ₁, rσ₂, lσ⟩ := CP
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
    ⟨‹_›, bF, bG, mF, mG, vF, vG, mσ₁, mσ₂, rσ₁, rσ₂, lσ, Q, hq⟩
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

end Recursion

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
def C3_0_4 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (471 * a ^ 3 + 3) / (q - 1) ^ 6

lemma le_C3_0_4 (hq : q ∈ Ioc 1 2) : C2_0_1 a q * (2 ^ 2 / (q - 1)) ≤ C3_0_4 a q :=
  calc
    _ = (2 ^ (471 * a ^ 3) * (q - 1) / (q - 1) ^ 5 + C5_1_3 a q) * (2 ^ 2 / (q - 1)) := by
      rw [C2_0_1, C2_0_2]; congr; rw [C5_1_2, pow_succ _ 4, mul_div_mul_right]
      rw [← zero_lt_iff, tsub_pos_iff_lt]; exact hq.1
    _ ≤ (2 ^ (471 * a ^ 3) * 1 / (q - 1) ^ 5 + 2 ^ (471 * a ^ 3) / (q - 1) ^ 5) *
        (2 ^ 2 / (q - 1)) := by
      rw [C5_1_3]; gcongr
      · rw [tsub_le_iff_left, one_add_one_eq_two]; exact hq.2
      · exact one_le_two
      · norm_num
    _ = _ := by
      rw [mul_one, ← two_mul, ← mul_div_assoc 2, ← pow_succ', div_mul_div_comm, ← pow_add,
        ← pow_succ, C3_0_4]

/-- Lemma 3.0.4. -/
lemma linearized_truncation (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (bG : IsBounded G) (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1) (mσ₁ : Measurable σ₁) (mσ₂ : Measurable σ₂)
    (rσ₁ : (range σ₁).Finite) (rσ₂ : (range σ₂).Finite) (lσ : σ₁ ≤ σ₂) :
    ∫⁻ x in G, ‖T_lin Q σ₁ σ₂ f x‖ₑ ≤
    C3_0_4 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  let CP : CP304 q q' F f σ₁ σ₂ := ⟨Q, hq, hqq', bF, mF, mf, nf, mσ₁, mσ₂, rσ₁, rσ₂, lσ⟩
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
    _ ≤ _ := by rw [← ENNReal.coe_mul]; gcongr; exact le_C3_0_4 hq

/-- Lemma 3.0.3. `B` is the blueprint's `S`. -/
lemma S_truncation {B : ℕ} (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (bF : IsBounded F) (bG : IsBounded G) (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1) :
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
  exact linearized_truncation hq hqq' bF bG mF mG mf nf mσ₁ mσ₂ rσ₁ rσ₂ lσ

/-- The operator T_{R₁, R₂, R} introduced in Lemma 3.0.2. -/
def T_R (K : X → X → ℂ) (Q : SimpleFunc X (Θ X)) (R₁ R₂ R : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  (ball o R).indicator (fun x ↦ carlesonOperatorIntegrand K (Q x) R₁ R₂ f x) x

/-- The constant used in `metric_carleson` and `R_truncation`.
Has value `2 ^ (450 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C1_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (450 * a ^ 3) / (q - 1) ^ 6

lemma C1_0_2_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C1_0_2 a q := by
  rw [C1_0_2]
  apply div_pos
  · positivity
  · exact pow_pos (tsub_pos_of_lt hq) _

lemma R_truncation
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : volume F < ∞) (hG : volume G < ∞)
    (hf : Measurable f) (h2f : (‖f ·‖) ≤ F.indicator 1)
    {n : ℤ} {R : ℝ} (hR : R = 2 ^ n) :
    ∫⁻ x in G, ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R⁻¹ < R₁) (_ : R₁ < R₂) (_ : R₂ < R), ‖T_R K Q R₁ R₂ R f x‖ₑ ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  sorry
