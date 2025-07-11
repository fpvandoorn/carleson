import Carleson.MetricCarleson.Linearized

open scoped NNReal
open MeasureTheory Set ENNReal Metric

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
variable [KernelProofData a K] {f : X → ℂ}

variable (X) in
/-- A countable dense set of `Θ X`. -/
def Θ' : Set (Θ X) := (TopologicalSpace.exists_countable_dense _).choose

lemma countable_Θ' : (Θ' X).Countable := (TopologicalSpace.exists_countable_dense _).choose_spec.1
lemma dense_Θ' : Dense (Θ' X) := (TopologicalSpace.exists_countable_dense _).choose_spec.2

/-- A countable dense subset of the range of `R₁` and `R₂`. -/
def J102 : Set (ℚ × ℚ) := {p | 0 < p.1 ∧ p.1 < p.2}

lemma carlesonOperator_eq_biSup_Θ'_J102 {x : X} (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) :
    carlesonOperator K f x =
    ⨆ θ ∈ Θ' X, ⨆ j ∈ J102, ‖carlesonOperatorIntegrand K θ j.1 j.2 f x‖ₑ := by
  unfold carlesonOperator linearizedCarlesonOperator; apply le_antisymm
  · refine iSup_le fun θ ↦ iSup₂_le fun R₁ R₂ ↦ iSup₂_le fun hR₁ hR₂ ↦ ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε εpos ltt ↦ ?_
    rw [← NNReal.coe_pos] at εpos
    -- Shift `θ` to an element of `Θ'` with error less than `ε / 2`
    have tcon := @continuous_carlesonOperatorIntegrand _ _ _ _ _ R₁ R₂ _ x mf nf hR₁
    rw [continuous_iff] at tcon; specialize tcon θ _ (half_pos εpos)
    obtain ⟨δ₀, δ₀pos, dθ⟩ := tcon
    have dΘ' := dense_Θ' (X := X)
    rw [dense_iff] at dΘ'; specialize dΘ' θ _ δ₀pos; obtain ⟨θ', mθ'₁, mθ'₂⟩ := dΘ'
    rw [mem_ball] at mθ'₁; specialize dθ _ mθ'₁
    -- Shift `R₁, R₂` to rationals with error less than `ε / 2`
    obtain ⟨q₁, q₂, lq₁, lq, -, dq⟩ :=
      exists_rat_near_carlesonOperatorIntegrand θ' x mf nf hR₁ hR₂ (half_pos εpos)
    -- Combine `dq` and `dθ`
    have final_bound := (dist_triangle ..).trans_lt (add_lt_add dq dθ)
    rw [add_halves] at final_bound
    calc
      _ = ‖carlesonOperatorIntegrand K θ' q₁ q₂ f x +
          (carlesonOperatorIntegrand K θ R₁ R₂ f x -
          carlesonOperatorIntegrand K θ' q₁ q₂ f x)‖ₑ := by rw [add_sub_cancel]
      _ ≤ ‖carlesonOperatorIntegrand K θ' q₁ q₂ f x‖ₑ +
          edist (carlesonOperatorIntegrand K θ' q₁ q₂ f x)
          (carlesonOperatorIntegrand K θ R₁ R₂ f x) := by rw [edist_comm]; exact enorm_add_le _ _
      _ ≤ _ := by
        gcongr
        · calc
            _ ≤ ⨆ j ∈ J102, ‖carlesonOperatorIntegrand K θ' j.1 j.2 f x‖ₑ := by
              have : (q₁, q₂) ∈ J102 := ⟨Rat.cast_pos.mp (hR₁.trans lq₁), lq⟩
              convert le_iSup₂ _ this; rfl
            _ ≤ _ := by apply le_iSup₂ _ mθ'₂
        · rw [edist_dist, coe_nnreal_eq]; exact ofReal_le_ofReal final_bound.le
  · refine iSup₂_le fun θ mθ ↦ iSup₂_le fun ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩ ↦ ?_
    conv_rhs => enter [1, θ, 1, R₁]; rw [iSup_comm]
    simp_rw [← Rat.cast_lt (K := ℝ), Rat.cast_zero] at hq₁ hq₂
    calc
      _ ≤ ⨆ (R₂ : ℝ), ⨆ (_ : q₁ < R₂),
          ‖carlesonOperatorIntegrand K θ q₁ R₂ f x‖ₑ := by convert le_iSup₂ _ hq₂; rfl
      _ ≤ ⨆ (R₁ : ℝ), ⨆ (_ : 0 < R₁), ⨆ R₂, ⨆ (_ : R₁ < R₂),
          ‖carlesonOperatorIntegrand K θ R₁ R₂ f x‖ₑ := by convert le_iSup₂ _ hq₁; rfl
      _ ≤ _ := le_iSup_iff.mpr fun _ a ↦ a θ

section Enum

variable (nΘ' : (Θ' X).Nonempty) (g : Θ X → X → ℝ≥0∞)

/-- An enumeration of `Θ' X`, assuming it is nonempty. It may contain duplicates. -/
def enumΘ' : ℕ → Θ' X :=
  (countable_Θ'.exists_surjective nΘ').choose

lemma surjective_enumΘ' : Function.Surjective (enumΘ' nΘ') :=
  (countable_Θ'.exists_surjective nΘ').choose_spec

lemma biSup_Θ'_eq_biSup_enumΘ' {x : X} :
    ⨆ θ ∈ Θ' X, g θ x = ⨆ n, ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x := by
  apply le_antisymm
  · refine iSup₂_le fun θ mθ ↦ ?_
    obtain ⟨n, hn⟩ := surjective_enumΘ' nΘ' ⟨θ, mθ⟩
    have eg : g θ x = g (enumΘ' nΘ' n).1 x := by simp [hn]
    rw [eg]
    calc
      _ ≤ ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x := by
        have : n ∈ Finset.range (n + 1) := by rw [Finset.mem_range]; omega
        convert le_iSup₂ _ this; rfl
      _ ≤ _ := le_iSup_iff.mpr fun _ a ↦ a n
  · refine iSup_le fun n ↦ iSup₂_le fun i mi ↦ ?_
    obtain ⟨θ, mθ⟩ := enumΘ' nΘ' i; apply le_iSup₂ _ mθ

/-- The argmax of `g (enumΘ' nΘ' i) x` over `i ≤ n` with lower indices winning ties. -/
def enumΘ'ArgMax (n : ℕ) (x : X) : ℕ :=
  (List.range (n + 1)).findIdx fun i ↦ ∀ j ≤ n, g (enumΘ' nΘ' j) x ≤ g (enumΘ' nΘ' i) x

lemma enumΘ'ArgMax_mem_range {n : ℕ} {x : X} : enumΘ'ArgMax nΘ' g n x ∈ Finset.range (n + 1) := by
  rw [Finset.mem_range, ← @List.length_range (n + 1), enumΘ'ArgMax, List.findIdx_lt_length]
  simp_rw [List.mem_range, decide_eq_true_eq]
  obtain ⟨i₀, mi₀, li₀⟩ :=
    (Finset.range (n + 1)).exists_max_image (fun i ↦ g (enumΘ' nΘ' i) x) (by simp)
  simp_rw [Finset.mem_range, Nat.lt_add_one_iff] at mi₀ li₀ ⊢; use i₀

/-- The characterising property of `enumΘ'ArgMax`. -/
lemma enumΘ'ArgMax_eq_iff {n i : ℕ} {x : X} (hi : i ≤ n) :
    enumΘ'ArgMax nΘ' g n x = i ↔
    (∀ j ≤ n, g (enumΘ' nΘ' j) x ≤ g (enumΘ' nΘ' i) x) ∧
    ∀ j < i, g (enumΘ' nΘ' j) x < g (enumΘ' nΘ' i) x := by
  rw [enumΘ'ArgMax, List.findIdx_eq (by rw [List.length_range]; omega)]
  simp_rw [List.getElem_range, decide_eq_true_eq, decide_eq_false_iff_not, not_forall, not_le,
    exists_prop, and_congr_right_iff]
  refine fun ismax ↦ forall₂_congr fun j lj ↦ ⟨fun h ↦ ?_, fun h ↦ by use i⟩
  obtain ⟨k, lk, lk'⟩ := h; exact lk'.trans_le (ismax _ lk)

variable {g} (mg : ∀ θ, Measurable (g θ))

/-- The simple function corresponding to the blueprint's `Q_n`. -/
def QΘ' (n : ℕ) : SimpleFunc X (Θ X) where
  toFun x := enumΘ' nΘ' (enumΘ'ArgMax nΘ' g n x)
  measurableSet_fiber' θ := by
    simp_rw [← measurable_mem, mem_preimage, mem_singleton_iff]
    apply Measurable.comp (g := fun i ↦ (enumΘ' nΘ' i).1 = θ) (f := enumΘ'ArgMax nΘ' g n)
    · exact measurable_id
    refine measurable_to_countable' fun i ↦ ?_
    simp_rw [← measurable_mem, mem_preimage, mem_singleton_iff]
    rcases lt_or_ge n i with hi | hi
    · have (x : X) : enumΘ'ArgMax nΘ' g n x ≠ i := by
        contrapose! hi; rw [← hi, ← Nat.lt_add_one_iff, ← Finset.mem_range]
        exact enumΘ'ArgMax_mem_range nΘ' g
      simp_rw [this]; exact measurable_const
    simp_rw [enumΘ'ArgMax_eq_iff nΘ' g hi]; apply Measurable.and
    all_goals refine (Measurable.forall fun j ↦ measurable_const.imp ?_); rw [← measurableSet_setOf]
    · exact measurableSet_le (mg _) (mg _)
    · exact measurableSet_lt (mg _) (mg _)
  finite_range' := by
    classical
    have fbs : ((Finset.range (n + 1)).image fun i ↦ (enumΘ' nΘ' i).1).toSet.Finite :=
      Finset.finite_toSet _
    refine fbs.subset fun θ mθ ↦ ?_
    simp only [mem_range, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio] at mθ ⊢
    obtain ⟨x, hx⟩ := mθ
    have key := enumΘ'ArgMax_mem_range nΘ' g (n := n) (x := x)
    rw [Finset.mem_range] at key; exact ⟨_, key, hx⟩

lemma biSup_enumΘ'_le_biSup_QΘ' {n : ℕ} {x : X} :
    ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x ≤ g (QΘ' nΘ' mg n x) x := by
  rw [QΘ', SimpleFunc.coe_mk]; refine iSup₂_le fun i mi ↦ ?_
  have mam := enumΘ'ArgMax_mem_range nΘ' g (n := n) (x := x)
  rw [Finset.mem_range, Nat.lt_add_one_iff] at mi mam
  have key := enumΘ'ArgMax_eq_iff nΘ' g mam (x := x)
  simp only [true_iff] at key; exact key.1 _ mi

end Enum

lemma BST_LNT_of_BST_NT {Q : SimpleFunc X (Θ X)}
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)) :
    ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a) := fun θ f bf ↦ by
  constructor
  · dsimp only; unfold linearizedNontangentialOperator
    sorry
  · refine (eLpNorm_mono_enorm fun x ↦ ?_).trans (hT f bf).2
    simp_rw [enorm_eq_self]
    refine iSup_le fun R₂ ↦ iSup₂_le fun R₁ mR₁ ↦ iSup₂_le fun x' mx' ↦ ?_
    rw [min_def]; split_ifs with h
    · trans ⨆ R₁ ∈ Ioo 0 R₂, ⨆ x' ∈ ball x R₁, ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ; swap
      · apply le_iSup _ R₂
      trans ⨆ x' ∈ ball x R₁, ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ; swap
      · apply le_iSup₂ _ mR₁
      rw [EAnnulus.oo_eq_annulus mR₁.1.le]
      apply le_iSup₂ _ mx'
    · rcases le_or_gt (upperRadius Q θ x') (ENNReal.ofReal R₁) with hur | hur
      · rw [EAnnulus.oo_eq_empty hur, setIntegral_empty, enorm_zero]; exact zero_le _
      rw [not_le] at h
      have urnt : upperRadius Q θ x' ≠ ⊤ := by
        rw [← lt_top_iff_ne_top]; exact h.trans (by finiteness)
      rw [← ofReal_toReal urnt] at h hur ⊢
      rw [ofReal_lt_ofReal_iff (mR₁.1.trans mR₁.2)] at h
      rw [ofReal_lt_ofReal_iff_of_nonneg mR₁.1.le] at hur
      rw [EAnnulus.oo_eq_annulus mR₁.1.le]; set R := (upperRadius Q θ x').toReal
      trans ⨆ R₁ ∈ Ioo 0 R, ⨆ x' ∈ ball x R₁, ‖∫ y in Annulus.oo x' R₁ R, K x' y * f y‖ₑ; swap
      · convert le_iSup _ R; rfl
      trans ⨆ x' ∈ ball x R₁, ‖∫ y in Annulus.oo x' R₁ R, K x' y * f y‖ₑ; swap
      · have : R₁ ∈ Ioo 0 R := ⟨mR₁.1, hur⟩
        apply le_iSup₂ _ this
      apply le_iSup₂ _ mx'

/-- Theorem 1.0.2 -/
theorem metric_carleson [IsCancellative X (defaultτ a)]
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹ := by
  have nf' : (‖f ·‖) ≤ 1 := nf.trans (indicator_le_self' (by simp))
  calc
    _ = ∫⁻ x in G, ⨆ θ ∈ Θ' X, ⨆ j ∈ J102, ‖carlesonOperatorIntegrand K θ j.1 j.2 f x‖ₑ := by
      congr with x; exact carlesonOperator_eq_biSup_Θ'_J102 mf nf'
    _ ≤ _ := ?_
  rcases (Θ' X).eq_empty_or_nonempty with eΘ' | nΘ'
  · simp_rw [eΘ', iSup_emptyset, bot_eq_zero, lintegral_zero]; exact zero_le _
  let g (θ : Θ X) (x : X) := ⨆ j ∈ J102, ‖carlesonOperatorIntegrand K θ j.1 j.2 f x‖ₑ
  have mg (θ : Θ X) : Measurable (g θ) :=
    Measurable.biSup _ J102.to_countable fun j mj ↦
      (measurable_carlesonOperatorIntegrand (Q := SimpleFunc.const X θ) mf).enorm
  calc
    _ = ∫⁻ x in G, ⨆ n, ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x := by
      congr with x; exact biSup_Θ'_eq_biSup_enumΘ' nΘ' g
    _ = ⨆ n, ∫⁻ x in G, ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x := by
      refine lintegral_iSup (fun n ↦ ?_) (fun i j hl ↦ ?_)
      · refine Measurable.iSup fun i ↦ Measurable.iSup fun mi ↦ ?_
        refine Measurable.iSup fun j ↦ Measurable.iSup fun mj ↦ Measurable.enorm ?_
        exact measurable_carlesonOperatorIntegrand (Q := SimpleFunc.const X (enumΘ' nΘ' i)) mf
      · intro x; apply biSup_mono; simp_rw [Finset.mem_range]; omega
    _ ≤ ⨆ n, ∫⁻ x in G, g (QΘ' nΘ' mg n x) x := by
      gcongr with n x; exact biSup_enumΘ'_le_biSup_QΘ' nΘ' mg
    _ ≤ ⨆ n, ∫⁻ x in G, linearizedCarlesonOperator (QΘ' nΘ' mg n) K f x := by
      gcongr with n x; set Q := QΘ' nΘ' mg n; unfold linearizedCarlesonOperator
      refine iSup₂_le fun ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩ ↦ ?_
      conv_rhs => enter [1, R₁]; rw [iSup_comm]
      simp_rw [← Rat.cast_lt (K := ℝ), Rat.cast_zero] at hq₁ hq₂
      calc
        _ ≤ ⨆ (R₂ : ℝ), ⨆ (_ : q₁ < R₂),
            ‖carlesonOperatorIntegrand K (Q x) q₁ R₂ f x‖ₑ := by convert le_iSup₂ _ hq₂; rfl
        _ ≤ _ := by convert le_iSup₂ _ hq₁; rfl
    _ ≤ _ := iSup_le fun n ↦ linearized_metric_carleson hq hqq' mF mG mf nf (BST_LNT_of_BST_NT hT)

end
