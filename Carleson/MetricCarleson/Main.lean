import Carleson.MetricCarleson.Linearized

open scoped NNReal
open MeasureTheory Set ENNReal Metric

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
variable [KernelProofData a K] {f : X → ℂ} {x : X}

variable (X) in
/-- A countable dense set of `Θ X`. -/
def Θ' : Set (Θ X) := (TopologicalSpace.exists_countable_dense _).choose

lemma countable_Θ' : (Θ' X).Countable := (TopologicalSpace.exists_countable_dense _).choose_spec.1
lemma dense_Θ' : Dense (Θ' X) := (TopologicalSpace.exists_countable_dense _).choose_spec.2

/-- A countable dense subset of the range of `R₁` and `R₂`. -/
def J102 : Set (ℚ × ℚ) := {p | 0 < p.1 ∧ p.1 < p.2}

lemma carlesonOperator_eq_biSup_Θ'_J102 (mf : Measurable f) (nf : (‖f ·‖) ≤ 1) :
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

lemma biSup_Θ'_eq_biSup_enumΘ' :
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

/-- The argmax over the first `n + 1` functions of `enumΘ'` with respect to `g`,
with ties broken in favour of the lower-indexed function. -/
def enumΘ'ArgMax : ℕ → X → Θ' X
  | 0, _ => enumΘ' nΘ' 0
  | n + 1, x =>
    if g (enumΘ'ArgMax n x) x < g (enumΘ' nΘ' (n + 1)) x
    then enumΘ' nΘ' (n + 1) else enumΘ'ArgMax n x

/-- The simple function corresponding to the blueprint's `Q_n`. -/
def QΘ' (n : ℕ) : SimpleFunc X (Θ X) where
  toFun x := enumΘ'ArgMax nΘ' g n x
  measurableSet_fiber' x := by
    sorry
  finite_range' := by
    sorry

lemma biSup_enumΘ'_eq_biSup_QΘ' {n : ℕ} :
    ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x = g (QΘ' nΘ' g n x) x := by
  sorry

end Enum

lemma BST_LNT_of_BST_NT {Q : SimpleFunc X (Θ X)}
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)) :
    ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a) := fun θ f bf ↦ by
  constructor
  · dsimp only
    sorry
  · refine (eLpNorm_mono_enorm fun x ↦ ?_).trans (hT f bf).2
    simp_rw [enorm_eq_self, nontangentialOperator]
    refine iSup_le fun x' ↦ iSup₂_le fun R₁ mR₁ ↦ ?_
    rw [mem_Ioi] at mR₁
    have R₁pos : 0 < R₁ := dist_nonneg.trans_lt mR₁
    trans ⨆ R₂, ⨆ (_ : R₁ < R₂), ⨆ x', ⨆ (_ : dist x x' < R₁),
      ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ; swap
    · apply le_iSup₂ _ R₁pos
    conv_rhs => enter [1, R₂]; rw [iSup_comm]; enter [1, x']; rw [iSup_comm]
    conv_rhs => rw [iSup_comm]; enter [1, x']; rw [iSup_comm]
    trans ⨆ (_ : dist x x' < R₁), ⨆ R₂, ⨆ (_ : R₁ < R₂),
      ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ; swap
    · apply le_iSup _ x'
    trans ⨆ R₂, ⨆ (_ : R₁ < R₂), ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ; swap
    · apply le_iSup _ mR₁
    rcases ne_or_eq (upperRadius Q θ x') ⊤ with hur | hur
    · rw [← ofReal_toReal_eq_iff] at hur
      set R₂ := (upperRadius Q θ x').toReal
      rw [← hur, EAnnulus.oo_eq_annulus R₁pos.le]
      rcases le_or_gt R₂ R₁ with hR₂ | hR₂
      · rw [Annulus.oo_eq_empty hR₂, setIntegral_empty, enorm_zero]; exact zero_le _
      · convert le_iSup₂ _ hR₂; rfl
    rw [hur]
    sorry

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
  calc
    _ = ∫⁻ x in G, ⨆ n, ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x := by
      congr with x; exact biSup_Θ'_eq_biSup_enumΘ' nΘ' g
    _ = ⨆ n, ∫⁻ x in G, ⨆ i ∈ Finset.range (n + 1), g (enumΘ' nΘ' i) x := by
      refine lintegral_iSup (fun n ↦ ?_) (fun i j hl ↦ ?_)
      · refine Measurable.iSup fun i ↦ Measurable.iSup fun mi ↦ ?_
        refine Measurable.iSup fun j ↦ Measurable.iSup fun mj ↦ Measurable.enorm ?_
        exact measurable_carlesonOperatorIntegrand (Q := SimpleFunc.const X (enumΘ' nΘ' i)) mf
      · intro x; apply biSup_mono; simp_rw [Finset.mem_range]; omega
    _ = ⨆ n, ∫⁻ x in G, g (QΘ' nΘ' g n x) x := by
      congr! with n x; exact biSup_enumΘ'_eq_biSup_QΘ' nΘ' g
    _ ≤ ⨆ n, ∫⁻ x in G, linearizedCarlesonOperator (QΘ' nΘ' g n) K f x := by
      gcongr with n x; set Q := QΘ' nΘ' g n; unfold linearizedCarlesonOperator
      refine iSup₂_le fun ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩ ↦ ?_
      conv_rhs => enter [1, R₁]; rw [iSup_comm]
      simp_rw [← Rat.cast_lt (K := ℝ), Rat.cast_zero] at hq₁ hq₂
      calc
        _ ≤ ⨆ (R₂ : ℝ), ⨆ (_ : q₁ < R₂),
            ‖carlesonOperatorIntegrand K (Q x) q₁ R₂ f x‖ₑ := by convert le_iSup₂ _ hq₂; rfl
        _ ≤ _ := by convert le_iSup₂ _ hq₁; rfl
    _ ≤ _ := iSup_le fun n ↦ linearized_metric_carleson hq hqq' mF mG mf nf (BST_LNT_of_BST_NT hT)

end
