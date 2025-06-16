import Carleson.TwoSidedCarleson.Basic
import Carleson.ToMathlib.HardyLittlewood

open MeasureTheory Set Bornology Function ENNReal Metric Filter Topology
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable {f : X → ℂ} {α : ℝ≥0∞}

/-! ## Section 10.2 and Lemma 10.0.3

Question: -/

/-- The constant used in `nontangential_from_simple`.
I(F) think the constant needs to be fixed in the blueprint. -/
irreducible_def C10_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (4 * a)

/-- Lemma 10.2.1, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem maximal_theorem [Nonempty X] :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  apply HasWeakType.hasBoundedWeakType
  have : C10_2_1 a = C_weakType_globalMaximalFunction (defaultA a) 1 1 := by
    unfold C_weakType_globalMaximalFunction C_weakType_maximalFunction
    split_ifs with h; swap; simp at h
    simp_rw [C10_2_1_def, defaultA, coe_pow, coe_ofNat, Nat.cast_pow, Nat.cast_ofNat,
        NNReal.coe_one, div_one, rpow_ofNat, pow_mul', ← npow_add,
        two_add_two_eq_four]; rfl
  rw [this]
  apply hasWeakType_globalMaximalFunction (μ := volume) le_rfl le_rfl

/-- Lemma 10.2.2.
Should be an easy consequence of `VitaliFamily.ae_tendsto_average`. -/
theorem lebesgue_differentiation
    {f : X → ℂ} (hf : BoundedFiniteSupport f) :
    ∀ᵐ x ∂volume, ∃ (c : ℕ → X) (r : ℕ → ℝ),
    Tendsto (fun i ↦ ⨍ y in ball (c i) (r i), f y ∂volume) atTop (𝓝 (f x)) ∧
    Tendsto r atTop (𝓝[>] 0) ∧
    ∀ i, x ∈ ball (c i) (r i) := by
  sorry

/-! Lemma 10.2.3 is in Mathlib: `Pairwise.countable_of_isOpen_disjoint`. -/

section Depth

/-- `δ(x)` in the blueprint. The depth of a point `x` in a set `O` is the supremum of radii of
balls centred on `x` that are subsets of `O`. -/
def depth (O : Set X) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ≥0, ⨆ (_ : ball x r ⊆ O), r

variable {O : Set X} {x y : X}

lemma depth_lt_iff_not_disjoint {d : ℝ} :
    depth O x < ENNReal.ofReal d ↔ ¬Disjoint (ball x d) Oᶜ where
  mp hd := by
    simp_rw [depth, iSup_lt_iff, iSup_le_iff] at hd; obtain ⟨d', ld', hd'⟩ := hd
    have ns := (hd' d.toNNReal).mt; rw [not_le] at ns; specialize ns ld'
    rw [not_subset_iff_exists_mem_notMem] at ns; obtain ⟨y, my, ny⟩ := ns
    have pd := (zero_le _).trans_lt ld'
    rw [ofReal_pos] at pd; replace pd := Real.coe_toNNReal d pd.le
    rw [pd] at my; exact not_disjoint_iff.mpr ⟨y, my, ny⟩
  mpr hd := by
    obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp hd
    simp_rw [depth, iSup_lt_iff, iSup_le_iff]; use edist x y
    rw [mem_ball'] at my₁; simp_rw [edist_lt_ofReal, my₁, true_and]; intro d' sd; by_contra! h
    rw [← ofReal_coe_nnreal, edist_lt_ofReal, ← mem_ball'] at h
    exact my₂ (sd h)

lemma le_depth_iff_subset {d : ℝ} : ENNReal.ofReal d ≤ depth O x ↔ ball x d ⊆ O := by
  rw [← disjoint_compl_right_iff_subset, ← not_iff_not, not_le]
  exact depth_lt_iff_not_disjoint

/-- A point's depth in an open set `O` is positive iff it lies in `O`. -/
lemma depth_pos_iff_mem (hO : IsOpen O) : 0 < depth O x ↔ x ∈ O := by
  constructor <;> intro h
  · contrapose! h; simp_rw [le_zero_iff, depth, iSup_eq_zero]; intro d hd
    by_contra! dpos; apply absurd _ h; rw [coe_ne_zero, ← zero_lt_iff] at dpos
    exact hd (mem_ball_self dpos)
  · obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h)
    lift ε to ℝ≥0 using εpos.le
    calc
      _ < ofNNReal ε := mod_cast εpos
      _ ≤ _ := le_biSup _ hε

lemma depth_eq_zero_iff_notMem (hO : IsOpen O) : depth O x = 0 ↔ x ∉ O := by
  have := (depth_pos_iff_mem hO (x := x)).not
  rwa [not_lt, le_zero_iff] at this

/-- A point has finite depth in `O` iff `O` is not the whole space. -/
lemma depth_lt_top_iff_ne_univ : depth O x < ⊤ ↔ O ≠ univ := by
  constructor <;> intro h
  · contrapose! h; simp_rw [top_le_iff, depth, iSup₂_eq_top, h, subset_univ, exists_const]
    intro r rlt; lift r to ℝ≥0 using rlt.ne
    use r + 1; exact coe_lt_coe_of_lt (lt_add_one r)
  · obtain ⟨p, np⟩ := (ne_univ_iff_exists_notMem _).mp h
    calc
      _ ≤ edist x p := by
        refine iSup₂_le fun r hr ↦ ?_
        contrapose! hr; rw [not_subset]; use p, ?_, np
        rw [coe_nnreal_eq, edist_dist, ofReal_lt_ofReal_iff_of_nonneg dist_nonneg] at hr
        rwa [mem_ball']
      _ < _ := edist_lt_top ..

/-- A "triangle inequality" for depths. -/
lemma depth_le_edist_add_depth : depth O x ≤ edist x y + depth O y := by
  refine iSup₂_le fun d sd ↦ ?_; contrapose! sd
  rw [← lt_tsub_iff_left, coe_nnreal_eq, edist_dist, ← ENNReal.ofReal_sub _ dist_nonneg,
    depth_lt_iff_not_disjoint, not_disjoint_iff] at sd
  obtain ⟨z, mz₁, mz₂⟩ := sd
  rw [mem_ball, lt_tsub_iff_left] at mz₁
  replace mz₁ := mem_ball'.mpr <| (dist_triangle_right ..).trans_lt mz₁
  exact fun w ↦ mz₂ (w mz₁)

lemma depth_bound_1 (hO : O ≠ univ)
    (h : ¬Disjoint (ball x ((depth O x).toReal / 6)) (ball y ((depth O y).toReal / 6))) :
    x ∈ ball y (3 * ((depth O y).toReal / 6)) := by
  rw [mem_ball]
  have dnt {z : X} : depth O z ≠ ⊤ := (depth_lt_top_iff_ne_univ.mpr hO).ne
  have pre : depth O x / 6 + 5 * depth O x / 6 ≤ depth O x / 6 + 7 * depth O y / 6 := by
    calc
      _ = depth O x := by
        rw [← ENNReal.add_div, ← one_add_mul, show (1 : ℝ≥0∞) + 5 = 6 by norm_num, mul_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
      _ ≤ edist x y + depth O y := depth_le_edist_add_depth
      _ ≤ ENNReal.ofReal ((depth O x).toReal / 6 + (depth O y).toReal / 6) + depth O y := by
        rw [edist_dist]
        exact add_le_add_right (ofReal_le_ofReal (dist_lt_of_not_disjoint_ball h).le) _
      _ ≤ depth O x / 6 + depth O y / 6 + depth O y := by
        rw [ofReal_add (by positivity) (by positivity)]
        iterate 2 rw [ofReal_div_of_pos (by norm_num), ofReal_ofNat, ofReal_toReal dnt]
      _ = _ := by
        rw [show (7 : ℝ≥0∞) = 1 + 6 by norm_num, one_add_mul, ENNReal.add_div, mul_comm,
          ENNReal.mul_div_cancel_right (by norm_num) (by norm_num), add_assoc]
  rw [ENNReal.add_le_add_iff_left (div_ne_top dnt (by norm_num)),
    ENNReal.div_le_iff (by norm_num) (by norm_num),
    ENNReal.div_mul_cancel (by norm_num) (by norm_num), mul_comm,
    ← ENNReal.le_div_iff_mul_le (.inl (by norm_num)) (.inl (by norm_num)),
    ENNReal.mul_div_right_comm] at pre
  calc
    _ < (depth O x).toReal / 6 + (depth O y).toReal / 6 := dist_lt_of_not_disjoint_ball h
    _ ≤ (7 / 5 * depth O y).toReal / 6 + (depth O y).toReal / 6 := by
      gcongr; exact mul_ne_top (by finiteness) dnt
    _ ≤ 2 * (depth O y).toReal / 6 + (depth O y).toReal / 6 := by
      nth_rw 3 [← toReal_ofNat]; rw [← toReal_mul]; gcongr
      · exact mul_ne_top (by finiteness) dnt
      · rw [ENNReal.div_le_iff_le_mul (.inl (by norm_num)) (.inl (by norm_num))]
        norm_num
    _ = _ := by rw [mul_div_assoc, ← add_one_mul, two_add_one_eq_three]

lemma depth_bound_2 (hO : O ≠ univ) (h : x ∈ ball y (3 * ((depth O y).toReal / 6))) :
    (depth O x).toReal / 6 + dist x y ≤ 8 * (depth O y).toReal / 6 := by
  rw [mem_ball] at h
  have ent : edist x y ≠ ⊤ := by finiteness
  have dnt {z : X} : depth O z ≠ ⊤ := (depth_lt_top_iff_ne_univ.mpr hO).ne
  calc
    _ ≤ (edist x y + depth O y).toReal / 6 + dist x y := by
      gcongr
      · rw [ENNReal.add_ne_top]; exact ⟨ent, dnt⟩
      · exact depth_le_edist_add_depth
    _ = (depth O y).toReal / 6 + (7 / 6) * dist x y := by
      rw [ENNReal.toReal_add ent dnt, ← dist_edist]; ring
    _ ≤ (depth O y).toReal / 6 + (7 / 6) * (3 * ((depth O y).toReal / 6)) := by gcongr
    _ = (9 / 2) * (depth O y).toReal / 6 := by ring
    _ ≤ _ := by gcongr; norm_num

lemma depth_bound_3 (hO : O ≠ univ) (h : x ∈ ball y (3 * ((depth O y).toReal / 6))) :
    (depth O y).toReal / 6 + dist y x ≤ 8 * (depth O x).toReal / 6 := by
  rw [mem_ball'] at h
  have dnt {z : X} : depth O z ≠ ⊤ := (depth_lt_top_iff_ne_univ.mpr hO).ne
  have dnt2 : depth O y / 2 ≠ ⊤ := ENNReal.div_ne_top dnt (by norm_num)
  have hti : depth O y ≤ 2 * depth O x := by
    rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl (by norm_num)) (.inl (by norm_num)),
      ← ENNReal.add_le_add_iff_left dnt2, ENNReal.add_halves]
    calc
      _ ≤ edist y x + depth O x := depth_le_edist_add_depth
      _ ≤ _ := by
        gcongr; rw [edist_dist]; apply ofReal_le_of_le_toReal
        rw [toReal_div, toReal_ofNat]; linarith
  calc
    _ ≤ (2 * depth O x).toReal / 6 + 3 * ((depth O y).toReal / 6) := by
      gcongr; exact mul_ne_top ofNat_ne_top dnt
    _ ≤ (2 * depth O x).toReal / 6 + 3 * ((2 * depth O x).toReal / 6) := by
      gcongr; exact mul_ne_top ofNat_ne_top dnt
    _ = _ := by rw [toReal_mul, toReal_ofNat]; ring

lemma ball_covering_bounded_intersection
    (hO : IsOpen O ∧ O ≠ univ) {U : Set X} (countU : U.Countable)
    (pdU : U.PairwiseDisjoint fun c ↦ ball c ((depth O c).toReal / 6)) {x : X} (mx : x ∈ O) :
    {c ∈ U | x ∈ ball c (3 * ((depth O c).toReal / 6))}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  set V := {c ∈ U | x ∈ ball c (3 * ((depth O c).toReal / 6))}
  have vbpos : 0 < volume (ball x ((depth O x).toReal / 6)) := by
    refine measure_ball_pos volume x (div_pos ?_ (by norm_num))
    rw [toReal_pos_iff, depth_pos_iff_mem hO.1, depth_lt_top_iff_ne_univ]; exact ⟨mx, hO.2⟩
  have vbnt : volume (ball x ((depth O x).toReal / 6)) ≠ ⊤ := by finiteness
  rw [← ENat.toENNReal_le, Nat.cast_pow, Nat.cast_ofNat, ENat.toENNReal_pow, ENat.toENNReal_ofNat,
    ← ENNReal.mul_le_mul_right vbpos.ne' vbnt]
  have Aeq : (2 : ℝ≥0∞) ^ (3 * a) = defaultA a ^ 3 := by
    rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm]
  calc
    _ = ∑' c : V, volume (ball x ((depth O x).toReal / 6)) := (ENNReal.tsum_set_const _ _).symm
    _ ≤ ∑' c : V, volume (ball c.1 (8 * (depth O c.1).toReal / 6)) :=
      ENNReal.tsum_le_tsum fun ⟨u, mu, xu⟩ ↦
        measure_mono (ball_subset_ball' (depth_bound_2 hO.2 xu))
    _ ≤ 2 ^ (3 * a) * ∑' v : V, volume (ball v.1 ((depth O v.1).toReal / 6)) := by
      rw [← ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun ⟨u, mu, xu⟩ ↦ ?_
      rw [mul_div_assoc, show (8 : ℝ) = 2 ^ 3 by norm_num, Aeq]
      apply measure_ball_two_le_same_iterate
    _ = 2 ^ (3 * a) * volume (⋃ v : V, ball v.1 ((depth O v.1).toReal / 6)) := by
      have VsU : V ⊆ U := sep_subset ..
      haveI : Countable V := by rw [countable_coe_iff]; exact countU.mono VsU
      congr 1
      refine (measure_iUnion (fun ⟨v₁, mv₁⟩ ⟨v₂, mv₂⟩ hn ↦ ?_) (fun _ ↦ measurableSet_ball)).symm
      rw [ne_eq, Subtype.mk.injEq] at hn
      exact pdU (VsU mv₁) (VsU mv₂) hn
    _ ≤ 2 ^ (3 * a) * volume (ball x (8 * (depth O x).toReal / 6)) := by
      gcongr; exact iUnion_subset fun ⟨u, mu, xu⟩ ↦ ball_subset_ball' (depth_bound_3 hO.2 xu)
    _ ≤ _ := by
      rw [show 6 * a = 3 * a + 3 * a by omega, pow_add, mul_assoc]; gcongr
      rw [mul_div_assoc, show (8 : ℝ) = 2 ^ 3 by norm_num, Aeq]
      apply measure_ball_two_le_same_iterate

/-- Lemma 10.2.4, but following the blueprint exactly (with a countable set of centres rather than
functions from `ℕ`). -/
lemma ball_covering' (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (U : Set X) (r : X → ℝ), U.Countable ∧ (U.PairwiseDisjoint fun c ↦ ball c (r c)) ∧
      ⋃ c ∈ U, ball c (3 * r c) = O ∧ (∀ c ∈ U, ¬Disjoint (ball c (7 * r c)) Oᶜ) ∧
      ∀ x ∈ O, {c ∈ U | x ∈ ball c (3 * r c)}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  let W : Set (Set X) := {U | U ⊆ O ∧ U.PairwiseDisjoint fun c ↦ ball c ((depth O c).toReal / 6)}
  obtain ⟨U, maxU⟩ : ∃ U, Maximal (· ∈ W) U := by
    refine zorn_subset _ fun U sU cU ↦ ⟨⋃₀ U, ?_, fun _ ↦ subset_sUnion_of_mem⟩
    simp only [W, sUnion_subset_iff, mem_setOf_eq]
    exact ⟨fun u hu ↦ (sU hu).1, (pairwiseDisjoint_sUnion cU.directedOn).2 fun u hu ↦ (sU hu).2⟩
  have countU : U.Countable := by
    refine maxU.1.2.countable_of_isOpen (fun _ _ ↦ isOpen_ball) (fun u mu ↦ ?_)
    rw [nonempty_ball]; refine div_pos (toReal_pos ?_ ?_) (by norm_num)
    · rw [← zero_lt_iff, depth_pos_iff_mem hO.1]; exact maxU.1.1 mu
    · rw [← lt_top_iff_ne_top, depth_lt_top_iff_ne_univ]; exact hO.2
  refine ⟨U, fun c ↦ (depth O c).toReal / 6, countU, maxU.1.2, ?_, fun c mc ↦ ?_, fun x mx ↦ ?_⟩
  · refine subset_antisymm (fun x mx ↦ ?_) (fun x mx ↦ ?_)
    · simp only [mem_iUnion₂] at mx; obtain ⟨c, mc, mx⟩ := mx
      refine (le_depth_iff_subset.mp ?_) mx
      rw [← mul_comm_div, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_toReal (depth_lt_top_iff_ne_univ.mpr hO.2).ne]
      nth_rw 2 [← one_mul (depth O _)]; gcongr; norm_num
    · rw [mem_iUnion₂]
      by_cases mxU : x ∈ U
      · refine ⟨x, mxU, mem_ball_self ?_⟩
        simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, div_pos_iff_of_pos_right, toReal_pos_iff]
        rw [depth_pos_iff_mem hO.1, depth_lt_top_iff_ne_univ]; exact ⟨mx, hO.2⟩
      obtain ⟨i, mi, hi⟩ : ∃ i ∈ U,
          ¬Disjoint (ball x ((depth O x).toReal / 6)) (ball i ((depth O i).toReal / 6)) := by
        by_contra! h; apply absurd maxU; simp_rw [not_maximal_iff maxU.1]
        exact ⟨insert x U, ⟨insert_subset mx maxU.1.1, maxU.1.2.insert_of_notMem mxU h⟩,
          ssubset_insert mxU⟩
      use i, mi, depth_bound_1 hO.2 hi
  · rw [← depth_lt_iff_not_disjoint, ← mul_comm_div, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_toReal (depth_lt_top_iff_ne_univ.mpr hO.2).ne]
    nth_rw 1 [← one_mul (depth O _)]
    have dpos := (depth_pos_iff_mem hO.1).mpr (maxU.1.1 mc)
    have dlt := (depth_lt_top_iff_ne_univ (x := c)).mpr hO.2
    exact ENNReal.mul_lt_mul_right' dpos.ne' dlt.ne (by norm_num)
  · exact ball_covering_bounded_intersection hO countU maxU.1.2 mx

/-- Lemma 10.2.4. -/
theorem ball_covering (ha : 4 ≤ a) {O : Set X} (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ ball (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, 0 < r i → ¬Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, {i | x ∈ ball (c i) (3 * r i)}.encard ≤ (2 ^ (6 * a) : ℕ) := by
  sorry

#exit

end Depth

variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ### Lemma 10.2.5

Lemma 10.2.5 has an annoying case distinction between the case `E_α ≠ X` (general case) and
`E_α = X` (finite case). It isn't easy to get rid of this case distinction.

In the formalization we state most properties of Lemma 10.2.5 twice, once for each case
(in some cases the condition is vacuous in the finite case, and then we omit it)

We could have tried harder to uniformize the cases, but in the finite case there is really only set
`B*_j`, and in the general case it is convenient to index `B*_j` by the natural numbers.
-/

/-- The property specifying whether we are in the "general case". -/
def GeneralCase (f : X → ℂ) (α : ℝ≥0∞) : Prop :=
  ∃ x, α ≥ globalMaximalFunction (X := X) volume 1 f x

omit [IsCancellative X (defaultτ a)] in
/-- In the finite case, the volume of `X` is finite. -/
lemma volume_lt_of_not_GeneralCase (hf : BoundedFiniteSupport f) (h : ¬ GeneralCase f α)
    (hα : 0 < α) : volume (univ : Set X) < ∞ := by
  simp only [GeneralCase, not_exists, not_le] at h
  have ne_top : α ≠ ⊤ := have ⟨x⟩ : Nonempty X := inferInstance; (h x).ne_top
  have ineq := (maximal_theorem f hf).2
  simp only [wnorm, one_ne_top, reduceIte, wnorm', distribution, toReal_one, inv_one, rpow_one,
    iSup_le_iff] at ineq
  rw [← eq_univ_iff_forall.mpr fun x ↦ (coe_toNNReal ne_top) ▸ h x]
  refine lt_top_of_mul_ne_top_right ?_ (coe_ne_zero.mpr (toNNReal_ne_zero.mpr ⟨hα.ne.symm, ne_top⟩))
  refine (lt_of_le_of_lt (ineq α.toNNReal) ?_).ne
  exact mul_lt_top (by norm_num) <| (BoundedFiniteSupport.memLp hf 1).eLpNorm_lt_top

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
lemma isOpen_MB_preimage_Ioi (hX : GeneralCase f α) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α) ∧
    globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ :=
  have ⟨x, hx⟩ := hX
  ⟨lowerSemiContinuous_globalMaximalFunction.isOpen_preimage _,
    (Set.ne_univ_iff_exists_notMem _).mpr ⟨x, by simpa using hx⟩⟩

/-- The center of B_j in the proof of Lemma 10.2.5 (general case). -/
def czCenter (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : X :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose i

/-- The radius of B_j in the proof of Lemma 10.2.5 (general case). -/
def czRadius (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : ℝ :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose i

/-- The ball B_j in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (czRadius ha hX i)

/-- The ball B_j' introduced below Lemma 10.2.5 (general case). -/
abbrev czBall2 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (2 * czRadius ha hX i)

/-- The ball B_j* in Lemma 10.2.5 (general case). -/
abbrev czBall3 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (3 * czRadius ha hX i)

/-- The ball B_j** in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall7 (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hX i) (7 * czRadius ha hX i)

lemma czBall_pairwiseDisjoint (ha : 4 ≤ a) {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ ball (czCenter ha hX i) (czRadius ha hX i) :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.1

lemma iUnion_czBall3 (ha : 4 ≤ a) {hX : GeneralCase f α} :
    ⋃ i, czBall3 ha hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_czBall7 (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} (hi : 0 < czRadius ha hX i) :
    ¬Disjoint (czBall7 ha hX i) (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.1 i hi

/-- Part of Lemma 10.2.5 (general case). -/
lemma encard_czBall3_le (ha : 4 ≤ a) {hX : GeneralCase f α}
    {y : X} (hy : α < globalMaximalFunction volume 1 f y) :
    {i | y ∈ czBall3 ha hX i}.encard ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering ha (isOpen_MB_preimage_Ioi hX) |>.choose_spec.choose_spec.2.2.2 y hy

lemma mem_czBall3_finite (ha : 4 ≤ a) {hX : GeneralCase f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    {i | y ∈ czBall3 ha hX i}.Finite :=
  finite_of_encard_le_coe (encard_czBall3_le ha hy)

/-- `Q_i` in the proof of Lemma 10.2.5 (general case). -/
def czPartition (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  czBall3 ha hX i \ ((⋃ j < i, czPartition ha hX j) ∪ ⋃ j > i, czBall ha hX j)

lemma MeasurableSet.czPartition (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) :
    MeasurableSet (czPartition ha hX i) := by
  refine i.strong_induction_on (fun j hj ↦ ?_)
  unfold _root_.czPartition
  apply measurableSet_ball.diff ∘ (MeasurableSet.biUnion (to_countable _) hj).union
  exact MeasurableSet.biUnion (to_countable _) (fun _ _ ↦ measurableSet_ball)

lemma czBall_subset_czPartition (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    czBall ha hX i ⊆ czPartition ha hX i := by
  intro r hr
  rw [czPartition]
  refine mem_diff_of_mem ?_ ?_
  · have : dist r (czCenter ha hX i) ≥ 0 := dist_nonneg
    simp_all only [mem_ball]
    linarith
  · rw [mem_ball] at hr
    simp only [mem_union, mem_iUnion, mem_ball, not_or, not_exists, not_lt]
    constructor
    · unfold czPartition
      simp only [mem_diff, mem_ball, mem_union, mem_iUnion, not_or, not_and, not_forall, not_not]
      exact fun _ _ _ _ ↦ by use i
    · intro x hx
      have := pairwiseDisjoint_iff.mp <| czBall_pairwiseDisjoint ha (hX := hX)
      simp only [mem_univ, forall_const] at this
      have := (disjoint_or_nonempty_inter _ _).resolve_right <| (@this i x).mt (by omega)
      exact not_lt.mp <| mem_ball.mpr.mt <| disjoint_left.mp this hr

lemma czPartition_subset_czBall3 (ha : 4 ≤ a) {hX : GeneralCase f α} {i : ℕ} :
    czPartition ha hX i ⊆ czBall3 ha hX i := by
  rw [czPartition]; exact diff_subset

lemma czPartition_pairwiseDisjoint (ha : 4 ≤ a) {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ czPartition ha hX i := by
  simp only [pairwiseDisjoint_iff, mem_univ, forall_const]
  intro i k hik
  have ⟨x, hxi, hxk⟩ := inter_nonempty.mp hik
  have (t d) (hx : x ∈ czPartition ha hX t) (hd : t < d) : x ∉ czPartition ha hX d := by
    have : czPartition ha hX t ⊆ ⋃ j < d, czPartition ha hX j := subset_biUnion_of_mem hd
    rw [czPartition]
    exact notMem_diff_of_mem <| mem_union_left _ (this hx)
  have : _ ∧ _ := ⟨this i k hxi |>.mt (· hxk), this k i hxk |>.mt (· hxi)⟩
  omega

lemma czPartition_pairwiseDisjoint' (ha : 4 ≤ a) {hX : GeneralCase f α}
    {x : X} {i j : ℕ} (hi : x ∈ czPartition ha hX i) (hj : x ∈ czPartition ha hX j) :
    i = j := by
  have := czPartition_pairwiseDisjoint ha (hX := hX)
  apply pairwiseDisjoint_iff.mp this (mem_univ i) (mem_univ j)
  exact inter_nonempty.mp <| .intro x ⟨hi, hj⟩

lemma iUnion_czPartition (ha : 4 ≤ a) {hX : GeneralCase f α} :
    ⋃ i, czPartition ha hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α := by
  rw [← iUnion_czBall3 ha (hX := hX)]
  refine ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have : ⋃ i, czPartition ha hX i ⊆ ⋃ i, czBall3 ha hX i := fun y hy ↦
      have ⟨r, hr⟩ := mem_iUnion.mp hy
      mem_iUnion_of_mem r (czPartition_subset_czBall3 ha hr)
    exact this hx
  · rw [mem_iUnion] at hx ⊢
    by_contra! hp
    obtain ⟨g, hg⟩ := hx
    have ⟨t, ht⟩ : ∃ i, x ∈ (⋃ j < i, czPartition ha hX j) ∪ ⋃ j > i, czBall ha hX j := by
      by_contra! hb
      absurd hp g
      rw [czPartition, mem_diff]
      exact ⟨hg, hb g⟩
    have : ⋃ j > t, czBall ha hX j ⊆ ⋃ j > t, czPartition ha hX j :=
      iUnion₂_mono fun i j ↦ czBall_subset_czPartition ha (i := i)
    have := (mem_or_mem_of_mem_union ht).imp_right (this ·)
    simp_all

open scoped Classical in
variable (f) in
/-- The function `g` in Lemma 10.2.5. (both cases) -/
def czApproximation (ha : 4 ≤ a) (α : ℝ≥0∞) (x : X) : ℂ :=
  if hX : GeneralCase f α then
    if hx : ∃ j, x ∈ czPartition ha hX j then ⨍ y in czPartition ha hX hx.choose, f y else f x
  else ⨍ y, f y

lemma czApproximation_def_of_mem (ha : 4 ≤ a) {hX : GeneralCase f α} {x : X}
    {i : ℕ} (hx : x ∈ czPartition ha hX i) :
    czApproximation f ha α x = ⨍ y in czPartition ha hX i, f y := by
  have : ∃ i, x ∈ czPartition ha hX i := ⟨i, hx⟩
  simp [czApproximation, hX, this, czPartition_pairwiseDisjoint' ha this.choose_spec hx]

lemma czApproximation_def_of_notMem (ha : 4 ≤ a) {x : X} (hX : GeneralCase f α)
    (hx : x ∉ globalMaximalFunction volume 1 f ⁻¹' Ioi α) :
    czApproximation f ha α x = f x := by
  rw [← iUnion_czPartition ha (hX := hX), mem_iUnion, not_exists] at hx
  simp only [czApproximation, hX, ↓reduceDIte, hx, exists_const]

lemma czApproximation_def_of_volume_lt (ha : 4 ≤ a) {x : X}
    (hX : ¬ GeneralCase f α) : czApproximation f ha α x = ⨍ y, f y := by
  simp [czApproximation, hX]

/-- The function `b_i` in Lemma 10.2.5 (general case). -/
def czRemainder' (ha : 4 ≤ a) (hX : GeneralCase f α) (i : ℕ) (x : X) : ℂ :=
  (czPartition ha hX i).indicator (f - czApproximation f ha α) x

variable (f) in
/-- The function `b = ∑ⱼ bⱼ` introduced below Lemma 10.2.5.
In the finite case, we also use this as the function `b = b₁` in Lemma 10.2.5.
We choose a more convenient definition, but prove in `tsum_czRemainder'` that this is the same. -/
def czRemainder (ha : 4 ≤ a) (α : ℝ≥0∞) (x : X) : ℂ :=
  f x - czApproximation f ha α x

/-- Part of Lemma 10.2.5, this is essentially (10.2.16) (both cases). -/
def tsum_czRemainder' (ha : 4 ≤ a) (hX : GeneralCase f α) (x : X) :
    ∑ᶠ i, czRemainder' ha hX i x = czRemainder f ha α x := by
  simp only [czRemainder', czRemainder]
  by_cases hx : ∃ j, x ∈ czPartition ha hX j
  · have ⟨j, hj⟩ := hx
    rw [finsum_eq_single _ j, indicator_of_mem hj]
    · rfl
    · refine fun i hi ↦ indicator_of_notMem ?_ _
      exact (czPartition_pairwiseDisjoint ha (mem_univ i) (mem_univ j) hi).notMem_of_mem_right hj
  · simp only [czApproximation, hX, reduceDIte, hx, sub_self]
    exact finsum_eq_zero_of_forall_eq_zero fun i ↦ indicator_of_notMem (fun hi ↦ hx ⟨i, hi⟩) _

open scoped Classical in
/-- Part of Lemma 10.2.5 (both cases). -/
lemma aemeasurable_czApproximation (ha : 4 ≤ a) {hf : AEMeasurable f} :
    AEMeasurable (czApproximation f ha α) := by
  by_cases hX : GeneralCase f α; swap
  · unfold czApproximation; simp [hX]
  let czA (x : X) := -- Measurable version of `czApproximation f ha α`
    if hx : ∃ j, x ∈ czPartition ha hX j then ⨍ y in czPartition ha hX hx.choose, f y else hf.mk f x
  refine ⟨czA, fun T hT ↦ ?_, hf.ae_eq_mk.mono fun x h ↦ by simp [czApproximation, czA, hX, h]⟩
  let S := {x : X | ∃ j, x ∈ czPartition ha hX j}ᶜ ∩ (hf.mk f) ⁻¹' T
  have : czA ⁻¹' T = S ∪ ⋃₀ (czPartition ha hX '' {i | ⨍ y in czPartition ha hX i, f y ∈ T}) := by
    refine subset_antisymm (fun x h ↦ ?_) (fun x h ↦ ?_)
    · by_cases hx : ∃ j, x ∈ czPartition ha hX j
      · refine Or.inr ⟨czPartition ha hX hx.choose, ⟨mem_image_of_mem _ ?_, hx.choose_spec⟩⟩
        simpa [czA, hx] using h
      · exact Or.inl ⟨hx, by simpa [czA, hx, hX] using h⟩
    · cases h with
      | inl h => simpa [czA, mem_setOf_eq ▸ mem_setOf_eq ▸ h.1] using h.2
      | inr h => obtain ⟨_, ⟨⟨i, ⟨hi, rfl⟩⟩, hxi⟩⟩ := h
                 have hx : ∃ j, x ∈ czPartition ha hX j := ⟨i, hxi⟩
                 simpa [czA, hx, czPartition_pairwiseDisjoint' ha hx.choose_spec hxi] using hi
  rw [this]
  have := Measurable.exists (MeasurableSet.czPartition ha hX · |>.mem)
  apply MeasurableSet.union (by measurability) ∘ MeasurableSet.sUnion ((to_countable _).image _)
  simp [MeasurableSet.czPartition ha hX]

/-- Part of Lemma 10.2.5, equation (10.2.16) (both cases).
This is true by definition, the work lies in `tsum_czRemainder'` -/
lemma czApproximation_add_czRemainder (ha : 4 ≤ a) {x : X} :
    czApproximation f ha α x + czRemainder f ha α x = f x := by
  simp [czApproximation, czRemainder]

/-- Part of Lemma 10.2.5, equation (10.2.17) (both cases). -/
lemma norm_czApproximation_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    ∀ᵐ x, ‖czApproximation f ha α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  sorry

/-- Equation (10.2.17) specialized to the general case. -/
lemma norm_czApproximation_le_infinite (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hX : GeneralCase f α) (hα : 0 < α) :
    ∀ᵐ x, ‖czApproximation f ha α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.18) (both cases). -/
lemma eLpNorm_czApproximation_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : 0 < α) :
    eLpNorm (czApproximation f ha α) 1 volume ≤ eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.19) (general case). -/
lemma support_czRemainder'_subset (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} (hα : 0 < α)
    {i : ℕ} :
    support (czRemainder' ha hX i) ⊆ czBall3 ha hX i := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.20) (general case). -/
lemma integral_czRemainder' (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} (hα : 0 < α)
    {i : ℕ} :
    ∫ x, czRemainder' ha hX i x = 0 := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.20) (finite case). -/
lemma integral_czRemainder (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    ∫ x, czRemainder f ha α x = 0 := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.21) (general case). -/
lemma eLpNorm_czRemainder'_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    (hα : 0 < α) {i : ℕ} :
    eLpNorm (czRemainder' ha hX i) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 ha hX i) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.21) (finite case). -/
lemma eLpNorm_czRemainder_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    eLpNorm (czRemainder f ha α) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.22) (general case). -/
lemma tsum_volume_czBall3_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∑' i, volume (czBall3 ha hX i) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.22) (finite case). -/
lemma volume_univ_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    volume (univ : Set X) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.23) (general case). -/
lemma tsum_eLpNorm_czRemainder'_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∑' i, eLpNorm (czRemainder' ha hX i) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.23) (finite case). -/
lemma tsum_eLpNorm_czRemainder_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    eLpNorm (czRemainder f ha α) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  sorry

/- ### Lemmas 10.2.6 - 10.2.9 -/

/-- The constant `c` introduced below Lemma 10.2.5. -/
irreducible_def c10_0_3 (a : ℕ) : ℝ≥0 := (2 ^ (a ^ 3 + 12 * a + 4))⁻¹

open scoped Classical in
variable (f) in
/-- The set `Ω` introduced below Lemma 10.2.5. -/
def Ω (ha : 4 ≤ a) (α : ℝ≥0∞) : Set X :=
  if hX : GeneralCase f α then ⋃ i, czBall2 ha hX i else univ

/-- The constant used in `estimate_good`. -/
irreducible_def C10_2_6 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a ^ 3 + 3 * a + 2) * c10_0_3 a

/-- Lemma 10.2.6 -/
lemma estimate_good (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) :
    distribution (czOperator K r (czApproximation f ha α)) (α / 2) volume ≤
    C10_2_6 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `czOperatorBound`. -/
irreducible_def C10_2_7 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1) * c10_0_3 a

/-- The function `F` defined in Lemma 10.2.7. -/
def czOperatorBound (ha : 4 ≤ a) (hX : GeneralCase f α) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * ∑' i, ((czRadius ha hX i).toNNReal / nndist x (czCenter ha hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 ha hX i) / volume (ball x (dist x (czCenter ha hX i)))

/-- Lemma 10.2.7.
Note that `hx` implies `hX`, but we keep the superfluous hypothesis to shorten the statement. -/
lemma estimate_bad_partial (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hx : x ∈ (Ω f ha α)ᶜ) (hX : GeneralCase f α) :
    ‖czOperator K r (czRemainder f ha α) x‖ₑ ≤ 3 * czOperatorBound ha hX x + α / 8 := by
  sorry

/-- The constant used in `distribution_czOperatorBound`. -/
irreducible_def C10_2_8 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.8 -/
lemma distribution_czOperatorBound (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    volume ((Ω f ha α)ᶜ ∩ czOperatorBound ha hX ⁻¹' Ioi (α / 8)) ≤
    C10_2_8 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `estimate_bad`. -/
irreducible_def C10_2_9 (a : ℕ) : ℝ≥0 := 2 ^ (5 * a) / c10_0_3 a + 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.9 -/
-- In the proof, case on `GeneralCase f α`, noting in the finite case that `Ω = univ`
lemma estimate_bad (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    distribution (czOperator K r (czRemainder f ha α)) (α / 2) volume ≤
    C10_2_9 a / α * eLpNorm f 1 volume := by
  sorry


/- ### Lemmas 10.0.3 -/

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
-- in proof: do cases on `α ≤ ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a`.
-- If true, use the argument directly below (10.2.37)
theorem czoperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
