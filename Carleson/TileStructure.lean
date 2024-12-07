import Carleson.GridStructure
import Carleson.Psi

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

section Generic
universe u
variable {𝕜 : Type*} [_root_.RCLike 𝕜]
variable {X : Type u} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

/- The data in a tile structure, and some basic properties.
This is mostly separated out so that we can nicely define the notation `d_𝔭`.
Note: compose `𝓘` with `Grid` to get the `𝓘` of the paper. -/
class PreTileStructure {A : outParam ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
  [FunctionDistances 𝕜 X] (Q : outParam (SimpleFunc X (Θ X)))
  (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X)
  extends GridStructure X D κ S o where
  protected 𝔓 : Type u
  fintype_𝔓 : Fintype 𝔓
  protected 𝓘 : 𝔓 → Grid
  surjective_𝓘 : Surjective 𝓘
  𝒬 : 𝔓 → Θ X
  range_𝒬 : range 𝒬 ⊆ range Q

export PreTileStructure (𝒬 range_𝒬)

variable {D : ℕ} {κ : ℝ} {S : ℕ} {o : X}
variable [FunctionDistances 𝕜 X]  {Q : SimpleFunc X (Θ X)} [PreTileStructure Q D κ S o]

variable (X) in
def 𝔓 := PreTileStructure.𝔓 𝕜 X
instance : Fintype (𝔓 X) := PreTileStructure.fintype_𝔓
def 𝓘 : 𝔓 X → Grid X := PreTileStructure.𝓘
lemma surjective_𝓘 : Surjective (𝓘 : 𝔓 X → Grid X) := PreTileStructure.surjective_𝓘
instance : Inhabited (𝔓 X) := ⟨(surjective_𝓘 default).choose⟩
def 𝔠 (p : 𝔓 X) : X := c (𝓘 p)
def 𝔰 (p : 𝔓 X) : ℤ := s (𝓘 p)

local notation "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- A tile structure. -/
-- note: we don't explicitly include injectivity of `Ω` on `𝔓(I)`, since it follows from these
-- axioms: see `toTileLike_injective`
class TileStructure {A : outParam ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
    [FunctionDistances ℝ X] (Q : outParam (SimpleFunc X (Θ X)))
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X)
    extends PreTileStructure Q D κ S o where
  Ω : 𝔓 → Set (Θ X)
  biUnion_Ω {i} : range Q ⊆ ⋃ p ∈ 𝓘 ⁻¹' {i}, Ω p -- 2.0.13, union contains `Q`
  disjoint_Ω {p p'} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') : -- 2.0.13, union is disjoint
    Disjoint (Ω p) (Ω p')
  relative_fundamental_dyadic {p p'} (h : 𝓘 p ≤ 𝓘 p') : -- 2.0.14
    Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  cball_subset {p} : ball_(D, p) (𝒬 p) 5⁻¹ ⊆ Ω p -- 2.0.15, first inclusion
  subset_cball {p} : Ω p ⊆ ball_(D, p) (𝒬 p) 1 -- 2.0.15, second inclusion

export TileStructure (Ω biUnion_Ω disjoint_Ω relative_fundamental_dyadic)

end Generic


open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]

section

variable [TileStructure Q D κ S o] {p p' : 𝔓 X} {f g : Θ X}

-- maybe we should delete the following three notations, and use `dist_{𝓘 p}` instead?
notation "dist_(" 𝔭 ")" => @dist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "nndist_(" 𝔭 ")" => @nndist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "ball_(" 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _


@[simp] lemma dist_𝓘 (p : 𝔓 X) : dist_{𝓘 p} f g = dist_(p) f g := rfl
@[simp] lemma nndist_𝓘 (p : 𝔓 X) : nndist_{𝓘 p} f g = nndist_(p) f g := rfl
@[simp] lemma ball_𝓘 (p : 𝔓 X) {r : ℝ} : ball_{𝓘 p} f r = ball_(p) f r := rfl

@[simp] lemma cball_subset {p : 𝔓 X} : ball_(p) (𝒬 p) 5⁻¹ ⊆ Ω p := TileStructure.cball_subset
@[simp] lemma subset_cball {p : 𝔓 X} : Ω p ⊆ ball_(p) (𝒬 p) 1 := TileStructure.subset_cball

lemma ball_eq_of_grid_eq {p q : 𝔓 X} {ϑ : Θ X} {r : ℝ} (h : 𝓘 p = 𝓘 q) :
    ball_(p) ϑ r = ball_(q) ϑ r := by rw [← ball_𝓘, h]

lemma cball_disjoint {p p' : 𝔓 X} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') :
    Disjoint (ball_(p) (𝒬 p) 5⁻¹) (ball_(p') (𝒬 p') 5⁻¹) :=
  disjoint_of_subset cball_subset cball_subset (disjoint_Ω h hp)

/-- The set `E` defined in Proposition 2.0.2. -/
def E (p : 𝔓 X) : Set X :=
  { x ∈ 𝓘 p | Q x ∈ Ω p ∧ 𝔰 p ∈ Icc (σ₁ x) (σ₂ x) }

lemma E_subset_𝓘 {p : 𝔓 X} : E p ⊆ 𝓘 p := fun _ ↦ mem_of_mem_inter_left

lemma measurableSet_E {p : 𝔓 X} : MeasurableSet (E p) := by
  refine (Measurable.and ?_ (Measurable.and ?_ ?_)).setOf
  · rw [← measurableSet_setOf]; exact coeGrid_measurable
  · simp_rw [← mem_preimage, ← measurableSet_setOf]; exact SimpleFunc.measurableSet_preimage ..
  · apply (measurable_set_mem _).comp
    apply Measurable.comp (f := fun x ↦ (σ₁ x, σ₂ x)) (g := fun p ↦ Icc p.1 p.2)
    · exact measurable_from_prod_countable fun _ _ _ ↦ trivial
    · exact measurable_σ₁.prod_mk measurable_σ₂

section T

/-- The operator `T_𝔭` defined in Proposition 2.0.2, considered on the set `F`.
It is the map `T ∘ (1_F * ·) : f ↦ T (1_F * f)`, also denoted `T1_F`
The operator `T` in Proposition 2.0.2 is therefore `applied to `(F := Set.univ)`. -/
def carlesonOn (p : 𝔓 X) (f : X → ℂ) : X → ℂ :=
  indicator (E p)
    fun x ↦ ∫ y, exp (I * (Q x y - Q x x)) * K x y * ψ (D ^ (- 𝔰 p) * dist x y) * f y

-- obsolete in favor of `AEStronglyMeasurable.carlesonOn`?
lemma measurable_carlesonOn {p : 𝔓 X} {f : X → ℂ} (measf : Measurable f) :
    Measurable (carlesonOn p f) := by
  refine (StronglyMeasurable.integral_prod_right ?_).measurable.indicator measurableSet_E
  refine (((Measurable.mul ?_ measurable_K).mul ?_).mul ?_).stronglyMeasurable
  · have : Measurable fun (p : X × X) ↦ (p.1, p.1) := by fun_prop
    refine ((Measurable.sub ?_ ?_).const_mul I).cexp <;> apply measurable_ofReal.comp
    · exact measurable_Q₂
    · exact measurable_Q₂.comp this
  · apply measurable_ofReal.comp
    apply Measurable.comp (f := fun x : X × X ↦ D ^ (-𝔰 p) * dist x.1 x.2) (g := ψ)
    · exact measurable_const.max (measurable_const.min (Measurable.min (by fun_prop) (by fun_prop)))
    · exact measurable_dist.const_mul _
  · exact measf.comp measurable_snd

open Classical in
/-- The operator `T_ℭ f` defined at the bottom of Section 7.4.
We will use this in other places of the formalization as well. -/
def carlesonSum (ℭ : Set (𝔓 X)) (f : X → ℂ) (x : X) : ℂ :=
  ∑ p ∈ {p | p ∈ ℭ}, carlesonOn p f x

-- obsolete in favor of `AEStronglyMeasurable.carlesonSum`?
@[fun_prop]
lemma measurable_carlesonSum {ℭ : Set (𝔓 X)} {f : X → ℂ} (measf : Measurable f) :
    Measurable (carlesonSum ℭ f) :=
  Finset.measurable_sum _ fun _ _ ↦ measurable_carlesonOn measf

--    fun x ↦ ∫ y, exp (I * (Q x y - Q x x)) * K x y * ψ (D ^ (- 𝔰 p) * dist x y) * f y
lemma _root_.MeasureTheory.AEStronglyMeasurable.carlesonOn {p : 𝔓 X} {f : X → ℂ}
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (carlesonOn p f) := by
  refine .indicator ?_ measurableSet_E
  -- refine AEStronglyMeasurable.integral_prod_right ?_
  refine .integral_prod_right'
    (f := fun z ↦ exp (Complex.I * (Q z.1 z.2 - Q z.1 z.1)) * K z.1 z.2 *
      ψ (D ^ (- 𝔰 p) * dist z.1 z.2) * f z.2) ?_
  refine (((AEStronglyMeasurable.mul ?_ aestronglyMeasurable_K).mul ?_).mul ?_)
  · apply Measurable.aestronglyMeasurable
    have : Measurable fun (p : X × X) ↦ (p.1, p.1) := by fun_prop
    refine ((Measurable.sub ?_ ?_).const_mul I).cexp <;> apply measurable_ofReal.comp
    · exact measurable_Q₂
    · exact measurable_Q₂.comp this
  · apply Measurable.aestronglyMeasurable
    apply measurable_ofReal.comp
    apply Measurable.comp (f := fun x : X × X ↦ D ^ (-𝔰 p) * dist x.1 x.2) (g := ψ)
    · exact measurable_const.max (measurable_const.min (Measurable.min (by fun_prop) (by fun_prop)))
    · exact measurable_dist.const_mul _
  · exact hf.snd

lemma _root_.MeasureTheory.AEStronglyMeasurable.carlesonSum {ℭ : Set (𝔓 X)}
    {f : X → ℂ} (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (carlesonSum ℭ f) :=
  Finset.aestronglyMeasurable_sum _ fun _ _ ↦ hf.carlesonOn

lemma carlesonOn_def' (p : 𝔓 X) (f : X → ℂ) : carlesonOn p f =
    indicator (E p) fun x ↦ ∫ y, Ks (𝔰 p) x y * f y * exp (I * (Q x y - Q x x)) := by
  unfold carlesonOn Ks
  exact congr_arg _ (funext fun x ↦ (congr_arg _ (funext fun y ↦ by ring)))

end T

variable (X) in
def TileLike : Type _ := Grid X × OrderDual (Set (Θ X))

def TileLike.fst (x : TileLike X) : Grid X := x.1
def TileLike.snd (x : TileLike X) : Set (Θ X) := x.2

@[simp] lemma TileLike.fst_mk (x : Grid X) (y : Set (Θ X)) : TileLike.fst (x, y) = x := by rfl
@[simp] lemma TileLike.snd_mk (x : Grid X) (y : Set (Θ X)) : TileLike.snd (x, y) = y := by rfl

instance : PartialOrder (TileLike X) := by dsimp [TileLike]; infer_instance

lemma TileLike.le_def (x y : TileLike X) : x ≤ y ↔ x.fst ≤ y.fst ∧ y.snd ⊆ x.snd := by rfl

def toTileLike (p : 𝔓 X) : TileLike X := (𝓘 p, Ω p)

@[simp] lemma toTileLike_fst (p : 𝔓 X) : (toTileLike p).fst = 𝓘 p := by rfl
@[simp] lemma toTileLike_snd (p : 𝔓 X) : (toTileLike p).snd = Ω p := by rfl

/-- This is not defined as such in the blueprint, but `λp ≲ λ'p'` can be written using
`smul l p ≤ smul l' p'`.
Beware: `smul 1 p` is very different from `toTileLike p`. -/
def smul (l : ℝ) (p : 𝔓 X) : TileLike X :=
  (𝓘 p, ball_(p) (𝒬 p) l)

@[simp] lemma smul_fst (l : ℝ) (p : 𝔓 X) : (smul l p).fst = 𝓘 p := by rfl
@[simp] lemma smul_snd (l : ℝ) (p : 𝔓 X) : (smul l p).snd = ball_(p) (𝒬 p) l := by rfl

lemma smul_mono_left {l l' : ℝ} {p : 𝔓 X} (h : l ≤ l') : smul l' p ≤ smul l p := by
  simp [TileLike.le_def, h, ball_subset_ball]

lemma smul_le_toTileLike : smul 1 p ≤ toTileLike p := by
  simp [TileLike.le_def, subset_cball (p := p)]

lemma toTileLike_le_smul : toTileLike p ≤ smul 5⁻¹ p := by
  simp [TileLike.le_def, cball_subset (p := p)]

lemma 𝒬_mem_Ω : 𝒬 p ∈ Ω p := cball_subset <| mem_ball_self <| by norm_num

lemma 𝒬_inj {p' : 𝔓 X} (h : 𝒬 p = 𝒬 p') (h𝓘 : 𝓘 p = 𝓘 p') : p = p' := by
  contrapose! h
  exact fun h𝒬 ↦ (not_disjoint_iff.2 ⟨𝒬 p, 𝒬_mem_Ω, h𝒬 ▸ 𝒬_mem_Ω⟩) (disjoint_Ω h h𝓘)

lemma toTileLike_injective : Injective (fun p : 𝔓 X ↦ toTileLike p) := by
  intros p p' h
  simp_rw [toTileLike, TileLike, Prod.ext_iff] at h
  by_contra h2
  have : Disjoint (Ω p) (Ω p') := disjoint_Ω h2 h.1
  have : Ω p = ∅ := by simpa [← h.2]
  exact not_mem_empty _ (by rw [← this]; exact 𝒬_mem_Ω)

instance : PartialOrder (𝔓 X) := PartialOrder.lift toTileLike toTileLike_injective

lemma 𝔓.le_def {p q : 𝔓 X} : p ≤ q ↔ toTileLike p ≤ toTileLike q := by rfl
lemma 𝔓.le_def' {p q : 𝔓 X} : p ≤ q ↔ 𝓘 p ≤ 𝓘 q ∧ Ω q ⊆ Ω p := by rfl

lemma dist_𝒬_lt_one_of_le {p q : 𝔓 X} (h : p ≤ q) : dist_(p) (𝒬 q) (𝒬 p) < 1 :=
  ((cball_subset.trans h.2).trans subset_cball) (mem_ball_self (by norm_num))

lemma dist_𝒬_lt_one_of_le' {p q : 𝔓 X} (h : p ≤ q) : dist_(p) (𝒬 p) (𝒬 q) < 1 :=
  mem_ball'.mp (dist_𝒬_lt_one_of_le h)

lemma 𝓘_strictMono : StrictMono (𝓘 (X := X)) := fun _ _ h ↦ h.le.1.lt_of_ne <|
  fun h' ↦ disjoint_left.mp (disjoint_Ω h.ne h') (h.le.2 𝒬_mem_Ω) 𝒬_mem_Ω

/-- Lemma 5.3.1 -/
lemma smul_mono {m m' n n' : ℝ} (hp : smul n p ≤ smul m p') (hm : m' ≤ m) (hn : n ≤ n') :
    smul n' p ≤ smul m' p' :=
  smul_mono_left hn |>.trans hp |>.trans <| smul_mono_left hm

/-- Lemma 5.3.2 (generalizing `1` to `k > 0`) -/
lemma smul_C2_1_2 (m : ℝ) {n k : ℝ} (hk : 0 < k) (hp : 𝓘 p ≠ 𝓘 p') (hl : smul n p ≤ smul k p') :
    smul (n + C2_1_2 a * m) p ≤ smul m p' := by
  replace hp : 𝓘 p < 𝓘 p' := hl.1.lt_of_ne hp
  have : ball_(p') (𝒬 p') m ⊆ ball_(p) (𝒬 p) (n + C2_1_2 a * m) := fun x hx ↦ by
    rw [@mem_ball] at hx ⊢
    calc
      _ ≤ dist_(p) x (𝒬 p') + dist_(p) (𝒬 p') (𝒬 p) := dist_triangle ..
      _ ≤ C2_1_2 a * dist_(p') x (𝒬 p') + dist_(p) (𝒬 p') (𝒬 p) := by
        gcongr; exact Grid.dist_strictMono hp
      _ < C2_1_2 a * m + dist_(p) (𝒬 p') (𝒬 p) := by gcongr; rw [C2_1_2]; positivity
      _ < _ := by
        rw [add_comm]; gcongr
        exact mem_ball.mp <| mem_of_mem_of_subset (by convert mem_ball_self hk) hl.2
  exact ⟨hl.1, this⟩

lemma dist_LTSeries {n : ℕ} {u : Set (𝔓 X)} {s : LTSeries u} (hs : s.length = n) {f g : Θ X} :
    dist_(s.head.1) f g ≤ C2_1_2 a ^ n * dist_(s.last.1) f g := by
  induction n generalizing s with
  | zero => rw [pow_zero, one_mul]; apply Grid.dist_mono s.head_le_last.1
  | succ n ih =>
    let s' : LTSeries u := s.eraseLast
    specialize ih (show s'.length = n by simp [s', hs])
    have link : dist_(s'.last.1) f g ≤ C2_1_2 a * dist_(s.last.1) f g :=
      Grid.dist_strictMono <| 𝓘_strictMono <| s.eraseLast_last_rel_last (by omega)
    apply ih.trans; rw [pow_succ, mul_assoc]; gcongr; unfold C2_1_2; positivity

end

/-- The constraint on `λ` in the first part of Lemma 5.3.3. -/
def C5_3_3 (a : ℕ) : ℝ := (1 - C2_1_2 a)⁻¹

include q K σ₁ σ₂ F G in
lemma C5_3_3_le : C5_3_3 a ≤ 11 / 10 := by
  rw [C5_3_3, inv_le_comm₀ (sub_pos.mpr <| C2_1_2_lt_one X) (by norm_num), le_sub_comm]
  exact C2_1_2_le_inv_512 X |>.trans <| by norm_num

variable [TileStructure Q D κ S o] {p p' : 𝔓 X} {f g : Θ X}

/-- Lemma 5.3.3, Equation (5.3.3) -/
lemma wiggle_order_11_10 {n : ℝ} (hp : p ≤ p') (hn : C5_3_3 a ≤ n) : smul n p ≤ smul n p' := by
  rcases eq_or_ne (𝓘 p) (𝓘 p') with h | h
  · rcases eq_or_ne p p' with rfl | h2
    · rfl
    · exact absurd h (𝓘_strictMono (lt_of_le_of_ne hp h2)).ne
  · calc
      _ ≤ smul (1 + C2_1_2 a * n) p := by
        apply smul_mono_left
        rwa [← le_sub_iff_add_le, ← one_sub_mul, ← inv_le_iff_one_le_mul₀']
        linarith [C2_1_2_le_inv_512 (X := X)]
      _ ≤ smul n p' := smul_C2_1_2 (k := 5⁻¹) n (by norm_num) h
        (smul_le_toTileLike.trans <| 𝔓.le_def.mp hp |>.trans toTileLike_le_smul)

/-- Lemma 5.3.3, Equation (5.3.4) -/
lemma wiggle_order_100 (hp : smul 10 p ≤ smul 1 p') (hn : 𝓘 p ≠ 𝓘 p') :
    smul 100 p ≤ smul 100 p' :=
  calc
    _ ≤ smul (10 + C2_1_2 a * 100) p :=
      smul_mono_left (by linarith [C2_1_2_le_inv_512 (X := X)])
    _ ≤ _ := smul_C2_1_2 100 zero_lt_one hn hp

/-- Lemma 5.3.3, Equation (5.3.5) -/
lemma wiggle_order_500 (hp : smul 2 p ≤ smul 1 p') (hn : 𝓘 p ≠ 𝓘 p') :
    smul 4 p ≤ smul 500 p' :=
  calc
    _ ≤ smul (2 + C2_1_2 a * 500) p :=
      smul_mono_left (by linarith [C2_1_2_le_inv_512 (X := X)])
    _ ≤ _ := smul_C2_1_2 500 zero_lt_one hn hp

def C5_3_2 (a : ℕ) : ℝ := 2 ^ (-95 * (a : ℝ))

def TileLike.toTile (t : TileLike X) : Set (X × Θ X) :=
  (t.fst : Set X) ×ˢ t.snd

/-- From a TileLike, we can construct a set. This is used in the definitions `E₁` and `E₂`. -/
def TileLike.toSet (t : TileLike X) : Set X :=
  t.fst ∩ G ∩ Q ⁻¹' t.snd

def E₁ (p : 𝔓 X) : Set X :=
  (toTileLike p).toSet

def E₂ (l : ℝ) (p : 𝔓 X) : Set X :=
  (smul l p).toSet

lemma E₁_subset (p : 𝔓 X) : E₁ p ⊆ 𝓘 p := by
  change ↑(𝓘 p) ∩ G ∩ (Q ⁻¹' Ω p) ⊆ ↑(𝓘 p)
  rw [inter_assoc]
  exact inter_subset_left

lemma E₂_subset (l : ℝ) (p : 𝔓 X) : E₂ l p ⊆ 𝓘 p := by
  change ↑(𝓘 p) ∩ G ∩ (Q ⁻¹' (ball_(p) (𝒬 p) l)) ⊆ ↑(𝓘 p)
  rw [inter_assoc]
  exact inter_subset_left

/-! `𝔓(𝔓')` in the blueprint is `lowerClosure 𝔓'` in Lean. -/

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₁ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p' ∈ 𝔓') (l ≥ (2 : ℝ≥0)), l ^ (-a : ℝ) *
  ⨆ (p ∈ lowerClosure 𝔓') (_h2 : smul l p' ≤ smul l p),
  volume (E₂ l p) / volume (𝓘 p : Set X)

lemma dens₁_mono {𝔓₁ 𝔓₂ : Set (𝔓 X)} (h : 𝔓₁ ⊆ 𝔓₂) :
    dens₁ 𝔓₁ ≤ dens₁ 𝔓₂ := by
  simp only [dens₁, iSup_le_iff]
  intro p hp r hr
  refine le_iSup₂_of_le p (h hp) ?_
  apply ENNReal.mul_le_of_le_div'
  simp only [iSup_le_iff]
  intro q hq hqr
  rw [ENNReal.le_div_iff_mul_le (by left; simp)]
  · refine le_iSup₂_of_le r hr ?_
    rw [mul_comm]
    gcongr
    exact le_iSup₂_of_le q (lowerClosure_mono h hq) (le_iSup_iff.mpr fun b a ↦ a hqr)
  · left
    have hr0 : r ≠ 0 := by positivity
    simp [hr0]

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₂ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (r ≥ 4 * (D ^ 𝔰 p : ℝ)),
  volume (F ∩ ball (𝔠 p) r) / volume (ball (𝔠 p) r)

-- a small characterization that might be useful
lemma isAntichain_iff_disjoint (𝔄 : Set (𝔓 X)) :
    IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄) ↔
    ∀ p p', p ∈ 𝔄 → p' ∈ 𝔄 → p ≠ p' →
    Disjoint (toTileLike (X := X) p).toTile (toTileLike p').toTile := sorry

lemma ENNReal.rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (hz : z ≤ 0) (h : x ≤ y) :
    y ^ z ≤ x ^ z := by
  rw [← neg_neg z, rpow_neg y, rpow_neg x, ← inv_rpow, ← inv_rpow]
  exact rpow_le_rpow (ENNReal.inv_le_inv.mpr h) (neg_nonneg.mpr hz)

/- A rough estimate. It's also less than 2 ^ (-a) -/
def dens₁_le_one {𝔓' : Set (𝔓 X)} : dens₁ 𝔓' ≤ 1 := by
  conv_rhs => rw [← mul_one 1]
  simp only [dens₁, mem_lowerClosure, iSup_exists, iSup_le_iff]
  intros i _ j hj
  gcongr
  · calc
    (j : ℝ≥0∞) ^ (-(a : ℝ)) ≤ 2 ^ (-(a : ℝ)) := by
      apply ENNReal.rpow_le_rpow_of_nonpos
      · simp_rw [neg_nonpos, Nat.cast_nonneg']
      exact_mod_cast hj
    _ ≤ 2 ^ (0 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg' _))
    _ = 1 := by norm_num
  simp only [iSup_le_iff, and_imp]
  intros i' _ _ _ _
  calc
  volume (E₂ j i') / volume (𝓘 i' : Set X) ≤ volume (𝓘 i' : Set X) / volume (𝓘 i' : Set X) := by
    gcongr
    apply E₂_subset
  _ ≤ 1 := ENNReal.div_self_le_one

/-! ### Stack sizes -/

variable {C C' : Set (𝔓 X)} {x x' : X}
open scoped Classical

/-- The number of tiles `p` in `s` whose underlying cube `𝓘 p` contains `x`. -/
def stackSize (C : Set (𝔓 X)) (x : X) : ℕ :=
  ∑ p ∈ { p | p ∈ C }, (𝓘 p : Set X).indicator 1 x

lemma stackSize_setOf_add_stackSize_setOf_not {P : 𝔓 X → Prop} :
    stackSize {p ∈ C | P p} x + stackSize {p ∈ C | ¬ P p} x = stackSize C x := by
  classical
  simp_rw [stackSize]
  conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not _ P]
  simp_rw [Finset.filter_filter]
  congr

lemma stackSize_congr (h : ∀ p ∈ C, x ∈ (𝓘 p : Set X) ↔ x' ∈ (𝓘 p : Set X)) :
    stackSize C x = stackSize C x' := by
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp_rw [indicator, h p hp, Pi.one_apply]

lemma stackSize_mono (h : C ⊆ C') : stackSize C x ≤ stackSize C' x := by
  apply Finset.sum_le_sum_of_subset (fun x ↦ ?_)
  simp [iff_true_intro (@h x)]

-- Simplify the cast of `stackSize C x` from `ℕ` to `ℝ`
lemma stackSize_real (C : Set (𝔓 X)) (x : X) : (stackSize C x : ℝ) =
    ∑ p ∈ { p | p ∈ C }, (𝓘 p : Set X).indicator (1 : X → ℝ) x := by
  rw [stackSize, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  by_cases hx : x ∈ (𝓘 u : Set X) <;> simp [hx]

lemma stackSize_measurable : Measurable fun x ↦ (stackSize C x : ℝ≥0∞) := by
  simp_rw [stackSize, Nat.cast_sum, indicator, Nat.cast_ite]
  refine Finset.measurable_sum _ fun _ _ ↦ Measurable.ite coeGrid_measurable ?_ ?_ <;> simp
