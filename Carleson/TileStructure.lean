import Carleson.GridStructure

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
variable [FunctionDistances 𝕜 X] {Q : SimpleFunc X (Θ X)} [PreTileStructure Q D κ S o]

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
  relative_fundamental_dyadic {p p'} (h :
    -- why is the next line needed?!!
    letI : PartialOrder (Grid) := @instPartialOrderGrid X A _ _ D κ S o _
    𝓘 p ≤ 𝓘 p') : -- 2.0.14
    Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  cball_subset {p : _root_.𝔓 X} : ball_(D, p) (𝒬 p) 5⁻¹ ⊆ Ω p -- 2.0.15, first inclusion
  subset_cball {p : _root_.𝔓 X} : Ω p ⊆ ball_(D, p) (𝒬 p) 1 -- 2.0.15, second inclusion

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
notation "edist_(" 𝔭 ")" => @edist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "ball_(" 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

@[simp] lemma dist_𝓘 (p : 𝔓 X) : dist_{𝓘 p} f g = dist_(p) f g := rfl
@[simp] lemma nndist_𝓘 (p : 𝔓 X) : nndist_{𝓘 p} f g = nndist_(p) f g := rfl
@[simp] lemma ball_𝓘 (p : 𝔓 X) {r : ℝ} : ball_{𝓘 p} f r = ball_(p) f r := rfl

@[simp] lemma cball_subset {p : 𝔓 X} : ball_(p) (𝒬 p) 5⁻¹ ⊆ Ω p := TileStructure.cball_subset
@[simp] lemma subset_cball {p : 𝔓 X} : Ω p ⊆ ball_(p) (𝒬 p) 1 := TileStructure.subset_cball

set_option backward.isDefEq.respectTransparency false in
lemma ball_eq_of_grid_eq {p q : 𝔓 X} {ϑ : Θ X} {r : ℝ} (h : 𝓘 p = 𝓘 q) :
    ball_(p) ϑ r = ball_(q) ϑ r := by rw [← ball_𝓘, h]

lemma cball_disjoint {p p' : 𝔓 X} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') :
    Disjoint (ball_(p) (𝒬 p) 5⁻¹) (ball_(p') (𝒬 p') 5⁻¹) :=
  disjoint_of_subset cball_subset cball_subset (disjoint_Ω h hp)

/-- A bound used in both nontrivial cases of Lemma 7.5.5. -/
lemma volume_xDsp_bound {x : X} (hx : x ∈ 𝓘 p) :
    volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a) ≤ volume (ball x (D ^ 𝔰 p)) := by
  apply ENNReal.div_le_of_le_mul'
  have h : dist x (𝔠 p) + 4 * D ^ 𝔰 p ≤ 8 * D ^ 𝔰 p := by
    calc
      _ ≤ 4 * (D : ℝ) ^ 𝔰 p + 4 * ↑D ^ 𝔰 p := by
        gcongr; exact (mem_ball.mp (Grid_subset_ball hx)).le
      _ = _ := by rw [← add_mul]; norm_num
  convert measure_ball_le_of_dist_le' (μ := volume) (by norm_num) h
  unfold As defaultA; norm_cast
  rw [← pow_mul', show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.clog_pow]; norm_num

/-- A bound used in Lemma 7.6.2. -/
lemma volume_xDsp_bound_4 {x : X} (hx : x ∈ 𝓘 p) :
    volume (ball (𝔠 p) (8 * D ^ 𝔰 p)) / 2 ^ (4 * a) ≤ volume (ball x (D ^ 𝔰 p)) := by
  apply ENNReal.div_le_of_le_mul'
  have h : dist x (𝔠 p) + 8 * D ^ 𝔰 p ≤ 16 * D ^ 𝔰 p := by
    calc
      _ ≤ 4 * (D : ℝ) ^ 𝔰 p + 8 * ↑D ^ 𝔰 p := by
        gcongr; exact (mem_ball.mp (Grid_subset_ball hx)).le
      _ ≤ _ := by rw [← add_mul]; gcongr; norm_num
  convert measure_ball_le_of_dist_le' (μ := volume) (by norm_num) h
  unfold As defaultA; norm_cast
  rw [← pow_mul', show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.clog_pow]; norm_num

/-- The set `E` defined in Proposition 2.0.2. -/
def E (p : 𝔓 X) : Set X :=
  { x ∈ 𝓘 p | Q x ∈ Ω p ∧ 𝔰 p ∈ Icc (σ₁ x) (σ₂ x) }

lemma E_subset_𝓘 {p : 𝔓 X} : E p ⊆ 𝓘 p := fun _ ↦ mem_of_mem_inter_left

lemma Q_mem_Ω {p : 𝔓 X} {x : X} (hp : x ∈ E p) : Q x ∈ Ω p := hp.right.left

lemma disjoint_E {p p' : 𝔓 X} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') : Disjoint (E p) (E p') := by
  have := disjoint_Ω h hp; contrapose! this
  rw [not_disjoint_iff] at this ⊢; obtain ⟨x, mx, mx'⟩ := this
  use Q x, Q_mem_Ω mx, Q_mem_Ω mx'

lemma measurableSet_E {p : 𝔓 X} : MeasurableSet (E p) := by
  refine (Measurable.and ?_ (Measurable.and ?_ ?_)).setOf
  · rw [← measurableSet_setOf]; exact coeGrid_measurable
  · simp_rw [← mem_preimage, ← measurableSet_setOf]; exact SimpleFunc.measurableSet_preimage ..
  · apply (measurable_set_mem _).comp
    apply Measurable.comp (f := fun x ↦ (σ₁ x, σ₂ x)) (g := fun p ↦ Icc p.1 p.2)
    · exact measurable_from_prod_countable_left fun _ _ _ ↦ trivial
    · exact measurable_σ₁.prodMk measurable_σ₂

lemma volume_E_lt_top : volume (E p) < ⊤ := trans (measure_mono E_subset_𝓘) volume_coeGrid_lt_top

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

set_option backward.isDefEq.respectTransparency false in
lemma smul_mono_left {l l' : ℝ} {p : 𝔓 X} (h : l ≤ l') : smul l' p ≤ smul l p := by
  simp [TileLike.le_def, h, ball_subset_ball]

set_option backward.isDefEq.respectTransparency false in
lemma smul_le_toTileLike : smul 1 p ≤ toTileLike p := by
  simp [TileLike.le_def, subset_cball (p := p)]

set_option backward.isDefEq.respectTransparency false in
lemma toTileLike_le_smul : toTileLike p ≤ smul 5⁻¹ p := by
  simp [TileLike.le_def, cball_subset (p := p)]

lemma 𝒬_mem_Ω : 𝒬 p ∈ Ω p := cball_subset <| mem_ball_self <| by norm_num

lemma 𝒬_inj {p' : 𝔓 X} (h : 𝒬 p = 𝒬 p') (h𝓘 : 𝓘 p = 𝓘 p') : p = p' := by
  contrapose! h
  exact fun h𝒬 ↦ (not_disjoint_iff.2 ⟨𝒬 p, 𝒬_mem_Ω, h𝒬 ▸ 𝒬_mem_Ω⟩) (disjoint_Ω h h𝓘)

set_option backward.isDefEq.respectTransparency false in
lemma toTileLike_injective : Injective (fun p : 𝔓 X ↦ toTileLike p) := by
  intros p p' h
  simp_rw [toTileLike, TileLike, Prod.ext_iff] at h
  by_contra h2
  have : Disjoint (Ω p) (Ω p') := disjoint_Ω h2 h.1
  have : Ω p = ∅ := by simpa [← h.2]
  exact notMem_empty _ (by rw [← this]; exact 𝒬_mem_Ω)

instance : PartialOrder (𝔓 X) := PartialOrder.lift toTileLike toTileLike_injective

lemma 𝔓.le_def {p q : 𝔓 X} : p ≤ q ↔ toTileLike p ≤ toTileLike q := by rfl
lemma 𝔓.le_def' {p q : 𝔓 X} : p ≤ q ↔ 𝓘 p ≤ 𝓘 q ∧ Ω q ⊆ Ω p := by rfl

/-- Deduce an inclusion of tiles from an inclusion of their cubes and
non-disjointness of their `Ω`s. -/
lemma tile_le_of_cube_le_and_not_disjoint {p q : 𝔓 X} (hi : 𝓘 p ≤ 𝓘 q)
    {x : Θ X} (mxp : x ∈ Ω p) (mxq : x ∈ Ω q) : p ≤ q :=
  ⟨hi, (relative_fundamental_dyadic hi).resolve_left (not_disjoint_iff.mpr ⟨x, mxp, mxq⟩)⟩

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

set_option backward.isDefEq.respectTransparency false in
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
      Grid.dist_strictMono <| 𝓘_strictMono <| s.eraseLast_last_rel_last (by lia)
    apply ih.trans; rw [pow_succ, mul_assoc]; gcongr; unfold C2_1_2; positivity

end

/-- The constraint on `λ` in the first part of Lemma 5.3.3. -/
def C5_3_3 (a : ℕ) : ℝ := (1 - C2_1_2 a)⁻¹

include q K σ₁ σ₂ F G in
lemma C5_3_3_le : C5_3_3 a ≤ 11 / 10 := by
  rw [C5_3_3, inv_le_comm₀ (sub_pos.mpr <| C2_1_2_lt_one X) (by norm_num), le_sub_comm]
  exact C2_1_2_le_inv_256 X |>.trans <| by norm_num

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
        linarith [C2_1_2_le_inv_256 (X := X)]
      _ ≤ smul n p' := smul_C2_1_2 (k := 5⁻¹) n (by norm_num) h
        (smul_le_toTileLike.trans <| 𝔓.le_def.mp hp |>.trans toTileLike_le_smul)

/-- Lemma 5.3.3, Equation (5.3.4) -/
lemma wiggle_order_100 (hp : smul 10 p ≤ smul 1 p') (hn : 𝓘 p ≠ 𝓘 p') :
    smul 100 p ≤ smul 100 p' :=
  calc
    _ ≤ smul (10 + C2_1_2 a * 100) p :=
      smul_mono_left (by linarith [C2_1_2_le_inv_256 (X := X)])
    _ ≤ _ := smul_C2_1_2 100 zero_lt_one hn hp

/-- Lemma 5.3.3, Equation (5.3.5) -/
lemma wiggle_order_500 (hp : smul 2 p ≤ smul 1 p') (hn : 𝓘 p ≠ 𝓘 p') :
    smul 4 p ≤ smul 500 p' :=
  calc
    _ ≤ smul (2 + C2_1_2 a * 500) p :=
      smul_mono_left (by linarith [C2_1_2_le_inv_256 (X := X)])
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

lemma E₂_mono {p : 𝔓 X} : Monotone fun l ↦ E₂ l p := fun l l' hl ↦ by
  simp_rw [E₂, TileLike.toSet, inter_assoc]
  refine inter_subset_inter_right _ (inter_subset_inter_right _ (preimage_mono ?_))
  rw [smul_snd]; exact ball_subset_ball hl

/-- `𝔓(𝔓')` in the blueprint.
The set of all tiles whose cubes are less than the cube of some tile in the given set. -/
def lowerCubes (𝔓' : Set (𝔓 X)) : Set (𝔓 X) :=
  {p | ∃ p' ∈ 𝔓', 𝓘 p ≤ 𝓘 p'}

lemma mem_lowerCubes {𝔓' : Set (𝔓 X)} : p ∈ lowerCubes 𝔓' ↔ ∃ p' ∈ 𝔓', 𝓘 p ≤ 𝓘 p' := by rfl

lemma lowerCubes_mono : Monotone (lowerCubes (X := X)) := fun 𝔓₁ 𝔓₂ hs p mp ↦ by
  rw [lowerCubes, mem_setOf] at mp ⊢; obtain ⟨p', mp', hp'⟩ := mp; use p', hs mp'

lemma subset_lowerCubes {𝔓' : Set (𝔓 X)} : 𝔓' ⊆ lowerCubes 𝔓' := fun p mp ↦ by
  rw [lowerCubes, mem_setOf]; use p

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₁ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p' ∈ 𝔓') (l ≥ (2 : ℝ≥0)), l ^ (-a : ℝ) *
    ⨆ (p ∈ lowerCubes 𝔓') (_h2 : smul l p' ≤ smul l p),
      volume (E₂ l p) / volume (𝓘 p : Set X)

lemma dens₁_mono {𝔓₁ 𝔓₂ : Set (𝔓 X)} (h : 𝔓₁ ⊆ 𝔓₂) :
    dens₁ 𝔓₁ ≤ dens₁ 𝔓₂ := by
  simp only [dens₁, iSup_le_iff]
  intro p hp r hr
  apply le_iSup₂_of_le p (h hp) <| ENNReal.mul_le_of_le_div' ?_
  simp only [iSup_le_iff]
  intro q hq hqr
  rw [ENNReal.le_div_iff_mul_le (by left; simp)]
  · refine le_iSup₂_of_le r hr ?_
    rw [mul_comm]
    gcongr
    exact le_iSup₂_of_le q (lowerCubes_mono h hq) (le_iSup_iff.mpr fun b a ↦ a hqr)
  · left
    have hr0 : r ≠ 0 := by positivity
    simp [hr0]

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₂ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (r ≥ 4 * (D ^ 𝔰 p : ℝ)),
    volume (F ∩ ball (𝔠 p) r) / volume (ball (𝔠 p) r)

lemma le_dens₂ (𝔓' : Set (𝔓 X)) {p : 𝔓 X} (hp : p ∈ 𝔓') {r : ℝ} (hr : r ≥ 4 * (D ^ 𝔰 p : ℝ)) :
    volume (F ∩ ball (𝔠 p) r) / volume (ball (𝔠 p) r) ≤ dens₂ 𝔓' :=
  le_trans (le_iSup₂ (α := ℝ≥0∞) r hr) (le_iSup₂ p hp)

set_option backward.isDefEq.respectTransparency false in
lemma dens₂_eq_biSup_dens₂ (𝔓' : Set (𝔓 X)) :
    dens₂ (𝔓') = ⨆ (p ∈ 𝔓'), dens₂ ({p}) := by
  simp [dens₂]

/- A rough estimate. It's also less than 2 ^ (-a) -/
lemma dens₁_le_one {𝔓' : Set (𝔓 X)} : dens₁ 𝔓' ≤ 1 := by
  conv_rhs => rw [← mul_one 1]
  simp only [dens₁, mem_lowerCubes, iSup_exists, iSup_le_iff]
  intros i _ j hj
  gcongr
  · calc
    (j : ℝ≥0∞) ^ (-(a : ℝ)) ≤ 2 ^ (-(a : ℝ)) :=
      ENNReal.rpow_le_rpow_of_nonpos (by simp_rw [neg_nonpos, Nat.cast_nonneg'])
        (by exact_mod_cast hj)
    _ ≤ 2 ^ (0 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg' _))
    _ = 1 := by norm_num
  simp only [iSup_le_iff, and_imp]
  intros i' _ _ _ _
  calc volume (E₂ j i') / volume (𝓘 i' : Set X)
  _ ≤ volume (𝓘 i' : Set X) / volume (𝓘 i' : Set X) := by gcongr; apply E₂_subset
  _ ≤ 1 := ENNReal.div_self_le_one

lemma volume_E₂_le_dens₁_mul_volume {𝔓' : Set (𝔓 X)} (mp : p ∈ lowerCubes 𝔓') (mp' : p' ∈ 𝔓')
    {l : ℝ≥0} (hl : 2 ≤ l) (sp : smul l p' ≤ smul l p) :
    volume (E₂ l p) ≤ l ^ a * dens₁ 𝔓' * volume (𝓘 p : Set X) := by
  have vpos : volume (𝓘 p : Set X) ≠ 0 := (volume_coeGrid_pos (defaultD_pos a)).ne'
  rw [← ENNReal.div_le_iff_le_mul (.inl vpos) (.inl volume_coeGrid_lt_top.ne),
    ← ENNReal.rpow_natCast, ← neg_neg (a : ℝ), ENNReal.rpow_neg, ← ENNReal.div_eq_inv_mul]
  have plt : (l : ℝ≥0∞) ^ (-(a : ℝ)) ≠ ⊤ := by finiteness
  rw [ENNReal.le_div_iff_mul_le (by simp) (.inl plt), mul_comm, dens₁]
  refine le_iSup₂_of_le p' mp' (le_iSup₂_of_le l hl ?_); gcongr
  exact le_iSup₂_of_le p mp (le_iSup_of_le sp le_rfl)

/-! ### Stack sizes -/

variable {C C' : Set (𝔓 X)} {x x' : X}

open scoped Classical in
/-- The number of tiles `p` in `s` whose underlying cube `𝓘 p` contains `x`. -/
def stackSize (C : Set (𝔓 X)) (x : X) : ℕ :=
  ∑ p with p ∈ C, (𝓘 p : Set X).indicator 1 x

lemma stackSize_setOf_add_stackSize_setOf_not {P : 𝔓 X → Prop} :
    stackSize {p ∈ C | P p} x + stackSize {p ∈ C | ¬P p} x = stackSize C x := by
  classical
  simp_rw [stackSize]
  conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not _ P]
  simp_rw [Finset.filter_filter]
  congr

lemma stackSize_inter_add_stackSize_sdiff :
    stackSize (C ∩ C') x + stackSize (C \ C') x = stackSize C x :=
  stackSize_setOf_add_stackSize_setOf_not

lemma stackSize_sdiff_eq (x : X) :
    stackSize (C \ C') x = stackSize C x - stackSize (C ∩ C') x := by
  exact Nat.eq_sub_of_add_eq' stackSize_inter_add_stackSize_sdiff

lemma stackSize_congr (h : ∀ p ∈ C, x ∈ (𝓘 p : Set X) ↔ x' ∈ (𝓘 p : Set X)) :
    stackSize C x = stackSize C x' := by
  classical
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.mem_filter_univ] at hp
  simp_rw [indicator, h p hp, Pi.one_apply]

set_option backward.isDefEq.respectTransparency false in
lemma stackSize_mono (h : C ⊆ C') : stackSize C x ≤ stackSize C' x := by
  apply Finset.sum_le_sum_of_subset (fun x ↦ ?_)
  simp [iff_true_intro (@h x)]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
-- Simplify the cast of `stackSize C x` from `ℕ` to `ℝ`
lemma stackSize_real (C : Set (𝔓 X)) (x : X) :
    (stackSize C x : ℝ) = ∑ p with p ∈ C, (𝓘 p : Set X).indicator (1 : X → ℝ) x := by
  rw [stackSize, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  by_cases hx : x ∈ (𝓘 u : Set X) <;> simp [hx]

lemma stackSize_measurable : Measurable fun x ↦ (stackSize C x : ℝ≥0∞) := by
  simp_rw [stackSize, Nat.cast_sum, indicator, Nat.cast_ite]
  refine Finset.measurable_sum _ fun _ _ ↦ Measurable.ite coeGrid_measurable ?_ ?_ <;> simp

set_option backward.isDefEq.respectTransparency false in
lemma stackSize_le_one_of_pairwiseDisjoint {C : Set (𝔓 X)} {x : X}
    (h : C.PairwiseDisjoint (fun p ↦ (𝓘 p : Set X))) : stackSize C x ≤ 1 := by
  by_cases hx : ∃ p ∈ C, x ∈ (𝓘 p : Set X)
  · rcases hx with ⟨p, pC, hp⟩
    rw [stackSize, Finset.sum_eq_single_of_mem p]; rotate_left
    · simp [pC]
    · intro b hb hbp
      simp only [indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false]
      simp only [Finset.mem_filter_univ] at hb
      exact disjoint_left.1 (h pC hb hbp.symm) hp
    simp [hp]
  · have : stackSize C x = 0 := by
      apply Finset.sum_eq_zero (fun p hp ↦ ?_)
      simp only [Finset.mem_filter_univ, not_exists, not_and,
        indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false] at hp hx ⊢
      exact hx _ hp
    linarith

lemma eq_empty_of_forall_stackSize_zero (s : Set (𝔓 X)) :
    (∀ x, stackSize s x = 0) → s = ∅ := by
  intro h
  dsimp [stackSize] at h
  simp only [Finset.sum_eq_zero_iff, Finset.mem_filter_univ,
    indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false] at h
  ext 𝔲
  simp only [mem_empty_iff_false, iff_false]
  obtain ⟨x,hx⟩ := (𝓘 𝔲).nonempty
  exact fun h𝔲 => h x 𝔲 h𝔲 hx

/-! ### Decomposing a set of tiles into disjoint subfamilies -/

set_option backward.isDefEq.respectTransparency false in
/-- Given any family of tiles, one can extract a maximal disjoint subfamily, covering everything. -/
lemma exists_maximal_disjoint_covering_subfamily (A : Set (𝔓 X)) :
    ∃ (B : Set (𝔓 X)), B.PairwiseDisjoint (fun p ↦ (𝓘 p : Set X)) ∧
      B ⊆ A ∧ (∀ a ∈ A, ∃ b ∈ B, (𝓘 a : Set X) ⊆ 𝓘 b) := by
  -- consider the pairwise disjoint families in `A` such that any element of `A` is disjoint from
  -- every member of the family, or contained in one of them.
  let M : Set (Set (𝔓 X)) := {B | B.PairwiseDisjoint (fun p ↦ (𝓘 p : Set X)) ∧ B ⊆ A ∧ ∀ a ∈ A,
    (∃ b ∈ B, (𝓘 a : Set X) ⊆ 𝓘 b) ∨ (∀ b ∈ B, Disjoint (𝓘 a : Set X) (𝓘 b))}
  -- let `B` be a maximal such family. It satisfies the properties of the lemma.
  obtain ⟨B, BM, hB⟩ : ∃ B, MaximalFor (· ∈ M) id B :=
    M.toFinite.exists_maximalFor id _ ⟨∅, by simp [M]⟩
  refine ⟨B, BM.1, BM.2.1, fun a ha ↦ ?_⟩
  rcases BM.2.2 a ha with h'a | h'a
  · exact h'a
  exfalso
  let F := {a' ∈ A | (𝓘 a : Set X) ⊆ 𝓘 a' ∧ ∀ b ∈ B, Disjoint (𝓘 a' : Set X) (𝓘 b)}
  obtain ⟨a', a'F, ha'⟩ : ∃ a' ∈ F, ∀ p ∈ F, (𝓘 a' : Set X) ⊆ 𝓘 p → (𝓘 a' : Set X) = 𝓘 p := by
    obtain ⟨a₀, a₀F, ha₀⟩ :=
      F.toFinite.exists_maximalFor (fun p ↦ (𝓘 p : Set X)) _ ⟨a, ⟨ha, subset_rfl, h'a⟩⟩
    exact ⟨a₀, a₀F, fun p mp lp ↦ subset_antisymm lp (ha₀ mp lp)⟩
  have : insert a' B ∈ M := by
    refine ⟨?_, ?_, fun p hp ↦ ?_⟩
    · apply PairwiseDisjoint.insert BM.1 (fun b hb h'b ↦ a'F.2.2 b hb)
    · apply insert_subset a'F.1 BM.2.1
    rcases BM.2.2 p hp with ⟨b, hb⟩ | h'p
    · exact Or.inl ⟨b, mem_insert_of_mem _ hb.1, hb.2⟩
    by_cases Hp : Disjoint (𝓘 p : Set X) (𝓘 a')
    · right
      simpa [Hp] using h'p
    refine Or.inl ⟨a', mem_insert a' B, ?_⟩
    rcases le_or_ge_or_disjoint (i := 𝓘 p) (j := 𝓘 a') with hij | hij |hij
    · exact (Grid.le_def.1 hij).1
    · have : p ∈ F := ⟨hp, a'F.2.1.trans (Grid.le_def.1 hij).1, h'p⟩
      rw [ha' p this (Grid.le_def.1 hij).1]
    · exact (Hp hij).elim
  have : B = insert a' B := le_antisymm (subset_insert a' B) (hB this (subset_insert a' B))
  have : a' ∈ B := by rw [this]; exact mem_insert a' B
  have : Disjoint (𝓘 a' : Set X) (𝓘 a' : Set X) := a'F.2.2 _ this
  exact disjoint_left.1 this Grid.c_mem_Grid Grid.c_mem_Grid

/-- A disjoint subfamily of `A` covering everything. -/
def maximalSubfamily (A : Set (𝔓 X)) : Set (𝔓 X) :=
  (exists_maximal_disjoint_covering_subfamily A).choose

/-- Iterating `maximalSubfamily` to obtain disjoint subfamilies of `A`. -/
def iteratedMaximalSubfamily (A : Set (𝔓 X)) (n : ℕ) : Set (𝔓 X) :=
  maximalSubfamily (A \ (⋃ (i : {i | i < n}), have : i < n := i.2; iteratedMaximalSubfamily A i))

lemma pairwiseDisjoint_iteratedMaximalSubfamily_image (A : Set (𝔓 X)) (n : ℕ) :
    (iteratedMaximalSubfamily A n).PairwiseDisjoint (fun p ↦ (𝓘 p : Set X)) := by
  rw [iteratedMaximalSubfamily]
  exact (exists_maximal_disjoint_covering_subfamily (X := X) _).choose_spec.1

lemma iteratedMaximalSubfamily_subset (A : Set (𝔓 X)) (n : ℕ) :
    iteratedMaximalSubfamily A n ⊆ A := by
  rw [iteratedMaximalSubfamily]
  exact (exists_maximal_disjoint_covering_subfamily (X := X) _).choose_spec.2.1.trans diff_subset

set_option backward.isDefEq.respectTransparency false in
lemma pairwiseDisjoint_iteratedMaximalSubfamily (A : Set (𝔓 X)) :
    univ.PairwiseDisjoint (iteratedMaximalSubfamily A) := by
  intro m hm n hn hmn
  wlog h'mn : m < n generalizing m n with H
  · exact (H (mem_univ n) (mem_univ m) hmn.symm (by lia)).symm
  have : iteratedMaximalSubfamily A n
      ⊆ A \ ⋃ (i : {i | i < n}), iteratedMaximalSubfamily A i := by
    conv_lhs => rw [iteratedMaximalSubfamily]
    apply (exists_maximal_disjoint_covering_subfamily _).choose_spec.2.1
  apply subset_compl_iff_disjoint_left.1
  rw [compl_eq_univ_diff]
  apply this.trans
  apply diff_subset_diff (subset_univ _)
  apply subset_iUnion_of_subset ⟨m, h'mn⟩
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Any set of tiles can be written as the union of disjoint subfamilies, their number being
controlled by the maximal stack size. -/
lemma eq_biUnion_iteratedMaximalSubfamily (A : Set (𝔓 X)) {N : ℕ} (hN : ∀ x, stackSize A x ≤ N) :
    A = ⋃ n < N, iteratedMaximalSubfamily A n := by
  apply Subset.antisymm; swap
  · simp [iUnion_subset_iff, iteratedMaximalSubfamily_subset]
  -- we show that after `N` steps the maximal subfamilies cover everything. Otherwise, say some
  -- `p` is left. Then `𝓘 p` is contained in an element of each of the previous subfamilies.
  -- This gives `N+1` different elements containing any element of `𝓘 p`, a contradiction with
  -- the maximal stack size.
  intro p hp
  contrapose! hN
  simp only [mem_iUnion, exists_prop, not_exists, not_and] at hN
  have E n (hn : n < N) : ∃ u ∈ iteratedMaximalSubfamily A n, (𝓘 p : Set X) ⊆ (𝓘 u : Set X) := by
    rw [iteratedMaximalSubfamily]
    apply (exists_maximal_disjoint_covering_subfamily _).choose_spec.2.2
    simp only [coe_setOf, mem_setOf_eq, mem_diff, hp,
      mem_iUnion, Subtype.exists, exists_prop, not_exists, not_and, true_and]
    intro i hi
    exact hN i (hi.trans hn)
  choose! u hu h'u using E
  obtain ⟨x, hxp⟩ : ∃ x, x ∈ (𝓘 p : Set X) := ⟨_, Grid.c_mem_Grid⟩
  use x
  have : stackSize {q ∈ A | q = p} x + stackSize {q ∈ A | q ≠ p} x = stackSize A x :=
    stackSize_setOf_add_stackSize_setOf_not
  have : 1 = stackSize {q ∈ A | q = p} x := by
    have : 1 = ∑ q ∈ {p}, (𝓘 q : Set X).indicator 1 x := by simp [hxp]
    rw [this]
    congr
    ext
    simp (config := {contextual := true}) [hp]
  classical
  have : ∑ p with p ∈ u '' (Iio N), (𝓘 p : Set X).indicator 1 x
      ≤ stackSize {q | q ∈ A ∧ q ≠ p} x := by
    apply Finset.sum_le_sum_of_subset
    rintro p hp
    simp only [Finset.mem_filter_univ, mem_image, mem_Iio] at hp
    rcases hp with ⟨n, hn, rfl⟩
    simp only [ne_eq, mem_setOf_eq, Finset.mem_filter,
      Finset.mem_univ, iteratedMaximalSubfamily_subset _ _ (hu n hn), true_and]
    rintro rfl
    exact hN n hn (hu n hn)
  have : ∑ p with p ∈ u '' (Iio N), (𝓘 p : Set X).indicator 1 x
      = ∑ p with p ∈ u '' (Iio N), 1 := by
    apply Finset.sum_congr rfl (fun p hp ↦ ?_)
    simp only [Finset.mem_filter_univ, mem_image, mem_Iio] at hp
    rcases hp with ⟨n, hn, rfl⟩
    have : x ∈ (𝓘 (u n) : Set X) := h'u n hn hxp
    simp [this]
  have : ∑ p with p ∈ u '' (Iio N), 1 = N := by
    have : Finset.filter (fun p ↦ p ∈ u '' Iio N) Finset.univ = Finset.image u (Finset.Iio N) := by
      ext p; simp
    simp only [Finset.sum_const, smul_eq_mul, mul_one, this]
    rw [Finset.card_image_of_injOn, Nat.card_Iio N]
    intro a ha b hb hab
    contrapose! hab
    simp only [Finset.coe_Iio, mem_Iio] at ha hb
    have := pairwiseDisjoint_iteratedMaximalSubfamily A (mem_univ a) (mem_univ b) hab
    exact disjoint_iff_forall_ne.1 this (hu a ha) (hu b hb)
  lia
