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
class PreTileStructure [FunctionDistances 𝕜 X] (Q : outParam (SimpleFunc X (Θ X)))
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
def 𝔓 := PreTileStructure.𝔓 𝕜 X A
instance : Fintype (𝔓 X) := PreTileStructure.fintype_𝔓
def 𝓘 : 𝔓 X → Grid X := PreTileStructure.𝓘
lemma surjective_𝓘 : Surjective (𝓘 : 𝔓 X → Grid X) := PreTileStructure.surjective_𝓘
def 𝔠 (p : 𝔓 X) : X := c (𝓘 p)
def 𝔰 (p : 𝔓 X) : ℤ := s (𝓘 p)


local notation "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- A tile structure. -/
class TileStructure [FunctionDistances ℝ X] (Q : outParam (SimpleFunc X (Θ X)))
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X)
    extends PreTileStructure Q D κ S o where
  Ω : 𝔓 → Set (Θ X)
  biUnion_Ω {i} : range Q ⊆ ⋃ p ∈ 𝓘 ⁻¹' {i}, Ω p -- 2.0.13, union contains `Q`
  disjoint_Ω {p p'} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') : -- 2.0.13, union is disjoint
    Disjoint (Ω p) (Ω p')
  relative_fundamental_dyadic {p p'} (h : 𝓘 p ≤ 𝓘 p') : -- 2.0.14
    Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  cdist_subset {p} : ball_(D, p) (𝒬 p) 5⁻¹ ⊆ Ω p -- 2.0.15, first inclusion
  subset_cdist {p} : Ω p ⊆ ball_(D, p) (𝒬 p) 1 -- 2.0.15, second inclusion

export TileStructure (Ω biUnion_Ω disjoint_Ω relative_fundamental_dyadic cdist_subset subset_cdist)

end Generic


open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]
variable [TileStructure Q D κ S o] {p p' : 𝔓 X} {f g : Θ X}

-- maybe we should delete the following three notations, and use `dist_{𝓘 p}` instead?
notation "dist_(" 𝔭 ")" => @dist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "nndist_(" 𝔭 ")" => @nndist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "ball_(" 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _


@[simp] lemma dist_𝓘 (p : 𝔓 X) : dist_{𝓘 p} f g = dist_(p) f g := rfl
@[simp] lemma nndist_𝓘 (p : 𝔓 X) : nndist_{𝓘 p} f g = nndist_(p) f g := rfl
@[simp] lemma ball_𝓘 (p : 𝔓 X) {r : ℝ} : ball_{𝓘 p} f r = ball_(p) f r := rfl

/-- The set `E` defined in Proposition 2.0.2. -/
def E (p : 𝔓 X) : Set X :=
  { x ∈ 𝓘 p | Q x ∈ Ω p ∧ 𝔰 p ∈ Icc (σ₁ x) (σ₂ x) }

section T

/-- The operator `T_𝔭` defined in Proposition 2.0.2, considered on the set `F`.
It is the map `T ∘ (1_F * ·) : f ↦ T (1_F * f)`, also denoted `T1_F`
The operator `T` in Proposition 2.0.2 is therefore `applied to `(F := Set.univ)`. -/
def T (p : 𝔓 X) (f : X → ℂ) : X → ℂ :=
  indicator (E p)
    fun x ↦ ∫ y, exp (Q x x - Q x y) * K x y * ψ (D ^ (- 𝔰 p) * dist x y) * F.indicator f y

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
  simp [TileLike.le_def, subset_cdist]

lemma 𝒬_mem_Ω : 𝒬 p ∈ Ω p := cdist_subset <| mem_ball_self <| by norm_num

lemma toTileLike_injective : Injective (fun p : 𝔓 X ↦ toTileLike p) := by
  intros p p' h
  simp_rw [toTileLike, TileLike, Prod.ext_iff] at h
  by_contra h2
  have : Disjoint (Ω p) (Ω p') := disjoint_Ω h2 h.1
  have : Ω p = ∅ := by simpa [← h.2]
  exact not_mem_empty _ (by rw [← this]; exact 𝒬_mem_Ω)

instance : PartialOrder (𝔓 X) := PartialOrder.lift toTileLike toTileLike_injective

/-- Lemma 5.3.1 -/
lemma smul_mono {m m' n n' : ℝ} (hp : smul n p ≤ smul m p') (hm : m' ≤ m) (hn : n ≤ n') :
    smul n' p ≤ smul m' p' :=
  smul_mono_left hn |>.trans hp |>.trans <| smul_mono_left hm

/-- Lemma 5.3.2 -/
lemma smul_C2_1_2 (m : ℝ) {n : ℝ} (hp : 𝓘 p ≠ 𝓘 p') (hl : smul n p ≤ smul 1 p') :
    smul (n + C2_1_2 a * m) p ≤ smul m p' := by
  replace hp : 𝓘 p < 𝓘 p' := lt_of_le_of_ne hl.1 hp
  have : ball_(p') (𝒬 p') m ⊆ ball_(p) (𝒬 p) (n + C2_1_2 a * m) := fun x hx ↦ by
    rw [@mem_ball] at hx ⊢
    calc
      _ ≤ dist_(p) x (𝒬 p') + dist_(p) (𝒬 p') (𝒬 p) := dist_triangle ..
      _ ≤ C2_1_2 a * dist_(p') x (𝒬 p') + dist_(p) (𝒬 p') (𝒬 p) := by
        gcongr; exact Grid.dist_strictMono hp
      _ < C2_1_2 a * m + dist_(p) (𝒬 p') (𝒬 p) := by gcongr; rw [C2_1_2]; positivity
      _ < _ := by
        rw [add_comm]; gcongr
        exact mem_ball.mp <| mem_of_mem_of_subset (by convert mem_ball_self zero_lt_one) hl.2
  exact ⟨hl.1, this⟩

/-- The constraint on `λ` in the first part of Lemma 5.3.3. -/
def C5_3_3 (a : ℕ) : ℝ := (1 - C2_1_2 a)⁻¹

lemma C5_3_3_le : C5_3_3 a ≤ 11 / 10 := by
  have := ‹ProofData a q K σ₁ σ₂ F G› -- remove once the proof is finished
  sorry

/-- Lemma 5.3.3, Equation (5.3.3) -/
lemma wiggle_order_11_10 {n : ℝ} (hp : smul 1 p ≤ smul 1 p') (hn : C5_3_3 a ≤ n) :
    smul n p ≤ smul n p' := by sorry

/-- Lemma 5.3.3, Equation (5.3.4) -/
lemma wiggle_order_100 (hp : smul 10 p ≤ smul 1 p') (hn : 𝓘 p ≠ 𝓘 p') :
    smul 100 p ≤ smul 100 p' :=
  calc
    _ ≤ smul (10 + C2_1_2 a * 100) p :=
      smul_mono_left (by linarith [C2_1_2_le_inv_512 (X := X)])
    _ ≤ _ := smul_C2_1_2 100 hn hp

/-- Lemma 5.3.3, Equation (5.3.5) -/
lemma wiggle_order_500 (hp : smul 2 p ≤ smul 1 p') (hn : 𝓘 p ≠ 𝓘 p') :
    smul 4 p ≤ smul 500 p' :=
  calc
    _ ≤ smul (2 + C2_1_2 a * 500) p :=
      smul_mono_left (by linarith [C2_1_2_le_inv_512 (X := X)])
    _ ≤ _ := smul_C2_1_2 500 hn hp

def C5_3_2 (a : ℕ) : ℝ := 2 ^ (-95 * (a : ℝ))

def TileLike.toTile (t : TileLike X) : Set (X × Θ X) :=
  (t.fst : Set X) ×ˢ t.snd

/-- From a TileLike, we can construct a set. This is used in the definitions `E₁` and `E₂`. -/
def TileLike.toSet (t : TileLike X) : Set X :=
  t.1 ∩ G ∩ Q ⁻¹' t.2

def E₁ (p : 𝔓 X) : Set X :=
  (toTileLike p).toSet

def E₂ (l : ℝ) (p : 𝔓 X) : Set X :=
  (smul l p).toSet

/-! `𝔓(𝔓')` in the blueprint is `lowerClosure 𝔓'` in Lean. -/

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₁ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (l ≥ (2 : ℝ≥0)), l ^ (-a : ℝ) *
  ⨆ (p' ∈ lowerClosure 𝔓') (_h2 : smul l p ≤ smul l p'),
  volume (E₂ l p) / volume (𝓘 p : Set X)

/-- This density is defined to live in `ℝ≥0∞`. Use `ENNReal.toReal` to get a real number. -/
def dens₂ (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (r ≥ 4 * (D ^ 𝔰 p : ℝ)),
  volume (F ∩ ball (𝔠 p) r) / volume (ball (𝔠 p) r)

-- a small characterization that might be useful
lemma isAntichain_iff_disjoint (𝔄 : Set (𝔓 X)) :
    IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄) ↔
    ∀ p p', p ∈ 𝔄 → p' ∈ 𝔄 → p ≠ p' →
    Disjoint (toTileLike (X := X) p).toTile (toTileLike p').toTile := sorry
