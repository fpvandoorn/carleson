import Carleson.ToMathlib.RealInterpolation.Minkowski

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set MeasureTheory
open scoped NNReal

variable {𝓐 : Type*} [AddMonoid 𝓐] {𝓑 : Type*} [AddMonoid 𝓑]

variable (𝓐) in
structure EAddSubmonoid where
  carrier : AddSubmonoid 𝓐
  protected enorm : ENorm 𝓐
  protected C : ℝ≥0∞
  protected enorm_zero : ‖(0 : 𝓐)‖ₑ = 0
  protected enorm_add_le_mul' : ∀ x y, x ∈ carrier → y ∈ carrier → ‖x + y‖ₑ ≤ C * (‖x‖ₑ + ‖y‖ₑ)


-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ : EAddSubmonoid 𝓐} {t s : ℝ≥0∞} {x y z : 𝓐} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ : EAddSubmonoid 𝓑} {C C₀ C₁ D D₀ D₁ E : ℝ≥0∞}

namespace EAddSubmonoid

instance : CoeTC (EAddSubmonoid 𝓐) (AddSubmonoid 𝓐) where coe := EAddSubmonoid.carrier
instance : CoeTC (EAddSubmonoid 𝓐) (Set 𝓐) where coe := fun A ↦ A.carrier

instance (priority := 100) instMembership : Membership 𝓐 (EAddSubmonoid 𝓐) :=
  ⟨fun p x => x ∈ (p : Set 𝓐)⟩

instance (priority := 100) : CoeSort (EAddSubmonoid 𝓐) (Type _) :=
  ⟨fun p => { x : 𝓐 // x ∈ p }⟩

attribute [simp] EAddSubmonoid.enorm_zero

notation "‖" e "‖ₑ[" A "]" => @enorm _ (EAddSubmonoid.enorm A) e

-- todo: make constant explicit
-- todo: make preorder
instance (priority := 100) : LE (EAddSubmonoid 𝓐) :=
  ⟨fun A₀ A₁ => (A₀ : Set 𝓐) ⊆ (A₁ : Set 𝓐) ∧ ∃ C : ℝ≥0, ∀ x ∈ A₀, ‖x‖ₑ[A₁] ≤ C * ‖x‖ₑ[A₀]⟩

-- def Compatible (A₀ A₁ : EAddSubmonoid 𝓐) : Prop :=
--   ∃ C : ℝ≥0, ∀ x, x ∈ A → x ∈ B → ‖x‖ₑ[B] ≤ C * ‖x‖ₑ[A]

lemma enorm_add_le_mul (hx : x ∈ A) (hy : y ∈ A) :
    ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := A.enorm_add_le_mul' x y hx hy

variable (A) in
@[simp] protected lemma zero_mem : (0 : 𝓐) ∈ A := A.carrier.zero_mem

instance : Min (EAddSubmonoid 𝓐) :=
  ⟨fun A₀ A₁ => {
    carrier := A₀ ⊓ A₁
    enorm := ⟨fun x ↦ max ‖x‖ₑ[A₀] ‖x‖ₑ[A₁]⟩
    C := max A₀.C A₁.C
    enorm_zero := by simp_rw [EAddSubmonoid.enorm_zero, max_self]
    enorm_add_le_mul' x y hx hy :=
      calc
        max ‖x + y‖ₑ[A₀] ‖x + y‖ₑ[A₁] ≤
          max (A₀.C * (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀])) (A₁.C * (‖x‖ₑ[A₁] + ‖y‖ₑ[A₁])) := by
            gcongr <;> apply enorm_add_le_mul
            · exact hx.1
            · exact hy.1
            · exact hx.2
            · exact hy.2
        _ ≤ max A₀.C A₁.C * max (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀]) (‖x‖ₑ[A₁] + ‖y‖ₑ[A₁]) :=
            max_mul_mul_le_max_mul_max'
        _ ≤ max A₀.C A₁.C * (max ‖x‖ₑ[A₀] ‖x‖ₑ[A₁] + max ‖y‖ₑ[A₀] ‖y‖ₑ[A₁]) := by
            gcongr
            exact max_add_add_le_max_add_max }⟩

/-- `K(t,x)` in Section 3.1. For `t = 1` this is the norm of `A₀ + A₁`. -/
def addNorm (A₀ A₁ : EAddSubmonoid 𝓐) (t : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  ⨅ (x₀ ∈ A₀) (x₁ ∈ A₁) (_h : x₀ + x₁ = x), ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]

/-- The addition `A₀ + A₁` equipped with the norm `K(t,-)` -/
def add (A₀ A₁ : EAddSubmonoid 𝓐) (t : ℝ≥0∞) : EAddSubmonoid 𝓐 where
  carrier := A₀ ⊔ A₁
  enorm := ⟨addNorm A₀ A₁ t⟩
  C := A₀.C + A₁.C -- maybe
  enorm_zero := by
    simp_rw [← le_zero_iff]
    apply iInf₂_le_of_le 0 A₀.carrier.zero_mem
    apply iInf₂_le_of_le 0 A₁.carrier.zero_mem
    simp
  enorm_add_le_mul' x y hx hy := by
    sorry

instance : Add (EAddSubmonoid 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.add A₁ 1⟩

-- Part of Lemma 3.1.1
-- assume t ≠ ∞ if needed
lemma monotone_add (hx : x ∈ A₀ + A₁) : Monotone (addNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1 (if convenient: make the scalar ring `ℝ≥0`)
-- assume t ≠ ∞ if needed
lemma concave_add (hx : x ∈ A₀ + A₁) : ConcaveOn ℝ≥0∞ univ (addNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1
-- assume s ≠ 0, s ≠ ∞, t ≠ ∞ if needed
lemma addNorm_le_mul (hx : x ∈ A₀ + A₁) :
    addNorm A₀ A₁ t x ≤ max 1 (t / s) * addNorm A₀ A₁ s x := by
  sorry

/-- The functional `Φ` in Section 3.1. Todo: better name. Todo: generalize type of `f`?
If we put a σ-algebra + measure on `ℝ≥0∞` we can get rid of the `ofReal`s. -/
def functional (θ : ℝ) (q : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm ((Ioi 0).indicator fun t ↦ ENNReal.ofReal t ^ (- θ) * f (ENNReal.ofReal t)) q
    (volume.withDensity fun t ↦ (ENNReal.ofReal t)⁻¹)

/- ‖-‖_{θ, q, K} in Section 3.1. -/
def KNorm (A₀ A₁ : EAddSubmonoid 𝓐) (θ : ℝ) (q : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  functional θ q (addNorm A₀ A₁ · x)

/-- The space K_{θ,q}(\bar{A}) in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
def KMethod (A₀ A₁ : EAddSubmonoid 𝓐) (θ : ℝ) (q : ℝ≥0∞) : EAddSubmonoid 𝓐 where
  carrier := A₀ ⊔ A₁
  enorm := ⟨KNorm A₀ A₁ θ q⟩
  C := sorry
  enorm_zero := sorry
  enorm_add_le_mul' := sorry

structure IsIntermediateSpace (A A₀ A₁ : EAddSubmonoid 𝓐) : Prop where
  inf_le : A₀ ⊓ A₁ ≤ A
  le_add : A ≤ A₀ + A₁

-- Todo: find better name?
-- question: how do we get real interpolation with a.e.-subadditivity:
-- probably this works if we apply it to L^p-spaces (i.e. quotients of functions)
structure IsSubadditiveOn (T : 𝓐 → 𝓑) (A : EAddSubmonoid 𝓐) (B : EAddSubmonoid 𝓑) (C D : ℝ≥0∞) :
    Prop where
  mapsTo : Set.MapsTo T A B
  bounded : ∀ x, x ∈ A → ‖T x‖ₑ[B] ≤ C * ‖x‖ₑ[A]
  subadditive : ∀ x y, x ∈ A → y ∈ A → ‖T (x + y)‖ₑ[B] ≤ D * (‖T x‖ₑ[B] + ‖T y‖ₑ[B])

-- `C = ‖T‖_{A, B}`
-- perhaps we don't have to let `C` and `D` depend on all other parameters.
structure AreInterpolationSpaces (A A₀ A₁ : EAddSubmonoid 𝓐) (B B₀ B₁ : EAddSubmonoid 𝓑)
    (C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop where
  isIntermediateSpace_fst : IsIntermediateSpace A A₀ A₁
  isIntermediateSpace_snd : IsIntermediateSpace B B₀ B₁
  prop : ∀ C₀ D₀ C₁ D₁ (T : 𝓐 → 𝓑), IsSubadditiveOn T A₀ B₀ C₀ D₀ → IsSubadditiveOn T A₁ B₁ C₁ D₁ →
    IsSubadditiveOn T A B (C C₀ D₀ C₁ D₁) (D C₀ D₀ C₁ D₁)

/-- `T` is of exponent `θ` w.r.t. constant `E` if `C ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ` -/
def IsOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) (E : ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ

/-- `T` is exact of exponent `θ` -/
def IsExactOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) : Prop :=
  IsOfExponent C θ 1

/-- `T` is exact -/
def IsExact (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ max C₀ C₁

/-- The boundedness constant for the K-method. -/
def C_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- The subadditivity constant for the K-method. -/
def D_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Theorem 3.1.2: The K-method in an interpolation functor. -/
lemma areInterpolationSpaces_kmethod : AreInterpolationSpaces
    (KMethod A₀ A₁ θ q) A₀ A₁ (KMethod B₀ B₁ θ q) B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) := by
  sorry

/-- Part of Theorem 3.1.2 -/
lemma isExactOfExponent_kmethod : IsExactOfExponent (C_KMethod θ q) θ := by
  sorry

/-- The constant of inequality (6). -/
def γKMethod' (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Part of Theorem 3.1.2 -/
lemma addNorm_le_knorm (hx : x ∈ A₀ + A₁) :
    addNorm A₀ A₁ t x ≤ γKMethod' θ q * t ^ θ * KNorm A₀ A₁ θ q x  := by
  sorry

/-- Theorem 3.1.2: If intermediate spaces are equivalent on their . -/
lemma areInterpolationSpaces_of_leKMethod
    /- todo: A equivalent to KMethod A₀ A₁ θ q, similar for B-/ :
    AreInterpolationSpaces A A₀ A₁ B B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) := by
  sorry


end EAddSubmonoid
