import Carleson.ToMathlib.RealInterpolation.Minkowski

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set
open scoped NNReal

variable {𝓐 : Type*} [AddMonoid 𝓐] {𝓑 : Type*} [AddMonoid 𝓑]

variable (𝓐) in
structure EAddSubmonoid where
  carrier : AddSubmonoid 𝓐
  protected enorm : ENorm 𝓐
  protected C : ℝ≥0∞
  protected enorm_zero : ‖(0 : 𝓐)‖ₑ = 0
  protected enorm_add_le_mul' : ∀ x y, x ∈ carrier → y ∈ carrier → ‖x + y‖ₑ ≤ C * (‖x‖ₑ + ‖y‖ₑ)


namespace EAddSubmonoid

variable {A A₀ A₁ : EAddSubmonoid 𝓐} {x y z : 𝓐}

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

/-- `K(t,x)` in Section 3.1 -/
def combineNorm (A₀ A₁ : EAddSubmonoid 𝓐) (t : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  ⨅ (x₀ ∈ A₀) (x₁ ∈ A₁) (_h : x₀ + x₁ = x), ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]

/-- The addition `A₀ + A₁` equipped with the norm `K(t,-)` -/
def add (A₀ A₁ : EAddSubmonoid 𝓐) (t : ℝ≥0∞) : EAddSubmonoid 𝓐 where
  carrier := A₀ ⊔ A₁
  enorm := ⟨combineNorm A₀ A₁ t⟩
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

lemma increasing_add (hx : x ∈ A₀ ⊔ A₁)

end EAddSubmonoid

structure IsIntermediateSpace (A A₀ A₁ : EAddSubmonoid 𝓐) : Prop where
  inf_le : A₀ ⊓ A₁ ≤ A
  le_add : A ≤ A₀ + A₁

-- rename
-- quesion: how do we get real interpolation with a.e.-subadditivity:
-- probably this works if we apply it to L^p-spaces (i.e. quotients of functions)
structure IsSubadditiveOn (T : 𝓐 → 𝓑) (A : EAddSubmonoid 𝓐) (B : EAddSubmonoid 𝓑) (C D : ℝ≥0∞) :
    Prop where
  mapsTo : Set.MapsTo T A B
  bounded : ∀ x, x ∈ A → ‖T x‖ₑ[B] ≤ C * ‖x‖ₑ[A]
  subadditive : ∀ x y, x ∈ A → y ∈ A → ‖T (x + y)‖ₑ[B] ≤ D * (‖T x‖ₑ[B] + ‖T y‖ₑ[B])

-- `C = ‖T‖_{A, B}`
structure AreInterpolationSpaces (A A₀ A₁ : EAddSubmonoid 𝓐) (B B₀ B₁ : EAddSubmonoid 𝓑)
    (C₀ D₀ C₁ D₁ C D : ℝ≥0∞) where
  isIntermediateSpace_fst : IsIntermediateSpace A A₀ A₁
  isIntermediateSpace_snd : IsIntermediateSpace B B₀ B₁
  prop : ∀ T : 𝓐 → 𝓑, IsSubadditiveOn T A₀ B₀ C₀ D₀ → IsSubadditiveOn T A₁ B₁ C₁ D₁ →
    IsSubadditiveOn T A B C D

/-- `T` is of exponent `θ` w.r.t. constant `E` if `C ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ` -/
def IsOfExponent (C C₀ C₁ : ℝ≥0∞) (θ : ℝ) (E : ℝ≥0∞) : Prop :=
  C ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ
