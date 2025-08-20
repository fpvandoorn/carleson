import Mathlib.Algebra.Order.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SimpleFunc

noncomputable section

/-
--TODO: use ConditionallyCompleteLattice instead?
theorem iSup_le' {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] [Nonempty ι] {f : ι → α}
    {a : α} (h : ∀ (i : ι), f i ≤ a) :
  iSup f ≤ a := csSup_le (Set.range_nonempty f) fun _ ⟨i, Eq⟩ => Eq ▸ h i
-/
/-
theorem isLUB_iSup' {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] {f : ι → α} :
    IsLUB (Set.range f) (⨆ j, f j) :=
  isLUB_csSup _

@[simp]
theorem iSup_le_iff' {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] {f : ι → α} {a : α} :
    iSup f ≤ a ↔ ∀ i, f i ≤ a := by
  --(isLUB_le_iff isLUB_iSup').trans Set.forall_mem_range
  constructor
  · intro h i
    --apply le_of_iSup_le
    apply csSup_le_iff'
-/

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

namespace SimpleFunc

variable [MeasurableSpace α]


instance [CompleteSemilatticeSup β] : SemilatticeSup β where
  sup := fun a b ↦ sSup {a, b}
  le_sup_left := by
    intro a b
    apply le_sSup (by simp)
  le_sup_right := by
    intro a b
    apply le_sSup (by simp)
  sup_le := by
    intro a b c ha hb
    apply sSup_le
    simp [ha, hb]

section Approx

--variable [ConditionallyCompleteLattice β]

theorem approx_le {α : Type u_1} {β : Type u_2}
  [inst : MeasurableSpace α] [ConditionallyCompleteLinearOrderBot β] [Zero β] [TopologicalSpace β]
  [OrderClosedTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
  {i : ℕ → β} {f : α → β} (hf : Measurable f) (h_zero : (0 : β) = ⊥)
  {a : α} {n : ℕ} :
    (approx i f n) a ≤ f a := by
  rw [approx_apply a hf, h_zero]
  simp only [Finset.sup_le_iff, Finset.mem_range]
  intro b _
  split_ifs with hb
  · exact hb
  · simp only [bot_le]

theorem iSup_approx_apply' [ConditionallyCompleteLinearOrderBot β] [Zero β] [TopologicalSpace β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f n : SimpleFunc α β) a = ⨆ (k) (_ : i k ≤ f a), i k := by
  refine le_antisymm (ciSup_le fun n => ?_) (ciSup_le ?_)
  · rw [approx_apply a hf, h_zero]
    refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · rw [le_ciSup_iff' (by use f a; rw [mem_upperBounds]; simp only [Set.mem_range,
        forall_exists_index, forall_apply_eq_imp_iff]; intro n; apply ciSup_le'; simp only [imp_self])]
      intro b hb
      have := hb k
      rw [ciSup_le_iff' (by rw [BddAbove, upperBounds]; use i k; simp)] at this
      exact this h
    · exact bot_le
  · intro k
    rw [le_ciSup_iff']
    · intro b hb
      have := hb (k + 1)
      rw [approx_apply a hf, h_zero] at this
      apply le_trans _ this
      have : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
      refine le_trans (le_of_eq ?_) (Finset.le_sup this)
      rw [ciSup_eq_ite, csSup_empty]
      simp only [dite_eq_ite, ite_eq_ite]
    use f a
    rw [mem_upperBounds]
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro n
    apply approx_le hf h_zero


end Approx



section NNApprox

--instance : ConditionallyCompleteLattice ℝ≥0 := inferInstance

variable {f : α → ℝ≥0}

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def nnrealRatEmbed (n : ℕ) : ℝ≥0 :=
  Real.toNNReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))

theorem nnrealRatEmbed_encode (q : ℚ) :
    nnrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [nnrealRatEmbed, Encodable.encodek]; rfl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def nnapprox : (α → ℝ≥0) → ℕ → SimpleFunc α ℝ≥0 :=
  approx nnrealRatEmbed

@[mono]
theorem monotone_nnapprox {f : α → ℝ≥0} : Monotone (nnapprox f) :=
  monotone_approx _ f

lemma iSup_nnapprox_apply (hf : Measurable f) (a : α) : ⨆ n, (nnapprox f n : SimpleFunc α ℝ≥0) a = f a := by
  rw [nnapprox]
  apply le_antisymm
  · apply ciSup_le
    intro n
    apply approx_le hf rfl
  · apply le_of_not_gt
    intro h
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 h with ⟨q, _, lt_q, q_lt⟩
    have :
      (Real.toNNReal q : ℝ≥0) ≤ ⨆ (k : ℕ) (_ : nnrealRatEmbed k ≤ f a), nnrealRatEmbed k := by
      apply le_ciSup_of_le _ (Encodable.encode q)
      · rw [← nnrealRatEmbed_encode q] at *
        apply le_csSup_of_le
        · rw [BddAbove]
          use nnrealRatEmbed (Encodable.encode q)
          rw [mem_upperBounds]
          simp
        use le_of_lt q_lt
        simp
      · use f a
        rw [mem_upperBounds]
        simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        intro n
        exact ciSup_le' fun i ↦ i
    rw [iSup_approx_apply' _ _ _ hf (by simp)] at lt_q
    apply lt_irrefl _ (lt_of_le_of_lt this lt_q)

lemma iSup_nnapprox (hf : Measurable f) : (fun a ↦ ⨆ n, (nnapprox f n) a) = f := by
  funext a
  exact iSup_nnapprox_apply hf a

end NNApprox

end SimpleFunc

/-- modelled after Measurable.ennreal_induction but with very raw assumptions -/
@[elab_as_elim]
protected theorem Measurable.nnreal_induction {α : Type*} {mα : MeasurableSpace α} {motive : (α → ℝ≥0) → Prop}
    (simpleFunc : ∀ ⦃f : SimpleFunc α ℝ≥0⦄, motive f)
    (approx :
      ∀ ⦃f : α → ℝ≥0⦄, (_ : Measurable f) → (∀ (n : ℕ), motive (SimpleFunc.nnapprox f n)) → motive f)
    ⦃f : α → ℝ≥0⦄ (hf : Measurable f) : motive f := by
  apply approx hf
  intro n
  apply simpleFunc

end MeasureTheory
