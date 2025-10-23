import Mathlib.Algebra.Order.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SimpleFunc

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

namespace SimpleFunc

/- Proof stolen from the mathlib `SimpleFunc.induction` with a minor modification
   that is even suggested there. -/
--TODO: update notation in mathlib version to match this one
@[elab_as_elim]
protected theorem induction₀ [MeasurableSpace α] [AddZeroClass γ]
    {motive : SimpleFunc α γ → Prop}
    (const : ∀ (c) {s} (_ : MeasurableSet s),
      motive ((SimpleFunc.const _ c).restrict s))
    (add : ∀ ⦃f : SimpleFunc α γ⦄ (c : γ) ⦃s : Set α⦄ (_ : MeasurableSet s), Disjoint (Function.support ⇑f) s →
      motive f → motive ((SimpleFunc.const α c).restrict s) →
        motive (f + ((SimpleFunc.const α c).restrict s)))
    (f : SimpleFunc α γ) : motive f := by
  classical
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty, Set.diff_eq_empty, Set.range_subset_singleton] at h
    convert const 0 MeasurableSet.univ
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx 0 f
    have Pg : motive g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, Set.range_piecewise]
      rw [Set.image_compl_preimage, Set.union_diff_distrib, Set.diff_diff_comm, h, Finset.coe_insert,
        Set.insert_diff_self_of_notMem, Set.diff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]
        convert Set.subset_univ _
        exact Set.preimage_const_of_mem (Set.mem_singleton _)
      · rwa [Finset.mem_coe]
    convert add _ mx _ Pg (const x mx)
    · ext1 y
      simp only [coe_add, Pi.add_apply]
      rw [SimpleFunc.restrict_apply _ mx]
      by_cases hy : y ∈ f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]
    rw [disjoint_iff_inf_le]
    rintro y
    by_cases hy : y ∈ f ⁻¹' {x} <;> simp [g, hy]


--TODO: generalize this to not only work for ℝ≥0 ?
open Pointwise in
private lemma helper [MeasurableSpace α] {f : SimpleFunc α ℝ≥0} (hs : (f.range \ {0}).Nonempty) :
  let s := f.range \ {0};
  ((f - (const α (s.min' hs)).restrict (support ⇑f)).range \ {0}).card + 1
    = (f.range \ {0}).card := by
  intro s
  have : f.range \ {0} =
    insert (s.min' hs)
      ((((f - (const α (s.min' hs)).restrict (support ⇑f)).range \ {0})) + ({s.min' hs} : Finset ℝ≥0)) := by
    rw [← Finset.coe_inj]
    push_cast
    ext x
    simp only [coe_range, mem_diff, Set.mem_range, mem_singleton_iff, coe_sub, add_singleton,
      mem_insert_iff, mem_image, Pi.sub_apply]
    constructor
    · rintro ⟨⟨y, hfyx⟩, x_ne_zero⟩
      rw [or_iff_not_imp_left]
      intro hx
      have : s.min' hs < x := by
        apply lt_of_le_of_ne
        · rw [← hfyx]
          apply Finset.min'_le
          unfold s
          rw [← hfyx] at x_ne_zero
          simpa
        · symm
          simpa
      use x - s.min' hs
      constructor
      · constructor
        · use y
          rw [← hfyx]
          congr
          rw [restrict_apply _ (f.measurableSet_support)]
          unfold indicator
          simp only [Function.mem_support, ne_eq, coe_const, Function.const_apply, ite_not,
            ite_eq_right_iff]
          intro hfy
          rw [hfyx] at hfy
          contradiction
        contrapose! this
        exact tsub_eq_zero_iff_le.mp this
      · rw [← NNReal.coe_inj, NNReal.coe_add, NNReal.coe_sub this.le, sub_add_cancel]
    · rintro (x_eq | ⟨y', ⟨⟨⟨y, hy⟩, y'_ne_zero⟩ , h⟩⟩)
      · have x_mem := Finset.min'_mem s hs
        rw [← x_eq] at x_mem
        unfold s at x_mem
        simp only [Finset.mem_sdiff, mem_range, Set.mem_range, Finset.mem_singleton] at x_mem
        exact x_mem
      · constructor
        · use y
          rw [restrict_apply _ (f.measurableSet_support)] at hy
          unfold indicator at hy
          simp only [Function.mem_support, ne_eq, ite_not] at hy
          split_ifs at hy with hfy
          · simp only [tsub_zero] at hy
            rw [hy] at hfy
            contradiction
          · rw [← h, add_comm]
            rwa [← NNReal.coe_inj, NNReal.coe_sub, sub_eq_iff_eq_add', ← NNReal.coe_add, NNReal.coe_inj] at hy
            apply Finset.min'_le--TODO: generalize this to not only work for ℝ≥0 ?
            unfold s
            simpa
        · rw [← h, ← ne_eq]
          apply @ne_zero_of_lt _ _ _ (0 : NNReal)
          apply add_pos_of_pos_of_nonneg _ (by simp)
          rw [← NNReal.coe_pos]
          apply lt_of_le_of_ne (by simp)
          rw [← NNReal.coe_inj, ← ne_eq] at y'_ne_zero
          simp only [NNReal.coe_zero] at y'_ne_zero
          exact y'_ne_zero.symm
  rw [this, Finset.card_insert_of_notMem, Finset.card_add_singleton]
  rw [Finset.add_def]
  simp


--TODO: generalize this to not only work for ℝ≥0 ?
@[elab_as_elim]
protected theorem induction'' [MeasurableSpace α]
  {motive : (SimpleFunc α ℝ≥0) → Prop}
  (const : ∀ (c : ℝ≥0) {s : Set α} (_ : MeasurableSet s), motive ((SimpleFunc.const α c).restrict s))
  (add : ∀ ⦃f : SimpleFunc α ℝ≥0⦄ (c : ℝ≥0) ⦃s : Set α⦄ (_ : MeasurableSet s), (Function.support ⇑f) ⊆ s →
    motive f → motive ((SimpleFunc.const α c).restrict s) →
      motive (f + ((SimpleFunc.const α c).restrict s))) (f : SimpleFunc α ℝ≥0) :
        motive f := by
  classical
  generalize h : (f.range \ {0}).card = n
  induction n generalizing f with
  | zero =>
    rw [Finset.card_eq_zero] at h
    rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
    rw [Finset.coe_empty, diff_eq_empty, Set.range_subset_singleton] at h
    convert const 0 MeasurableSet.univ
    ext x
    simp [h]
  | succ n ih =>
    have nonempty : (f.range \ {0}).Nonempty := by
      rw [← Finset.card_ne_zero]
      simp [h]
    have my := f.measurableSet_support
    let g := (SimpleFunc.const α (Finset.min' _ nonempty)).restrict (support ⇑f)
    let f' := f - g
    have Pg : motive g := by
      apply const _ my
    have Pf' : motive f' := by
      let t := f'.range \ {0}
      apply ih _
      · apply @Nat.add_right_cancel _ 1
        unfold f' g
        rwa [SimpleFunc.helper]
    have f_eq : f = f' + g := by
      unfold f'
      ext x
      simp only [coe_add, coe_sub, Pi.add_apply, Pi.sub_apply, NNReal.coe_add]
      rw [NNReal.coe_sub]
      · simp
      unfold g
      rw [restrict_apply _ my]
      apply indicator_le
      simp only [Function.mem_support, ne_eq]
      intro y hy
      apply Finset.min'_le
      simpa
    rw [f_eq]
    apply add _ my _ Pf' Pg
    intro x
    unfold f'
    simp only [coe_sub, Function.mem_support, Pi.sub_apply, ne_eq]
    intro h
    contrapose! h
    rw [h]
    simp


variable [MeasurableSpace α]


section Approx

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

/- Version of `iSup_approx_apply` for `ConditionallyCompleteLinearOrderBot`. -/
theorem iSup_approx_apply' [ConditionallyCompleteLinearOrderBot β] [TopologicalSpace β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f n : SimpleFunc α β) a = ⨆ (k) (_ : i k ≤ f a), i k := by
  refine le_antisymm (ciSup_le' fun n => ?_) (ciSup_le' fun k => ciSup_le' fun hk => ?_)
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
  · rw [le_ciSup_iff']
    · intro b hb
      have := hb (k + 1)
      rw [approx_apply a hf, h_zero] at this
      apply le_trans _ this
      have : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
      refine le_trans (le_of_eq ?_) (Finset.le_sup this)
      simp [hk]
    use f a
    rw [mem_upperBounds]
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro n
    apply approx_le hf h_zero


end Approx


section NNApprox

variable {f : α → ℝ≥0}

/-- A sequence of `ℝ≥0`s such that its range is the set of non-negative rational numbers. -/
def nnrealRatEmbed (n : ℕ) : ℝ≥0 :=
  Real.toNNReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))

theorem nnrealRatEmbed_encode (q : ℚ) :
    nnrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [nnrealRatEmbed, Encodable.encodek]; rfl

/-- Approximate a function `α → ℝ≥0` by a sequence of simple functions. -/
def nnapprox : (α → ℝ≥0) → ℕ → SimpleFunc α ℝ≥0 :=
  approx nnrealRatEmbed

@[mono]
theorem monotone_nnapprox {f : α → ℝ≥0} : Monotone (nnapprox f) :=
  monotone_approx _ f

set_option linter.style.multiGoal false in
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

--modified from ennreal_induction
@[elab_as_elim]
protected theorem Measurable.ennreal_induction' {α : Type*} {mα : MeasurableSpace α} {motive : (α → ℝ≥0∞) → Prop}
    (simpleFunc : ∀ ⦃f : SimpleFunc α ℝ≥0∞⦄, motive f)
    (iSup :
      ∀ ⦃f : ℕ → (SimpleFunc α ℝ≥0∞)⦄,
        Monotone f → (∀ (n : ℕ), motive (f n)) → motive fun x ↦ ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : motive f := by
  convert iSup (SimpleFunc.monotone_eapprox f) _ using 2
  · rw [SimpleFunc.iSup_eapprox_apply hf]
  · exact fun n =>
      @simpleFunc (SimpleFunc.eapprox f n)

end MeasureTheory
