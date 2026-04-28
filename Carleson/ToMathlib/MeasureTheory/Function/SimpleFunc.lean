import Mathlib.Algebra.Order.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SimpleFunc

-- Upstreaming status: under active development by @ldiedering.
-- Wait for the file to stabilise first.

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

namespace SimpleFunc

--TODO: tag this as @[fun_prop] (currently this gives an error)
theorem measurable_comp [MeasurableSpace α] [MeasurableSpace γ] {f : SimpleFunc α β}
  {g : β → γ} :
    Measurable (g ∘ f) :=
  SimpleFunc.measurable_bind _ (fun b _ ↦ g b) (fun _ ↦ measurable_const)

theorem measurable_comp' [MeasurableSpace α] [MeasurableSpace γ] {f : SimpleFunc α β}
  {g : β → γ} :
    Measurable fun a ↦ g (f a) :=
  SimpleFunc.measurable_bind _ (fun b _ ↦ g b) (fun _ ↦ measurable_const)

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


open Pointwise in
private lemma helper [MeasurableSpace α] [LinearOrder β] [AddCommMonoid β] [CanonicallyOrderedAdd β]
  [OrderBot β] [Sub β] [OrderedSub β]
  {f : SimpleFunc α β} (hs : (f.range \ {0}).Nonempty) :
  let s := f.range \ {0};
  ((f - (const α (s.min' hs)).restrict (support ⇑f)).range \ {0}).card + 1
    = (f.range \ {0}).card := by
  intro s
  have : f.range \ {0} =
    insert (s.min' hs)
      ((((f - (const α (s.min' hs)).restrict (support ⇑f)).range \ {0})) + ({s.min' hs} : Finset β)) := by
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
      · rw [tsub_add_cancel_of_le this.le]
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
          · rw [← h, add_comm, ← hy]
            simp only [coe_const, Function.const_apply]
            symm
            apply add_tsub_cancel_of_le
            apply Finset.min'_le
            unfold s
            simpa
        · rw [← h, ← ne_eq]
          rw [← bot_eq_zero', ← bot_lt_iff_ne_bot, bot_eq_zero']
          apply add_pos_of_pos_of_nonneg _ (by simp)
          apply lt_of_le_of_ne (by simp)
          symm
          exact y'_ne_zero
  rw [this, Finset.card_insert_of_notMem, Finset.add_def, Finset.card_image_of_injOn]
  · simp
  · simp only [Finset.product_singleton, Finset.coe_map, Function.Embedding.coeFn_mk,
    Finset.coe_sdiff, coe_range, coe_sub, Finset.coe_singleton]
    intro p hp q hq
    simp only [mem_image, mem_diff, Set.mem_range, Pi.sub_apply, mem_singleton_iff, ↓existsAndEq,
      true_and] at *
    rcases hp with ⟨y, hy, hp⟩
    rcases hq with ⟨z, hz, hq⟩
    have hy : y ∈ support ⇑f := by
      contrapose! hy
      rw [SimpleFunc.restrict_apply _ (measurableSet_support f), Set.indicator]
      split_ifs
      simp at hy
      simpa
    have hy : ((const α (s.min' hs)).restrict (support ⇑f)) y = s.min' hs := by
      rw [SimpleFunc.restrict_apply _ (measurableSet_support f), Set.indicator]
      split_ifs
      simp
    have hz : z ∈ support ⇑f := by
      contrapose! hz
      rw [SimpleFunc.restrict_apply _ (measurableSet_support f), Set.indicator]
      split_ifs
      simp at hz
      simpa
    have hz : ((const α (s.min' hs)).restrict (support ⇑f)) z = s.min' hs := by
      rw [SimpleFunc.restrict_apply _ (measurableSet_support f), Set.indicator]
      split_ifs
      simp
    rw [← hp, ← hq]
    simp only [Prod.mk.injEq, and_true]
    rw [hy, hz, tsub_add_cancel_of_le, tsub_add_cancel_of_le]
    · grind
    · apply Finset.min'_le
      unfold s
      simpa
    · apply Finset.min'_le
      unfold s
      simpa
  · rw [Finset.add_def]
    simp only [Finset.product_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_sdiff,
      mem_range, coe_sub, Set.mem_range, Pi.sub_apply, Finset.mem_singleton,
      Function.Embedding.coeFn_mk, ↓existsAndEq, true_and, exists_exists_and_eq_and, not_exists,
      not_and]
    intro x
    rw [SimpleFunc.restrict_apply _ (measurableSet_support f), Set.indicator]
    split_ifs with hx
    · simp only [coe_const, Function.const_apply]
      contrapose
      intro h
      rw [tsub_add_cancel_of_le] at h
      · rw [h, tsub_self]
      apply Finset.min'_le
      unfold s
      simpa
    · simp only [tsub_zero]
      contrapose
      intro _
      simp at hx
      assumption

--TODO: move
--TODO: formulate this with `IsLowerSet` and write a separate lemma to distinguish the cases
open Classical in
lemma Antitone.support_eq [ConditionallyCompleteLinearOrderBot α] [AddMonoid β] [LinearOrder β] [CanonicallyOrderedAdd β] [OrderBot β]
  {f : α → β} (hf : Antitone f) :
    f.support = if (BddAbove f.support) then
                  if (sSup f.support ∈ f.support)
                    then Set.Iic (sSup f.support)
                  else Set.Iio (sSup f.support)
                else Set.univ
    := by
  ext x
  simp only [Function.mem_support, ne_eq, ite_not]
  split_ifs with h h'
  · contrapose
    simp only [mem_Iio, not_lt]
    constructor
    · intro h''
      apply csSup_le'
      rw [mem_upperBounds]
      intro y hy
      contrapose! hy
      simp only [Function.mem_support, ne_eq, Decidable.not_not]
      rw [← bot_eq_zero', ← le_bot_iff]
      convert (hf hy.le).trans_eq h''
      exact bot_eq_zero'
    · intro h''
      rw [← bot_eq_zero', ← le_bot_iff]
      convert (hf h'').trans_eq h'
      exact bot_eq_zero'
  · contrapose
    simp only [mem_Iic, not_le]
    constructor
    · intro h''
      apply lt_of_le_of_ne
      · apply csSup_le'
        rw [mem_upperBounds]
        intro y hy
        contrapose! hy
        simp only [Function.mem_support, ne_eq, Decidable.not_not]
        rw [← bot_eq_zero', ← le_bot_iff]
        convert (hf hy.le).trans_eq h''
        exact bot_eq_zero'
      · contrapose! h'
        rwa [h']
    · intro h''
      contrapose! h''
      rw [le_csSup_iff' h]
      intro y hy
      rw [mem_upperBounds] at hy
      apply hy
      simpa
  · simp only [mem_univ, iff_true]
    contrapose! h
    use x
    intro y hy
    rw [Function.mem_support, ← bot_eq_zero', ← bot_lt_iff_ne_bot, bot_eq_zero'] at hy
    have := h.trans_lt hy
    contrapose! this
    exact hf this.le

@[elab_as_elim]
protected theorem antitone_induction [MeasurableSpace α] [ConditionallyCompleteLinearOrderBot α]
  [LinearOrder β] [AddCommMonoid β] [CanonicallyOrderedAdd β] [OrderBot β] [Sub β] [OrderedSub β]
  {motive : (SimpleFunc α β) → Prop}
  (const'' : ∀ (c : β) (b : α), motive ((SimpleFunc.const α c).restrict (Set.Iio b)))
  (const' : ∀ (c : β) (b : α), motive ((SimpleFunc.const α c).restrict (Set.Iic b)))
  (const : ∀ (c : β), motive (SimpleFunc.const α c))
  (add : ∀ ⦃f : SimpleFunc α β⦄ (c : β) ⦃s : Set α⦄ (_ : MeasurableSet s), (Function.support ⇑f) ⊆ s →
    motive f → motive ((SimpleFunc.const α c).restrict s) →
      motive (f + ((SimpleFunc.const α c).restrict s))) (f : SimpleFunc α β) (hf : Antitone f) :
        motive f := by
  classical
  generalize h : (f.range \ {0}).card = n
  induction n generalizing f with
  | zero =>
    rw [Finset.card_eq_zero] at h
    rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
    rw [Finset.coe_empty, diff_eq_empty, Set.range_subset_singleton] at h
    convert const 0
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
      unfold g
      rw [Antitone.support_eq hf]
      split_ifs
      · apply const'
      · apply const''
      · simp only [restrict_univ]
        apply const
    have f_eq : f = f' + g := by
      unfold f'
      ext x
      simp only [coe_add, coe_sub, Pi.add_apply, Pi.sub_apply]
      rw [tsub_add_cancel_of_le]
      unfold g
      rw [restrict_apply _ my]
      apply indicator_le
      simp only [Function.mem_support, ne_eq]
      intro y hy
      apply Finset.min'_le
      simpa
    have Pf' : motive f' := by
      let t := f'.range \ {0}
      apply ih _
      · unfold f'
        intro x y hxy
        simp only [coe_sub, Pi.sub_apply]
        · rw [SimpleFunc.restrict_apply _ (measurableSet_support f),
              SimpleFunc.restrict_apply _ (measurableSet_support f), Set.indicator, Set.indicator]
          split_ifs with hy hx hx
          · gcongr
            · exact hf hxy
            simp
          · exfalso
            simp only [Function.mem_support, ne_eq, Decidable.not_not] at hx hy
            apply hy
            rw [← bot_eq_zero', ← le_bot_iff]
            convert (hf hxy).trans_eq hx
            exact bot_eq_zero'
          · simp only [Function.mem_support, ne_eq, Decidable.not_not] at hy
            rw [hy]
            simp
          · simp only [tsub_zero]
            apply hf hxy
      · apply @Nat.add_right_cancel _ 1
        unfold f' g
        rwa [SimpleFunc.helper]
    rw [f_eq]
    apply add _ my _ Pf' Pg
    intro x
    unfold f'
    simp only [coe_sub, Function.mem_support, Pi.sub_apply, ne_eq]
    intro h
    contrapose! h
    rw [h]
    simp

@[elab_as_elim]
protected theorem induction'' [MeasurableSpace α] [LinearOrder β] [AddCommMonoid β]
  [CanonicallyOrderedAdd β] [OrderBot β] [Sub β] [OrderedSub β]
  {motive : (SimpleFunc α β) → Prop}
  (const : ∀ (c : β) {s : Set α} (_ : MeasurableSet s), motive ((SimpleFunc.const α c).restrict s))
  (add : ∀ ⦃f : SimpleFunc α β⦄ (c : β) ⦃s : Set α⦄ (_ : MeasurableSet s), (Function.support ⇑f) ⊆ s →
    motive f → motive ((SimpleFunc.const α c).restrict s) →
      motive (f + ((SimpleFunc.const α c).restrict s))) (f : SimpleFunc α β) :
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
      simp only [coe_add, coe_sub, Pi.add_apply, Pi.sub_apply]
      rw [tsub_add_cancel_of_le]
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

lemma nnapprox_le {f : α → ℝ≥0} (hf : Measurable f) {a : α} {n : ℕ} :
    (nnapprox f n) a ≤ f a := approx_le hf rfl

@[mono]
theorem monotone_nnapprox {f : α → ℝ≥0} : Monotone (nnapprox f) :=
  monotone_approx _ f

set_option linter.style.multiGoal false in
lemma iSup_nnapprox_apply (hf : Measurable f) (a : α) : ⨆ n, (nnapprox f n : SimpleFunc α ℝ≥0) a = f a := by
  apply le_antisymm
  · apply ciSup_le
    intro n
    exact nnapprox_le hf
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
    rw [nnapprox, iSup_approx_apply' _ _ _ hf (by simp)] at lt_q
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

lemma Antitone.antitone_eapprox {α : Type*} [TopologicalSpace α] {mα : MeasurableSpace α} [BorelSpace α]
  [LinearOrder α] [OrderClosedTopology α] ⦃f : α → ℝ≥0∞⦄ (hf : Antitone f) {n : ℕ} :
    Antitone (SimpleFunc.eapprox f n) := by
  unfold SimpleFunc.eapprox
  intro x y hxy
  rw [SimpleFunc.approx_apply _ hf.measurable, SimpleFunc.approx_apply _ hf.measurable]
  gcongr with m hm
  split_ifs with hy hx
  · rfl
  · exfalso
    push Not at hx
    exact lt_irrefl _ ((hy.trans (hf hxy)).trans_lt hx)
  · simp only [zero_le]
  · rfl

--modified from ennreal_induction
@[elab_as_elim]
protected theorem Antitone.ennreal_induction' {α : Type*} [TopologicalSpace α] {mα : MeasurableSpace α} [BorelSpace α]
  [LinearOrder α] [OrderClosedTopology α]
   {motive : (α → ℝ≥0∞) → Prop}
    (simpleFunc : ∀ ⦃f : SimpleFunc α ℝ≥0∞⦄, Antitone f → motive f)
    (iSup :
      ∀ ⦃f : ℕ → (SimpleFunc α ℝ≥0∞)⦄,
        Monotone f → (∀ (n : ℕ), motive (f n)) → motive fun x ↦ ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Antitone f) : motive f := by
  convert iSup (SimpleFunc.monotone_eapprox f) _ using 2
  · rw [SimpleFunc.iSup_eapprox_apply hf.measurable]
  · exact fun n =>
      simpleFunc hf.antitone_eapprox

end MeasureTheory
