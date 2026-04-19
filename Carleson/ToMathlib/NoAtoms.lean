/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.Data.PFun

/-!
# Measures having no atoms

A measure `μ` has no atoms if the measure of each singleton is zero.

## TODO

Should `NoAtoms` be redefined as `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`?
-/

@[expose] public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- Measure `μ` *has no atoms* if for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class NoAtoms' {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  exists_subset_lt : ∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s

export MeasureTheory.NoAtoms' (exists_subset_lt)

variable [na : NoAtoms' μ]

namespace NoAtoms'

instance : NoAtoms μ where
  measure_singleton := by
    intro x
    have := na.exists_subset_lt {x}
    by_contra! hx
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at hx
    rcases this hx with ⟨t, htx, ht, ht'⟩
    rw [subset_singleton_iff_eq] at htx
    rcases htx with h | h
    · rw [h] at ht
      simp at ht
    · rw [h] at ht'
      simp at ht'

theorem exists_nullmeasurable_subset_lt {s : Set α} (hs : NullMeasurableSet s μ) (hs' : 0 < μ s) :
    ∃ t ⊆ s, NullMeasurableSet t μ ∧ 0 < μ t ∧ μ t < μ s := by
  rcases exists_subset_lt _ hs' with ⟨t, hst, ht, hts⟩
  rcases exists_measurable_superset μ t with ⟨u, htu, hu, hut⟩
  use u ∩ s
  use inter_subset_right
  use hu.nullMeasurableSet.inter hs
  have : μ (u ∩ s) = μ t := by
    apply le_antisymm
    · rw [← hut]
      apply measure_mono inter_subset_left
    · calc _
        _ = μ (u ∩ t) := by
          congr
          symm
          rwa [inter_eq_right]
        _ ≤ μ (u ∩ s) := by gcongr
  rw [this]
  use ht, hts

--TODO: proof is very similar to lemma above; can they be unified?
theorem exists_measurable_subset_lt {s : Set α} (hs : MeasurableSet s) (hs' : 0 < μ s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := by
  rcases exists_subset_lt _ hs' with ⟨t, hst, ht, hts⟩
  rcases exists_measurable_superset μ t with ⟨u, htu, hu, hut⟩
  use u ∩ s
  use inter_subset_right
  use hu.inter hs
  have : μ (u ∩ s) = μ t := by
    apply le_antisymm
    · rw [← hut]
      apply measure_mono inter_subset_left
    · calc _
        _ = μ (u ∩ t) := by
          congr
          symm
          rwa [inter_eq_right]
        _ ≤ μ (u ∩ s) := by gcongr
  rw [this]
  use ht, hts

theorem exists_measurable_between {s t : Set α}
  (hs : MeasurableSet s) (ht : MeasurableSet t) (h : s ⊆ t) (h' : μ s < μ t) :
    ∃ u, MeasurableSet u ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t:= by
  have : 0 < μ (t \ s) := by
    calc _
      _ < μ t - μ s := by
        simpa
      _ ≤ _ := le_measure_diff
  rcases exists_measurable_subset_lt (by measurability) this with ⟨v, hv, meas_v, v_pos, v_lt⟩
  use v ∪ s, by measurability, subset_union_right, by simp [h, subset_diff.mp hv]
  have : v \ s = v := by grind
  constructor
  · rw [← diff_union_self, measure_union disjoint_sdiff_left hs, this, add_comm]
    exact ENNReal.lt_add_right h'.ne_top v_pos.ne'
  · rw [← diff_union_self, measure_union disjoint_sdiff_left hs,
        ← diff_union_of_subset h, measure_union disjoint_sdiff_left hs, this]
    apply ENNReal.add_lt_add_right h'.ne_top v_lt


--#check PartialOrder.lift
--#check PartialOrder.ofSetLike

#check Function.graph_injective
#check forall_existsUnique_iff
#check PFun.lift_graph
--#check Subsingleton

@[simp]
theorem PFun.mem_graph'_iff {β : Type*} {f : α →. β} {a : α} {b : β} : (a, b) ∈ f.graph' ↔ b ∈ f a := by
  unfold PFun.graph'
  simp

open SetRel

noncomputable def PFun.of_graph' {β : Type*} (r : SetRel α β) : α →. β := fun a ↦ (by
  by_cases h : ∃ b, a ~[r] b
  · exact Part.some h.choose
  · exact Part.none
  )

theorem PFun.compare_of_mem_of_graph' {β : Type*} {r : SetRel α β} {a : α} {b : β}
  (hb : b ∈ PFun.of_graph' r a) :
    a ~[r] b := by
  unfold PFun.of_graph' at hb
  split at hb
  next h =>
    simp only [Part.mem_some_iff] at hb
    rw [hb]
    exact h.choose_spec
  next h =>
    simp at hb

theorem PFun.mem_of_graph'_of_compare {β : Type*} {r : SetRel α β}
  (h : ∀ a b c, a ~[r] b → a ~[r] c → b = c) {a : α} {b : β} (hb : a ~[r] b) :
    b ∈ PFun.of_graph' r a := by
  unfold PFun.of_graph'
  split_ifs with h'
  · simp only [Part.mem_some_iff]
    exact h a  _ _ hb h'.choose_spec
  · aesop

theorem PFun.mem_of_graph'_iff_compare {β : Type*} {r : SetRel α β}
  (h : ∀ a b c, a ~[r] b → a ~[r] c → b = c) {a : α} {b : β} :
    b ∈ PFun.of_graph' r a ↔ a ~[r] b := by
  constructor
  · exact compare_of_mem_of_graph'
  · exact mem_of_graph'_of_compare h


/-
theorem PFun.of_graph'_eq {β : Type*} {r : SetRel α β} : ∀ {a b}, a ~[r] b ↔ (PFun.of_graph' r) a = b := by
  sorry
-/

theorem PFun.graph'_of_graph' {β : Type*} {r : SetRel α β}
    (h : ∀ a b c, a ~[r] b → a ~[r] c → b = c) : (PFun.of_graph' r).graph' = r := by
  ext ⟨a, b⟩
  rw [PFun.mem_graph'_iff, mem_of_graph'_iff_compare h]

/-
/-- A relation `r : α → β → Prop` is "partial function-like"
(for each `a` there exists at most one `b` such that `r a b`)
if and only if it is `(f · = ·)` for some function `f`. -/
lemma PFun.forall_existsUnique_iff {β : Type*} {r : α → β → Prop} :
    (∀ a b c, r a b → r a c → b = c) ↔ ∃ f : α →. β, ∀ {a b}, r a b ↔ f a = b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let f : (α →. β) := fun a ↦ (by
      by_cases h : ∃ b, r a b
      · exact Part.some h.choose
      · exact Part.none
      )
    use f
    intro a b
    simp_all only [Part.coe_some, f]
    apply Iff.intro
    · intro a_1
      split
      next h_1 =>
        simp_all only [Part.some_inj]
        apply h a _ _ (Classical.choose_spec _) a_1
      next h_1 => simp_all only [not_exists, Part.none_ne_some]
    · intro a_1
      split at a_1
      next h_1 =>
        simp_all only [Part.some_inj]
        subst a_1
        obtain ⟨w, h_1⟩ := h_1
        exact Classical.choose_spec _
      next h_1 => simp_all only [not_exists, Part.none_ne_some]
    /-
    refine ⟨fun a ↦ (h a).choose, fun hr ↦ ?_, fun h' ↦ h' ▸ ?_⟩
    exacts [((h _).choose_spec.2 _ hr).symm, (h _).choose_spec.1]
    -/
  · rintro ⟨f, hf⟩
    simp [hf]
    sorry
-/

theorem PFun.graph_injective {β : Type*} : Function.Injective (@PFun.graph α β) := by
  intro f g hfg
  ext a b
  exact Set.ext_iff.mp hfg (a, b)

theorem PFun.graph'_injective {β : Type*} : Function.Injective (@PFun.graph' α β) :=
  PFun.graph_injective


--#check CompleteLattice
--def PFun.of_graph' (r : α → β → Prop) (h : ∀ (a : α), ∃! b, r a b) :

/-
instance {β : Type*} : SetLike (α →. β) (α × β) where
  coe f := f.graph
  coe_injective' := by
    intro f g hfg
    sorry
-/

/-
instance {β : Type*} : PartialOrder (α →. β) := PartialOrder.ofSetLike _ _
--instance {β : Type*} : SupSet (α →. β) := by apply
-/
instance {β : Type*} : PartialOrder (α →. β) := PartialOrder.lift PFun.graph' PFun.graph'_injective

theorem PFun.le_iff {β : Type*} {f g : α →. β} :  f ≤ g ↔ f.graph' ≤ g.graph' := by rfl

theorem PFun.le_iff' {β : Type*} {f g : α →. β} :  f ≤ g ↔ ∀ (a : α), ∀ b ∈ f a, b ∈ g a := by
  rw [PFun.le_iff]
  unfold PFun.graph'
  simp only [le_eq_subset, setOf_subset_setOf, Prod.forall]

theorem PFun.Dom_mono {β : Type*} {f g : α →. β} (h : f ≤ g) : f.Dom ⊆ g.Dom := by
  unfold PFun.Dom --Part.Dom
  intro a ha
  simp only [mem_setOf_eq] at *
  rw [PFun.le_iff] at h
  unfold PFun.graph' at h
  simp only [le_eq_subset, setOf_subset_setOf, Prod.forall] at h
  rw [Part.dom_iff_mem] at *
  have := h a ha.choose ha.choose_spec
  use ha.choose

theorem PFun.fn_mem {β : Type*} {f : α →. β} {a : α} (ha : a ∈ f.Dom) : f.fn a ha ∈ f a :=
  (Part.eq_get_iff_mem ha).mp rfl

theorem PFun.fn_apply_eq_fn_apply_of_le {β : Type*} {f g : α →. β} (h : f ≤ g) {a : α} (ha : a ∈ f.Dom) :
    f.fn a ha = g.fn a (PFun.Dom_mono h ha) := by
  nth_rw 2 [PFun.fn_apply]
  rw [Part.eq_get_iff_mem]
  rw [PFun.le_iff'] at h
  exact h a _ (PFun.fn_mem ha)

theorem PFun.apply_eq_of_le {β : Type*} {f g : α →. β} (h : f ≤ g) {a : α} (ha : a ∈ f.Dom) :
    f a = g a := by
  rw [← Part.eq_iff_of_dom ha (PFun.Dom_mono h ha)]
  apply fn_apply_eq_fn_apply_of_le h

noncomputable instance {β : Type*} : SupSet (α →. β) where
  sSup S := PFun.of_graph' (sSup (PFun.graph' '' S))

theorem PFun.sSup_eq {β : Type*} {fs : Set (α →. β)} :
    sSup fs = of_graph' (⋃ a ∈ fs, a.graph') := by
  unfold sSup instSupSetPFun
  simp only [sSup_eq_sUnion, sUnion_image]

theorem PFun.exists_mem_of_mem_sSup {β : Type*} {fs : Set (α →. β)} {a : α} {b : β}
  (ha : b ∈ sSup fs a) :
    ∃ f ∈ fs, b ∈ f a := by
  unfold sSup instSupSetPFun at ha
  simp only [sSup_eq_sUnion, sUnion_image] at ha
  have := compare_of_mem_of_graph' ha
  simp at this
  assumption

theorem PFun.le_sSup {β : Type*} {fs : Set (α →. β)} (h : IsChain (· ≤ ·) fs) {f : (α →. β)}
  (hf : f ∈ fs) :
    f ≤ sSup fs := by
  rw [sSup_eq, le_iff, graph'_of_graph']
  · simp only [le_eq_subset]
    exact subset_biUnion_of_mem hf
  intro a b c
  simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro f hf hf' g hg hg'
  rw [mem_graph'_iff] at hf' hg'
  by_cases! hfg : f = g
  · rw [← hfg] at hg'
    exact Part.mem_unique hf' hg'
  rcases h hf hg hfg with h | h
  · rw [le_iff'] at h
    symm
    exact Part.mem_unique hg' (h a _ hf')
  · rw [le_iff'] at h
    exact Part.mem_unique hf' (h a _ hg')

/-
theorem PFun.Dom_sSup {β : Type*} {Ts : Set (α →. β)} : (sSup Ts).Dom = ⋃₀ (PFun.Dom '' Ts) := by
  sorry
-/

theorem PFun.mem_dom_of_mem {β : Type*} {f : α →. β} {a : α} {b : β} (h : b ∈ f a) : a ∈ f.Dom := by
  aesop

theorem PFun.exists_fn_of_fn_sSup {β : Type*} {fs : Set (α →. β)} (h : IsChain (· ≤ ·) fs) {a : α}
  (ha : a ∈ (sSup fs).Dom) :
    ∃ f ∈ fs, ∃ (haf : a ∈ f.Dom), (sSup fs).fn a ha = f.fn a haf := by
  rcases exists_mem_of_mem_sSup (fn_mem ha) with ⟨f, hf, hf'⟩
  use f, hf, mem_dom_of_mem hf'
  symm
  apply fn_apply_eq_fn_apply_of_le (le_sSup h hf)

--#check Monotone

open Classical in
noncomputable def PFun.insert {β : Type*} (f : α →. β) (a : α) (b : β) : α →. β :=
  fun x ↦ if x = a then b else f x

@[simp]
theorem PFun.Dom_insert {β : Type*} {f : α →. β} {a : α} {b : β} :
    (PFun.insert f a b).Dom = f.Dom.insert a := by
  unfold PFun.insert PFun.Dom Set.insert
  ext x
  simp only [Part.coe_some, mem_setOf_eq]
  split_ifs with hx <;> simp [hx]

def PFun.Monotone [Preorder α] {β : Type*} [Preorder β] (f : α →. β) :=
  ∀ ⦃a b⦄ (ha : a ∈ f.Dom) (hb : b ∈ f.Dom), a ≤ b → f.fn a ha ≤ f.fn b hb

theorem PFun.Monotone.Monotone [Preorder α] {β : Type*} [Preorder β] {f : α →. β}
  (hf : Monotone f) :
    _root_.Monotone (fun x : f.Dom ↦ f.fn x x.2) := by
  intro x y hxy
  apply hf
  simpa


theorem PFun.Monotone.insert [Preorder α] {β : Type*} [Preorder β] {f : α →. β}
  (hf : PFun.Monotone f) {a : α} {b : β}
  (hb : ∀ x ≤ a, ∀ (hx : x ∈ f.Dom), f.fn x hx ≤ b)
  (hb' : ∀ x ≥ a, ∀ (hx : x ∈ f.Dom), b ≤ f.fn x hx) :
    PFun.Monotone (PFun.insert f a b) := by
  intro x y hx hy hxy
  rw [PFun.Dom_insert, Set.insert] at hx hy
  unfold PFun.insert
  simp only [Part.coe_some, PFun.fn_apply]
  split_ifs with hx
  · simp only [Part.get_some]
    split_ifs with hy
    · simp
    · apply hb'
      rwa [← hx]
  · by_cases hy : y = a
    · simp only [hy, ↓reduceIte, Part.get_some]
      apply hb
      rwa [← hy]
    · simp only [hy, ↓reduceIte]
      apply hf
      exact hxy

/-
noncomputable instance {β : Type*} : CompleteSemilatticeSup (α →. β) where
  le_sSup s a hs := sorry
  sSup_le b hb := sorry
-/

--TODO: move
instance TopologicalSpace.SeparableSpace.subtype {X : Type*} [TopologicalSpace X] [SeparableSpace X]
    [PseudoMetrizableSpace X] {s : Set X} : SeparableSpace ↑s :=
  (IsSeparable.of_separableSpace s).separableSpace

/-
instance [TopologicalSpace α] [Preorder α] [OrderTopology α] {p : α → Prop} : OrderTopology (Subtype p) := by
  constructor
  refine Eq.symm (TopologicalSpace.ext ?_)
  unfold IsOpen TopologicalSpace.IsOpen instTopologicalSpaceSubtype
  sorry
-/
  --refine Eq.symm ((fun {X} {t t'} ↦ TopologicalSpace.ext_iff.mpr) ?_)
  /-
  have this : Continuous fun p : Subtype p × Subtype p => ((p.fst : α), (p.snd : α)) :=
    continuous_subtype_val.prodMap continuous_subtype_val
  OrderClosedTopology.mk (t.isClosed_le'.preimage this)
  -/

--TODO: move
instance ClosedIicTopology.subtype [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {p : α → Prop} :
    ClosedIicTopology (Subtype p) where
  isClosed_Iic := by
    intro a
    rw [← preimage_subtype_val_Iic]
    exact isClosed_induced isClosed_Iic

--TODO: move
instance instIsCountablyGenerated_atTop [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] [SeparableSpace α] :
    IsCountablyGenerated (atTop : Filter α) := by
  obtain (h | ⟨x, hx⟩) := Set.eq_empty_or_nonempty {x : α | IsTop x}
  · obtain ⟨s, s_count, hs⟩ := exists_countable_dense α
    have : atTop = generate (Ici '' s) := by
      refine atTop_eq_generate_of_not_bddAbove fun ⟨x, hx⟩ ↦ ?_
      simp only [eq_empty_iff_forall_notMem, IsTop, mem_setOf_eq, not_forall, not_le] at h
      obtain ⟨y, hy, hxy⟩ := hs.exists_mem_open isOpen_Ioi (h x)
      exact (hx hy).not_gt hxy
    rw [this]
    exact ⟨_, s_count.image _, rfl⟩
  · rw [atTop_eq_pure_of_isTop hx]
    exact isCountablyGenerated_pure x

--TODO: move
instance instIsCountablyGenerated_atBot [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α] [SeparableSpace α] :
    IsCountablyGenerated (atBot : Filter α) :=
  @NoAtoms'.instIsCountablyGenerated_atTop αᵒᵈ _ _ _ _

/-
--TODO: move
theorem Dense.ciSup' {γ : Type*} {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLinearOrder α]
  [ClosedIicTopology α] {f : γ → α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S) (hf : Continuous f) {x : γ} :
    ⨆ (s : S) (hs : s ≤ x), ↑s = ⨆ i, f i := by
  sorry
-/

theorem ENNReal.induction {p : ENNReal → Prop} (h_bot : p ⊥) (h_top : p ⊤)
  (h_iSup : ∀ t, p (⨆ (x ≤ t) (hx : p x), x)) (h_iInf : ∀ t, p (⨅ (x ≥ t) (hx : p x), x))
  (h_between : ∀ x y, p x → p y → ∃ z, x < z ∧ z < y ∧ p z) :
    ∀ x, p x := by
  sorry

theorem exists_measurable_sets_measure_eq {s t : Set α} :
    ∃ Ts : Set.Iic (μ univ) → Set α, Monotone Ts ∧ ∀ x, MeasurableSet (Ts x) ∧ μ (Ts x) = x := by
  set Γ := {S : Set.Iic (μ univ) →. (Set α) | PFun.Monotone S ∧
    ∀ x (hx : x ∈ S.Dom), MeasurableSet (S.fn x hx) ∧ μ (S.fn x hx) = x}
  have : ∃ S ∈ Γ, ∀ T ∈ Γ, S ≤ T → T ≤ S := by
    apply zorn_le₀
    intro Ts hTs hTs'
    use sSup Ts
    constructor
    · unfold Γ
      simp only [PFun.mem_dom, forall_exists_index, mem_setOf_eq]
      constructor
      · intro x y hx hy hxy
        simp only [le_eq_subset]
        rcases PFun.exists_fn_of_fn_sSup hTs' hx with ⟨f, hf, hfx, h⟩
        rcases PFun.exists_fn_of_fn_sSup hTs' hy with ⟨g, hg, hgy, h'⟩
        have hfΓ := hTs hf
        unfold Γ at hfΓ
        have hgΓ := hTs hg
        unfold Γ at hgΓ
        simp only [mem_setOf_eq] at hfΓ hgΓ --PFun.mem_dom, PFun.fn_apply, forall_exists_index,
        rw [h, h']
        by_cases! hfg : f = g
        · simp only [hfg]
          rw [hfg] at hfx
          exact hgΓ.1 _ _ hxy
        rcases hTs' hf hg hfg with h | h
        · rw [PFun.fn_apply_eq_fn_apply_of_le h hfx]
          --have hxy : (⟨x.1, PFun.Dom_mono h hfx⟩ : g.Dom) ≤ ⟨y.1, hgy⟩ := by simpa
          exact hgΓ.1 _ _ hxy
        · rw [PFun.fn_apply_eq_fn_apply_of_le h hgy]
          --have hxy : (⟨x.1, hfx⟩ : f.Dom) ≤ ⟨y.1, PFun.Dom_mono h hgy⟩ := by simpa
          exact hfΓ.1 _ _ hxy
      · intro x T hT
        rcases PFun.exists_fn_of_fn_sSup hTs' (PFun.mem_dom_of_mem hT) with ⟨f, hf, hfx, h⟩
        have hfΓ := hTs hf
        unfold Γ at hfΓ
        simp only [mem_setOf_eq] at hfΓ --PFun.mem_dom, PFun.fn_apply, forall_exists_index,
        rw [h]
        use (hfΓ.2 x hfx).1, (hfΓ.2 x hfx).2
    · intro f hf
      apply PFun.le_sSup hTs' hf
  rcases this with ⟨S, hSΓ, S_maximal⟩
  unfold Γ at hSΓ
  simp only [mem_setOf_eq] at hSΓ
  /-
  have dense_S_Dom : Dense S.Dom := by
    by_cases h : Nontrivial ↑(Iic (μ univ))
    · #check DenselyOrdered
      apply dense_of_exists_between
      intro x y hxy
      have : MeasurableSet (S.fn x x.2) := by
        sorry
      rcases exists_measurable_between

    · sorry
  -/
  have S_total : ∀ x, x ∈ S.Dom := by
    intro x
    contrapose! S_maximal
    --let dom := S.Dom
    let s := ⋃ (y : S.Dom) (hyx : y ≤ x), S.fn y y.2
    let T : Set.Iic (μ univ) →. Set α := PFun.insert S x s
    use T
    constructor
    · unfold T Γ
      constructor
      · apply PFun.Monotone.insert hSΓ.1
        · intro y hyx hy
          unfold s
          apply subset_iUnion_of_subset (⟨y, hy⟩ : S.Dom)
          apply subset_iUnion_of_subset hyx
          rfl
        · intro y hxy hy
          apply iUnion_subset
          intro t
          apply iUnion_subset
          intro ht
          apply hSΓ.1 _ _ (ht.trans hxy)
      intro y hy
      simp only [PFun.fn_apply]
      unfold PFun.insert
      split_ifs with hyx
      · let helper := S.Dom ∩ (Set.Iic x)
        have : s = ⋃ (y : helper), S.fn y y.2.1 := by
          unfold s
          apply le_antisymm
          · apply iSup_le
            intro y
            apply iSup_le
            intro hyx
            apply le_iSup_of_le ⟨y, ⟨y.2, hyx⟩⟩
            rfl
          · apply iSup_le
            intro y
            apply le_iSup_of_le ⟨y, y.2.1⟩
            apply le_iSup_of_le y.2.2
            rfl
        simp only [Part.coe_some, Part.get_some]
        rw [this]
        have mono_S : Monotone (fun y : helper ↦ S.fn y y.2.1) := by
          intro x y hxy
          apply hSΓ.1
          simpa
        constructor
        · apply MeasurableSet.iUnion_of_monotone mono_S
          intro y
          exact (hSΓ.2 y y.2.1).1
        · rw [Monotone.measure_iUnion mono_S]
          conv in μ _ => rw [(hSΓ.2 i i.2.1).2]
          rw [hyx]
          /-
          calc _
            _ = ⨆ (y : S.Dom), ↑y := by
              sorry
          -/
          apply le_antisymm
          · apply iSup_le
            intro y
            exact y.2.2
          · rw [Dense.ciSup' _ continuous_subtype_val]
            · sorry
            · sorry
            #check Dense.ciSup'

      · simp only [PFun.Dom_insert, Set.insert, mem_setOf_eq, hyx, false_or] at hy
        exact (hSΓ.2 y hy)
    · unfold T PFun.insert
      rw [PFun.le_iff', PFun.le_iff']
      constructor
      · aesop
      · simp only [not_forall]
        use x
        aesop
  use fun x : Set.Iic (μ univ) ↦ S.fn x (S_total x)
  constructor
  · intro x y hxy
    exact hSΓ.1 _ _ hxy
  · intro x
    exact hSΓ.2 x (S_total x)



theorem exists_measurable_set_measure_eq {s t : Set α}
  {x : ENNReal} (ub : x ≤ μ univ) :
    ∃ s, MeasurableSet s ∧ μ s = x := by
  sorry --TODO: use exists_measurable_sets_measure_eq

theorem exists_subset_measure_eq {s t : Set α}
  {x : ENNReal} (ub : x ≤ μ t) :
    ∃ s ⊆ t, μ s = x := by
  sorry

theorem exists_nullmeasurable_subset_measure_eq {s t : Set α} (ht : NullMeasurableSet t μ)
  {x : ENNReal} (ub : x ≤ μ t) :
    ∃ s, NullMeasurableSet s μ ∧ μ s = x := sorry

--more common definition implying the theorem
theorem exists_between₀ [NoAtoms μ] {s t : Set α}
  (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) (h : s ⊆ t)
  {x : ENNReal} (lb : μ s ≤ x) (ub : x ≤ μ t) :
    ∃ E, NullMeasurableSet E μ ∧ s ⊆ E ∧ E ⊆ t ∧ μ E = x := sorry

--TODO: Lyapunovs convexity theorem

end NoAtoms'

end MeasureTheory
