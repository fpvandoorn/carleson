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
  sorry

theorem PFun.graph'_injective {β : Type*} : Function.Injective (@PFun.graph' α β) := by
  sorry


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

/-
noncomputable instance {β : Type*} : CompleteSemilatticeSup (α →. β) where
  le_sSup s a hs := sorry
  sSup_le b hb := sorry
-/

theorem exists_measurable_sets_measure_eq {s t : Set α} :
    ∃ Ts : ENNReal → Set α, Monotone Ts ∧ ∀ x ≤ μ univ, MeasurableSet (Ts x) ∧ μ (Ts x) = x := by
  set Γ := {S : ENNReal →. (Set α) |
    ∀ x (hx : x ∈ S.Dom), MeasurableSet (S.fn x hx) ∧ μ (S.fn x hx) = x ∧
      ∀ y (hy : y ∈ S.Dom), x ≤ y → S.fn x hx ⊆ S.fn y hy}
  have : ∃ S ∈ Γ, ∀ T ∈ Γ, S ≤ T → T ≤ S := by
    apply zorn_le₀
    intro Ts hTs hTs'
    use sSup Ts
    constructor
    · unfold Γ
      simp only [PFun.mem_dom, forall_exists_index, mem_setOf_eq]
      intro x T hT
      rcases PFun.exists_fn_of_fn_sSup hTs' (PFun.mem_dom_of_mem hT) with ⟨f, hf, hfx, h⟩
      have hfΓ := hTs hf
      unfold Γ at hfΓ
      simp only [mem_setOf_eq] at hfΓ --PFun.mem_dom, PFun.fn_apply, forall_exists_index,
      rw [h]
      use (hfΓ x hfx).1, (hfΓ x hfx).2.1
      intro y R hR hxy
      rcases PFun.exists_fn_of_fn_sSup hTs' (PFun.mem_dom_of_mem hR) with ⟨g, hg, hgy, h'⟩
      have hgΓ := hTs hg
      unfold Γ at hgΓ
      simp only [mem_setOf_eq] at hgΓ --PFun.mem_dom, PFun.fn_apply, forall_exists_index,
      rw [h']
      by_cases! hfg : f = g
      · grind
      rcases hTs' hf hg hfg with h | h
      · rw [PFun.fn_apply_eq_fn_apply_of_le h hfx]
        exact (hgΓ x _).2.2 _ _ hxy
      · rw [PFun.fn_apply_eq_fn_apply_of_le h hgy]
        exact (hfΓ x _).2.2 _ _ hxy
    · intro f hf
      apply PFun.le_sSup hTs' hf
  rcases this with ⟨S, hSΓ, S_maximal⟩
  unfold Γ at hSΓ
  simp only [mem_setOf_eq] at hSΓ
  have S_total : ∀ x ≤ μ univ, x ∈ S.Dom := by
    intro x hx
    let s := ⋃ y ≤ x, ⨆ (hy : y ∈ S.Dom), S.fn y hy
    have hsx : μ s = x := by
      --rw [Antitone.measure_iUnion]
      --rw [measure_iUnion_of_tendsto_zero]
      --rw [Monotone.measure_iInter]
      --apply tendsto_measure_iUnion_atTop
      --apply tendsto_measure_biInter_gt
      sorry
    /-
    let t := ⋃ y ≥ x, ⨆ (hx' : x ≤ μ univ) (hx : x ∈ S.Dom), S.fn x hx
    have htx : x ≤ μ t := by
      sorry
    -/
    have hsx' : x ≤ μ s := by
      sorry
    sorry
    --TODO: use NoAtoms' and S_maximal
  use fun x ↦ if hx : x ≤ μ univ then S.fn x (S_total x hx) else univ
  constructor
  · intro x y hxy
    simp only [le_eq_subset]
    split_ifs with hx hy
    · use (hSΓ x (S_total x hx)).2.2 y (S_total y hy) hxy
    all_goals grind
  intro x hx
  simp only [hx, ↓reduceDIte]
  use (hSΓ x (S_total x hx)).1, (hSΓ x (S_total x hx)).2.1



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
