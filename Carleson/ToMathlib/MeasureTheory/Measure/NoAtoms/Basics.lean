/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Defs
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Data.PFun
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α}

namespace NoAtoms'

variable {μ : Measure α} [na : NoAtoms' μ]

--TODO: move
theorem measure_comap_eq_subtype_coe {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  {s : Set α} (hs : NullMeasurableSet s μ) {t : Set s}
  (ht : NullMeasurableSet t (μ.comap Subtype.val)) :
    μ.comap Subtype.val t = μ (((↑) : s → α) '' t) :=
  comap_apply₀ _ _ Subtype.coe_injective (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs)
    ht

lemma subtype {s : Set α} (hs : MeasurableSet s) : NoAtoms' (μ.comap Subtype.val : Measure s) :=
    by
  apply NoAtoms'.mk'
  intro t meas_t ht
  rw [comap_subtype_coe_apply hs] at ht
  rcases na.exists_measurable_subset_lt (hs.subtype_image meas_t) ht with ⟨r, hrt, _, hr, hr'⟩
  use Subtype.val ⁻¹' r, preimage_subset hrt injOn_subtype_val
  rw [comap_subtype_coe_apply hs, comap_subtype_coe_apply hs, image_preimage_eq_of_subset]
  · use hr, hr'
  · intro x hx
    apply image_subset_range _ t
    exact hrt hx

theorem exists_measurable_between {s t : Set α} (hs : MeasurableSet s) (ht : NullMeasurableSet t μ)
  (h : s ⊆ t) (h' : μ s < μ t) :
    ∃ u, MeasurableSet u ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t := by
  have : 0 < μ (t \ s) := by
    calc _
      _ < μ t - μ s := by
        simpa
      _ ≤ _ := le_measure_sdiff
  rcases exists_measurable_subset_lt₀ (by measurability) this with ⟨v, hv, meas_v, v_pos, v_lt⟩
  use v ∪ s, by measurability, subset_union_right, by simp [h, subset_sdiff.mp hv]
  have : v \ s = v := by grind
  constructor
  · rw [← sdiff_union_self, measure_union disjoint_sdiff_left hs, this, add_comm]
    exact ENNReal.lt_add_right h'.ne_top v_pos.ne'
  · rw [← sdiff_union_self, measure_union disjoint_sdiff_left hs,
        ← sdiff_union_of_subset h, measure_union disjoint_sdiff_left hs, this]
    apply ENNReal.add_lt_add_right h'.ne_top v_lt

theorem exists_nullmeasurable_between {s t : Set α} (hs : NullMeasurableSet s μ)
  (ht : NullMeasurableSet t μ) (h : s ⊆ t) (h' : μ s < μ t) :
    ∃ u, NullMeasurableSet u μ ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t:= by
  rcases hs.exists_measurable_subset_ae_eq with ⟨r, hrs, hr, hrs'⟩
  rw [← hrs'.measure_eq] at *
  rcases exists_measurable_between hr ht (hrs.trans h) h' with ⟨u, hu, hru, hut, hu'⟩
  use u ∪ s, hu.nullMeasurableSet.union hs, subset_union_right, union_subset hut h
  constructor
  · apply hu'.1.trans_le
    gcongr
    simp
  · calc _
      _ = μ (u ∪ r) := by
        apply measure_congr
        exact eventuallyEq_of_mem hrs'.symm fun ⦃x⦄ ↦ congrArg (Or (x ∈ u))
      _ = μ u := by congr; simpa
      _ < μ t := hu'.2

@[simp]
theorem PFun.mem_graph'_iff {β : Type*} {f : α →. β} {a : α} {b : β} : (a, b) ∈ f.graph' ↔ b ∈ f a := by
  unfold PFun.graph'
  simp

open SetRel

/-- Constructs a partial function `α →. β` from its graph of type `SetRel α β`. -/
noncomputable def PFun.ofGraph' {β : Type*} (r : SetRel α β) : α →. β := fun a ↦ (by
  by_cases h : ∃ b, a ~[r] b
  · exact Part.some h.choose
  · exact Part.none
  )

theorem PFun.compare_of_mem_ofGraph' {β : Type*} {r : SetRel α β} {a : α} {b : β}
  (hb : b ∈ PFun.ofGraph' r a) :
    a ~[r] b := by
  unfold PFun.ofGraph' at hb
  split at hb
  next h =>
    simp only [Part.mem_some_iff] at hb
    rw [hb]
    exact h.choose_spec
  next h =>
    simp at hb

theorem PFun.mem_ofGraph'_of_compare {β : Type*} {r : SetRel α β}
  (h : ∀ a b c, a ~[r] b → a ~[r] c → b = c) {a : α} {b : β} (hb : a ~[r] b) :
    b ∈ PFun.ofGraph' r a := by
  unfold PFun.ofGraph'
  split_ifs with h'
  · simp only [Part.mem_some_iff]
    exact h a  _ _ hb h'.choose_spec
  · aesop

theorem PFun.mem_ofGraph'_iff_compare {β : Type*} {r : SetRel α β}
  (h : ∀ a b c, a ~[r] b → a ~[r] c → b = c) {a : α} {b : β} :
    b ∈ PFun.ofGraph' r a ↔ a ~[r] b := by
  constructor
  · exact compare_of_mem_ofGraph'
  · exact mem_ofGraph'_of_compare h

theorem PFun.graph'_ofGraph' {β : Type*} {r : SetRel α β}
    (h : ∀ a b c, a ~[r] b → a ~[r] c → b = c) : (PFun.ofGraph' r).graph' = r := by
  ext ⟨a, b⟩
  rw [PFun.mem_graph'_iff, mem_ofGraph'_iff_compare h]

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

instance {β : Type*} : PartialOrder (α →. β) := PartialOrder.lift PFun.graph' PFun.graph'_injective

theorem PFun.le_iff {β : Type*} {f g : α →. β} :  f ≤ g ↔ f.graph' ≤ g.graph' := by rfl

theorem PFun.le_iff' {β : Type*} {f g : α →. β} :  f ≤ g ↔ ∀ (a : α), ∀ b ∈ f a, b ∈ g a := by
  rw [PFun.le_iff]
  unfold PFun.graph'
  simp only [setOf_subset_setOf, Prod.forall]

theorem PFun.Dom_mono {β : Type*} {f g : α →. β} (h : f ≤ g) : f.Dom ⊆ g.Dom := by
  unfold PFun.Dom --Part.Dom
  intro a ha
  simp only [mem_setOf_eq] at *
  rw [PFun.le_iff] at h
  unfold PFun.graph' at h
  simp only [setOf_subset_setOf, Prod.forall] at h
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
  sSup S := PFun.ofGraph' (sSup (PFun.graph' '' S))

theorem PFun.sSup_eq {β : Type*} {fs : Set (α →. β)} :
    sSup fs = ofGraph' (⋃ a ∈ fs, a.graph') := by
  unfold sSup instSupSetPFun
  simp only [sSup_eq_sUnion, sUnion_image]

theorem PFun.exists_mem_of_mem_sSup {β : Type*} {fs : Set (α →. β)} {a : α} {b : β}
  (ha : b ∈ sSup fs a) :
    ∃ f ∈ fs, b ∈ f a := by
  unfold sSup instSupSetPFun at ha
  simp only [sSup_eq_sUnion, sUnion_image] at ha
  have := compare_of_mem_ofGraph' ha
  simp at this
  assumption

theorem PFun.le_sSup {β : Type*} {fs : Set (α →. β)} (h : IsChain (· ≤ ·) fs) {f : (α →. β)}
  (hf : f ∈ fs) :
    f ≤ sSup fs := by
  rw [sSup_eq, le_iff, graph'_ofGraph']
  · exact subset_biUnion_of_mem hf
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

theorem PFun.mem_dom_of_mem {β : Type*} {f : α →. β} {a : α} {b : β} (h : b ∈ f a) : a ∈ f.Dom := by
  aesop

theorem PFun.exists_fn_of_fn_sSup {β : Type*} {fs : Set (α →. β)} (h : IsChain (· ≤ ·) fs) {a : α}
  (ha : a ∈ (sSup fs).Dom) :
    ∃ f ∈ fs, ∃ (haf : a ∈ f.Dom), (sSup fs).fn a ha = f.fn a haf := by
  rcases exists_mem_of_mem_sSup (fn_mem ha) with ⟨f, hf, hf'⟩
  use f, hf, mem_dom_of_mem hf'
  symm
  apply fn_apply_eq_fn_apply_of_le (le_sSup h hf)

open Classical in
/-- Gives the partial function sending `a` to `b` and agreeing with `f` otherwise. -/
noncomputable def PFun.insert {β : Type*} (f : α →. β) (a : α) (b : β) : α →. β :=
  fun x ↦ if x = a then b else f x

@[simp]
theorem PFun.Dom_insert {β : Type*} {f : α →. β} {a : α} {b : β} :
    (PFun.insert f a b).Dom = f.Dom.insert a := by
  unfold PFun.insert PFun.Dom Set.insert
  ext x
  simp only [Part.coe_some, mem_setOf_eq]
  split_ifs with hx <;> simp [hx]

theorem PFun.lt_insert {β : Type*} {f : α →. β} {a : α} {b : β} (ha : a ∉ f.Dom) :
    f ≤ PFun.insert f a b ∧ ¬PFun.insert f a b ≤ f := by
  unfold PFun.insert
  constructor
  · rw [PFun.le_iff']
    aesop
  · rw [PFun.le_iff', not_forall]
    use a
    aesop

theorem PFun.Prop_insert {β : Type*} {f : α →. β} {a : α} {b : β} {p : α → β → Prop}
  (hf : ∀ x, ∀ (hx : x ∈ f.Dom), p x (f.fn x hx)) (hb : p a b) :
    let g := PFun.insert f a b;
    ∀ x, ∀ (hx : x ∈ g.Dom), p x (g.fn x hx) := by
  intro g x hx
  unfold g PFun.insert
  simp only [Part.coe_some, PFun.fn_apply]
  split_ifs with hxa
  · simpa [hxa]
  · apply hf

/-- The property of a partial function `f` to be *monotone*, i.e. `f a ≤ f b` whenever `a ≤ b` and
both `a` and `b` are in the domain of `f`. -/
def PFun.Monotone [Preorder α] {β : Type*} [Preorder β] (f : α →. β) :=
  ∀ ⦃a b⦄ (ha : a ∈ f.Dom) (hb : b ∈ f.Dom), a ≤ b → f.fn a ha ≤ f.fn b hb

set_option linter.dupNamespace false in
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

--TODO: move
instance TopologicalSpace.SeparableSpace.subtype {X : Type*} [TopologicalSpace X] [SeparableSpace X]
    [PseudoMetrizableSpace X] {s : Set X} : SeparableSpace ↑s :=
  (IsSeparable.of_separableSpace s).separableSpace

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

protected theorem iInter_of_monotone_of_frequently
    {ι : Type*} [Preorder ι] [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α}
    (hsm : Monotone s) (hs : ∃ᶠ i in atBot, MeasurableSet (s i)) : MeasurableSet (⋂ i, s i) := by
  rcases exists_seq_forall_of_frequently hs with ⟨x, hx, hxm⟩
  rw [← hsm.iInter_comp_tendsto_atBot hx]
  exact .iInter hxm

protected theorem iInter_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α}
    (hsm : Monotone s) (hs : ∀ i, MeasurableSet (s i)) : MeasurableSet (⋂ i, s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ => exact MeasureTheory.NoAtoms'.iInter_of_monotone_of_frequently hsm <| .of_forall hs

theorem exists_measurable_sets_measure_eq :
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
        rcases PFun.exists_fn_of_fn_sSup hTs' hx with ⟨f, hf, hfx, h⟩
        rcases PFun.exists_fn_of_fn_sSup hTs' hy with ⟨g, hg, hgy, h'⟩
        have hfΓ := hTs hf
        unfold Γ at hfΓ
        have hgΓ := hTs hg
        unfold Γ at hgΓ
        simp only [mem_setOf_eq] at hfΓ hgΓ
        rw [h, h']
        by_cases! hfg : f = g
        · simp only [hfg]
          rw [hfg] at hfx
          exact hgΓ.1 _ _ hxy
        rcases hTs' hf hg hfg with h | h
        · rw [PFun.fn_apply_eq_fn_apply_of_le h hfx]
          exact hgΓ.1 _ _ hxy
        · rw [PFun.fn_apply_eq_fn_apply_of_le h hgy]
          exact hfΓ.1 _ _ hxy
      · intro x T hT
        rcases PFun.exists_fn_of_fn_sSup hTs' (PFun.mem_dom_of_mem hT) with ⟨f, hf, hfx, h⟩
        have hfΓ := hTs hf
        unfold Γ at hfΓ
        simp only [mem_setOf_eq] at hfΓ
        rw [h]
        use (hfΓ.2 x hfx).1, (hfΓ.2 x hfx).2
    · intro f hf
      apply PFun.le_sSup hTs' hf
  rcases this with ⟨S, hSΓ, S_maximal⟩
  unfold Γ at hSΓ
  simp only [mem_setOf_eq] at hSΓ
  have hμuniv : ⟨μ univ, self_mem_Iic⟩ ∈ S.Dom := by
    contrapose! S_maximal
    use PFun.insert S ⟨μ univ, self_mem_Iic⟩ univ
    constructor
    · unfold Γ
      constructor
      · apply PFun.Monotone.insert hSΓ.1
        · simp
        · intro x x_ge hx
          rw [le_antisymm x.2 x_ge] at hx
          contradiction
      exact PFun.Prop_insert (p := fun (t : Set.Iic (μ univ)) St ↦ MeasurableSet St ∧ μ St = t)
        hSΓ.2 ⟨MeasurableSet.univ, rfl⟩
    exact PFun.lt_insert S_maximal
  have S_total : ∀ x, x ∈ S.Dom := by
    intro x
    let s := ⋃ (y : S.Dom) (hyx : y ≤ x), S.fn y y.2
    let t := ⋂ (y : S.Dom) (hyx : y ≥ x), S.fn y y.2
    let s_helper := S.Dom ∩ (Set.Iic x)
    have s_eq : s = ⋃ (y : s_helper), S.fn y y.2.1 := by
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
    have mono_S : Monotone (fun y : s_helper ↦ S.fn y y.2.1) := by
      intro x y hxy
      apply hSΓ.1
      simpa
    have meas_s : MeasurableSet s := by
      rw [s_eq]
      apply MeasurableSet.iUnion_of_monotone mono_S
      intro y
      exact (hSΓ.2 y y.2.1).1
    let t_helper := S.Dom ∩ (Set.Ici x)
    have t_eq : t = ⋂ (y : t_helper), S.fn y y.2.1 := by
      unfold t
      apply le_antisymm
      · apply le_iInf
        intro y
        apply iInf_le_of_le ⟨y, y.2.1⟩
        apply iInf_le_of_le y.2.2
        rfl
      · apply le_iInf
        intro y
        apply le_iInf
        intro hyx
        apply iInf_le_of_le ⟨y, ⟨y.2, hyx⟩⟩
        rfl
    have mono_T : Monotone (fun y : t_helper ↦ S.fn y y.2.1) := by
      intro x y hxy
      apply hSΓ.1
      simpa
    have meas_t : MeasurableSet t := by
      rw [t_eq]
      apply MeasureTheory.NoAtoms'.iInter_of_monotone mono_T
      intro y
      exact (hSΓ.2 y y.2.1).1
    have hs : μ s ≤ x := by
      rw [s_eq]
      rw [Monotone.measure_iUnion mono_S]
      apply iSup_le
      intro y
      rw [(hSΓ.2 y y.2.1).2]
      exact y.2.2
    have μt : μ t = ⨅ y : t_helper, μ (S.fn y y.2.1) := by
      rw [t_eq]
      --TODO: the following should probably be put into some lemma
      by_cases h : ∃ i : t_helper, μ (S.fn i i.2.1) ≠ μ univ
      · rw [Monotone.measure_iInter mono_T]
        · intro y
          exact (hSΓ.2 y y.2.1).1.nullMeasurableSet
        rcases h with ⟨y, hy⟩
        use y
        have hy : μ (S.fn y y.2.1) < μ univ := lt_of_le_of_ne (measure_mono (subset_univ _)) hy
        rw [← lt_top_iff_ne_top]
        order
      · push Not at h
        convert Eq.refl (μ univ) using 1
        · have : t_helper = {⟨μ univ, self_mem_Iic⟩} := by
            ext y
            constructor
            · intro hy
              simp only [mem_singleton_iff]
              have := (hSΓ.2 y hy.1).2
              rw [h ⟨y, hy⟩] at this
              simp [this]
            · intro hy
              rw [hy]
              use hμuniv, x.2
          simp only [iInter_coe_set, this, mem_singleton_iff, iInter_iInter_eq_left]
          exact (hSΓ.2 _ _).2
        · have h' : Nonempty t_helper := by
            use ⟨μ univ, self_mem_Iic⟩, hμuniv, x.2
          simp_rw [h]
          simp
    have ht : x ≤ μ t := by
      rw [μt]
      apply le_iInf
      intro y
      rw [(hSΓ.2 y y.2.1).2]
      exact y.2.2
    have hst : μ t ≤ μ s := by
      contrapose! S_maximal
      obtain ⟨u, meas_u, su, ut, μsu, μut⟩ : ∃ u, MeasurableSet u ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t := by
        apply exists_measurable_between meas_s meas_t.nullMeasurableSet _ S_maximal
        rw [s_eq, t_eq]
        intro a
        simp only [mem_iUnion, mem_iInter, forall_exists_index]
        intro y hy z
        apply hSΓ.1 y.2.1 _ (y.2.2.trans z.2.2)
        exact hy
      use PFun.insert S ⟨μ u, measure_mono (subset_univ _)⟩ u
      constructor
      · constructor
        · apply PFun.Monotone.insert hSΓ.1
          · intro y hyu hy
            have hyx : y ≤ x := by
              contrapose! hyu
              have : y = ⟨y, y.2⟩ := rfl
              rw [this, Subtype.mk_lt_mk]
              rw [← (hSΓ.2 y hy).2]
              apply μut.trans_le
              apply measure_mono
              apply iInter_subset_of_subset ⟨y, hy⟩
              apply iInter_subset_of_subset (by simp [hyu.le])
              rfl
            apply su.trans'
            apply subset_iUnion_of_subset ⟨y, hy⟩
            apply subset_iUnion_of_subset (by simpa)
            rfl
          · intro y huy hy
            have hxy : x ≤ y := by
              contrapose! huy
              have : y = ⟨y, y.2⟩ := rfl
              rw [this, Subtype.mk_lt_mk]
              rw [← (hSΓ.2 y hy).2]
              apply μsu.trans_le'
              apply measure_mono
              apply subset_iUnion_of_subset ⟨y, hy⟩
              apply subset_iUnion_of_subset (by simp [huy.le])
              rfl
            apply ut.trans
            apply iInter_subset_of_subset ⟨y, hy⟩
            apply iInter_subset_of_subset (by simpa)
            rfl
        · apply PFun.Prop_insert (p := fun (t : Set.Iic (μ univ)) St ↦ MeasurableSet St ∧ μ St = t) hSΓ.2
          use meas_u
      apply PFun.lt_insert
      --main case
      rcases le_or_gt (μ u) x with hux | hux
      · contrapose! μsu
        rw [s_eq]
        rw [Monotone.measure_iUnion mono_S]
        apply le_iSup_of_le ⟨⟨μ u, _⟩, ⟨μsu, hux⟩⟩
        rw [(hSΓ.2 _ μsu).2]
      · contrapose! μut
        rw [μt]
        apply iInf_le_of_le ⟨⟨μ u, _⟩, ⟨μut, hux.le⟩⟩
        rw [(hSΓ.2 _ μut).2]
    have hs : μ s = x := le_antisymm hs (ht.trans hst)
    contrapose! S_maximal
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
      apply PFun.Prop_insert (p := fun (t : Set.Iic (μ univ)) St ↦ MeasurableSet St ∧ μ St = t) hSΓ.2
      use meas_s, hs
    · exact PFun.lt_insert S_maximal
  use fun x : Set.Iic (μ univ) ↦ S.fn x (S_total x)
  constructor
  · intro x y hxy
    exact hSΓ.1 _ _ hxy
  · intro x
    exact hSΓ.2 x (S_total x)

theorem exists_measurable_set_measure_eq {x : ENNReal} (ub : x ≤ μ univ) :
    ∃ s, MeasurableSet s ∧ μ s = x := by
  rcases exists_measurable_sets_measure_eq (μ := μ) with ⟨S, _, hS⟩
  use S ⟨x, ub⟩
  exact hS ⟨x, ub⟩

theorem exists_measurable_subset_measure_eq {t : Set α} (ht : NullMeasurableSet t μ)
  {x : ENNReal} (ub : x ≤ μ t) :
    ∃ s ⊆ t, MeasurableSet s ∧ μ s = x := by
  rcases ht.exists_measurable_subset_ae_eq with ⟨u, hut, hu, hut'⟩
  let ν : Measure u := μ.comap Subtype.val
  have ub' : x ≤ ν univ := by
    unfold ν
    apply (measure_subtype_coe_le_comap hu.nullMeasurableSet univ).trans'
    simpa [hut'.measure_eq]
  have na' : NoAtoms' ν := NoAtoms'.subtype hu
  rcases exists_measurable_set_measure_eq (μ := ν) ub' with ⟨r, meas_r, hrx⟩
  use r, hut.trans' (by simp), hu.subtype_image meas_r
  rwa [← comap_subtype_coe_apply hu]

theorem exists_measurable_between_measure_eq {s t : Set α} (hs : MeasurableSet s)
  (ht : NullMeasurableSet t μ) (h : s ⊆ t) {x : ENNReal} (lb : μ s ≤ x) (ub : x ≤ μ t) :
    ∃ u, MeasurableSet u ∧ s ⊆ u ∧ u ⊆ t ∧ μ u = x := by
  have : x - μ s ≤ μ (t \ s) := by
    calc _
      _ ≤ μ t - μ s := by
        gcongr
      _ ≤ _ := le_measure_sdiff
  rcases exists_measurable_subset_measure_eq (by measurability) this with ⟨v, hv, meas_v, hv'⟩
  use v ∪ s, by measurability, subset_union_right, by simp [h, subset_sdiff.mp hv]
  have : v \ s = v := by grind
  rw [← sdiff_union_self, measure_union disjoint_sdiff_left hs, this, hv']
  exact tsub_add_cancel_of_le lb

theorem exists_nullmeasurable_between_measure_eq {s t : Set α} (hs : NullMeasurableSet s μ)
  (ht : NullMeasurableSet t μ) (h : s ⊆ t) {x : ENNReal} (lb : μ s ≤ x) (ub : x ≤ μ t) :
    ∃ u, NullMeasurableSet u μ ∧ s ⊆ u ∧ u ⊆ t ∧ μ u = x := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨r, hrs, hr, hrs'⟩
  rw [← hrs'.measure_eq] at *
  rcases exists_measurable_between_measure_eq hr ht (hrs.trans h) lb ub with ⟨u, hu, hru, hut, hu'⟩
  use u ∪ s, hu.nullMeasurableSet.union hs, subset_union_right, union_subset hut h
  calc _
    _ = μ (u ∪ r) := by
      apply measure_congr
      exact eventuallyEq_of_mem hrs'.symm fun ⦃x⦄ ↦ congrArg (Or (x ∈ u))
    _ = μ u := by congr; simpa
    _ = x := hu'

end NoAtoms'

end MeasureTheory
