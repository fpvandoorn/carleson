import Mathlib.Data.Set.Finite.Lattice


variable {ι α : Type*}

namespace Set

/- These lemmas should be put just after `Finite.iUnion` -/

lemma finite_biUnion_iff_of_pairwiseDisjoint {f : ι → Set α} {s : Set ι}
    (hs : s.PairwiseDisjoint f) :
    Set.Finite (⋃ i ∈ s, f i)
      ↔ (∀ i ∈ s, Set.Finite (f i)) ∧ Set.Finite {i ∈ s | (f i).Nonempty} := by
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have : f i ⊆ ⋃ i ∈ s, f i := subset_biUnion_of_mem hi
      exact Finite.subset h this
    · let u : {i ∈ s | (f i).Nonempty} → ⋃ i ∈ s, f i := fun i ↦ ⟨i.2.2.choose, by
        have : i.2.2.choose ∈ f i := i.2.2.choose_spec
        simp only [mem_setOf_eq, mem_iUnion, exists_prop]
        exact ⟨i, i.2.1, this⟩⟩
      have u_inj : Function.Injective u := by
        rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
        simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
        by_contra h'ij
        have : Disjoint (f i) (f j) := hs hi.1 hj.1 h'ij
        have ui : (u ⟨i, hi⟩ : α) ∈ f i := hi.2.choose_spec
        rw [hij] at ui
        have uj : (u ⟨j, hj⟩ : α) ∈ f j := hj.2.choose_spec
        exact disjoint_left.1 this ui uj
      have : Finite (⋃ i ∈ s, f i) := h
      have : Finite {i ∈ s | (f i).Nonempty} := Finite.of_injective u u_inj
      exact this
  · rintro ⟨h, h'⟩
    have : ⋃ i ∈ s, f i = ⋃ i ∈ {i ∈ s | (f i).Nonempty}, f i := by
      ext; simp; tauto
    rw [this]
    apply Set.Finite.biUnion h'
    intro i hi
    exact h i hi.1

lemma finite_iUnion_iff_of_pairwiseDisjoint {f : ι → Set α} (hs : univ.PairwiseDisjoint f) :
    Set.Finite (⋃ i, f i) ↔ (∀ i, Set.Finite (f i)) ∧ Set.Finite {i | (f i).Nonempty} := by
  rw [← biUnion_univ, Set.finite_biUnion_iff_of_pairwiseDisjoint hs]
  simp

end Set
