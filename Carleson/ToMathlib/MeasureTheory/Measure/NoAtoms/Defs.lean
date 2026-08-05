/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/

module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measures having no atoms
-/

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- An *atom* of a measure `μ` is a set `s` of positive measure for which all measurable subsets
either have measure `0` or `μ s`. -/
@[expose]
def IsAtom (s : Set α) (μ : Measure α) :=
  0 < μ s ∧ ∀ t ⊆ s, MeasurableSet t → μ t = 0 ∨ μ t = μ s

/-- Measure `μ` *has no atoms* if for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class NoAtoms' (μ : Measure α) : Prop where
  no_atoms : ∀ s, MeasurableSet s → ¬ IsAtom s μ

export MeasureTheory.NoAtoms' (no_atoms)

theorem no_atoms_iff :
    NoAtoms' μ
      ↔ ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := by
  constructor
  · intro na s meas_s hs
    have := na.no_atoms
    unfold IsAtom at this
    push Not at this
    rcases this s meas_s hs with ⟨t, ts, meas_t, ht, ht'⟩
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at ht
    use t, ts, meas_t, ht, lt_of_le_of_ne (measure_mono ts) ht'
  · intro h
    apply NoAtoms'.mk
    intro s meas_s
    unfold IsAtom
    push Not
    intro hs
    rcases h s meas_s hs with ⟨t, ts, meas_t, ht, ht'⟩
    use t, ts, meas_t, ht.ne', ht'.ne

namespace NoAtoms'

theorem mk' {μ : Measure α}
  (h : ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s) :
    NoAtoms' μ := by
  rw [no_atoms_iff]
  intro s meas_s hs
  rcases h _ meas_s hs with ⟨t, hst, ht, hts⟩
  rcases exists_measurable_superset μ t with ⟨u, htu, hu, hut⟩
  use u ∩ s
  use inter_subset_right
  use hu.inter meas_s
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

variable [na : NoAtoms' μ]

theorem exists_measurable_subset_lt {s : Set α} (meas_s : MeasurableSet s) (hs : 0 < μ s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := no_atoms_iff.mp na s meas_s hs

theorem exists_measurable_subset_lt₀ {s : Set α} (meas_s : NullMeasurableSet s μ) (hs : 0 < μ s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := by
  rcases meas_s.exists_measurable_subset_ae_eq with ⟨r, hrs, hr, hrs'⟩
  rw [← hrs'.measure_eq] at *
  rcases exists_measurable_subset_lt hr hs with ⟨t, hts, ht⟩
  use t, hts.trans hrs

instance instNullSingletonClass [MeasurableSingletonClass (NullMeasurableSpace α μ)] :
    NullSingletonClass μ where
  measure_singleton := by
    intro x
    by_contra! hx
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at hx
    rcases exists_measurable_subset_lt₀ (nullMeasurableSet_singleton _) hx with ⟨t, htx, _, ht, ht'⟩
    rw [subset_singleton_iff_eq] at htx
    rcases htx with h | h
    · rw [h] at ht
      simp at ht
    · rw [h] at ht'
      simp at ht'

--TODO: Do we really need `SigmaFinite μ` or is `SFinite μ` sufficient?
instance instNullSingletonClass' [SigmaFinite μ] :
    NullSingletonClass μ where
  measure_singleton := by
    intro x
    by_contra! hx
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at hx
    set y := toMeasurable μ {x}
    rw [← measure_toMeasurable] at hx
    have : IsAtom y μ := by
      use hx
      intro t hty meas_t
      rw [← inter_eq_right.mpr hty, measure_toMeasurable_inter meas_t measure_singleton_lt_top.ne]
      by_cases hxt : x ∈ t
      · right
        rw [inter_eq_left.mpr (by simpa), measure_toMeasurable]
      · left
        rw [singleton_inter_eq_empty.mpr hxt, measure_empty]
    exact no_atoms _ (measurableSet_toMeasurable _ _) this

/- TODO: add sketch of counterexample(s) showing that we really need
   `MeasurableSingletonClass (NullMeasurableSpace α μ)` resp. `SigmaFinite μ`
-/

/-
instance instNullSingletonClass'' :
    NullSingletonClass μ where
  measure_singleton := by
    intro x
    by_contra! hx
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at hx
    set y := toMeasurable μ {x}
    rw [← measure_toMeasurable] at hx
    rcases exists_measurable_subset_lt (measurableSet_toMeasurable μ {x}) hx with
      ⟨s, hsx, meas_s, hs, hs'⟩
    rw [measure_toMeasurable] at hs'
    have : IsAtom s μ := by
      use hs
      intro t hts meas_t
      have hxs : x ∉ s := by
        by_contra!
        have : μ {x} < μ {x} := by
          calc μ {x}
            _ ≤ μ s := measure_mono (by simpa)
            _ < μ {x} := hs'
        simp at this
      sorry --TODO: not sure whether this is true
    exact no_atoms s meas_s this
-/

lemma restrict (s : Set α) (hs : NullMeasurableSet s μ) :
    NoAtoms' (μ.restrict s) := by
  apply NoAtoms'.mk'
  intro t meas_t ht
  rw [Measure.restrict_apply meas_t] at *
  rcases exists_measurable_subset_lt₀ (meas_t.nullMeasurableSet.inter hs) ht with
    ⟨r, hrts, meas_r, hr, hμrts⟩
  use r, (subset_inter_iff.mp hrts).1
  rw [Measure.restrict_apply meas_r, inter_eq_left.mpr (subset_inter_iff.mp hrts).2]
  use hr, hμrts

end NoAtoms'

end MeasureTheory
