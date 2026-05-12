module

public import Mathlib.MeasureTheory.Function.EssSup

--Upstreaming status: proofs might be shortened, otherwiseready

public section

open MeasureTheory ENNReal

lemma essSup_le_iSup {α : Type*} {β : Type*} {m : MeasurableSpace α} {μ : Measure α}
  [CompleteLattice β] {f : α → β} :
    essSup f μ ≤ ⨆ i, f i := by
  apply essSup_le_of_ae_le
  filter_upwards [] with i
  apply le_iSup

lemma iSup_le_essSup {α : Type*} {β : Type*} {m : MeasurableSpace α} {μ : Measure α}
  [CompleteLinearOrder β] {f : α → β} (h : ∀ ⦃x⦄, ∀ ⦃a⦄, a < f x → μ {y | a < f y} ≠ 0) :
    ⨆ x, f x ≤ essSup f μ := by
  apply iSup_le
  intro i
  rw [essSup_eq_sInf]
  apply le_sInf
  intro b hb
  simp only [Set.mem_setOf_eq] at hb
  apply le_of_forall_lt
  intro c hc
  have := h hc
  contrapose! this
  rw [← ENNReal.bot_eq_zero, ← le_bot_iff] at *
  apply le_trans _ hb
  apply measure_mono
  intro x
  simp only [Set.mem_setOf_eq]
  intro hc
  exact lt_of_le_of_lt this hc
