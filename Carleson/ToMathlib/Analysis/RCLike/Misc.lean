module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Carleson.ToMathlib.ENorm

public section

namespace RCLike

open NNReal

theorem enorm_eq_enorm_embedRCLike {α : Type*} {𝕂 : Type*} [RCLike 𝕂] {f : α → ℝ≥0} (x : α) :
    ‖(⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) x‖ₑ = ‖f x‖ₑ := by
  rw [← ofReal_norm]
  simp

open Topology MeasureTheory in
theorem aestronglyMeasurable_iff_aestronglyMeasurable_embedRCLike {α : Type*}
  {m : MeasurableSpace α} {μ : Measure α} {𝕂 : Type*} [RCLike 𝕂] {f : α → ℝ≥0} :
    AEStronglyMeasurable (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) μ ↔ AEStronglyMeasurable f μ := by
  constructor
  · intro hf
    have comp_eq : (⇑(algebraMap ℝ 𝕂) ∘ toReal ∘ f) = fun x ↦ ⇑(algebraMap ℝ 𝕂) (f x).toReal := by
      ext x
      simp
    rw [comp_eq] at hf
    rwa [IsEmbedding.aestronglyMeasurable_comp_iff, IsEmbedding.aestronglyMeasurable_comp_iff] at hf
    · exact (Isometry.isEmbedding fun _ ↦ congrFun rfl)
    · exact (algebraMap_isometry ℝ 𝕂).isEmbedding
  · intro hf
    fun_prop

end RCLike
