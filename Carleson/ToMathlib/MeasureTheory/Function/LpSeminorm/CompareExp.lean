module

public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/- This file upgrades Hölder's inequality to use enorm. -/

--Upstreaming status: ready

public section

open ENNReal

namespace MeasureTheory

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [TopologicalSpace E] [ENormedAddCommMonoid E] [TopologicalSpace F] [ENormedAddCommMonoid F]
  [TopologicalSpace G] [ENormedAddCommMonoid G] {μ : Measure α}

open NNReal in
theorem MemLp.of_bilin' {p q r : ℝ≥0∞} {f : α → E} {g : α → F} (b : E → F → G) (c : ℝ≥0)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h : AEStronglyMeasurable (fun x ↦ b (f x) (g x)) μ)
    (hb : ∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ b (f x) (g x)) r μ := by
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm b c (fun _ _ ↦ h) hf.aestronglyMeasurable
    hg.aestronglyMeasurable hb (p := p) (q := q)).trans_lt
  finiteness [hf, hg]

end Bilinear

end MeasureTheory
