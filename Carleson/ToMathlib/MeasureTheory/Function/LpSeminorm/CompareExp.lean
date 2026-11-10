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

section Prod

variable {ι α : Type*} {_ : MeasurableSpace α} {μ : Measure α} {f : ι → α → ℝ≥0∞}
  {p : ι → ℝ≥0∞} {s : Finset ι}

open Finset in
theorem eLpNorm_prod_le_ennreal {r : ℝ≥0∞} (hpr : ∑ i ∈ s, (p i)⁻¹ = r⁻¹) (hr : 0 < r) :
    eLpNorm (∏ i ∈ s, f i) r μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  induction s using cons_induction generalizing r with
  | empty =>
    rw [sum_empty, eq_comm, ENNReal.inv_eq_zero] at hpr
    rw [prod_empty, hpr, eLpNorm_exponent_top aestronglyMeasurable_one]
    exact eLpNormEssSup_le_of_ae_enorm_bound (by simp)
  | cons i s hi ih =>
    rw [sum_cons] at hpr
    have hs : ∑ j ∈ s, (p j)⁻¹ ≠ ∞ :=
      ne_top_of_le_ne_top (inv_ne_top.mpr hr.ne') (hpr ▸ le_add_self)
    rw [prod_cons, prod_cons]
    calc
      _ ≤ eLpNorm (f i) (p i) μ * eLpNorm (∏ j ∈ s, f j) (∑ j ∈ s, (p j)⁻¹)⁻¹ μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal_of_pos hr (hpqr := ⟨by simp [hpr]⟩)
      _ ≤ _ := by
        gcongr
        exact ih (inv_inv _).symm (ENNReal.inv_pos.mpr hs)

end Prod

end MeasureTheory
