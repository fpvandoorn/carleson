module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

--Upstreaming status: ready

public section

open Real Set Filter MeasureTheory intervalIntegral

theorem not_integrableOn_Ioi_rpow' {a s : ℝ} (ha : 0 ≤ a) (hs : -1 ≤ s) :
    ¬IntegrableOn (fun (x : ℝ) ↦ x ^ s) (Ioi a) volume := by
  by_cases! a_zero : a = 0
  · rw [a_zero]
    exact not_integrableOn_Ioi_rpow s
  · rw [integrableOn_Ioi_rpow_iff (ha.lt_of_ne' a_zero)]
    simpa
