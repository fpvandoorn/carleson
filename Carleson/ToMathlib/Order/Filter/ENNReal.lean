module

public import Mathlib.Order.Filter.ENNReal

--Upstreaming status: ready

public section

open ENNReal Filter

theorem ENNReal.limsup_mul_const_of_ne_top {α : Type*} {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞}
  (ha_top : a ≠ ⊤) :
    limsup (fun x ↦ u x * a) f = limsup u f * a := by
  simp_rw [mul_comm]
  exact limsup_const_mul_of_ne_top ha_top

theorem ENNReal.limsup_mul_const {α : Type*} {f : Filter α} [CountableInterFilter f] {u : α → ℝ≥0∞}
  {a : ℝ≥0∞} :
    limsup (fun x ↦ u x * a) f = limsup u f * a := by
  simp_rw [mul_comm, limsup_const_mul]
