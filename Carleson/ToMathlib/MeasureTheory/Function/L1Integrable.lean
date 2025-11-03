import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Carleson.ToMathlib.BoundedCompactSupport

-- Upstreaming status: both lemmas are useful, but need moving or comparing with other lemmas
-- Do upstream, but only after putting in that work.

open MeasureTheory Complex

variable {X : Type*} [MeasureSpace X]

open scoped ComplexConjugate

-- move to Function/L1/Integrable.lean
@[fun_prop]
lemma _root_.MeasureTheory.Integrable.conj {f : X → ℂ} (hf : Integrable f) :
    Integrable (fun x ↦ conj (f x)) :=
  Integrable.congr' hf (by fun_prop) (by simp)

-- TODO: compare with mul and conj in BoundedCompactSupport
@[fun_prop]
lemma _root_.MeasureTheory.Integrable.mul_conj [TopologicalSpace X] {f g : X → ℂ} (hf : Integrable f)
    (hf' : BoundedCompactSupport f) (hg : Integrable g) : Integrable (fun x ↦ f x * conj (g x)) := by
  apply Integrable.bdd_mul' hg.conj hf.1 (c := (eLpNormEssSup f volume).toReal)
  apply (ae_le_eLpNormEssSup (f := f) (μ := volume)).mono fun x hx ↦ ?_
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hf'.1.eLpNorm_ne_top).mp hx
