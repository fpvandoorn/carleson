module

public import Carleson.ToMathlib.BoundedCompactSupport

public section

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
