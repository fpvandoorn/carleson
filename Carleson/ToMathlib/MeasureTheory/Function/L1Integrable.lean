import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Carleson.ToMathlib.BoundedCompactSupport

open MeasureTheory Complex

variable {X : Type*} [MeasureSpace X]

open scoped ComplexConjugate

-- move to Function/L1/Integrable.lean
lemma _root_.MeasureTheory.Integrable.conj {f : X → ℂ} (hf : Integrable f) :
    Integrable (fun x ↦ conj (f x)) := by
  have := hf.1
  -- XXX: (by fun_prop) worked in Forests, but doesn't work here
  apply Integrable.congr' hf (Continuous.comp_aestronglyMeasurable continuous_conj this)
  filter_upwards with x
  exact (norm_conj (f x)).symm

-- TODO: compare with mul and conj in BoundedCompactSupport
@[fun_prop]
lemma _root_.MeasureTheory.Integrable.mul_conj [TopologicalSpace X] {f g : X → ℂ} (hf : Integrable f)
    (hf' : BoundedCompactSupport f) (hg : Integrable g) : Integrable (fun x ↦ f x * conj (g x)) := by
  apply Integrable.bdd_mul' hg.conj hf.1 (c := (eLpNormEssSup f volume).toReal)
  apply (ae_le_eLpNormEssSup (f := f) (μ := volume)).mono fun x hx ↦ ?_
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hf'.1.eLpNorm_ne_top).mp hx
