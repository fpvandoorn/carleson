module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Fourier.AddCircle

public section

-- Upstreaming status: seems ready to go; lemmas are usually analogues of existing mathlib lemmas
-- Sometimes, mathlib lemmas need to be renamed along with upstreaming this.
-- The lemmas from the last section should maybe be distributed to different files

noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]

namespace AddCircle

section Periodic

variable [Archimedean 𝕜] {p : 𝕜} [hp : Fact (0 < p)] (a a' : 𝕜) {f : 𝕜 → B} (hf : f.Periodic p)
include hf

-- TODO: Rename `liftIco_coe_apply_of_periodic` and `liftIoc_coe_apply_of_periodic` along with
-- `liftIco_coe_apply` and `liftIoc_coe_apply` which are already in Mathlib

theorem liftIco_coe_apply_of_periodic (x : 𝕜) : liftIco p a f ↑x = f x := by
  rw [liftIco, equivIco, comp_apply, restrict_apply, QuotientAddGroup.equivIcoMod_coe]
  simp_rw [← self_sub_toIcoDiv_zsmul, hf.sub_zsmul_eq]

theorem liftIoc_coe_apply_of_periodic (x : 𝕜) : liftIoc p a f ↑x = f x := by
  rw [liftIoc, equivIoc, comp_apply, restrict_apply, QuotientAddGroup.equivIocMod_coe]
  simp_rw [← self_sub_toIocDiv_zsmul, hf.sub_zsmul_eq]

theorem liftIco_comp_mk_eq_of_periodic : liftIco p a f ∘ QuotientAddGroup.mk = f := by
  ext; apply liftIco_coe_apply_of_periodic a hf

theorem liftIoc_comp_mk_eq_of_periodic : liftIoc p a f ∘ QuotientAddGroup.mk = f := by
  ext; apply liftIoc_coe_apply_of_periodic a hf

/-- If `f` has period `p`, then every lift of `f` to `AddCircle p` is the same. -/
theorem liftIco_eq_liftIco : liftIco p a f = liftIco p a' f :=
  funext fun q ↦ QuotientAddGroup.induction_on q fun _ ↦ by
    simp_rw [liftIco_coe_apply_of_periodic _ hf]

/-- If `f` has period `p`, then every lift of `f` to `AddCircle p` is the same. -/
theorem liftIoc_eq_liftIoc : liftIoc p a f = liftIoc p a' f :=
  funext fun q ↦ QuotientAddGroup.induction_on q fun _ ↦ by
    simp_rw [liftIoc_coe_apply_of_periodic _ hf]

/-- If `f` has period `p`, then every lift of `f` to `AddCircle p` is the same. -/
theorem liftIco_eq_liftIoc : liftIco p a f = liftIoc p a' f :=
  funext fun q ↦ QuotientAddGroup.induction_on q fun _ ↦ by
    rw [liftIco_coe_apply_of_periodic _ hf, liftIoc_coe_apply_of_periodic _ hf]

end Periodic

section

variable {𝕜 : Type*} [Field 𝕜] {p q : 𝕜}

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma equivAddCircle_eq [Archimedean 𝕜] [hp : Fact (0 < p)] [hq : Fact (0 < q)] :
    (equivAddCircle p q hp.out.ne' hq.out.ne' : AddCircle p → AddCircle q)
      = fun x ↦ ((equivIco p 0 x).val * (p⁻¹ * q) : AddCircle q) := by
  ext x
  have : ↑↑((equivIco p 0) x) = x := coe_equivIco
  nth_rw 1 [← this, equivAddCircle_apply_mk]

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

lemma continuous_equivAddCircle [hp : Fact (0 < p)]
  [hq : Fact (0 < q)] :
    Continuous (⇑(AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne')) :=
  (homeomorphAddCircle _ _ _ _).2

lemma measurePreserving_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)] :
    MeasureTheory.MeasurePreserving (⇑(AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne'))
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  AddMonoidHom.measurePreserving continuous_equivAddCircle
    (equivAddCircle p q (hp.out.ne') (hq.out.ne')).surjective (by simp)

end

end AddCircle
