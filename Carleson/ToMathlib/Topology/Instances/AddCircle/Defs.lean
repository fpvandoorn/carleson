import Mathlib.Topology.Instances.AddCircle.Defs

-- Upstreaming status: seems ready to go; lemmas are usually analogues of existing mathlib lemmas
-- Sometimes, mathlib lemmas need to be renamed along with upstreaming this.

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

end AddCircle
