import Mathlib.Topology.Instances.AddCircle.Defs

noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]

namespace AddCircle

section LinearOrderedAddCommGroup

variable [Archimedean 𝕜]
{p : 𝕜} [hp : Fact (0 < p)] {a : 𝕜}

-- Add after `liftIoc_coe_apply`
theorem liftIoc_eq_liftIco_of_ne (f : 𝕜 → B) {x : AddCircle p}
    (x_ne_a : x ≠ a) : liftIoc p a f x = liftIco p a f x := by
  let b := QuotientAddGroup.equivIcoMod hp.out a x
  have x_eq_b : x = ↑b := (QuotientAddGroup.equivIcoMod hp.out a).apply_eq_iff_eq_symm_apply.mp rfl
  rw [x_eq_b, liftIco_coe_apply b.coe_prop]
  exact liftIoc_coe_apply ⟨lt_of_le_of_ne b.coe_prop.1 (x_ne_a <| · ▸ x_eq_b), b.coe_prop.2.le⟩

end LinearOrderedAddCommGroup

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


/-- Ioc version of mathlib `coe_eq_coe_iff_of_mem_Ico` -/
lemma coe_eq_coe_iff_of_mem_Ioc {p : 𝕜} [hp : Fact (0 < p)]
    {a : 𝕜} [Archimedean 𝕜] {x y : 𝕜} (hx : x ∈ Set.Ioc a (a + p)) (hy : y ∈ Set.Ioc a (a + p)) : 
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Set.Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x, hx⟩, ← (equivIoc p a).right_inv ⟨y, hy⟩]
  exact h

/-- Ioc version of mathlib `eq_coe_Ico` -/
lemma eq_coe_Ioc {p : 𝕜} [hp : Fact (0 < p)] [Archimedean 𝕜]
    (a : AddCircle p) : ∃ b ∈ Set.Ioc 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩


end AddCircle
