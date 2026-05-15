module

public import Mathlib.Analysis.Fourier.AddCircle
public import Carleson.ToMathlib.Topology.Instances.AddCircle.Defs

public section

theorem fourier_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {x : AddCircle p} {n : ℤ} :
    (fourier n) ((AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne') x) = (fourier n) x := by
  simp only [fourier_apply, SetLike.coe_eq_coe]
  rw [AddCircle.toCircle_zsmul, AddCircle.toCircle_zsmul]
  congr 1
  rw [AddCircle.equivAddCircle_eq]
  have : ↑↑((AddCircle.equivIco p 0) x) = x := AddCircle.coe_equivIco
  nth_rw 2 [← this]
  rw [AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk]
  congr 1
  field [hq.out.ne']

theorem fourierCoeff_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {f : AddCircle q → ℂ} {n : ℤ} :
    fourierCoeff (fun x ↦ f ((AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne') x)) n
      = fourierCoeff f n := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  simp_rw [← @fourier_comp_equivAddCircle p q, ← Pi.mul_apply]
  apply AddCircle.measurePreserving_equivAddCircle.integral_comp
    (AddCircle.homeomorphAddCircle _ _ _ _).measurableEmbedding
