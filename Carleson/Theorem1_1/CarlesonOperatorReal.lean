import Carleson.Theorem1_1.Hilbert_kernel

noncomputable section

def CarlesonOperatorReal (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r),
  ‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * Complex.exp (Complex.I * n * y)‖
/-
def CarlesonOperatorReal' (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  sSup {‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, K x y * f y * Complex.exp (Complex.I * n * y)‖ | (n : ℤ) (r : ℝ) (r > 0)}
-/

--TODO: maybe just change back to usual norm s.th. the only difference is the coercion to ENNReal
def CarlesonOperatorReal' (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (n : ℤ) (r : ℝ) (_ : 0 < r) (_ : r < 1),
  ↑‖∫ y in {y | dist x y ∈ Set.Ioo r 1}, f y * K x y * Complex.exp (Complex.I * n * y)‖₊

def CarlesonOperatorRat' (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (n : ℤ) (r : ℚ) (_ : 0 < r),
  ↑‖∫ y in {y | dist x y ∈ Set.Ioo (r : ℝ) 1}, f y * K x y * Complex.exp (Complex.I * n * y)‖₊

#check (fun x ↦ CarlesonOperatorReal' K _ x)


--TODO: is this needed?
lemma annulus_real_eq {x r R: ℝ} (r_nonneg : 0 ≤ r) : {y | dist x y ∈ Set.Ioo r R} = Set.Ioo (x - R) (x - r) ∪ Set.Ioo (x + r) (x + R) := by
  ext y
  simp only [Real.dist_eq, Set.mem_Ioo, lt_abs, neg_sub, abs_lt, neg_lt_sub_iff_lt_add,
    Set.mem_setOf_eq, Set.mem_union]
  constructor
  . rintro ⟨(h₀ | h₀), h₁, h₂⟩
    . left
      constructor <;> linarith
    . right
      constructor <;> linarith
  . rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    . constructor
      . left
        linarith
      . constructor <;> linarith
    . constructor
      . right
        linarith
      . constructor <;> linarith

lemma annulus_measurableSet {x r R : ℝ} : MeasurableSet {y | dist x y ∈ Set.Ioo r R} := measurableSet_preimage (Measurable.dist measurable_const measurable_id) measurableSet_Ioo

lemma CarlesonOperatorRat'_measurable {f : ℝ → ℂ} (hf : Measurable f) : Measurable (CarlesonOperatorRat' K f):= by
  --apply Measurable.iSup
  apply measurable_iSup
  intro n
  apply measurable_iSup
  intro r
  apply measurable_iSup
  intro hr
  apply Measurable.coe_nnreal_ennreal
  apply Measurable.nnnorm
  /-
  apply Measurable.integral
  have {x : ℝ} : ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo (↑r) 1}, f y * K x y * (Complex.I * ↑n * ↑y).exp =
      ∫ (y : ℝ) in {y | dist x y ∈ Set.Ioo (↑r) 1}, f y * K x y * (Complex.I * ↑n * ↑y).exp := by
    sorry
  conv =>
    pattern fun a ↦ _
    ext x
    rw [annulus_real_eq sorry, MeasureTheory.integral_union sorry sorry sorry sorry]
  -/
  sorry

local notation "T'" => CarlesonOperatorReal' K

lemma CarlesonOperatorReal'_measurable {f : ℝ → ℂ} (hf : Measurable f) : Measurable (T' f):= by
  --use (prove) that CarlesonOperatorRat' = CarlesonOperatorReal' ?
  sorry

theorem CarlesonOperatorReal'_mul {f : ℝ → ℂ} {x : ℝ} {a : ℝ} (ha : 0 < a) : T' f x = a.toNNReal * T' (fun x ↦ 1 / a * f x) x := by
  rw [CarlesonOperatorReal', CarlesonOperatorReal', ENNReal.mul_iSup]
  congr with n
  rw [ENNReal.mul_iSup]
  congr with r
  rw [ENNReal.mul_iSup]
  congr
  ext rpos
  rw [ENNReal.mul_iSup]
  congr
  ext rle1
  norm_cast
  --rw [← norm_toNNReal, ← norm_toNNReal]
  apply NNReal.eq
  simp only [coe_nnnorm, NNReal.coe_mul]
  rw [← Real.norm_of_nonneg (@NNReal.zero_le_coe a.toNNReal), ← Complex.norm_real, ← norm_mul,
    ← MeasureTheory.integral_mul_left, Real.coe_toNNReal a ha.le]
  congr with y
  field_simp
  rw [mul_div_cancel_left₀]
  norm_cast
  exact ha.ne.symm
