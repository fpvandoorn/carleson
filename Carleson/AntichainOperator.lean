import Carleson.GridStructure

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

open scoped GridStructure
open Set

-- Lemma 6.1.1
lemma E_disjoint (σ σ' : X → ℤ) {𝔄 : Set (𝔓 X)} (h𝔄 : IsAntichain (·≤·) 𝔄) {p p' : 𝔓 X}
    (hp : p ∈ 𝔄) (hp' : p' ∈ 𝔄) (hE : (E p ∩ E p').Nonempty) : p = p' := by
  set x := hE.some
  have hx := hE.some_mem
  simp only [E, mem_inter_iff, mem_setOf_eq] at hx
  wlog h𝔰 : 𝔰 p ≤ 𝔰 p'
  · have hE' : (E p' ∩ E p).Nonempty := by simp only [inter_comm, hE]
    exact eq_comm.mp (this σ σ' h𝔄 hp' hp hE' hE'.some_mem (le_of_lt (not_le.mp h𝔰)))
  obtain ⟨⟨hx𝓓p, hxΩp, _⟩ , hx𝓓p', hxΩp', _⟩ := hx
  have h𝓓 : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 p') :=
    (or_iff_left (not_disjoint_iff.mpr ⟨x, hx𝓓p, hx𝓓p'⟩)).mp (fundamental_dyadic h𝔰)
  have hΩ : Ω p' ≤ Ω p :=
    (or_iff_right (not_disjoint_iff.mpr ⟨Q x, hxΩp, hxΩp'⟩)).mp (relative_fundamental_dyadic h𝓓)
  have hle : p ≤ p' := ⟨h𝓓, hΩ⟩
  exact IsAntichain.eq h𝔄 hp hp' hle
