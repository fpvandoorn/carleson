import Carleson.TileStructure
import Carleson.HardyLittlewood
import Carleson.Psi

noncomputable section

open scoped ENNReal NNReal ShortVariables

open GridStructure MeasureTheory Set

namespace Antichain

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

-- Lemma 6.3.1
lemma tile_reach {ϑ : Θ X} {N : ℕ} {p p' : 𝔓 X} (hp : dist_(p) (𝒬 p) ϑ ≤ 2^N)
    (hp' : dist_(p') (𝒬 p') ϑ ≤ 2^N) (hI : 𝓘 p ≤ 𝓘 p') (hs : 𝔰 p < 𝔰 p'):
  smul (2^(N + 2)) p ≤ smul (2^(N + 2)) p' := sorry

-- Def 6.3.15
def 𝔄_aux (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) : Finset (𝔓 X) :=
  {p ∈ 𝔄 | 1 + dist_(p) (𝒬 p) ϑ ∈ Icc (2^N) (2^(N+1))}

open Classical

-- Lemma 6.3.2
lemma stack_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) (L : Grid X) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L}), volume (E p ∩ G) ≤
      2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (coeGrid L) := sorry


-- Lemma 6.3.3
-- p' is 𝔭_ϑ in the blueprint
lemma local_antichain_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) {p' : 𝔓 X} (hp' : ϑ ∈ Ω p') :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝔰 p' < 𝔰 p}), volume (E p ∩ G ∩ 𝓘 p') ≤
      volume (E₂ (2 ^ (N + 3)) p') := by
  sorry

def C_6_3_4 (a N : ℕ) : ℝ≥0 := 2^(101*a^3 + N*a)

-- Lemma 6.3.4
lemma global_antichain_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) :
    ∑ (p ∈ 𝔄_aux 𝔄 ϑ N), volume (E p ∩ G) ≤
      (C_6_3_4 a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ (p ∈ 𝔄), coeGrid (𝓘 p)) := sorry

-- p in Lemma 6.1.6
private def p (a : ℕ) := 4 * a^2

def C_6_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (104 * a)

-- Lemma 6.1.6
-- Note: p' is introduced in the statement in the blueprint but not used. There may be a typo.
lemma tile_count {𝔄 𝔄' : Finset (𝔓 X)} (h_le : 𝔄' ⊆ 𝔄) (ϑ : Θ X) :
    eLpNorm (∑ 𝔭 ∈ 𝔄', (1 + dist_(𝔭) (𝒬 𝔭) ϑ) ^ ((-1 : ℝ)/(2*a^2 + a^3)) •
      ((E 𝔭).indicator 1) *  (G.indicator (1 : X → ℝ))) (p a) volume ≤
      (C_6_1_6 a) * dens₁ (𝔄 : Set (𝔓 X)) ^ ((1 : ℝ)/(p a)) *
        (volume (⋃ (p ∈ 𝔄), coeGrid (𝓘 p))) ^ ((1 : ℝ)/(p a)) := by
  sorry

end Antichain
