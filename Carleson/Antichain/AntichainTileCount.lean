import Carleson.TileStructure
import Carleson.HardyLittlewood
import Carleson.Psi

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ENNReal NNReal ShortVariables

open MeasureTheory Metric Set

namespace Antichain

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

-- Lemma 6.3.1
-- hp is eq. 6.3.1, hp' is eq. 6.3.2.
lemma tile_reach (ha : 4 ≤ a) {ϑ : Θ X} {N : ℕ} {p p' : 𝔓 X} (hp : dist_(p) (𝒬 p) ϑ ≤ 2^N)
    (hp' : dist_(p') (𝒬 p') ϑ ≤ 2^N) (hI : 𝓘 p ≤ 𝓘 p') (hs : 𝔰 p < 𝔰 p') :
    smul (2^(N + 2)) p ≤ smul (2^(N + 2)) p' := by
  -- 6.3.4
  have hp2 : dist_(p) ϑ (𝒬 p') ≤ 2^N := by
    rw [dist_comm]
    exact le_trans (Grid.dist_mono hI) hp'
  -- 6.3.5
  have hp'2 : dist_(p) (𝒬 p) (𝒬 p') ≤ 2^(N + 1) :=
    calc dist_(p) (𝒬 p) (𝒬 p')
      _ ≤ dist_(p) (𝒬 p) ϑ + dist_(p) ϑ (𝒬 p') := dist_triangle _ _ _
      _ ≤ 2^N + 2^N := add_le_add hp hp2
      _ = 2^(N + 1) := by ring
  -- Start proof of 6.3.3.
  simp only [TileLike.le_def, smul_fst, smul_snd]
  refine ⟨hI, fun o' ho' ↦ ?_⟩ -- o' is ϑ' in blueprint, ho' is 6.3.6.
  -- 6.3.7
  have hlt : dist_{𝔠 p', 8 * D^𝔰 p'} (𝒬 p') o' < 2^(5*a + N + 2) := by
    have hle : dist_{𝔠 p', 8 * D^𝔰 p'} (𝒬 p') o' ≤ (defaultA a) ^ 5 * dist_(p') (𝒬 p') o' := by
      have hpos : (0 : ℝ) < D^𝔰 p'/4 := by
        rw [div_eq_mul_one_div, mul_comm]
        apply mul_defaultD_pow_pos _ (by linarith)
      have h8 : (8 : ℝ) * D^𝔰 p' = 2^5 * (D^𝔰 p'/4) := by ring
      rw [h8]
      exact cdist_le_iterate hpos (𝒬 p') o' 5
    apply lt_of_le_of_lt hle
    simp only [defaultA, add_assoc]
    rw [pow_add, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm a, dist_comm]
    gcongr
    exact ho'
  -- 6.3.8
  have hin : 𝔠 p ∈ ball (𝔠 p') (4 * D^𝔰 p') := Grid_subset_ball (hI.1 Grid.c_mem_Grid)
  -- 6.3.9
  have hball_le : ball (𝔠 p) (4 * D^𝔰 p') ⊆ ball (𝔠 p') (8 * D^𝔰 p') := by
    intro x hx
    rw [mem_ball] at hx hin ⊢
    calc dist x (𝔠 p')
      _ ≤ dist x (𝔠 p)  + dist (𝔠 p) (𝔠 p') := dist_triangle _ _ _
      _ < 4 * ↑D ^ 𝔰 p' + 4 * ↑D ^ 𝔰 p' := add_lt_add hx hin
      _ = 8 * ↑D ^ 𝔰 p' := by ring
  -- 6.3.10
  have hlt2 : dist_{𝔠 p, 4 * D^𝔰 p'} (𝒬 p') o' < 2^(5*a + N + 2) :=
    lt_of_le_of_lt (cdist_mono hball_le) hlt
  -- 6.3.11
  have hlt3 : dist_{𝔠 p, 2^((2 : ℤ) - 5*a^2 - 2*a) * D^𝔰 p'} (𝒬 p') o' < 2^N := by
    have hle : 2 ^ ((5 : ℤ)*a + 2) * dist_{𝔠 p, 2^((2 : ℤ) - 5*a^2 - 2*a) * D^𝔰 p'} (𝒬 p') o' ≤
        dist_{𝔠 p, 4 * D^𝔰 p'} (𝒬 p') o' := by
      have heq : (defaultA a : ℝ) ^ ((5 : ℤ)*a + 2) * 2^((2 : ℤ) - 5*a^2 - 2*a) = 4 := by
        simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_mul]
        rw [← zpow_add₀ two_ne_zero]
        ring_nf
      rw [← heq, mul_assoc]
      exact le_cdist_iterate (by positivity) (𝒬 p') o' (5*a + 2)
    rw [← le_div_iff₀' (by positivity), div_eq_mul_inv, ← zpow_neg, neg_add, ← neg_mul,
      ← sub_eq_add_neg, mul_comm _ ((2 : ℝ) ^ _)] at hle
    calc dist_{𝔠 p, 2^((2 : ℤ) - 5*a^2 - 2*a) * D^𝔰 p'} (𝒬 p') o'
      _ ≤ 2^(-(5 : ℤ)*a - 2) * dist_{𝔠 p, 4 * D^𝔰 p'} (𝒬 p') o' := hle
      _ < 2^(-(5 : ℤ)*a - 2) * 2^(5*a + N + 2) := (mul_lt_mul_left (by positivity)).mpr hlt2
      _ = 2^N := by
        rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
        simp only [Int.reduceNeg, neg_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          sub_add_add_cancel, neg_add_cancel_left, zpow_natCast]
  -- 6.3.12
  have hp'3 : dist_(p) (𝒬 p') o' < 2^N := by
    apply lt_of_le_of_lt (cdist_mono _) hlt3
    gcongr
    rw [div_le_iff₀ (by positivity)]
    rw [mul_comm, ← mul_assoc]
    calc (D : ℝ) ^ 𝔰 p
      _ = 1 * (D : ℝ) ^ 𝔰 p := by rw [one_mul]
      _ ≤ 4 * 2 ^ (2 - 5 * (a : ℤ) ^ 2 - 2 * ↑a) * D * D ^ 𝔰 p := by
        have h4 : (4 : ℝ) = 2^(2 : ℤ) := by ring
        apply mul_le_mul _ (le_refl _) (by positivity) (by positivity)
        · have h12 : (1 : ℝ) ≤ 2 := one_le_two
          simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat]
          rw [h4, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
            ← zpow_zero (2 : ℝ)]
          rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
          gcongr --uses h12
          have : (2 : ℝ)^a = 2^(a : ℤ) := by rw [@zpow_natCast]
          ring_nf
          nlinarith
      _ = (4 * 2 ^ (2 - 5 * (a : ℤ)  ^ 2 - 2 * ↑a)) * (D * D ^ 𝔰 p) := by ring
      _ ≤ 4 * 2 ^ (2 - 5 * (a : ℤ)  ^ 2 - 2 * ↑a) * D ^ 𝔰 p' := by
        have h1D : 1 ≤ (D : ℝ) := one_le_D
        nth_rewrite 1 [mul_le_mul_left (by positivity), ← zpow_one (D : ℝ),
          ← zpow_add₀ (ne_of_gt (defaultD_pos _))]
        gcongr
        rw [add_comm]
        exact hs
  -- 6.3.13 (and 6.3.3.)
  have h34 : (3 : ℝ) < 4 := by linarith
  calc dist_(p) o' (𝒬 p)
    _ = dist_(p) (𝒬 p) o' := by rw [dist_comm]
    _ ≤ dist_(p) (𝒬 p) (𝒬 p') + dist_(p) (𝒬 p') o' := dist_triangle _ _ _
    _ < 2^(N + 1) + 2^N := add_lt_add_of_le_of_lt hp'2 hp'3
    _ < 2^(N + 2) := by ring_nf; gcongr -- uses h34
  -- 6.3.14 -- Not needed


-- Def 6.3.15
def 𝔄_aux (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) : Finset (𝔓 X) :=
  {p ∈ 𝔄 | 1 + dist_(p) (𝒬 p) ϑ ∈ Icc (2^N) (2^(N+1))}

open Classical

-- Lemma 6.3.2
lemma stack_density (𝔄 : Finset (𝔓 X)) (ϑ : Θ X) (N : ℕ) (L : Grid X) :
    ∑ (p ∈ {p ∈ (𝔄_aux 𝔄 ϑ N) | 𝓘 p = L}), volume (E p ∩ G) ≤
      2^(a * (N + 5)) * dens₁ (𝔄 : Set (𝔓 X)) * volume (L : Set X) := sorry


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
      (C_6_3_4 a N) * dens₁ (𝔄 : Set (𝔓 X)) * volume (⋃ (p ∈ 𝔄), (𝓘 p : Set X)) := sorry

-- p in Lemma 6.1.6
private def p (a : ℕ) := 4 * a^2

def C_6_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (104 * a)

-- Lemma 6.1.6
-- Note: p' is introduced in the statement in the blueprint but not used. There may be a typo.
lemma tile_count {𝔄 𝔄' : Finset (𝔓 X)} (h_le : 𝔄' ⊆ 𝔄) (ϑ : Θ X) :
    eLpNorm (∑ 𝔭 ∈ 𝔄', (1 + dist_(𝔭) (𝒬 𝔭) ϑ) ^ ((-1 : ℝ)/(2*a^2 + a^3)) •
      ((E 𝔭).indicator 1) *  (G.indicator (1 : X → ℝ))) (p a) volume ≤
      (C_6_1_6 a) * dens₁ (𝔄 : Set (𝔓 X)) ^ ((1 : ℝ)/(p a)) *
        (volume (⋃ (p ∈ 𝔄), (𝓘 p : Set X))) ^ ((1 : ℝ)/(p a)) := by
  sorry

end Antichain
