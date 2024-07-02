import Carleson.GridStructure
import Carleson.Psi
-- import Carleson.Proposition2
-- import Carleson.Proposition3

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
noncomputable section


open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

/-- Lemma 5.3.1 -/
lemma smul_mono {p p' : 𝔓 X} {m m' n n' : ℝ} (hp : smul n p ≤ smul m p')
    (hm : m' ≤ m) (hn : n ≤ n') : smul n' p ≤ smul m' p' := by
  change 𝓘 p ≤ 𝓘 p' ∧ ball_(p') (𝒬 p') m ⊆ ball_(p) (𝒬 p) n at hp
  change 𝓘 p ≤ 𝓘 p' ∧ ball_(p') (𝒬 p') m' ⊆ ball_(p) (𝒬 p) n'
  exact ⟨hp.1, (ball_subset_ball hm).trans (hp.2.trans (ball_subset_ball hn))⟩

/-- Lemma 5.3.2 -/
lemma smul_C2_1_2 {p p' : 𝔓 X} {m n : ℝ} (hp : 𝓘 p ≠ 𝓘 p') (hl : smul n p ≤ smul 1 p') :
    smul (n + C2_1_2 a * m) p ≤ smul m p' := by
  replace hp : 𝓘 p < 𝓘 p' := lt_of_le_of_ne hl.1 hp
  have : ball_(p') (𝒬 p') m ⊆ ball_(p) (𝒬 p) (n + C2_1_2 a * m) := fun x hx ↦ by
    rw [@mem_ball] at hx ⊢
    calc
      _ ≤ dist_(p) x (𝒬 p') + dist_(p) (𝒬 p') (𝒬 p) := dist_triangle ..
      _ ≤ C2_1_2 a * dist_(p') x (𝒬 p') + dist_(p) (𝒬 p') (𝒬 p) := by
        gcongr; exact Grid.dist_strictMono hp
      _ < C2_1_2 a * m + dist_(p) (𝒬 p') (𝒬 p) := by gcongr; rw [C2_1_2]; positivity
      _ < _ := by
        rw [add_comm]; gcongr
        exact mem_ball.mp <| mem_of_mem_of_subset (by convert mem_ball_self zero_lt_one) hl.2
  exact ⟨hl.1, this⟩

/- The constant used in Proposition 2.0.2 -/
def C2_0_2 (a : ℝ) (q : ℝ) : ℝ := 2 ^ (440 * a ^ 3) / (q - 1) ^ 5

lemma C2_0_2_pos : C2_0_2 a q > 0 := sorry

theorem discrete_carleson :
    ∃ G', Measurable G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ‖∫ x in G \ G', ∑' p, T p f x‖₊ ≤
    C2_0_2 a q * (volume.real G) ^ (1 - 1 / q) * (volume.real F) ^ (1 / q) := by sorry
