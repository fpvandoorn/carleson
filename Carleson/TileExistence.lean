import Carleson.GridStructure

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]


def grid_existence : GridStructure X D κ S o :=
  sorry

def tile_existence [GridStructure X D κ S o] :
    TileStructure Q D κ S o :=
  sorry
