import Mathlib.Data.Real.ConjExponents

open scoped ENNReal

namespace ENNReal
namespace IsConjExponent

variable {p q : ℝ≥0∞} (h : p.HolderConjugate q)

section
include h

@[deprecated ENNReal.HolderConjugate.toReal]
protected alias toReal := ENNReal.HolderConjugate.toReal

end
end IsConjExponent
end ENNReal
