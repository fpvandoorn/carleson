import Mathlib.Data.Set.Card

namespace Set

variable {α : Type*}

lemma encard_subtype_le (P Q : α → Prop) :
    {x : Subtype P | Q ↑x}.encard ≤ {x | Q x}.encard :=
  Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, hx⟩, fun _ _ h ↦ by
    simpa [Subtype.coe_inj] using h⟩

end Set
