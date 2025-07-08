import Mathlib.Data.Set.Card

namespace Set

variable {α : Type*}

open Notation in
lemma encard_preimage_val_le_encard_left (P Q : Set α) : (P ↓∩ Q).encard ≤ P.encard :=
  (Function.Embedding.subtype _).encard_le

open Notation in
lemma encard_preimage_val_le_encard_right (P Q : Set α) : (P ↓∩ Q).encard ≤ Q.encard :=
  Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, hx⟩, fun _ _ h ↦ by
    simpa [Subtype.coe_inj] using h⟩

end Set
