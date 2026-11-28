import Mathlib.Data.Fintype.BigOperators

/-!
# Counting factorizations of a fixed map

Source: Ben Deitmar, https://mathoverflow.net/questions/429021
Formalization: @YOHSUKE-TAKAHASHI

The source gives f : [a] → [b] and g : [b] → [c], so their composite is g ∘ f.
For a prescribed h, each choice of g contributes one independent choice of an
element of the appropriate fiber for every input of h. The exponent records
how many inputs have the same image.
-/

namespace OMA.S_mo_429021

theorem main : ∀ (a b c : ℕ) (h : Fin a → Fin c),
    Fintype.card {p : (Fin a → Fin b) × (Fin b → Fin c) // p.2 ∘ p.1 = h} =
      ∑ g : Fin b → Fin c, ∏ j : Fin c,
        (Fintype.card {y : Fin b // g y = j}) ^ (Fintype.card {x : Fin a // h x = j}) := by
  sorry

end OMA.S_mo_429021
