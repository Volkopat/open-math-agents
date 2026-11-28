import Mathlib

/-!
# Widths of inverse totient fibers (OEIS A196079)

Source: https://oeis.org/A196079
Credit: @etaubman

The entry lists the largest positive inverse minus the smallest, evaluated at
the positive totient values in increasing order (A002202). Quantifying over
all positive totient values removes the irrelevant enumeration.
-/

namespace OMA.S_oeis_a196079

def Carmichael : Prop :=
  ∀ x : ℕ, 0 < x → ∃ y : ℕ, 0 < y ∧ y ≠ x ∧ y.totient = x.totient

def fiber (t : ℕ) : Set ℕ := {x | 0 < x ∧ x.totient = t}

noncomputable def width (t : ℕ) : ℕ := sSup (fiber t) - sInf (fiber t)

theorem main : Carmichael → ∀ t : ℕ, (fiber t).Nonempty → 0 < width t := by
  sorry

end OMA.S_oeis_a196079
