import Mathlib

/-!
# OEIS A347063: doubling a double Zumkeller number

Source: https://oeis.org/A347063 (Ivan N. Ianakiev, OEIS Foundation, CC BY-SA 4.0)
Credit: @Medrov
-/

namespace OMA.S_oeis_a347063

/-- The positive divisors of `n > 0` split into two classes of equal size and equal sum.
    A subset `s` is the first class and its complement among the divisors is the second. -/
def IsDoubleZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ s ∈ n.divisors.powerset,
    s.card = (n.divisors \ s).card ∧ s.sum id = (n.divisors \ s).sum id

/-- The doubling conjecture for the terms of A347063. -/
theorem main : ∀ n : ℕ, IsDoubleZumkeller n → IsDoubleZumkeller (2 * n) := by
  sorry

end OMA.S_oeis_a347063
