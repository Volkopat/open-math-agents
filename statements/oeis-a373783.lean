import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic

/-!
# A recurrence for seating arrangements (OEIS A373783)

Seat at least one person in a line. If there are `k + 1` people, their
left-to-right labels form a permutation. The two end gaps have sizes `l, r ≤ 2`.
Of the `k` internal gaps, exactly `j` have three empty seats and the others
have two. Thus a choice of the `j` gaps and a permutation describes one seating
with `1 + 3*k + l + r + j` seats, and every seating determines these choices.

Source: https://oeis.org/A373783 (Enrique Navarrete; recurrence conjectured
by Pontus von Brömssen).
-/

namespace OMA.S_oeis_a373783

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1).factorial *
    (∑ l : Fin 3, ∑ r : Fin 3, ∑ j ∈ Finset.range (k + 1),
      if n = 1 + 3*k + l.val + r.val + j then k.choose j else 0)

theorem main : ∀ n : ℕ, 9 ≤ n →
    3 * (a n : ℤ) =
      -7 * (a (n-1) : ℤ) - 7 * (a (n-2) : ℤ) + ((n : ℤ)-2) * (a (n-3) : ℤ) +
      3 * ((n : ℤ)+1) * (a (n-4) : ℤ) + 4 * ((n : ℤ)-1) * (a (n-5) : ℤ) +
      3 * ((n : ℤ)-3) * (a (n-6) : ℤ) + ((n : ℤ)-4) * (a (n-7) : ℤ) := by
  sorry

end OMA.S_oeis_a373783
