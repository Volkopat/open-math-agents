import Mathlib.Data.Nat.Basic

/-!
# Comparing OEIS A116944 and A068894

Vim Wenders's A116944 entry records that the proposed recurrence for Amarnath
Murthy's A068894 gives a different sequence. Both sequences start at index one
with value one. Index zero below is unused.

Sources: https://oeis.org/A116944 and https://oeis.org/A068894
Formalization: @VirtualMe64
-/

namespace OMA.S_oeis_a116944

/-- A116944 raises one more than the preceding term to the new index. -/
def recurrence : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (recurrence (n + 1) + 1) ^ (n + 2)

/-- A068894 uses bases starting at two, as in the entry's program and its
initial terms. For a positive previous term, its successor is congruent to one
modulo that term. It therefore suffices to search the smaller bases in order. -/
def leastBase (exponent previous : ℕ) : ℕ :=
  ((List.range' 2 (previous - 1)).find? fun base =>
    base ^ exponent % previous == 1 % previous).getD (previous + 1)

/-- A068894 takes the smallest nontrivial power of the given exponent
congruent to one modulo the preceding term. -/
def leastPower : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (leastBase (n + 2) (leastPower (n + 1))) ^ (n + 2)

theorem main : ∃ n : ℕ, 1 ≤ n ∧ recurrence n ≠ leastPower n := by
  sorry

end OMA.S_oeis_a116944
