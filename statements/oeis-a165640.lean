import Mathlib

/-!
# OEIS A165640: Layman's floor formula for multisets of -2, 1 and 3 with sum 3

Source: https://oeis.org/A165640 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (John W. Layman, Sep 23 2009), offset 1: Number of distinct multisets of n integers, each of
which is -2, +1, or +3, such that the sum of the members of each multiset is 3. The formula
section states: Conjecture: a(n) = floor(4*(n+4)/5) - floor(2*(n+4)/3).

Formalization notes:
* A multiset of n integers, each -2, 1 or 3, is given by the multiplicities (x, y, z) of -2, 1 and
  3, with x + y + z = n, and its sum is -2x + y + 3z. a(n) is the number of such triples with sum
  3; each multiplicity is at most n, so the triples are taken in range (n + 1) cubed.
* The floors of quotients of natural numbers are natural-number divisions.
* Controls: the definitions give a(1..12) = 1, 0, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, as in the entry
  (the entry's example: a(6) = 2).
-/

namespace OMA.S_oeis_a165640

/-- The multiplicity triples `(x, y, z)` of `(-2, 1, 3)` with `n` members and sum 3. -/
def S (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t => t.1 + t.2.1 + t.2.2 = n ∧ (t.2.1 : ℤ) + 3 * t.2.2 - 2 * t.1 = 3)

/-- A165640(n): the number of such multisets. -/
def a (n : ℕ) : ℕ := (S n).card

/-- Layman's conjecture: a(n) = floor(4(n+4)/5) - floor(2(n+4)/3) for every n >= 1. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = ((4 * (n + 4) / 5 : ℕ) : ℤ) - ((2 * (n + 4) / 3 : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a165640
