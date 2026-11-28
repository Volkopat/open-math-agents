import Mathlib

/-!
# A287164: Primes having a unique partition into three squares.

Source: https://oeis.org/A287164
Credit: @keiichisince1986-bot

A287164 lists the primes that have exactly one partition into three squares:
`2, 3, 5, 11, 13, 19, 37, 43, 67, 163`.
The entry states: D. H. Lehmer conjectures that there are no more terms (see A094739 and
A094942).

Conventions:
- A partition of `n` into three squares is a way of writing `n = a^2 + b^2 + c^2` with
  `0 ≤ a ≤ b ≤ c`, so the order of the squares does not matter and zero squares are allowed, as
  in the data (`2 = 0 + 1 + 1`, `5 = 0 + 1 + 4`, `13 = 0 + 4 + 9`).
- `threeSquareReps n` is the finite set of such triples `(a, b, c)`. Each entry is at most `n`
  (since `a ≤ a^2 ≤ n`), so searching `a, b, c ∈ [0, n]` finds them all.
- No more terms means that the data list every term, so the conjecture says that the set of
  primes with exactly one such partition is exactly `{2, 3, 5, 11, 13, 19, 37, 43, 67, 163}`.
-/

namespace OMA.S_oeis_a287164

/-- The partitions of `n` into three squares, as triples `(a, b, c)` with `a ≤ b ≤ c`. -/
def threeSquareReps (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = n)

theorem main :
    {p : ℕ | p.Prime ∧ (threeSquareReps p).card = 1} =
      {2, 3, 5, 11, 13, 19, 37, 43, 67, 163} := by
  sorry

end OMA.S_oeis_a287164
