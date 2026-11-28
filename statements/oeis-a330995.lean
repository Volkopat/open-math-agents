import Mathlib

/-!
# A330995: when the number of strict partitions divides the number of partitions

Source: https://oeis.org/A330995

A330995 (Gus Wiseman), offset 0: a(n) is the denominator of P(n)/Q(n) = A000041(n)/A000009(n),
where P(n) counts the integer partitions of n and Q(n) the strict integer partitions of n.
Conjecture (in the entry): the only 1's occur at n = 0, 1, 2, 7.

Conventions:
* P(n) is `Fintype.card (Nat.Partition n)`; Q(n) is the number of partitions of n into distinct
  parts, `(Nat.Partition.distincts n).card` (Q(n) >= 1 for every n).
* The fraction is taken in `ℚ` and `Rat.den` reads the reduced denominator.
* "the only 1's occur at" is stated as an equivalence over all n >= 0, which matches the
  listed terms.
-/

namespace OMA.S_oeis_a330995

/-- A000041: the number of partitions of `n`. -/
def P (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- A000009: the number of partitions of `n` into distinct parts. -/
def Q (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- A330995: the reduced denominator of `P(n)/Q(n)`. -/
def a (n : ℕ) : ℕ := ((P n : ℚ) / Q n).den

/-- `a n = 1` exactly for `n = 0, 1, 2, 7`. -/
theorem main : ∀ n : ℕ, a n = 1 ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 7 := by
  sorry

end OMA.S_oeis_a330995
