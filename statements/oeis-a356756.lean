import Mathlib

/-!
# OEIS A356756: m such that x^2 + x + m is prime for at least m/2 of x = 1..m

Source: https://oeis.org/A356756
Credit: @unserus

OEIS: "Furthermore, it is conjectured that the present sequence consists of only
15 terms (it has been checked by brute force that there are only 15 terms which
are smaller than 20000)."

The terms are the positive integers `m` such that `x^2 + x + m` is prime for at
least `m/2` values of `x ∈ {1, ..., m}`; "at least m/2" is written
`m ≤ 2 * count` to stay in `ℕ`. The conjecture is that the 15 listed terms are
the only ones.
-/

namespace OMA.S_oeis_a356756

/-- The number of `x ∈ {1, ..., m}` with `x^2 + x + m` prime. -/
def primeCount (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter fun x => (x ^ 2 + x + m).Prime).card

/-- The terms of A356756. -/
def a356756Set : Set ℕ := {m | 1 ≤ m ∧ m ≤ 2 * primeCount m}

/-- A356756 consists of exactly the 15 listed terms. -/
theorem main :
    a356756Set = {1, 5, 11, 17, 41, 47, 59, 67, 101, 107, 161, 221, 227, 347, 377} := by
  sorry

end OMA.S_oeis_a356756
