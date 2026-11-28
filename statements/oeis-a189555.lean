import Mathlib

/-!
# OEIS A189555: n such that x' = n has exactly two solutions

Source: https://oeis.org/A189555
Credit: @unserus

OEIS: "Ufnarovski and Ahlander conjecture that this sequence, and any such
sequence that has numbers n such that x' = n has k solutions, is infinite."

`x'` is the arithmetic derivative (A003415): `0' = 1' = 0`, `p' = 1` for primes
`p`, and `(ab)' = a'b + ab'`; for `x ≥ 1`,
`x' = ∑_{p ∣ x} v_p(x) * (x / p)`, written with `Nat.primeFactors` and
`Nat.factorization`. The terms are the `n ≥ 1` with exactly two `x` such that
`x' = n`. (For `n ≥ 2` the solutions are finite, since a composite `x` has
`x' ≥ 2√x` and a prime has derivative 1; `Set.ncard` of an infinite set is 0,
so `n = 1`, with infinitely many solutions, is not a term.) The statement is the
conjecture for this sequence: it is infinite.
-/

namespace OMA.S_oeis_a189555

/-- The arithmetic derivative (A003415). -/
def arithDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- The terms of A189555: `n ≥ 1` with exactly two `x` such that `x' = n`. -/
def a189555Set : Set ℕ := {n | 1 ≤ n ∧ {x : ℕ | arithDeriv x = n}.ncard = 2}

/-- A189555 is infinite. -/
theorem main : a189555Set.Infinite := by
  sorry

end OMA.S_oeis_a189555
