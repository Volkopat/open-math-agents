import Mathlib

/-!
# OEIS A262447: Primes p with pi(p^2) = pi(q^2) + pi(r^2) for distinct primes q, r

Source: https://oeis.org/A262447
Credit: @unserus

OEIS: "Conjecture: The sequence has infinitely many terms."

`pi(x)` is the prime-counting function, the number of primes `≤ x`
(`Nat.primeCounting`). The terms are the primes `p` for which there are distinct
primes `q`, `r` with `pi(p^2) = pi(q^2) + pi(r^2)`. The conjecture is that there
are infinitely many such `p`.
-/

namespace OMA.S_oeis_a262447

/-- The terms of A262447. -/
def a262447Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧
    Nat.primeCounting (p ^ 2) = Nat.primeCounting (q ^ 2) + Nat.primeCounting (r ^ 2)}

/-- A262447 is infinite. -/
theorem main : a262447Set.Infinite := by
  sorry

end OMA.S_oeis_a262447
