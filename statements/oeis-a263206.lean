import Mathlib

/-!
# OEIS A263206: a prime with prime subscript between n^2 and (n+2)^2

Source: https://oeis.org/A263206
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A263206(n) is the number of primes `p` with `n² < prime(p) < (n+2)²`.

Conjecture: `a(n) > 0` for all `n > 0`. In other words, for each `n = 1, 2, 3, ...` the interval
`(n², (n+2)²)` contains a prime with prime subscript.

Formalization notes:
* `prime(p)` is the `p`-th prime (`prime(1) = 2`). For a prime `q`, `q = prime(p)` exactly when
  `p = π(q)` (`Nat.primeCounting`), so "a prime with prime subscript" is a prime `q` with `π(q)`
  prime. This avoids the 0-indexing of `Nat.nth Nat.Prime`.
-/

namespace OMA.S_oeis_a263206

/-- For each `n > 0`, some prime `q` with `n² < q < (n+2)²` has prime index `π(q)`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ q : ℕ, n ^ 2 < q ∧ q < (n + 2) ^ 2 ∧ q.Prime ∧
      (Nat.primeCounting q).Prime := by
  sorry

end OMA.S_oeis_a263206
