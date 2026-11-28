import Mathlib

/-!
# OEIS A262409: pi(x^3) + pi(y^3) = pi(z^3)

Source: https://oeis.org/A262409
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A262409 lists the positive integers `m` such that `π(m³) = π(j³) + π(k³)` for some
`0 < j ≤ k < m` (`π` the prime-counting function).

Conjecture: the Diophantine equation `π(x³) + π(y³) = π(z³)` with `0 < x ≤ y < z` has infinitely
many solutions.

Formalization notes:
* `π` is `Nat.primeCounting` (number of primes `≤ x`).
* "Infinitely many solutions" is stated as: the set of solution triples `(x, y, z)` is infinite.
-/

namespace OMA.S_oeis_a262409

/-- The equation `π(x³) + π(y³) = π(z³)` with `0 < x ≤ y < z` has infinitely many solutions. -/
theorem main :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2 ∧
      Nat.primeCounting (t.1 ^ 3) + Nat.primeCounting (t.2.1 ^ 3) =
        Nat.primeCounting (t.2.2 ^ 3)}.Infinite := by
  sorry

end OMA.S_oeis_a262409
