import Mathlib

/-!
# A178612: no perfect squares among p^6 - 4p^4q + 4p^2q^2 + 4q^3

Source: https://oeis.org/A178612

A178612 (offset 1): the positive numbers of the form `p^6 - 4*p^4*q + 4*p^2*q^2 + 4*q^3` (and
`p*q <> 0`): 5, 20, 32, 41, 124, 133, 140, 160, 189, 224, 257, 265, …

Conjecture (Artur Jasinski, May 30 2010): there are no perfect squares in this sequence (in
spite of all numbers being congruent to 0 or 1 mod 4). The entry notes that if any perfect
square occurred in this sequence then a septic trinomial `x^7 + A*x^2 + B` with two irreducible
factors of degree 3 and 4 would exist.

Conventions:
- `p` and `q` range over the nonzero integers (`p*q <> 0`). The listed terms are reproduced with
  `q` allowed to be negative (for example `140` comes from `p = 2`, `q = -1`), and not with
  `p, q > 0` only.
- The sequence consists of the positive values of the form, so the statement is: whenever
  `p, q` are nonzero integers and the value is positive, it is not a perfect square in `ℤ`.
-/

namespace OMA.S_oeis_a178612

theorem main :
    ∀ p q : ℤ, p ≠ 0 → q ≠ 0 →
      0 < p ^ 6 - 4 * p ^ 4 * q + 4 * p ^ 2 * q ^ 2 + 4 * q ^ 3 →
      ¬ IsSquare (p ^ 6 - 4 * p ^ 4 * q + 4 * p ^ 2 * q ^ 2 + 4 * q ^ 3) := by
  sorry

end OMA.S_oeis_a178612
