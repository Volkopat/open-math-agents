import Mathlib

/-!
# Non-trivial integer solutions to A^4 + B^4 + C^4 = 2 n^2 D^4

Source: https://mathoverflow.net/questions/506803
Credit: @Hyvok

Question (asked by Hisayasu Nakao on MathOverflow, January 2026): consider the Diophantine
equation `A^4 + B^4 + C^4 = 2 n^2 D^4` with `n` a square-free positive integer. An infinite
descent shows that there are no non-trivial solutions when `n` is divisible by `2`, `5` or `29`
(local obstructions; e.g. the fourth powers mod `29` are `0, 1, 7, 16, 20, 23, 24, 25`, and the
only three of them summing to `0` mod `29` are `0, 0, 0`). The asker found solutions, often
huge (the smallest for `n = 101` has over 40 digits), for many other `n` up to about `1000`, and
proposes:

Conjecture. Let `n` be a square-free integer with `gcd(n, 290) = 1`. Then the equation
`A^4 + B^4 + C^4 = 2 n^2 D^4` always has a non-trivial integer solution.

The asker asks (1) whether a counterexample is known and (2) whether the Brauer-Manin
obstruction is known to vanish for this family of diagonal quartic (K3) surfaces, and why the
smallest solutions are so large.

What the thread says. Comments (D. Loughran) point to M. Bright's thesis tables of Brauer groups
of diagonal quartic surfaces and note that very large smallest solutions are typical for such
surfaces, with no precise explanation beyond conjectural Manin-type heuristics. Seiji Tomita and
Oliver Couto gave polynomial solutions when `n = 3 p^2 + q^2`. An answer by Vepir supplies
solutions for the 88 values `n ≤ 1000` left unsolved on the asker's website (plus `n = 673`,
`8^4 + 21^4 + 29^4 = 2 * 673^2`), and states that all admissible `n ≤ 1000` are now solved
(we checked that all 88 listed solutions satisfy the equation exactly). The general statement
remains open (no local-global principle is known for these K3 surfaces).

## Formalization notes

* `n : ℕ` with `Squarefree n` (this excludes `n = 0`) and `Nat.Coprime n 290`
  (`290 = 2 * 5 * 29`); so `n` is a positive odd square-free integer prime to `5` and `29`.
* Non-trivial means `(A, B, C, D) ≠ (0, 0, 0, 0)`; over the integers this is equivalent to
  `D ≠ 0` (if `D = 0` then `A = B = C = 0`), which is what is stated. A solution with `D ≠ 0`
  gives a primitive one after dividing by the gcd, so primitivity is not imposed.
  For `n > 1` any such solution automatically has `A B C ≠ 0` (since `x^4 + y^4 = 2 z^2` has only
  solutions with `x^2 = y^2`, a classical result), so asking for all of `A, B, C` nonzero
  would only change the case `n = 1`, where `1^4 + 1^4 + 0^4 = 2 * 1^2 * 1^4`.
* Variables range over `ℤ`; signs are irrelevant since only fourth powers occur.
* Direction: the asker's conjecture (existence for every admissible `n`) is stated; all the
  computational evidence supports it. Our scratch search (all `0 ≤ A ≤ B ≤ C ≤ 6000`) finds
  solutions for 1479 of the 3266 admissible `n ≤ 10000` and none for inadmissible `n`, and a
  local check confirms that for odd primes `p < 400` the only local obstructions come from
  `p = 5, 29` dividing `n` (for larger `p` the Weil bounds give smooth local points). At `p = 2`,
  for odd `n` solubility depends only on `n^2 mod 16` (`1` or `9`), and both classes occur
  (`n = 1, 3`), so there is no further 2-adic obstruction.
-/

namespace OMA.S_mo_506803

/-- For every square-free `n` coprime to `290`, the equation `A^4 + B^4 + C^4 = 2 n^2 D^4` has
an integer solution with `D ≠ 0`. -/
theorem main : ∀ n : ℕ, Squarefree n → Nat.Coprime n 290 →
    ∃ A B C D : ℤ, D ≠ 0 ∧ A ^ 4 + B ^ 4 + C ^ 4 = 2 * (n : ℤ) ^ 2 * D ^ 4 := by
  sorry

end OMA.S_mo_506803
