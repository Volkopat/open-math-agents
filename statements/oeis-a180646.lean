import Mathlib

/-!
# A180646: Numbers k such that 3 + phi(k)^3 is prime, where phi is Euler's totient function.

Source: https://oeis.org/A180646
Credit: @gblacher2

Comment in A180646 (Robert Israel, Mar 11 2020): "The generalized Bunyakovsky conjecture implies
that there are infinitely many primes in the sequence, i.e. primes p such that
(p-1)^3+3 = phi(p)^3+3 is prime (sequence A333199)."

Formalization notes:
* The statement is the conjectured conclusion: there are infinitely many primes `p` that belong
  to A180646, i.e. with `φ(p)^3 + 3` prime. We write `φ(p)` with Mathlib's `Nat.totient`;
  for a prime `p` it equals `p - 1`, which gives the form `(p-1)^3+3` of the comment.
* With this definition the primes `p ≤ 4523` with `φ(p)^3 + 3` prime are exactly the 54 data
  terms of A333199, and the numbers `k ≤ 255295` with `φ(k)^3 + 3` prime are exactly the 10000
  terms of the b-file of A180646 (computed directly).
-/

namespace OMA.S_oeis_a180646

/-- There are infinitely many primes `p` such that `3 + φ(p)^3 = (p - 1)^3 + 3` is prime. -/
theorem main : {p : ℕ | p.Prime ∧ (3 + Nat.totient p ^ 3).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a180646
