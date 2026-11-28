import Mathlib

/-!
# A052999: distance from `prime(n)` to the closest other prime with the same nonzero digits.

Source: https://oeis.org/A052999
Credit: @cjchaffin

For a prime `p`, let `P(p)` be the set of primes obtained by permuting the digits of `p`
and possibly adding or omitting zeros. Then `a(n) = |p-q|` where `p = prime(n)` and `q` is
the closest element of `P(p)` different from `p`, or `0` if no such `q` exists. Examples:
`prime(6) = 13` and `31`; `prime(9) = 23` and `2003`; `prime(23) = 83` and `8*10^31+3`.

Conjecture (Sean A. Irvine, Nov 23 2021): `a(n) > 0` for `n > 4`. Formalized as existence
of some different prime with the same nonzero decimal digits (zeros may be added or
omitted), not the least-distance part of the name.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`. Two numbers
have the same nonzero digits when their lists of nonzero base-10 digits are
permutations of each other.
-/

namespace OMA.S_oeis_a052999

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

def nonzeroDigits (n : ℕ) : List ℕ :=
  (Nat.digits 10 n).filter (fun d => d ≠ 0)

def sameNonzeroDigits (p q : ℕ) : Prop :=
  (nonzeroDigits p).Perm (nonzeroDigits q)

theorem main : ∀ n : ℕ, 4 < n →
    ∃ q : ℕ, q.Prime ∧ q ≠ prime n ∧ sameNonzeroDigits (prime n) q := by
  sorry

end OMA.S_oeis_a052999
