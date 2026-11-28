import Mathlib

/-!
# A078902: Generalized Fermat primes of the form (k+1)^2^m + k^2^m, with m>1.

Source: https://oeis.org/A078902
Credit: @luciusacarr

The entry's comment (T. D. Noe) asks "Is the set of generalized Fermat primes infinite?" and
records one conjecture: there are only a finite number of generalized Fermat primes for each
value of k. For k = 1 these are the Fermat primes A019434 (with m > 1: 17, 257, 65537).

Reading of the source:
* A generalized Fermat prime for `k` is a prime of the form `(k+1)^(2^m) + k^(2^m)` with `m > 1`,
  as in the sequence's definition; `^2^m` is read as `^(2^m)` (e.g. 17 = 2^4 + 1^4, 97 = 3^4 + 2^4).
* `k` ranges over the positive integers (`k = 0` gives the non-prime value `1`).
* For a fixed `k` the values are strictly increasing in `m`, so finitely many such primes for `k`
  is the same as finitely many exponents `m`; it is stated as finiteness of the set of `m > 1`
  giving a prime.
* The open question "is the set of generalized Fermat primes infinite?" is a question, not a
  conjecture, and is not stated.
-/

namespace OMA.S_oeis_a078902

theorem main :
    ∀ k : ℕ, 1 ≤ k → {m : ℕ | 1 < m ∧ ((k + 1) ^ (2 ^ m) + k ^ (2 ^ m)).Prime}.Finite := by
  sorry

end OMA.S_oeis_a078902
