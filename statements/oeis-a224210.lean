import Mathlib

/-!
# A224210: Least prime p such that sum_{k=0}^n (k+1)^2*x^{n-k} is irreducible modulo p.

Source: https://oeis.org/A224210
Credit: @avivorly

A224210 (offset 1): `a(n)` is the least prime `p` such that the polynomial
`f_n(x) = sum_{k=0}^n (k+1)^2 x^(n-k) = x^n + 4 x^(n-1) + 9 x^(n-2) + ... + (n+1)^2`
is irreducible modulo `p`: 2, 11, 7, 17, 11, 3, 7, 97, 3, 89, 31, 113, ...

Conjecture (Zhi-Wei Sun, Apr 01 2013): `a(n)` does not exceed the `(4n-3)`-th prime for each `n > 0`.

Since `a(n)` is the least prime `p` such that `f_n` is irreducible modulo `p`, the inequality
`a(n) ≤ prime(4n-3)` says exactly that some prime `p ≤ prime(4n-3)` has `f_n` irreducible modulo `p`,
and the conjecture is stated in that form. The further conjectures that the entry lists after it
(for every `m > 1` and `n > 0`, `sum_{k=0}^n (k+1)^m x^(n-k)` is irreducible modulo some prime and has
Galois group `S_n` over the rationals; for `m, n ≥ 2` infinitely many bases `b > n^m` make the base-`b`
number with digits `n^m, ..., 2^m, 1^m` prime; the similar conjecture with `(2k+1)^m`) are separate
claims and are not part of this statement.

Conventions:
- `f n` has integer coefficients and leading coefficient 1. Irreducible modulo `p` means that its
  image in `(ZMod p)[X]` (coefficients reduced modulo `p`) is `Irreducible`.
- `prime(j)` is the `j`-th prime with `prime(1) = 2`, that is `Nat.nth Nat.Prime (j - 1)`; so
  `prime(4n-3)` is `Nat.nth Nat.Prime (4 * n - 4)`, an exact subtraction for `n ≥ 1`.
-/

namespace OMA.S_oeis_a224210

open Polynomial

/-- `f n = sum_{k=0}^n (k+1)^2 X^(n-k)`, a polynomial with integer coefficients. -/
noncomputable def f (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (((k + 1) ^ 2 : ℕ) : ℤ) * X ^ (n - k)

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ p : ℕ, p.Prime ∧ p ≤ Nat.nth Nat.Prime (4 * n - 4) ∧
        Irreducible ((f n).map (Int.castRingHom (ZMod p))) := by
  sorry

end OMA.S_oeis_a224210
