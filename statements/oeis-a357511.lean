import Mathlib

/-!
# A357511: a(n) = numerator of Sum_{k = 1..n} (1/k) * binomial(n,k)^2 * binomial(n+k,k)^2 for n >= 1 with a(0) = 0

Source: https://oeis.org/A357511

`a(n)` is the numerator (in lowest terms) of the rational number
`s(n) = Sum_{k = 1..n} (1/k) * binomial(n,k)^2 * binomial(n+k,k)^2` for `n >= 1`, and `a(0) = 0`;
offset 0. The first terms are `0, 4, 54, 2182, 36625, 3591137, 25952409, 4220121443, ...`.

The entry (Peter Bala, Oct 01 2022) makes one conjectural statement, stated here:

  Conjecture: `a(p-1) == 0 (mod p^4)` for all primes `p >= 7` (checked up to `p = 499`).

The other formula line is not part of the target: the supercongruence `A(p-1) == 1 (mod p^3)` for
the Apery numbers A005259 is quoted as a known fact (Straub). The example line `a(13 - 1) == 0
(mod 13^4)` is an instance of the conjecture.

Formalized: `s n` is the rational sum exactly as in the name line, with `k` running over
`Finset.Icc 1 n`, that is `1 <= k <= n`, with `Nat.choose` for the binomial coefficients and the
factor `1/k` taken in the rationals. `a n` is the integer `(s n).num`, the numerator of `s n` in
lowest terms with positive denominator (`Rat.num`), which is what Maple `numer` and PARI
`numerator` return. For `n = 0` the sum is empty, `s 0 = 0` and `(0 : ℚ).num = 0`, which agrees
with the convention `a(0) = 0` of the entry, so no case distinction is needed. The index `p - 1` is
a natural-number subtraction, harmless because a prime is at least 2. The congruence
`a(p-1) == 0 (mod p^4)` is written as divisibility of `a (p - 1)` by `p ^ 4` in the integers. The
range is every prime `p` with `7 <= p`; the claim is false for `p = 5` (`a(4) = 36625 = 5^3 * 293`),
and also for `p = 2` and `p = 3` (`a(1) = 4`, `a(2) = 54`), which is why the entry starts at 7.
-/

namespace OMA.S_oeis_a357511

/-- The rational sum `s(n) = Sum_{k=1..n} (1/k) * C(n,k)^2 * C(n+k,k)^2`. -/
def s (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℚ)) * (n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2

/-- A357511: `a(n)` is the numerator of `s(n)` in lowest terms; `a(0) = 0` since `s(0) = 0`. -/
def a (n : ℕ) : ℤ := (s n).num

/-- Bala's conjecture: `a(p-1) == 0 (mod p^4)` for every prime `p >= 7`. -/
theorem main : ∀ p : ℕ, p.Prime → 7 ≤ p → ((p : ℤ) ^ 4) ∣ a (p - 1) := by
  sorry

end OMA.S_oeis_a357511
