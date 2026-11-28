import Mathlib

/-!
# A357561: a(n) = the numerator of ( Sum_{k = 1..n} (-1)^(n+k)*(1/k^3)*binomial(n,k)*binomial(n+k,k)^2 )

Source: https://oeis.org/A357561

Offset 0. The first terms are `0, 4, -27, 1367, -15625, 3129353, -14749, 308477847, ...`.
A comment of the entry defines, for every exponent `m`,
`S_m(n) = the numerator of Sum_{k = 1..n} (-1)^(n+k)*(1/k^m)*binomial(n,k)*binomial(n+k,k)^2`,
and says that the present sequence is the case `m = 3`, that is `a(n) = S_3(n)`.

The entry (Peter Bala, Oct 04 2022) makes two conjectural statements, stated here as a conjunction
in the order of the entry:

1. (comment) Conjecture: for odd `m >= 1`, `S_m(p-1) == 0 (mod p^4)` for all primes `p > m+4`.
2. (formula) Conjecture: `a(p-1) == 0 (mod p^4)` for `p = 5` and all primes `p >= 11`
   (checked up to `p = 499`).

Not part of the target: the remark `S_0(n) = -1 + A005258(n)` and the note that the Apery numbers
A005258 satisfy `B(p-1) == 1 (mod p^3)` for all primes `p >= 5` are quoted as known facts (Straub).
The example line `a(17 - 1) == 0 (mod 17^4)` is an instance of the second conjecture.

Formalized: `s m n` is the rational sum exactly as written in the entry, with `k` running over
`Finset.Icc 1 n`, that is `1 <= k <= n`, with `Nat.choose` for the binomial coefficients, the sign
`(-1)^(n+k)` and the factor `1/k^m` taken in the rationals. `S m n` is the integer `(s m n).num`,
the numerator of `s m n` in lowest terms with positive denominator (`Rat.num`), which is what Maple
`numer` returns. `a n` is `S 3 n`, which unfolds to the name line of the sequence. For `n = 0` the
sum is empty, `s m 0 = 0` and `(0 : ℚ).num = 0`, in agreement with `a(0) = 0`. The index `p - 1` is
a natural-number subtraction, harmless because a prime is at least 2. A congruence
`x == 0 (mod p^4)` is written as divisibility of `x` by `p ^ 4` in the integers.
Claim 1: `m` is a natural number with `Odd m`; an odd natural number is automatically at least 1,
so `m >= 1` needs no separate hypothesis; the range of primes is `m + 4 < p`.
Claim 2: the range `p = 5 and all primes p >= 11` is the disjunction `p = 5 ∨ 11 ≤ p` for a prime
`p`; the claim is false for `p = 7` (`a(6) = -14749 = -7^3 * 43`) and for `p = 2, 3`
(`a(1) = 4`, `a(2) = -27`). For `p >= 11` claim 2 is the case `m = 3` of claim 1 (`3 + 4 < p`);
the case `p = 5` (`a(4) = -15625 = -5^6`) is not covered by claim 1.
-/

namespace OMA.S_oeis_a357561

/-- The rational sum `s_m(n) = Sum_{k=1..n} (-1)^(n+k) * (1/k^m) * C(n,k) * C(n+k,k)^2`. -/
def s (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n + k) * (1 / (k : ℚ) ^ m) * (n.choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2

/-- `S_m(n)` of the entry: the numerator of `s_m(n)` in lowest terms. -/
def S (m n : ℕ) : ℤ := (s m n).num

/-- A357561: `a(n) = S_3(n)`, the numerator of
`Sum_{k=1..n} (-1)^(n+k) * (1/k^3) * C(n,k) * C(n+k,k)^2`. -/
def a (n : ℕ) : ℤ := S 3 n

/-- Bala's two conjectures: for odd `m` and every prime `p > m + 4`, `S_m(p-1) == 0 (mod p^4)`;
and `a(p-1) == 0 (mod p^4)` for `p = 5` and every prime `p >= 11`. -/
theorem main :
    (∀ m p : ℕ, Odd m → p.Prime → m + 4 < p → ((p : ℤ) ^ 4) ∣ S m (p - 1)) ∧
    (∀ p : ℕ, p.Prime → (p = 5 ∨ 11 ≤ p) → ((p : ℤ) ^ 4) ∣ a (p - 1)) := by
  sorry

end OMA.S_oeis_a357561
