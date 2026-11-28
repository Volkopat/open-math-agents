import Mathlib

/-!
# A218867: Number of prime pairs {p,q} with p>q and {p-4,q+4} also prime such that p+(1+(n mod 6))q=n if n is not congruent to 4 (mod 6), and p-q=n and q<n/2 if n=4 (mod 6).

Source: https://oeis.org/A218867
Credit: @eltociear

`a(n)` (offset 1) counts the pairs of primes `p > q` with `p - 4` and `q + 4` also prime such that
* `p + (1 + (n mod 6)) q = n`, if `n` is not congruent to `4` modulo `6`;
* `p - q = n` and `q < n/2`, if `n ≡ 4 (mod 6)`.

For example `a(20) = 1` from `20 = 11 + 3·3` and `a(28) = 1` from `28 = 41 - 13`. The entry
conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 50000 with n different from 50627, 61127, 66503.

`main` states that such a pair exists for each such `n`. `q < n/2` is written `2 * q < n`.
The natural-number subtraction `p - 4` is `0` when `p < 4`, and `0` is not prime, so it adds
nothing; `p - q` is exact since `p > q`.
-/

namespace OMA.S_oeis_a218867

/-- The pair `(p, q)` is counted by A218867 at `n`. -/
def Counted (n p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ q < p ∧ (p - 4).Prime ∧ (q + 4).Prime ∧
    (if n % 6 = 4 then p - q = n ∧ 2 * q < n else p + (1 + n % 6) * q = n)

/-- The conjecture in OEIS A218867: `a(n) > 0` for every `n > 50000` other than
`50627, 61127, 66503`. -/
theorem main : ∀ n : ℕ, 50000 < n → n ∉ ({50627, 61127, 66503} : Finset ℕ) →
    ∃ p q : ℕ, Counted n p q := by
  sorry

end OMA.S_oeis_a218867
