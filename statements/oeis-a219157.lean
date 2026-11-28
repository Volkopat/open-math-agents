import Mathlib

/-!
# A219157: Number of prime pairs {p,q} with p>q and p-2,q+2 also prime such that p+(1+mod(-n,6))q=n if n is not congruent to 2 mod 6, and p-q=n and q<n/2 if n=2 (mod 6).

Source: https://oeis.org/A219157
Credit: @eltociear

`a(n)` (offset 1) counts the pairs of primes `p > q` with `p - 2` and `q + 2` also prime such that
* `p + (1 + mod(-n, 6)) q = n`, if `n` is not congruent to `2` modulo `6`;
* `p - q = n` and `q < n/2`, if `n ≡ 2 (mod 6)`.

For example `a(16) = 1` from `16 = 7 + 3·3` and `a(26) = 1` from `26 = 31 - 5`. The entry
conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 30000 with n different from 38451, 46441, 50671, 62371.

`main` states that such a pair exists for each such `n`. `mod(-n, 6)` is the least nonnegative
residue of `-n` modulo `6`, which is `(6 - n % 6) % 6`. `q < n/2` is written `2 * q < n`.
Since `p > q ≥ 2`, the natural-number subtractions `p - 2` and `p - q` are exact.
-/

namespace OMA.S_oeis_a219157

/-- The pair `(p, q)` is counted by A219157 at `n`. -/
def Counted (n p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ q < p ∧ (p - 2).Prime ∧ (q + 2).Prime ∧
    (if n % 6 = 2 then p - q = n ∧ 2 * q < n else p + (1 + (6 - n % 6) % 6) * q = n)

/-- The conjecture in OEIS A219157: `a(n) > 0` for every `n > 30000` other than
`38451, 46441, 50671, 62371`. -/
theorem main : ∀ n : ℕ, 30000 < n → n ∉ ({38451, 46441, 50671, 62371} : Finset ℕ) →
    ∃ p q : ℕ, Counted n p q := by
  sorry

end OMA.S_oeis_a219157
