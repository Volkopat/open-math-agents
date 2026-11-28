import Mathlib

/-!
# A142591: composite terms of A143578

Source: https://oeis.org/A142591
Credit: @avivorly

A143578 (name): A positive integer n is included if j+n/j divides k+n/k for every divisor k of n, where j is the
largest divisor of n that is <= sqrt(n).

A142591 (name): Composite terms in A143578.

Conjecture (Mohamed Bouhamida, Aug 17 2009, in the entry; comment edited by N. J. A. Sloane, Sep 01 2019):
This consists exactly of the semiprimes p*q for which p + q divides p*q + 1.

Conventions:
- A divisor of `n` is a positive divisor (`Nat.divisors n`); `n / d` is natural division, exact for a divisor `d`.
- For a natural number `d`, `d <= sqrt(n)` is read as `d * d ≤ n` (the same condition, as `d ≥ 0`).
- `j n` is the largest divisor `d` of `n` with `d * d ≤ n`, written as the supremum of that finite set; for `n ≥ 1`
  the set contains `1`, so the supremum is a member of it.
- Composite means `2 ≤ n` and not prime.
- A semiprime `p*q` has `p` and `q` prime, not assumed distinct. The condition `p + q ∣ p*q + 1` itself forces
  `p ≠ q` (for `p = q`, `2*p` does not divide `p^2 + 1`), so distinctness is not imposed.
-/

namespace OMA.S_oeis_a142591

/-- The largest divisor `d` of `n` with `d * d ≤ n` (that is, `d ≤ sqrt(n)`); for `n ≥ 1` the set holds `1`. -/
def j (n : ℕ) : ℕ := ((n.divisors).filter (fun d => d * d ≤ n)).sup id

/-- `n` is a term of A143578: `n` is positive and `j n + n / j n` divides `k + n / k` for every divisor `k`
of `n`. -/
def inA143578 (n : ℕ) : Prop :=
  0 < n ∧ ∀ k ∈ n.divisors, (j n + n / j n) ∣ (k + n / k)

theorem main :
    ∀ n : ℕ, (inA143578 n ∧ 2 ≤ n ∧ ¬ n.Prime) ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q ∧ (p + q) ∣ (p * q + 1) := by
  sorry

end OMA.S_oeis_a142591
