import Mathlib

/-!
# A227908: Number of ways to write 2*n = p + q with p, q and (p-1)^2 + q^2 all prime.

Source: https://oeis.org/A227908
Credit: @eltociear

`a(n)` (offset 1) counts the ordered pairs of primes `(p, q)` with `p + q = 2n` and
`(p - 1)^2 + q^2` prime (the expression is not symmetric in `p` and `q`; for example
`a(7) = 1` from `14 = 11 + 3`, `10^2 + 3^2 = 109`). The entry conjectures:

  a(n) > 0 except for n = 1, 16, 292.

`main` states that for every `n ≥ 1` other than `1, 16, 292`, such a pair exists. Since `p` is
prime, `p ≥ 2` and the natural-number subtraction `p - 1` is exact.
-/

namespace OMA.S_oeis_a227908

/-- The conjecture in OEIS A227908: for every `n ≥ 1` other than `1, 16, 292`, `2n = p + q` with
`p`, `q` and `(p - 1)^2 + q^2` all prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ∉ ({1, 16, 292} : Finset ℕ) →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * n ∧ ((p - 1) ^ 2 + q ^ 2).Prime := by
  sorry

end OMA.S_oeis_a227908
-- ci: re-run check-proof
