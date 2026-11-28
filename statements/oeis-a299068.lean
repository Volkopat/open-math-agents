import Mathlib

/-!
# A299068: Number of pairs of factors of n^2*(n^2-1) which differ by n.

Source: https://oeis.org/A299068
Credit: @ceejcake

Claim (OEIS A299068, comment of Robert Israel, Feb 04 2018): `For n > 7, a(n) >= 7`.
The comment lists seven such pairs: `(1, n+1)`, `(n, 2*n)`, `(2*n, 3*n)`,
`((n^2-n)/2, (n^2+n)/2)`, `(n^2-n, n^2)`, `(n^2, n^2+n)`, and `(3*n, 4*n)` if `n` is odd or
`(n/2, 3*n/2)` if `n` is even.

Formalization notes:
* The sequence has offset `2` (`n : ℕ`); the claim concerns `n > 7`.
* A pair of factors of `N = n^2 * (n^2 - 1)` that differ by `n` is a pair `(d, d + n)` of
  positive divisors of `N`; it is determined by its smaller element `d`. So `a n` counts the
  `d ∈ N.divisors` such that `d + n ∣ N`. For `n ≥ 2` we have `N ≠ 0`, so `N.divisors` is exactly
  the set of positive divisors of `N`.
* Only the first sentence of the comment is formalized here, not its remark that depends on
  Dickson's conjecture.
* Initial values for `n = 2, ..., 9`: `a(n) = 3, 4, 8, 7, 11, 6, 10, 12`.
-/

namespace OMA.S_oeis_a299068

/-- `a n` is the number of pairs `(d, d + n)` of positive divisors of `n^2 * (n^2 - 1)`. -/
def a (n : ℕ) : ℕ :=
  ((n ^ 2 * (n ^ 2 - 1)).divisors.filter (fun d => d + n ∣ n ^ 2 * (n ^ 2 - 1))).card

/-- OEIS A299068, comment of Robert Israel: for `n > 7`, `a(n) ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 < n → 7 ≤ a n := by
  sorry

end OMA.S_oeis_a299068
