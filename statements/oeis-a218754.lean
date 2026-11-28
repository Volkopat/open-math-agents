import Mathlib

/-!
# A218754: Number of ways to write n=p+q(3+(-1)^n)/2 with q<=n/2 and p, q, p^2+3pq+q^2 all prime.

Source: https://oeis.org/A218754
Credit: @eltociear

`a(n)` (offset 1) counts the primes `q ≤ n/2` such that `p = n - c·q` and `p^2 + 3pq + q^2` are
prime, where `c` is `1` for even `n` and `2` for odd `n`. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n >= 1188,

and remarks that this is stronger than both Goldbach's conjecture (even `n = p + q`) and
Lemoine's conjecture (odd `n = p + 2q`).

Note for reviewers: the entry's name writes the factor as `(3+(-1)^n)/2`, which would give
`c = 2` for even `n`. The entry's own example (`a(72) = 1` from `72 = 67 + 5`), its data and its
Goldbach/Lemoine remark all use `c = 1` for even `n` and `c = 2` for odd `n`, i.e.
`(3-(-1)^n)/2`. Under the name's literal reading the data does not match (for example `a(5)`
would be `1` instead of `0`). `main` follows the data: with `c = (3-(-1)^n)/2`, a direct
computation reproduces the listed terms, its last zero is at `n = 1187`, and there are no zeros
in `[1188, 40000]`.
-/

namespace OMA.S_oeis_a218754

/-- The multiplier `(3 - (-1)^n)/2`: `1` for even `n`, `2` for odd `n`. -/
def c (n : ℕ) : ℕ := if Even n then 1 else 2

/-- The conjecture in OEIS A218754: for every `n ≥ 1188` there are primes `p`, `q` with
`n = p + c(n) q`, `q ≤ n/2` and `p^2 + 3pq + q^2` prime. -/
theorem main : ∀ n : ℕ, 1188 ≤ n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + c n * q ∧ 2 * q ≤ n ∧
      (p ^ 2 + 3 * p * q + q ^ 2).Prime := by
  sorry

end OMA.S_oeis_a218754
