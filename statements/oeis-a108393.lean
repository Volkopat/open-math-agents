import Mathlib

/-!
# A108393: a(n)=number of primes of the form p^2+k^2 with 2<=k<=floor(sqrt(2*p+1)) (less than (p+1)^2), for every p(n).

Source: https://oeis.org/A108393
Credit: @divmxnd0x

Conjecture (stated in A108393): 23, 83, 113 and 811 are the only primes with a 0 value in the
sequence: there is always a prime of the form `p^2 + k^2` between `p^2` and `(p+1)^2` for every
prime `p` other than 23, 83, 113 and 811.

Formalization notes:
* `k` ranges over the positive integers with `p^2 + k^2 < (p+1)^2`. (The name of the entry says
  `k ≥ 2`, but its data — e.g. `a(1) = 1` for `p = 2`, from `2^2 + 1^2 = 5` — and the statement of the
  conjecture count `k = 1` as well; with `k ≥ 1` the primes `p < 200000` without such a prime are
  exactly 23, 83, 113 and 811.)
-/

namespace OMA.S_oeis_a108393

/-- For every prime `p ∉ {23, 83, 113, 811}` there is `k ≥ 1` with `p^2 + k^2` prime and
`p^2 + k^2 < (p+1)^2`. -/
theorem main : ∀ p : ℕ, p.Prime → p ∉ ({23, 83, 113, 811} : Finset ℕ) →
    ∃ k : ℕ, 1 ≤ k ∧ (p ^ 2 + k ^ 2).Prime ∧ p ^ 2 + k ^ 2 < (p + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a108393
