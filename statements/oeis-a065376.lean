import Mathlib

/-!
# A065376: Primes of the form p + k^2, p prime and k > 0.

Source: https://oeis.org/A065376
Credit: @EmircanEsen

Conjecture (Robert Israel, Sep 03 2014): The sequence contains all primes > 7549.

Formalization notes:
* A prime `q` is in the sequence when `q = p + k²` for some prime `p` and some `k > 0`.
* The conjecture: every prime `q > 7549` has such a representation. The bound is sharp: `7549`
  itself has none. Up to `2·10⁶` exactly 15 primes have none, the largest being `7549`.
-/

namespace OMA.S_oeis_a065376

/-- `q` is a term of A065376: a prime of the form `p + k²` with `p` prime and `k > 0`. -/
def IsTerm (q : ℕ) : Prop := q.Prime ∧ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ q = p + k ^ 2

/-- Every prime greater than `7549` is a term of A065376. -/
theorem main : ∀ q : ℕ, q.Prime → 7549 < q → IsTerm q := by
  sorry

end OMA.S_oeis_a065376
