import Mathlib

/-!
# A033932: Least positive m such that n! + m is prime

Source: https://oeis.org/A033932
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Amarnath Murthy, OEIS, 2004): no term is a composite number.

## Encoding

* `a n` is the least `m ≥ 1` with `n! + m` prime (it exists since there are infinitely many
  primes); the offset is `0`.
* "Composite" means `> 1` and not prime, so the statement is: every term is `1` or a prime.
* The second sentence of the same comment (a lower bound in terms of `prime(k)`) fails for the
  terms equal to `1` and is not stated here.
-/

namespace OMA.S_oeis_a033932

/-- `a n`: the least positive `m` such that `n! + m` is prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 ≤ m ∧ (n.factorial + m).Prime}

theorem main : ∀ n : ℕ, a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a033932
