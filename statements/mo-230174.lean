import Mathlib

/-!
# Odd perfect numbers with `q + 1 = σ(n)`

Source: https://mathoverflow.net/questions/230174
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: if `N = q n²` is an odd perfect number with Euler prime `q` and `gcd(q, n) = 1`, is it
possible to have `q + 1 = σ(n)`? The poster's heuristic (from the Descartes spoof) suggests that
one can prove `q + 1 ≠ σ(n)`; `main` states this, so a counterexample answers the question yes.

Conventions:
* `σ = ArithmeticFunction.sigma 1`; `N` is perfect iff `σ(N) = 2N` (`N > 0`).
* `q` is prime with `gcd(q, n) = 1` (the Euler prime appearing to the first power, as in the
  question). Euler's theorem forces such a `q` to be `≡ 1 (mod 4)`; that condition is not needed
  as a hypothesis.
-/

namespace OMA.S_mo_230174

open ArithmeticFunction

/-- No odd perfect number `N = q n²` with `q` prime and `gcd(q, n) = 1` has `q + 1 = σ(n)`. -/
theorem main : ∀ N q n : ℕ, 0 < N → Odd N → sigma 1 N = 2 * N → q.Prime → N = q * n ^ 2 →
    Nat.Coprime q n → q + 1 ≠ sigma 1 n := by
  sorry

end OMA.S_mo_230174
